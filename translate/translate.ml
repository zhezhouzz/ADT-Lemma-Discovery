open Parsetree;;
open Printf;;
open Utils;;
module Vc = Language.SpecAst;;
module E = Vc.E;;
module SE = E.SE;;
module T = Tp.Tp;;
module Helper = Language.Helper;;
module V = Pred.Value;;

module Impmap = struct
  (* hardcode the Polymorphic Variants! *)
  let handle f = try Some (f ()) with | _ -> None
  let reduce f =
    match f with
    | `StackIsEmpty f ->
      ("Customstk.is_empty", function
          | [V.L l] -> handle (fun () -> [V.B (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `StackPush f ->
      ("Customstk.push", function
          | [V.I x; V.L l] -> handle (fun () -> [V.L (f x l)])
          | _ -> raise @@ InterExn "bad prog")
    | `StackTop f ->
      ("Customstk.top", function
          | [V.L l] -> handle (fun () -> [V.I (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `StackTail f ->
      ("Customstk.tail", function
          | [V.L l] -> handle (fun () -> [V.L (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `Concat f ->
      ("concat", function
          | [V.L l1; V.L l2] -> handle (fun () -> [V.L (f l1 l2)])
          | _ -> raise @@ InterExn "bad prog")
    | `BankersqNil f ->
      ("Bankersq.nil", function
          | [] -> handle (fun () -> [V.L f])
          | _ -> raise @@ InterExn "bad prog")
    | `BankersqCons f ->
      ("Bankersq.cons", function
          | [V.I h; V.L t] -> handle (fun () -> [V.L (f h t)])
          | _ -> raise @@ InterExn "bad prog")
    | `BankersqLiblazy f ->
      ("Bankersq.liblazy", function
          | [V.L l] -> handle (fun () -> [V.L (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `BankersqLibforce f ->
        ("Bankersq.libforce", function
            | [V.L l] -> handle (fun () -> [V.L (f l)])
            | _ -> raise @@ InterExn "bad prog")
    | `BankersqReverse f ->
      ("Bankersq.reverse", function
          | [V.L l] -> handle (fun () -> [V.L (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `BankersqConcat f ->
      ("Bankersq.concat", function
          | [V.L l1; V.L l2] -> handle (fun () -> [V.L (f l1 l2)])
          | _ -> raise @@ InterExn "bad prog")
    | `Snoc func ->
      ("snoc", function
          | [V.I lenf; V.L f; V.I lenr; V.L r; V.I x;] ->
            let (lenf', f', lenr', r') = func lenf f lenr r x in
            handle (fun () -> [V.I lenf'; V.L f'; V.I lenr'; V.L r';])
          | _ -> raise @@ InterExn "bad prog")
    | _ -> raise @@ InterExn "unknown implementation"
  let l_to_map l =
    List.fold_left (fun m (name, f) ->
        StrMap.add name f m
      ) StrMap.empty (List.map reduce l)
end

let type_reduction = function
  | "Customstk.t" -> T.IntList
  | "Bankersq.t" -> T.IntList
  | "bool" -> T.Bool
  | _ -> T.Int

;;

type asst =
  | NoPre of string * Vc.spec
  | HasPre of string * Vc.spec * string * Vc.spec

let client_pre client_name = sprintf "%s_pre" client_name
let client_post client_name = sprintf "%s_post" client_name

let longident_to_string ld =
  let x =
    List.fold_left (fun res x ->
        match res with
        | None -> Some x
        | Some res -> Some (sprintf "%s.%s" res x)
      ) None (Longident.flatten ld)
  in
  match x with
  | None -> raise @@ InterExn "longident_to_string"
  | Some x -> x

let pattern_to_string pattern =
  match pattern.ppat_desc with
  | Ppat_var ident -> ident.txt
  | _ ->
    printf "pattern_to_string\n";
    Pprintast.pattern Format.std_formatter pattern;
    raise @@ InterExn "wrong pattern name, maybe untyped"

let pattern_to_typedvar pattern =
  let get_type tp =
    match tp.ptyp_desc with
    | Ptyp_var tp -> type_reduction tp
    | Ptyp_package _ -> raise @@ InterExn "package pattern type"
    | Ptyp_poly (_, _) -> raise @@ InterExn "poly pattern type"
    | Ptyp_extension _ -> raise @@ InterExn "extension pattern type"
    | Ptyp_class (_, _) -> raise @@ InterExn "class pattern type"
    | Ptyp_any -> raise @@ InterExn "any pattern type"
    | Ptyp_constr (const, tps) ->
      if List.length tps != 0 then raise @@ InterExn "not imp get_type" else
        type_reduction (longident_to_string const.txt)
    | _ -> raise @@ InterExn "wrong pattern type"
  in
  match pattern.ppat_desc with
  | Ppat_constraint (ident, tp) ->
    get_type tp, pattern_to_string ident
  | _ ->
    printf "pattern_to_typedvar\n";
    Pprintast.pattern Format.std_formatter pattern;
    raise @@ InterExn "wrong pattern name"

let parse_func_args expr =
  let rec aux args expr =
    match expr.pexp_desc with
    | Pexp_fun (_, _, arg, expr) ->
      aux (args @ [arg]) expr
    | _ -> (args, expr)
  in
  aux [] expr

let expr_to_name expr =
  match expr.pexp_desc with
  | Pexp_ident ld -> longident_to_string ld.txt
  | _ -> raise @@ InterExn "expr_to_name"

let expr_to_se env expr fmap =
  match expr.pexp_desc with
  | Pexp_ident ld ->
    let name = longident_to_string ld.txt in
    (match StrMap.find_opt env name with
     | None ->
       (match StrMap.find_opt fmap name with
        | Some (t1, t2) ->
          if List.length t1 == 0 && List.length t2 == 1
          then
            let tp = List.nth t2 0 in
            let se = SE.from_tpedvar (tp, T.universal_auto_name tp) in
            let c = Vc.SpecApply (name, [se]) in
            [c], se
          else raise @@ InterExn "expr_to_se wrong app"
        | _ -> raise @@ InterExn (sprintf "expr_to_se: untyped variable(%s)" name))
     | Some tp -> [], SE.Var (tp, name)
    )
  | Pexp_constant _ -> raise @@ InterExn "do not support complicate literal"
  | _ ->
    let _ = Pprintast.expression Format.std_formatter expr in
    raise @@ InterExn "expr_to_se"

let body_vc_gen client_name funcm init_tenv asst expr =
  let tps_to_ses = List.fold_left (fun r tp ->
      r @ [SE.from_tpedvar (tp, T.universal_auto_name tp)]) [] in
  let handle_let vb tenv =
    let leftvar = pattern_to_typedvar vb.pvb_pat in
    (* we ask all variables have unique name now. TODO: alpha renaming *)
    let tenv = match StrMap.find_opt tenv (snd leftvar) with
      | Some _ -> raise @@ InterExn "source code: unique name"
      | None -> StrMap.add (snd leftvar) (fst leftvar) tenv
    in
    [SE.from_tpedvar leftvar], vb.pvb_expr, tenv
  in
  let solve_function_name funcname funcm =
    match funcname with
    | "+" -> "intadd", [T.Int; T.Int], [T.Int]
    | "<=" -> "le", [T.Int; T.Int], [T.Bool]
    | _ ->
      let intps, outtps = StrMap.find (sprintf "map: body_vc_gen Pexp_apply(%s)" funcname) funcm funcname in
      funcname, intps, outtps
  in
  let rec aux expr target tenv =
    match expr.pexp_desc, target with
    | Pexp_tuple es, Some target ->
      if List.length target != List.length es
      then raise @@ InterExn "body_vc_gen: Tuple length does not macthed"
      else
        Vc.And (List.map (fun (e, target) -> aux e (Some [target]) tenv) (List.combine es target))
    | Pexp_tuple _, None -> raise @@ InterExn "body_vc_gen: Tuple"
    | Pexp_ident _, Some target ->
      if List.length target != 1 then raise @@ InterExn "body_vc_gen:Pexp_ident" else
        let c, arg1 = expr_to_se tenv expr funcm in
        let c' = Helper.poly_eq [arg1; List.nth target 0] in
        (match c with
         | [] -> c'
         | _ -> Vc.And (c @ [c']))
    | Pexp_ident _, None -> raise @@ InterExn "not imp body_vc_gen"
    | Pexp_constant (Pconst_integer (istr, None)), Some target ->
      Helper.poly_eq [List.nth target 0; SE.Literal (T.Int, SE.L.Int (int_of_string istr))]
    | Pexp_constraint (expr, _), target -> aux expr target tenv
    | Pexp_let (_, vbs, e), target ->
      let tenv, cs = List.fold_left (fun (tenv, cs) vb ->
          let new_target, let_body, tenv = handle_let vb tenv in
          tenv, cs @ [aux let_body (Some new_target) tenv]
        ) (tenv, []) vbs in
      Vc.And (cs @ [aux e target tenv])
    | Pexp_apply (func, args), target ->
      let funcname = expr_to_name func in
      let funcname, intps, outtps = solve_function_name funcname funcm in
      let to_se arg tp =
        match arg.pexp_desc with
        | Pexp_ident _ -> expr_to_se tenv arg funcm
        | Pexp_constant (Pconst_string ("true", None)) -> [], SE.Literal (T.Bool, SE.L.Bool true)
        | Pexp_constant (Pconst_string ("false", None)) -> [], SE.Literal (T.Bool, SE.L.Bool false)
        | Pexp_constant (Pconst_integer (istr, None)) -> [], SE.Literal (T.Int, SE.L.Int (int_of_string istr))
        | Pexp_constant _ -> failwith "source code: comlicate literal"
        | _ ->
          let nu = SE.from_tpedvar (tp, T.universal_auto_name tp) in
          [aux arg (Some [nu]) tenv], nu
      in
      let cs, args = List.split @@ List.map (fun ((_, arg), tp) -> to_se arg tp) (List.combine args intps) in
      let target = match target with
        | Some target -> target
        | None -> tps_to_ses outtps in
      let spec_c =
        if String.equal client_name funcname
        then
          match asst with
          | NoPre (postname, _) -> Vc.SpecApply (postname, args @ target)
          | HasPre (prename, _, postname, _) ->
            Vc.Implies (Vc.SpecApply (prename, args @ target),
                        Vc.SpecApply (postname, args @ target))
        else
          Vc.SpecApply (funcname, args @ target)
      in
      Vc.And ((List.flatten cs) @ [spec_c])
    | Pexp_ifthenelse (e1, e2, Some e3), target ->
      let bname = SE.from_tpedvar (T.Bool, T.universal_auto_name T.Bool) in
      let c1 =
        match aux e1 (Some [bname]) tenv with
        | Vc.And [c1] -> c1
        | _ -> raise @@ InterExn "parsing: wrong ite cond"
      in
      let c2 = aux e2 target tenv in
      let c3 = aux e3 target tenv in
      Vc.Ite (c1, c2, c3)
    | Pexp_ifthenelse (_, _, None), _ -> raise @@ InterExn "no else branch in ite"
    | _ -> raise @@ InterExn (sprintf "not imp body_vc_gen:%s" (Pprintast.string_of_expression expr))
  in
  let _, client_outtps = StrMap.find "map: body_vc_gen client_name" funcm client_name in
  let nus = tps_to_ses client_outtps in
  (* let _ = printf "nus:%s\n" (List.to_string SE.layout nus); raise @@ InterExn "end" in *)
  aux expr (Some nus) init_tenv, List.map SE.to_tpedvar nus

let structure_to_signagture struc =
  match struc.pstr_desc with
  | Pstr_modtype m ->
    let mname = m.pmtd_name.txt in
    (match m.pmtd_type with
     | Some mt ->
       (match mt.pmty_desc with
        | Pmty_signature signature ->
          mname, signature
        | _ -> raise @@ InterExn "not a struct")
     | _ -> raise @@ InterExn "not a struct")
  | _ -> raise @@ InterExn "not a struct"

let signame_concat signame name =
  match signame with
  | Some signame -> sprintf "%s.%s" signame name
  | None -> name

let solve_functype (signame, ct) =
  let rec parse_currying previous ct =
    match ct.ptyp_desc with
    | Ptyp_arrow (_, t1, t2) ->
      parse_currying (previous @ [t1]) t2
    | _ -> previous, ct
  in
  let argtps, rettp = parse_currying [] ct in
  let rec aux ct =
    match ct.ptyp_desc with
    | Ptyp_constr (tpc, cts) ->
      if not (List.length cts == 0)
      then
        raise @@ InterExn "solve_functype constr"
      else
        let name = longident_to_string tpc.txt in
        if (String.equal name "t")
        then
          [type_reduction (signame_concat signame "t")]
        else
          [type_reduction name]
    | Ptyp_tuple cts -> List.flatten @@ List.map aux cts
    | Ptyp_var tp -> [type_reduction tp]
    | Ptyp_arrow (_, _, _) -> raise @@ InterExn "solve_functype: function type"
    | _ -> raise @@ InterExn "solve_functype"
  in
  List.flatten @@ List.map aux argtps, aux rettp

let vd_to_tpedvars signame vd =
  let funcname = signame_concat signame vd.pval_name.txt in
  let tp = solve_functype (signame, vd.pval_type) in
  (* let () = printf "%s -> %s\n" (List.to_string T.layout (fst tp)) (List.to_string T.layout (snd tp)) in *)
  funcname, tp

let signature_to_functypes (signame, signature) =
  let aux (fnames, funcmapping) sig_item =
    match sig_item.psig_desc with
    | Psig_value vd ->
      let funcname, tp = vd_to_tpedvars (Some signame) vd in
      fnames @ [funcname], StrMap.add funcname tp funcmapping
    | Psig_type _ -> fnames, funcmapping
    | _ -> raise @@ InterExn "signature_to_functypes"
  in
  (signame, type_reduction (signame_concat (Some signame) "t")),
  List.fold_left aux ([], StrMap.empty) signature

let structure_to_vd struc =
  match struc.pstr_desc with
  | Pstr_primitive vd -> vd
  | _ -> raise @@ InterExn "structure_to_vd"

let layout_funcm funcm =
  StrMap.iter (fun name (argtps, rettp) ->
      printf "val %s(%s) => (%s)\n" name (List.to_string T.layout argtps) (List.to_string T.layout rettp)
    ) funcm

let parse_source asts =
  if List.length asts != 3 then
    raise @@ InterExn "source wrong format"
  else
    let signature = List.nth asts 0 in
    let clienttp = List.nth asts 1 in
    let client = List.nth asts 2 in
    let (signame, mtp), (fnames, funcm) = signature_to_functypes @@ structure_to_signagture signature in
    (* let _ =
     *   printf "solve_functype\n";
     *   Pprintast.core_type Format.std_formatter (structure_to_vd clienttp).pval_type;
     *   raise @@ InterExn "end" in *)
    let client_name, (intp, outtp) = vd_to_tpedvars None @@ structure_to_vd clienttp in
    let funcm = StrMap.add client_name (intp, outtp) funcm in
    (* let _ = layout_funcm funcm in *)
    client_name, (signame, mtp), fnames, funcm, (intp, outtp), client

let vcgen client_name funcm asst client =
  match client.pstr_desc with
  | Pstr_value (_, [value_binding]) ->
    let expr = value_binding.pvb_expr in
    (* let _ = Pprintast.expression ppf expr in *)
    let rawargs, body = parse_func_args expr in
    let rawargs = List.map pattern_to_typedvar rawargs in
    let tenv = List.fold_left (fun e (tp, name) ->
        StrMap.add name tp e
      ) StrMap.empty rawargs in
    (* let _ = List.map (fun arg ->
     *     printf "%s\n" (T.layouttvar (pattern_to_typedvar arg))
     *   ) args in
     * let _ = Pprintast.expression ppf body in *)
    let vc, nus = body_vc_gen client_name funcm tenv asst body in
    (* let _ = printf "body:=\n%s\n" (Vc.layout vc) in *)
    (rawargs, nus), vc
  | _ -> raise @@ InterExn "translate not a function value"

let known_preds mtp name =
  match mtp, name with
  | T.IntList, "mem" -> "list_member"
  | T.IntList, "hd" -> "list_head"
  | T.IntList, "ord" -> "list_order"
  | _, _ -> raise @@ InterExn "unknown preds"

let parse_propositional_term mtp tenv expr =
  let expr_to_se = fun x -> snd @@ expr_to_se tenv x StrMap.empty in
  let rec handle_logic func args =
    match func, args with
    | "implies", [e1; e2] -> E.Implies (aux e1, aux e2)
    | "iff", [e1; e2] -> E.Iff (aux e1, aux e2)
    | "&&", [e1; e2] -> E.And [aux e1; aux e2]
    | "||", [e1; e2] -> E.Or [aux e1; aux e2]
    | "not", [e1] -> E.Not (aux e1)
    | "==", [e1; e2] -> E.Atom (SE.Op (T.Int, "==", [expr_to_se e1; expr_to_se e2]))
    | "mem", [e1; e2] ->
      let p = known_preds mtp func in
      E.Atom (SE.Op (T.Bool, p, [expr_to_se e1; expr_to_se e2]))
    | "hd", [e1; e2] ->
      let p = known_preds mtp func in
      E.Atom (SE.Op (T.Bool, p, [expr_to_se e1; expr_to_se e2]))
    | "ord", [e1; e2; e3] ->
      let p = known_preds mtp func in
      E.Atom (SE.Op (T.Bool, p, [expr_to_se e1; expr_to_se e2; expr_to_se e3]))
    | _ -> raise @@ InterExn (sprintf "wrong assertion format: %s" func)
  and aux expr =
    match expr.pexp_desc with
    | Pexp_constant (Pconst_string ("true", None)) -> E.True
    | Pexp_constant (Pconst_string ("false", None)) -> E.Not E.True
    | Pexp_constant _ -> raise @@ InterExn "do not support complicate literal"
    | Pexp_apply (func, args) ->
      let funcname = expr_to_name func in
      handle_logic funcname (List.map snd args)
    | Pexp_construct (id, None) ->
      (match longident_to_string id.txt with
       | "true" -> E.True
       | "false" -> E.Not E.True
       | _ -> raise @@ InterExn "do not support complicate literal")
    | Pexp_construct (_, Some _) ->  raise @@ InterExn "Pexp_construct"
    | _ -> raise @@ InterExn "parse_propositional_term"
  in
  aux expr

let parse_assertion client_name mtp argtps asts =
  (* let ppf = Format.std_formatter in *)
  let get_preds p =
    match p.pstr_desc with
    | Pstr_value (_, [value_binding]) ->
      let expr = value_binding.pvb_expr in
      (match expr.pexp_desc with
       | Pexp_array es ->
         List.map (fun e ->
             match e.pexp_desc with
             | Pexp_constant (Pconst_string (c, None)) -> c
             | _ -> raise @@ InterExn "parse_assertion::get_preds"
           ) es
       | _ -> raise @@ InterExn "parse_assertion::get_preds")
    | _ -> raise @@ InterExn "parse_assertion::get_preds"
  in
  let get_assertion p =
    match p.pstr_desc with
    | Pstr_value (_, [value_binding]) ->
      let expr = value_binding.pvb_expr in
      (* let _ = Pprintast.expression ppf expr in *)
      let rawargs, body = parse_func_args expr in
      let rawargs = List.map pattern_to_typedvar rawargs in
      let tenv = List.fold_left (fun e (tp, name) ->
          StrMap.add name tp e
        ) StrMap.empty rawargs in
      (* let _ = printf "length argtps:%i\n" (List.length argtps); raise @@ InterExn "end" in *)
      let args = List.sublist rawargs (0, List.length argtps) in
      let qvs = List.sublist rawargs (List.length argtps, List.length rawargs) in
      (* let _ = printf "rawargs:%s\n" (List.to_string T.layouttvar rawargs) in
       * let _ = printf "args:%s\n" (List.to_string T.layouttvar args) in
       * let _ = printf "qvs:%s\n" (List.to_string T.layouttvar qvs) in *)
      let body = parse_propositional_term mtp tenv body in
      let spec = args, (qvs, body) in
      spec
    | _ -> raise @@ InterExn "translate not an assertion"
  in
  let preds, asst =
    if List.length asts == 3 then
      let preds = get_preds @@ List.nth asts 0 in
      let pre = get_assertion @@ List.nth asts 1 in
      let post = get_assertion @@ List.nth asts 2 in
      preds, HasPre (client_pre client_name, pre, client_post client_name, post)
    else if List.length asts == 2 then
      let preds = get_preds @@ List.nth asts 0 in
      let post = get_assertion @@ List.nth asts 1 in
      preds, NoPre (client_post client_name, post)
    else
      raise @@ InterExn "assertions wrong format"
  in
  let spectab =
    match asst with
    | NoPre (a, b) -> StrMap.add a b Helper.predefined_spec_tab
    | HasPre (a, b, c, d) ->
      StrMap.add a b @@ StrMap.add c d Helper.predefined_spec_tab
  in
  preds, asst, spectab

let make_holes funcnames funcmap imp_map =
  let aux funcname =
    let intps, outtps = StrMap.find "make_hole::funcmap" funcmap funcname in
    let argstp = intps @ outtps in
    let names = T.auto_name argstp in
    let imp = StrMap.find (sprintf "make_hole::imp_map(%s)" funcname) imp_map funcname in
    let open Helper in
    let hole = {name = funcname; args = List.combine argstp names} in
    (hole, imp)
  in
  List.map aux funcnames

let trans (source, assertion) =
  let client_name, (signame, mtp), fnames, funcm, (intp, outtp), client = parse_source source in
  (* let _ = printf "%s\n" (List.to_string T.layout intp) in
   * let _ = printf "%s\n" (List.to_string T.layout outtp) in
   * let _ = raise @@ InterExn "end" in *)
  let imp_map = Impmap.l_to_map (Imps.find signame) in
  let preds, asst, spectab = parse_assertion client_name mtp (intp @ outtp) assertion in
  let (uinputs, uoutputs), vc = vcgen client_name funcm asst client in
  (* let _ = printf "vc:%s\n" (Vc.layout vc); raise @@ InterExn "end" in *)
  let preds = List.map (fun p -> known_preds mtp p) preds in
  let holes = make_holes fnames funcm imp_map in
  let uvars = Vc.get_uvars vc in
  (* let _ = printf "%s\n" (List.to_string T.layouttvar uvars); raise @@ InterExn "end" in *)
  (* let _ = printf "%s\n" (List.to_string T.layouttvar uinputs) in
   * let _ = printf "%s\n" (List.to_string T.layouttvar uoutputs) in
   * let _ = raise @@ InterExn "end" in *)
  let open Inference.SpecAbduction in
  let mii =
    let args = List.map SE.from_tpedvar (uinputs @ uoutputs) in
    let upost =
      match asst with
      | NoPre (postname, _) -> Vc.SpecApply(postname, args)
      | HasPre (prename, _, postname, _) ->
        Vc.Implies (Vc.SpecApply(prename, args),
                    Vc.SpecApply(postname, args))
    in
    { upost = upost;
      uvars = uvars;
      uinputs = uinputs;
      uoutputs = uoutputs;
      uprog = StrMap.find "trans::imp_map" imp_map client_name
    }
  in
  (* let _ = printf "preds:%s\n" (StrList.to_string preds); raise @@ InterExn "end" in *)
  (* let _ = printf "holes:%s\n" (List.to_string (fun (h, _) ->
   *     h.Helper.name
   *   ) holes); raise @@ InterExn "end" in *)
  mii, vc, holes, preds, spectab
