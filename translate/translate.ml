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
  let reduce f =
    match f with
    | `StackIsEmpty f ->
      ("Customstk.is_empty", function
          | [V.L l] ->
            (try Some [V.B (f l)] with
             | _ -> None)
          | _ -> raise @@ InterExn "bad prog"
      )
    | `StackPush f ->
      ("Customstk.push", function
          | [V.I x; V.L l] ->
            (try Some [V.L (f x l)] with
             | _ -> None)
          | _ -> raise @@ InterExn "bad prog"
      )
    | `StackTop f ->
      ("Customstk.top", function
          | [V.L l] ->
            (try Some [V.I (f l)] with
             | _ -> None)
          | _ -> raise @@ InterExn "bad prog"
      )
    | `StackTail f ->
      ("Customstk.tail", function
          | [V.L l] ->
            (try Some [V.L (f l)] with
             | _ -> None)
          | _ -> raise @@ InterExn "bad prog"
      )
    | `Concat f ->
      ("concat", function
          | [V.L l1; V.L l2] ->
            (try Some [V.L (f l1 l2)] with
             | _ -> None
            )
          | _ -> raise @@ InterExn "bad prog"
      )
    | _ -> raise @@ InterExn "unknown implementation"
  let l_to_map l =
    List.fold_left (fun m (name, f) ->
        StrMap.add name f m
      ) StrMap.empty (List.map reduce l)
end

let client_pre client_name = sprintf "%s_pre" client_name
let client_post client_name = sprintf "%s_post" client_name

let type_reduction = function
  | "Customstk.t" -> T.IntList
  | "bool" -> T.Bool
  | _ -> T.Int

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

let patten_to_string pattern =
  match pattern.ppat_desc with
  | Ppat_var ident -> ident.txt
  | _ -> raise @@ InterExn "wrong patten name"

let patten_to_typedvar patten =
  let get_type tp =
    match tp.ptyp_desc with
    | Ptyp_var tp -> type_reduction tp
    | Ptyp_package _ -> raise @@ InterExn "package patten type"
    | Ptyp_poly (_, _) -> raise @@ InterExn "poly patten type"
    | Ptyp_extension _ -> raise @@ InterExn "extension patten type"
    | Ptyp_class (_, _) -> raise @@ InterExn "class patten type"
    | Ptyp_any -> raise @@ InterExn "any patten type"
    | Ptyp_constr (const, tps) ->
      if List.length tps != 0 then raise @@ InterExn "not imp get_type" else
        type_reduction (longident_to_string const.txt)
    | _ -> raise @@ InterExn "wrong patten type"
  in
  match patten.ppat_desc with
  | Ppat_constraint (ident, tp) ->
    get_type tp, patten_to_string ident
  | _ -> raise @@ InterExn "wrong patten name"

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

let expr_to_se env expr =
  match expr.pexp_desc with
  | Pexp_ident ld ->
    let name = longident_to_string ld.txt in
    (match StrMap.find_opt env name with
    | None -> raise @@ InterExn "expr_to_se: untyped variable"
    | Some tp -> SE.Var (tp, name)
    )
  | Pexp_constant _ -> raise @@ InterExn "do not support complicate literal"
  | _ ->
    let _ = Pprintast.expression Format.std_formatter expr in
    raise @@ InterExn "expr_to_se"

let body_vc_gen client_name funcm tenv expr =
  let counter = ref 0 in
  let newtmp () =
    let x = !counter in
    let _ = counter := (!counter) + 1 in
    x
  in
  let tps_to_vars tps =
    List.map (fun (tp, name) ->
        SE.Var (tp, name)
      ) (List.combine tps (T.auto_name tps))
  in
  let rec aux expr target =
    match expr.pexp_desc, target with
    | Pexp_ident _, Some target ->
      if List.length target != 1 then raise @@ InterExn "body_vc_gen:Pexp_ident" else
      Helper.poly_eq [expr_to_se tenv expr; List.nth target 0]
    | Pexp_ident _, None -> raise @@ InterExn "not imp body_vc_gen"
    | Pexp_constraint (expr, _), target -> aux expr target
    | Pexp_apply (func, args), target ->
      let funcname = expr_to_name func in
      let intps, outtps = StrMap.find "map: body_vc_gen" funcm funcname in
      let nuargs = tps_to_vars intps in
      let to_se arg nu =
        match arg.pexp_desc with
        | Pexp_ident _ -> [], expr_to_se tenv arg
        | _ ->
          [aux arg (Some [nu])], nu
      in
      let cs, args = List.split @@ List.map (fun ((_, arg), nu) -> to_se arg nu) (List.combine args nuargs) in
      let nus = tps_to_vars outtps in
      let target = match target with
        | Some target -> target
        | None -> nus in
      let spec_c =
        if String.equal client_name funcname
        then
          Vc.Implies (Vc.SpecApply (client_pre funcname, args @ target),
                      Vc.SpecApply (client_post funcname, args @ target))
        else
          Vc.SpecApply (funcname, args @ target)
      in
      Vc.And ((List.flatten cs) @ [spec_c])
    | Pexp_ifthenelse (e1, e2, Some e3), target ->
      let bname = SE.Var (T.Bool, sprintf "b%i" (newtmp ())) in
      let c1 =
        match aux e1 (Some [bname]) with
        | Vc.And [c1] -> c1
        | _ -> raise @@ InterExn "parsing: wrong ite cond"
      in
      let c2 = aux e2 target in
      let c3 = aux e3 target in
      Vc.Ite (c1, c2, c3)
    | Pexp_ifthenelse (_, _, None), _ -> raise @@ InterExn "no else branch in ite"
    | _ -> raise @@ InterExn "not imp body_vc_gen"
  in
  let _, client_outtps = StrMap.find "map: body_vc_gen" funcm client_name in
  let nus = tps_to_vars client_outtps in
  aux expr (Some nus), List.map SE.to_tpedvar nus

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
    | Ptyp_var tp -> [type_reduction tp]
    | Ptyp_arrow (_, t1, t2) ->
      (aux t1) @ (aux t2)
    | _ -> raise @@ InterExn "solve_functype"
  in
  match List.rev (aux ct) with
  | [] -> raise @@ InterExn "solve_functype"
  | hd :: tl -> List.rev tl, [hd]


let vd_to_tpedvars signame vd =
  let funcname = signame_concat signame vd.pval_name.txt in
  let tp = solve_functype (signame, vd.pval_type) in
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

let vcgen asts =
  let ppf = Format.std_formatter in
  if List.length asts != 3 then
    (* let _ = Pprintast.structure ppf [ List.nth asts 1] in *)
    raise @@ InterExn "vcgen wrong format"
  else
    let signature = List.nth asts 0 in
    let clienttp = List.nth asts 1 in
    let client = List.nth asts 2 in
    (* let _ = Pprintast.structure ppf [signature] in *)
    let (signame, mtp), (fnames, funcm) = signature_to_functypes @@ structure_to_signagture signature in
    let client_name, (intp, outtp) = vd_to_tpedvars None @@ structure_to_vd clienttp in
    let funcm = StrMap.add client_name (intp, outtp) funcm in
    let _ = layout_funcm funcm in
    match client.pstr_desc with
    | Pstr_value (_, [value_binding]) ->
      let expr = value_binding.pvb_expr in
      let _ = Pprintast.expression ppf expr in
      let rawargs, body = parse_func_args expr in
      let rawargs = List.map patten_to_typedvar rawargs in
      let tenv = List.fold_left (fun e (tp, name) ->
          StrMap.add name tp e
        ) StrMap.empty rawargs in
      (* let _ = List.map (fun arg ->
       *     printf "%s\n" (T.layouttvar (patten_to_typedvar arg))
       *   ) args in
       * let _ = Pprintast.expression ppf body in *)
      let vc, nus = body_vc_gen client_name funcm tenv body in
      let _ = printf "body:=\n%s\n" (Vc.layout vc) in
      client_name, (signame, mtp), fnames, funcm, (intp, outtp), (rawargs, nus), vc
    | _ -> raise @@ InterExn "translate not a function value"

let known_preds mtp name =
  match mtp, name with
  | T.IntList, "mem" -> "list_member"
  | T.IntList, "hd" -> "list_head"
  | T.IntList, "ord" -> "list_order"
  | _, _ -> raise @@ InterExn "unknown preds"

let parse_propositional_term mtp tenv expr =
  let expr_to_se = expr_to_se tenv in
  let rec handle_logic func args =
    match func, args with
    | "implies", [e1; e2] -> E.Implies (aux e1, aux e2)
    | "iff", [e1; e2] -> E.Iff (aux e1, aux e2)
    | "&&", [e1; e2] -> E.And [aux e1; aux e2]
    | "||", [e1; e2] -> E.Or [aux e1; aux e2]
    | "not", [e1] -> E.Not (aux e1)
    | "mem", [e1; e2] ->
      let p = known_preds mtp func in
      E.Atom (SE.Op (T.Bool, p, [expr_to_se e1; expr_to_se e2]))
    | "hd", [e1; e2] ->
      let p = known_preds mtp func in
      E.Atom (SE.Op (T.Bool, p, [expr_to_se e1; expr_to_se e2]))
    | "ord", [e1; e2; e3] ->
      let p = known_preds mtp func in
      E.Atom (SE.Op (T.Bool, p, [expr_to_se e1; expr_to_se e2; expr_to_se e3]))
    | _ -> raise @@ InterExn "wrong assertion format"
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
  let ppf = Format.std_formatter in
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
      let _ = Pprintast.expression ppf expr in
      let rawargs, body = parse_func_args expr in
      let rawargs = List.map patten_to_typedvar rawargs in
      let tenv = List.fold_left (fun e (tp, name) ->
          StrMap.add name tp e
        ) StrMap.empty rawargs in
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
  if List.length asts != 3 then
    raise @@ InterExn "assertions wrong format"
  else
    let preds = get_preds @@ List.nth asts 0 in
    let pre = get_assertion @@ List.nth asts 1 in
    let post = get_assertion @@ List.nth asts 2 in
    let spectab =
      StrMap.add (client_pre client_name) pre @@
      StrMap.add (client_post client_name) post
        Helper.predefined_spec_tab
    in
    preds, spectab

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
  let client_name, (signame, mtp), fnames, funcm, (intp, outtp), (uinputs, uoutputs), vc = vcgen source in
  let imp_map = Impmap.l_to_map (Imps.find signame) in
  let preds, spectab = parse_assertion client_name mtp (intp @ outtp) assertion in
  let preds = List.map (fun p -> known_preds mtp p) preds in
  let holes = make_holes fnames funcm imp_map in
  let uvars = Vc.get_uvars vc in
  let _ = printf "%s\n" (List.to_string T.layouttvar uvars) in
  let open Inference.SpecAbduction in
  let mii =
    let args = List.map SE.from_tpedvar (uinputs @ uoutputs) in
    { upost =
        Vc.Implies (Vc.SpecApply(client_pre client_name, args),
                    Vc.SpecApply(client_post client_name, args));
      uvars = uvars;
      uinputs = uinputs;
      uoutputs = uoutputs;
      uprog = StrMap.find "trans::imp_map" imp_map client_name
    }
  in
  (* let _ = printf "pres:%s\n" (StrList.to_string preds); raise @@ InterExn "end" in *)
  (* let _ = printf "holes:%s\n" (List.to_string (fun (h, _) ->
   *     h.Helper.name
   *   ) holes); raise @@ InterExn "end" in *)
  mii, vc, holes, preds, spectab
