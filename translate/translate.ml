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
    | `BatchedqNil f ->
      ("Batchedq.nil", function
          | [] -> handle (fun () -> [V.L f])
          | _ -> raise @@ InterExn "bad prog")
    | `BatchedqCons f ->
      ("Batchedq.cons", function
          | [V.I h; V.L t] -> handle (fun () -> [V.L (f h t)])
          | _ -> raise @@ InterExn "bad prog")
    | `BatchedqRev f ->
      ("Batchedq.rev", function
          | [V.L l] -> handle (fun () -> [V.L (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `BatchedqIsEmpty f ->
      ("Batchedq.is_empty", function
          | [V.L l] -> handle (fun () -> [V.B (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `Tail func ->
      ("tail", function
          | [V.L f; V.L r;] ->
            let (f', r') = func f r in
            handle (fun () -> [V.L f'; V.L r';])
          | _ -> raise @@ InterExn "bad prog")
    | `LeftisthpLeaf f ->
      ("Leftisthp.leaf", function
          | [] -> handle (fun () -> [V.TI f])
          | _ -> raise @@ InterExn "bad prog")
    | `LeftisthpTree f ->
      ("Leftisthp.tree", function
          | [V.I r; V.I x; V.TI a; V.TI b] -> handle (fun () -> [V.TI (f r x a b)])
          | _ -> raise @@ InterExn "bad prog")
    | `LeftisthpMakeTree f ->
      ("Leftisthp.make_tree", function
          | [V.I x; V.TI a; V.TI b] -> handle (fun () -> [V.TI (f x a b)])
          | _ -> raise @@ InterExn "bad prog")
    | `Merge f ->
      ("merge", function
          | [V.TI tree1; V.TI tree2] -> handle (fun () -> [V.TI (f tree1 tree2)])
          | _ -> raise @@ InterExn "bad prog")
    | `RbsetLeaf f ->
      ("Rbset.leaf", function
          | [] -> handle (fun () -> [V.TB f])
          | _ -> raise @@ InterExn "bad prog")
    | `RbsetTree f ->
      ("Rbset.tree", function
          | [V.B r; V.TB a; V.I x; V.TB b] -> handle (fun () -> [V.TB (f r a x b)])
          | _ -> raise @@ InterExn "bad prog")
    | `Balance f ->
      ("balance", function
          | [V.B r; V.TB tree1; V.I x; V.TB tree2] -> handle (fun () -> [V.TB (f r tree1 x tree2)])
          | _ -> raise @@ InterExn "bad prog")
    | `SplayhpLeaf f ->
      ("Splayhp.leaf", function
          | [] -> handle (fun () -> [V.T f])
          | _ -> raise @@ InterExn "bad prog")
    | `SplayhpNode f ->
      ("Splayhp.node", function
          | [V.T left; V.I x; V.T right] -> handle (fun () -> [V.T (f left x right)])
          | _ -> raise @@ InterExn "bad prog")
    | `Partition f ->
      ("partition", function
          | [V.I pivot; V.T tr] ->
            let (small, big) = f pivot tr in
            handle (fun () -> [V.T small; V.T big])
          | _ -> raise @@ InterExn "bad prog")
    | `StreamNil f ->
      ("Stream.nil", function
          | [] -> handle (fun () -> [V.L f])
          | _ -> raise @@ InterExn "bad prog")
    | `StreamCons f ->
      ("Stream.cons", function
          | [V.I h; V.L t] -> handle (fun () -> [V.L (f h t)])
          | _ -> raise @@ InterExn "bad prog")
    | `StreamLiblazy f ->
      ("Stream.liblazy", function
          | [V.L l] -> handle (fun () -> [V.L (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `StreamLibforce f ->
      ("Stream.libforce", function
          | [V.L l] -> handle (fun () -> [V.L (f l)])
          | _ -> raise @@ InterExn "bad prog")
    | `Reverse f ->
      ("reverse", function
          | [V.L acc; V.L s;] -> handle (fun () -> [V.L (f acc s)])
          | _ -> raise @@ InterExn "bad prog")
    | `TrieNil f ->
      ("Trie.nil", function
          | [] -> handle (fun () -> [V.L f])
          | _ -> raise @@ InterExn "bad prog")
    | `TrieCons f ->
      ("Trie.cons", function
          | [V.I h; V.L t] -> handle (fun () -> [V.L (f h t)])
          | _ -> raise @@ InterExn "bad prog")
    | `TrieLeaf f ->
      ("Trie.leaf", function
          | [] -> handle (fun () -> [V.T f])
          | _ -> raise @@ InterExn "bad prog")
    | `TrieNode f ->
      ("Trie.node", function
          | [V.T l; V.I a; V.T r] -> handle (fun () -> [V.T (f l a r)])
          | _ -> raise @@ InterExn "bad prog")
    | `Ins f ->
      ("ins", function
          | [V.I default; V.L i; V.I a; V.T m;] -> handle (fun () -> [V.T (f default i a m)])
          | _ -> raise @@ InterExn "bad prog")
    | `UnbsetLeaf f ->
      ("Unbset.leaf", function
          | [] -> handle (fun () -> [V.T f])
          | _ -> raise @@ InterExn "bad prog")
    | `UnbsetNode f ->
      ("Unbset.node", function
          | [V.T l; V.I a; V.T r] -> handle (fun () -> [V.T (f l a r)])
          | _ -> raise @@ InterExn "bad prog")
    | `Insert f ->
      ("insert", function
          | [V.I x; V.T tree3] -> Some [V.T (f x tree3)]
          | _ -> raise @@ InterExn "bad prog")
    | `UniquelNil f ->
      ("Uniquel.nil", function
          | [] -> handle (fun () -> [V.L f])
          | _ -> raise @@ InterExn "bad prog")
    | `UniquelCons f ->
      ("Uniquel.cons", function
          | [V.I h; V.L t] -> handle (fun () -> [V.L (f h t)])
          | _ -> raise @@ InterExn "bad prog")
    | `SetAdd f ->
      ("set_add", function
          | [V.I a; V.L x;] -> Some [V.L (f a x)]
          | _ -> raise @@ InterExn "bad prog")
    | _ -> raise @@ InterExn "unknown implementation"
  let l_to_map l =
    List.fold_left (fun m (name, f) ->
        StrMap.add name f m
      ) StrMap.empty (List.map reduce l)
end

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

module TenvEngine = struct
  type t = {
    signame: string;
    sigtps: string list;
    tmap: T.t StrMap.t;
    funcm: (T.t list * T.t list) StrMap.t;
  }
  let make_tenv signame sigtps tmap funcm =
    { signame = signame; sigtps = sigtps; tmap = tmap; funcm = funcm}
  let print_tmap tmap =
    StrMap.iter (fun name t ->
        printf "%s: %s\n" name (T.layout t)
      ) tmap
  let print_tenv tenv =
    printf "signame:%s\nsigtps:%s\n" tenv.signame (StrList.to_string tenv.sigtps); print_tmap tenv.tmap
  let signame_concat signame name =
    match signame with
    | Some signame -> sprintf "%s.%s" signame name
    | None -> name
  let type_reduction = function
    | "Customstk.t" -> T.IntList
    | "Bankersq.t" -> T.IntList
    | "Batchedq.t" -> T.IntList
    | "Leftisthp.t" -> T.IntTreeI
    | "Rbset.t" -> T.IntTreeB
    | "Splayhp.t" -> T.IntTree
    | "Stream.t" -> T.IntList
    | "Trie.t" -> T.IntTree
    | "Trie.tp" -> T.IntList
    | "Unbset.t" -> T.IntTree
    | "Uniquel.t" -> T.IntList
    | "bool" -> T.Bool
    | "int" -> T.Int
    | tp -> failwith (sprintf "unknown type(%s)" tp)
  let rawtp_to_tp tenv rawtp =
    match List.find_opt (fun sigtp -> String.equal rawtp sigtp) tenv.sigtps with
    | Some _ -> type_reduction @@ sprintf "%s.%s" tenv.signame rawtp
    | None -> type_reduction rawtp
  let renew_raw_funcm tenv raw_funcm =
    let funcm =
    StrMap.map (fun (t1, t2) ->
          List.map (rawtp_to_tp tenv) t1, List.map (rawtp_to_tp tenv) t2
      ) raw_funcm in
    { signame = tenv.signame;
      sigtps = tenv.sigtps;
      tmap = tenv.tmap;
      funcm = funcm;
    }
  let known_preds fsttp name =
    match fsttp, name with
    | T.IntList, "mem" -> "list_member"
    | T.IntTree, "mem" -> "tree_member"
    | T.IntTreeI, "mem" -> "treei_member"
    | T.IntTreeB, "mem" -> "treeb_member"
    | T.IntList, "hd" -> "list_head"
    | T.IntList, "ord" -> "list_order"
    | T.IntList, "once" -> "list_once"

    | T.IntTree, "root" -> "tree_head"
    | T.IntTreeB, "root" -> "treeb_head"
    | T.IntTreeI, "root" -> "treei_head"

    | T.IntTree, "ance" -> "tree_ancestor"
    | T.IntTreeB, "ance" -> "treeb_ancestor"
    | T.IntTreeI, "ance" -> "treei_ancestor"

    | T.IntTree, "left" -> "tree_left"
    | T.IntTreeB, "left" -> "treeb_left"
    | T.IntTreeI, "left" -> "treei_left"

    | T.IntTree, "right" -> "tree_right"
    | T.IntTreeB, "right" -> "treeb_right"
    | T.IntTreeI, "right" -> "treei_right"

    | T.IntTree, "para" -> "tree_parallel"
    | T.IntTreeB, "para" -> "treeb_parallel"
    | T.IntTreeI, "para" -> "treei_parallel"
    | _, _ -> raise @@ InterExn (sprintf "unknown predicate: %s" name)
  let all_preds tenv preds =
    let tps = List.map (fun sigtp -> rawtp_to_tp tenv sigtp) tenv.sigtps in
    List.map (fun (tp, name) -> known_preds tp name) @@ List.cross tps preds
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
  let pattern_to_typedvar pattern =
    match pattern.ppat_desc with
    | Ppat_var name -> None, name.txt
    | Ppat_constraint (ident, tp) ->
      Some (get_type tp), pattern_to_string ident
    | _ ->
      printf "pattern_to_typedvar\n";
      Pprintast.pattern Format.std_formatter pattern;
      raise @@ InterExn "wrong pattern name"
  type if_new =
    | MustNew
    | MustOld
    | NoRequirement
  let register_tmap tenv tvar if_new =
    let tpopt, name = tvar in
    (* printf "register\n"; print_tenv tenv;
     * printf "(%s:%s)\n" name (match tpopt with | None -> "_" | Some tp -> T.layout tp);
     * printf "====\n"; *)
    let oldtp = match StrMap.find_opt tenv name, if_new with
      | None, MustOld -> failwith "unknown variable"
      | Some _, MustNew -> failwith (sprintf "need unique name: %s" name)
      | tp, _ -> tp
    in
    match tpopt, oldtp with
    | None, None ->
      print_tmap tenv;
      failwith (sprintf "untyped variable(%s)" name)
    | None, Some tp -> tenv, (tp, name)
    | Some tp, None ->
      StrMap.add name tp tenv, (tp, name)
    | Some tp1, Some tp2 ->
      if T.eq tp1 tp2 then tenv, (tp1, name)
      else failwith "variable type mismatch"
  let register tenv tvar if_new =
    let tmap, tvar = register_tmap tenv.tmap tvar if_new in
    { signame = tenv.signame;
      sigtps = tenv.sigtps;
      tmap = tmap;
      funcm = tenv.funcm;
    }, tvar
  let register_pattern_ tenv pattern if_new =
    register tenv (pattern_to_typedvar pattern) if_new

  let register_pattern tenv pattern if_new =
    match pattern.ppat_desc with
    | Ppat_tuple ps ->
      List.fold_left (fun (tenv, tvars) p ->
          let tenv, tvar = register_pattern_ tenv p if_new in
          tenv, tvars @ [tvar]
        ) (tenv, []) ps
    | _ ->
      let tenv, tvar = register_pattern_ tenv pattern if_new in
      tenv, [tvar]
end

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

let expr_to_se (tenv: TenvEngine.t) expr =
  let aux ld tpopt =
    let name = longident_to_string ld in
    match tpopt with
    | Some tp ->
      let tenv, tvar = TenvEngine.register tenv (Some tp, name) TenvEngine.NoRequirement in
      [], SE.from_tpedvar tvar, tenv
    | None ->
      (match StrMap.find_opt tenv.funcm name with
       | Some (t1, t2) ->
         if List.length t1 == 0 && List.length t2 == 1
         then
           let tp = List.nth t2 0 in
           let se = SE.from_tpedvar (tp, T.universal_auto_name tp) in
           let c = Vc.SpecApply (name, [se]) in
           [c], se, tenv
         else raise @@ InterExn "expr_to_se wrong app"
       | _ ->
         let tenv, tvar = TenvEngine.register tenv (None, name) TenvEngine.NoRequirement in
         [], SE.from_tpedvar tvar, tenv
      )
  in
  match expr.pexp_desc with
  | Pexp_ident ld -> aux ld.txt None
  | Pexp_constraint (expr, ct) ->
    (match expr.pexp_desc with
     | Pexp_ident ld -> aux ld.txt (Some (TenvEngine.get_type ct))
     | _ -> raise @@ InterExn "only add type denotation to variable"
    )
  | Pexp_constant _ -> raise @@ InterExn "do not support complicate literal"
  | _ ->
    let _ = Pprintast.expression Format.std_formatter expr in
    raise @@ InterExn "expr_to_se"

type termi_status =
  | TermiRaiseExn
  | TermiNormal of Vc.t * TenvEngine.t

let body_vc_gen client_name (init_tenv: TenvEngine.t) asst expr =
  let tps_to_ses = List.fold_left (fun r tp ->
      r @ [SE.from_tpedvar (tp, T.universal_auto_name tp)]) [] in
  let handle_let vb tenv =
    let tenv, leftvars = TenvEngine.register_pattern tenv vb.pvb_pat TenvEngine.MustNew in
    leftvars, vb.pvb_expr, tenv
  in
  let handle_match_args match_args tenv =
    let rec aux e =
      match e.pexp_desc with
      | Pexp_tuple es -> List.flatten @@ List.map aux es
      | Pexp_ident ld ->
        let _, tvar = TenvEngine.register tenv (None, longident_to_string ld.txt) TenvEngine.MustOld in
        [tvar]
      | _ -> failwith "parser: wrong format in match"
    in
    aux match_args
  in
  let handle_case case =
    match case.pc_guard with
    | None -> failwith "handle_case"
    | Some guard -> guard, case.pc_rhs
  in
  let solve_function_name funcname funcm =
    match funcname with
    | "+" -> "intadd", [T.Int; T.Int], [T.Int]
    | "<=" -> "le", [T.Int; T.Int], [T.Bool]
    | ">=" -> "ge", [T.Int; T.Int], [T.Bool]
    | ">" -> "gt", [T.Int; T.Int], [T.Bool]
    | "<" -> "lt", [T.Int; T.Int], [T.Bool]
    | "==" -> "inteq", [T.Int; T.Int], [T.Bool]
    | _ ->
      let intps, outtps = StrMap.find (sprintf "map: body_vc_gen Pexp_apply(%s)" funcname) funcm funcname in
      funcname, intps, outtps
  in
  let rec handle_varaible expr target tenv =
    if List.length target != 1 then raise @@ InterExn "body_vc_gen:Pexp_ident" else
      let c, arg1, tenv = expr_to_se tenv expr in
      let c' = Helper.poly_eq [arg1; List.nth target 0] in
      TermiNormal
        ((match c with
            | [] -> c'
            | _ -> Vc.And (c @ [c'])), tenv)
  and aux_seq exprs targets (tenv: TenvEngine.t) =
    let r = List.fold_left (fun status (e, target) ->
        match status with
        | None -> None
        | Some (tenv, cs) ->
          match aux e (Some [target]) tenv with
          | TermiRaiseExn -> None
          | TermiNormal (c, tenv) -> Some (tenv, cs @ [c])
      ) (Some (tenv, [])) (List.combine exprs targets) in
    match r with
    | None -> TermiRaiseExn
    | Some (tenv, cs) ->
      (* printf "\taux_seq\n"; print_tenv tenv; printf "\n"; *)
      TermiNormal (Vc.And cs, tenv)
  and aux expr target tenv =
    match expr.pexp_desc, target with
    | Pexp_tuple es, Some target ->
      if List.length target != List.length es
      then raise @@ InterExn "body_vc_gen: Tuple length does not macthed"
      else aux_seq es target tenv
    | Pexp_tuple _, None -> raise @@ InterExn "body_vc_gen: Tuple"
    | Pexp_constraint (_, _), Some target -> handle_varaible expr target tenv
    | Pexp_ident _, Some target -> handle_varaible expr target tenv
    | Pexp_constraint (_, _), None -> raise @@ InterExn "not imp body_vc_gen"
    | Pexp_ident _, None -> raise @@ InterExn "not imp body_vc_gen"
    | Pexp_construct (id, None), Some target ->
      let lit =
      match longident_to_string id.txt with
        | "true" -> SE.Literal (T.Bool, SE.L.Bool true)
        | "false" -> SE.Literal (T.Bool, SE.L.Bool false)
        | _ -> raise @@ InterExn "do not support complicate literal"
      in
      TermiNormal (Helper.poly_eq [List.nth target 0; lit], tenv)
    (* | Pexp_constant (Pconst_string ("true", None)), Some target ->
     *   TermiNormal (Helper.poly_eq [List.nth target 0; SE.Literal (T.Bool, SE.L.Bool true)], tenv)
     * | Pexp_constant (Pconst_string ("false", None)), Some target ->
     *   TermiNormal (Helper.poly_eq [List.nth target 0; SE.Literal (T.Bool, SE.L.Bool false)], tenv) *)
    | Pexp_constant (Pconst_integer (istr, None)), Some target ->
      TermiNormal (Helper.poly_eq [List.nth target 0; SE.Literal (T.Int, SE.L.Int (int_of_string istr))], tenv)
    | Pexp_let (_, vbs, e), target ->
      let r = List.fold_left (fun status vb ->
          match status with
          | None -> None
          | Some (tenv, cs) ->
            let new_target, let_body, tenv = handle_let vb tenv in
            match aux let_body (Some (List.map SE.from_tpedvar new_target)) tenv with
            | TermiRaiseExn -> None
            | TermiNormal (c, tenv) -> Some (tenv, cs @ [c])
        ) (Some (tenv, [])) vbs in
      (match r with
       | None -> TermiRaiseExn
       | Some (tenv, cs) ->
         match aux e target tenv with
         | TermiRaiseExn -> TermiRaiseExn
         | TermiNormal (c, tenv) -> TermiNormal (Vc.And (cs @ [c]), tenv)
      )
    | Pexp_apply (func, args), target ->
      let funcname = expr_to_name func in
      if String.equal funcname "raise" then TermiRaiseExn else
        let funcname, intps, outtps = solve_function_name funcname tenv.funcm in
        let to_se arg tp tenv =
          match arg.pexp_desc with
          | Pexp_ident _ -> Some (expr_to_se tenv arg)
          | Pexp_constant (Pconst_string ("true", None)) ->
            Some ([], SE.Literal (T.Bool, SE.L.Bool true), tenv)
          | Pexp_constant (Pconst_string ("false", None)) ->
            Some ([], SE.Literal (T.Bool, SE.L.Bool false), tenv)
          | Pexp_constant (Pconst_integer (istr, None)) ->
            Some ([], SE.Literal (T.Int, SE.L.Int (int_of_string istr)), tenv)
          | Pexp_constant _ -> failwith "source code: comlicate literal"
          | _ ->
            let nu = SE.from_tpedvar (tp, T.universal_auto_name tp) in
            match aux arg (Some [nu]) tenv with
            | TermiNormal (c, tenv) -> Some ([c], nu, tenv)
            | TermiRaiseExn -> None
        in
        let r = List.fold_left (fun status ((_, arg), tp) ->
            match status with
            | None -> None
            | Some (tenv, cs, nus) ->
              match to_se arg tp tenv with
              | None -> None
              | Some (c, nu, tenv) -> Some (tenv, cs @ c, nus @ [nu])
          ) (Some (tenv, [], [])) (List.combine args intps) in
        (match r with
         | None -> TermiRaiseExn
         | Some (tenv, cs, args) ->
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
           TermiNormal (Vc.And (cs @ [spec_c]), tenv)
        )
    | Pexp_ifthenelse (e1, e2, Some e3), target ->
      let bname = SE.from_tpedvar (T.Bool, T.universal_auto_name T.Bool) in
      (match aux e1 (Some [bname]) tenv with
       | TermiRaiseExn -> failwith "condition raise exn"
       | TermiNormal (Vc.And [c1], _) ->
         (match aux e2 target tenv, aux e3 target tenv with
         | TermiRaiseExn, TermiRaiseExn -> TermiRaiseExn
         | TermiNormal (c2, _), TermiRaiseExn -> TermiNormal (Vc.Implies (c1, c2), tenv)
         | TermiRaiseExn, TermiNormal (c3, _) -> TermiNormal (Vc.Implies (Vc.Not c1, c3), tenv)
         | TermiNormal (c2, _), TermiNormal (c3, _) -> TermiNormal (Vc.Ite (c1, c2, c3), tenv))
       | TermiNormal (_, _) -> failwith "condition should be a single application"
      )
    | Pexp_ifthenelse (_, _, None), _ -> raise @@ InterExn "no else branch in ite"
    | Pexp_match (case_target, cases), target ->
      let case_targets = List.map SE.from_tpedvar @@ handle_match_args case_target tenv in
      let cs = List.filter_map (fun case ->
          let case_e, body = handle_case case in
          match aux case_e (Some case_targets) tenv with
          | TermiRaiseExn -> None
          | TermiNormal (case_c, tenv) ->
            (* printf "--case--\n"; print_tenv tenv; *)
            match aux body target tenv with
            | TermiRaiseExn -> None
            | TermiNormal (body_c, _) -> Some (Vc.And [case_c; body_c])
        ) cases in
      (match cs with
       | [] -> TermiRaiseExn
       | _ -> TermiNormal (Vc.Or cs, tenv))
    | _ -> raise @@ InterExn (sprintf "not imp body_vc_gen:%s ~> %s"
                                (Pprintast.string_of_expression expr)
                                (match target with
                                 | Some e -> List.to_string SE.layout e
                                 | None -> "none")
                             )
  in
  let _, client_outtps = StrMap.find "map: body_vc_gen client_name" init_tenv.funcm client_name in
  let nus = tps_to_ses client_outtps in
  (* let _ = printf "nus:%s\n" (List.to_string SE.layout nus); raise @@ InterExn "end" in *)
  match aux expr (Some nus) init_tenv with
  | TermiRaiseExn -> failwith "wrong function, raise exn in all control flows"
  | TermiNormal (vc, _) -> vc, List.map SE.to_tpedvar nus

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

let solve_functype ct =
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
        [longident_to_string tpc.txt]
    | Ptyp_tuple cts -> List.flatten @@ List.map aux cts
    | Ptyp_var tp -> [tp]
    | Ptyp_arrow (_, _, _) -> raise @@ InterExn "solve_functype: function type"
    | _ -> raise @@ InterExn "solve_functype"
  in
  List.flatten @@ List.map aux argtps, aux rettp

let vd_to_tpedvars signame vd =
  let funcname = TenvEngine.signame_concat signame vd.pval_name.txt in
  let tp = solve_functype vd.pval_type in
  (* let () = printf "%s -> %s\n" (List.to_string T.layout (fst tp)) (List.to_string T.layout (snd tp)) in *)
  funcname, tp

let signature_to_functypes (signame, signature) =
  let handle_type_def tdl =
    match tdl with
    | [td] -> td.ptype_name.txt
    | _ -> failwith "parse signature: the type definition should be abstract"
  in
  let aux (tpnames, fnames, funcmapping) sig_item =
    match sig_item.psig_desc with
    | Psig_value vd ->
      let funcname, tp = vd_to_tpedvars (Some signame) vd in
      tpnames, fnames @ [funcname], StrMap.add funcname tp funcmapping
    | Psig_type (_, tdl) ->
      tpnames @ [handle_type_def tdl], fnames, funcmapping
    | _ -> raise @@ InterExn "signature_to_functypes"
  in
  let tpnames, fnames, funcm = List.fold_left aux ([], [], StrMap.empty) signature in
  (* let tps = List.map (fun t -> type_reduction (signame_concat (Some signame) t)) tpnames in *)
  (signame, tpnames), (fnames, funcm)

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
    let (signame, tpnames), (fnames, funcm) = signature_to_functypes @@ structure_to_signagture signature in
    (* let _ =
     *   printf "solve_functype\n";
     *   Pprintast.core_type Format.std_formatter (structure_to_vd clienttp).pval_type;
     *   raise @@ InterExn "end" in *)
    let client_name, (intp, outtp) = vd_to_tpedvars None @@ structure_to_vd clienttp in
    let raw_funcm = StrMap.add client_name (intp, outtp) funcm in
    (* let _ = layout_funcm funcm in *)
    client_name, (signame, tpnames), fnames, raw_funcm, (intp, outtp), client

let parse_func_update_tenv tenv expr =
  let rawargs, body = parse_func_args expr in
  (* let _ = TenvEngine.print_tenv tenv in
   * let _ = List.iter (fun p ->
   *     Pprintast.pattern Format.std_formatter p) rawargs in *)
  let tenv, rawargs = List.fold_left (fun (tenv, tvars) pattern ->
      let tenv, tvar = TenvEngine.register_pattern tenv pattern TenvEngine.MustNew in
      (tenv, tvars @ tvar)
    ) (tenv, []) rawargs in
  tenv, rawargs, body

(* let vcgen (signame, tpnames) client_name funcm asst client =
 *   match client.pstr_desc with
 *   | Pstr_value (_, [value_binding]) ->
 *     let expr = value_binding.pvb_expr in
 *     (\* let _ = Pprintast.expression ppf expr in *\)
 *     let tenv, rawargs, body = parse_func_build_tenv (signame, tpnames) expr in
 *     let vc, nus = body_vc_gen client_name funcm tenv asst body in
 *     (\* let _ = printf "body:=\n%s\n" (Vc.layout vc) in *\)
 *     (rawargs, nus), vc
 *   | _ -> raise @@ InterExn "translate not a function value" *)

let parse_client init_tenv client =
  match client.pstr_desc with
  | Pstr_value (_, [value_binding]) ->
    let expr = value_binding.pvb_expr in
    (* let _ = Pprintast.expression ppf expr in *)
    let tenv, rawargs, body = parse_func_update_tenv init_tenv expr in
    tenv, rawargs, body
  | _ -> raise @@ InterExn "translate not a function value"

let parse_propositional_term tenv expr =
  let expr_to_se = fun x ->
    match expr_to_se tenv x with
    | _, x, _ -> x
  in
  let rec handle_logic func args =
    let op2 (func, e1, e2) =
      let se = expr_to_se e1 in
      let p = TenvEngine.known_preds (SE.get_tp se) func in
      E.Atom (SE.Op (T.Bool, p, [se; expr_to_se e2]))
    in
    let op3 (func, e1, e2, e3) =
      let se = expr_to_se e1 in
      let p = TenvEngine.known_preds (SE.get_tp se) func in
      E.Atom (SE.Op (T.Bool, p, [se; expr_to_se e2; expr_to_se e3]))
    in
    match func, args with
    | "implies", [e1; e2] -> E.Implies (aux e1, aux e2)
    | "iff", [e1; e2] -> E.Iff (aux e1, aux e2)
    | "&&", [e1; e2] -> E.And [aux e1; aux e2]
    | "||", [e1; e2] -> E.Or [aux e1; aux e2]
    | "not", [e1] -> E.Not (aux e1)
    | "==", [e1; e2] -> E.Atom (SE.Op (T.Bool, "==", [expr_to_se e1; expr_to_se e2]))
    | "!=", [e1; e2] -> E.Not (E.Atom (SE.Op (T.Bool, "==", [expr_to_se e1; expr_to_se e2])))
    | "<=", [e1; e2] -> E.Atom (SE.Op (T.Bool, "<=", [expr_to_se e1; expr_to_se e2]))
    | ">=", [e1; e2] -> E.Atom (SE.Op (T.Bool, ">=", [expr_to_se e1; expr_to_se e2]))
    | "<", [e1; e2] -> E.Atom (SE.Op (T.Bool, "<", [expr_to_se e1; expr_to_se e2]))
    | ">", [e1; e2] -> E.Atom (SE.Op (T.Bool, ">", [expr_to_se e1; expr_to_se e2]))
    | "mem", [e1; e2] -> op2 (func, e1, e2)
    | "hd", [e1; e2] -> op2 (func, e1, e2)
    | "root", [e1; e2] -> op2 (func, e1, e2)
    | "once", [e1; e2] -> op2 (func, e1, e2)
    | "ord", [e1; e2; e3] -> op3 (func, e1, e2, e3)
    | "ance", [e1; e2; e3] -> op3 (func, e1, e2, e3)
    | "left", [e1; e2; e3] -> op3 (func, e1, e2, e3)
    | "right", [e1; e2; e3] -> op3 (func, e1, e2, e3)
    | "para", [e1; e2; e3] -> op3 (func, e1, e2, e3)
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

let parse_assertion client_name init_tenv argtps asts =
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
      let tenv, rawargs, body = parse_func_update_tenv init_tenv expr in
      (* let _ = printf "length argtps:%i\n" (List.length argtps); raise @@ InterExn "end" in *)
      let args = List.sublist rawargs (0, List.length argtps) in
      let qvs = List.sublist rawargs (List.length argtps, List.length rawargs) in
      (* let _ = printf "rawargs:%s\n" (List.to_string T.layouttvar rawargs) in
       * let _ = printf "args:%s\n" (List.to_string T.layouttvar args) in
       * let _ = printf "qvs:%s\n" (List.to_string T.layouttvar qvs) in *)
      let body = parse_propositional_term tenv body in
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

let count_r vc fnames =
  let pres = List.map Vc.merge_and @@ Vc.to_dnf @@ Vc.eliminate_cond_one vc in
  let c = List.fold_left (fun c pre -> c + (Vc.count_apps pre fnames)) 0 pres in
  (* let _ = printf "#R:%i\n" c; raise @@ InterExn "end" in *)
  c
  (* Vc.(
   *   let rec aux pre = function
   *     | ForAll _ -> raise @@ InterExn "never happen aux"
   *     | Implies (p1, p2) -> aux (aux pre p1) p2
   *     | And ps -> List.fold_left (fun c p -> (aux c p)) pre ps
   *     | Or ps -> List.fold_left (fun c p ->
   *         let _ = printf "pre:%i res:%i" pre (aux pre p) in
   *         c + (aux pre p)
   *       ) 0 ps
   *     | Not p -> aux pre p
   *     | Iff (p1, p2) ->
   *       aux (aux pre p1) p2
   *     | Ite (p1, p2, p3) ->
   *       (\* raise @@ InterExn "never happen aux" *\)
   *       (aux (aux pre p1) p2) + (aux (aux pre p1) p3)
   *     | SpecApply (specname, _) ->
   *       match List.find_opt (fun name -> String.equal name specname) fnames with
   *       | Some _ -> pre + 1
   *       | None -> pre
   *   in
   *   List.fold_left (fun pre vc -> aux pre vc) 0 (to_dnf vc)
   * ) *)

let trans (source, assertion) =
  let client_name, (signame, tpnames), fnames, raw_funcm, (intp, outtp), client = parse_source source in
  let init_tenv = TenvEngine.make_tenv signame tpnames StrMap.empty StrMap.empty in
  (* let _ = printf "%s\n" (StrList.to_string intp) in
   * let _ = printf "%s\n" (StrList.to_string outtp) in
   * let _ = raise @@ InterExn "end" in *)
  let _ = printf "%s\n" signame in
  let imp_map = Impmap.l_to_map (Imps.find signame) in
  let preds, asst, spectab = parse_assertion client_name init_tenv (intp @ outtp) assertion in
  let tenv = TenvEngine.renew_raw_funcm init_tenv raw_funcm in
  let tenv, uinputs, body = parse_client tenv client in
  let vc, uoutputs = body_vc_gen client_name tenv asst body in
    let _ = printf "vc:%s\n" (Vc.vc_layout vc) in
   (* let _ = printf "vc:%s\n" (Vc.vc_layout vc); raise @@ InterExn "end" in  *)
  let preds = TenvEngine.all_preds tenv preds in
  let holes = make_holes fnames tenv.funcm imp_map in
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
    let _ = printf "client: %s\n" client_name in 
    { upost = upost;
      uvars = uvars;
      uinputs = uinputs;
      uoutputs = uoutputs;
      uprog = StrMap.find "trans::imp_map" imp_map client_name
    }
  in
  let basic_info =
    `Assoc [
      "num_f", `Int (List.length holes);
      "num_r", `Int (count_r vc fnames);
      "num_p", `Int (List.length preds);
    ]
  in
  (* let _ = printf "preds:%s\n" (StrList.to_string preds); raise @@ InterExn "end" in *)
  (* let _ = printf "holes:%s\n" (List.to_string (fun (h, _) ->
   *     h.Helper.name
   *   ) holes); raise @@ InterExn "end" in *)
  mii, vc, holes, preds, spectab, basic_info
