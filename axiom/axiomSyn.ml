module type AxiomSyn = sig
  module D: Dtree.Dtree
  module Ast = Language.SpecAst
  type vec = bool list
  type value = Pred.Value.t
  type sample = {dt: value; args: value list; vec: vec}
  type title = D.feature list
  val layout_title: title -> string
  val make_title: string list -> int -> title
  val make_sample: title -> value -> value list -> sample
  val cex_to_sample: value list -> vec -> sample
  val layout_sample: sample -> string
  val classify: title -> pos: sample list -> neg: sample list -> D.feature D.t
  val randomgen: int list -> value list
  val sample_constraint: Z3.context ->
    Ast.E.SE.t list -> (string * value) list -> (int * int) -> Z3.Expr.expr
  val axiom_infer: ctx:Z3.context -> vc:Ast.t -> spectable:Ast.spec Utils.StrMap.t -> pred_names: string list -> dttp:Ast.E.SE.tp -> Ast.E.forallformula
  val spec_infer: ctx:Z3.context -> progtp:(Ast.E.SE.tp list * Ast.E.SE.tp list) -> prog:(value list -> value list) -> Ast.spec
end

module AxiomSyn (D: Dtree.Dtree) (F: Ml.FastDT.FastDT) = struct
  module D = D
  module V = Pred.Value
  module P = Pred.Pred
  module Ast = Language.SpecAst
  module Epr = Ast.E
  module S = Solver
  module T = Tp.Tp
  open Utils
  open Printf
  type vec = bool list
  type sample = {dt: V.t; args: V.t list; vec: vec}
  type title = D.feature list

  let make_title names fvs_num =
    let aux info =
      (* let _ = printf "%s(arglen = %i)\n" info.P.name info.P.num_int in *)
      let fvs_c = List.combination fvs_num info.P.num_int in
      let fvs_c =
        if info.P.permu then
          List.concat (List.map (fun l -> List.permutation l) fvs_c)
        else fvs_c
      in
      List.map (fun fv_c -> (info.P.name, fv_c)) fvs_c
    in
    let info = List.filter_map (fun info ->
        match List.find_opt (fun name -> String.equal name info.P.name) names with
        | None -> None
        | Some _ -> Some info
      ) P.preds_info in
    List.fold_left (fun r info -> r @ (aux info)) [] info

  let layout_title (title: title) =
    List.fold_left (fun r pred -> sprintf "%s [%s]" r (D.layout_feature pred)) "" title

  let additional fv =
    match IntList.max_opt fv with
    | None -> raise @@ InterExn "additional"
    | Some m -> m + 1

  let randomgen_list (fv: int list) =
    List.map (fun l -> V.L l) @@
    List.remove_duplicates IntList.eq @@
    List.choose_eq_all (fun a b -> a == b) ((additional fv):: (fv @ fv))

  let randomgen_list2 (fv: int list) =
    let ad = additional fv in
    let values = (ad :: fv) @ fv in
    let list_gen = QCheck.Gen.(list_size (int_bound 10) (oneofl values)) in
    let s = QCheck.Gen.generate ~n:10 list_gen in
    let s = List.remove_duplicates IntList.eq s in
    List.map (fun l -> V.L l) s

  let randomgen_tree2 (fv: int list) =
    let values = fv in
    let _ = printf "fv:%s\n" (IntList.to_string values) in
    let node a l r = Tree.Node (a, l, r) in
    let tree_gen =
      QCheck.Gen.((sized_size (int_bound 10)) @@ fix
                    (fun self n -> match n with
                       | 0 -> oneofl [Tree.Leaf]
                       | n ->
                         frequency
                           [1, oneofl [Tree.Leaf];
                            3, QCheck.Gen.map3 node (oneofl values)
                              (self (n/2)) (self (n/2))]
                    ))
    in
    let trs = QCheck.Gen.generate ~n:20 tree_gen in
    let trs = List.remove_duplicates (Tree.eq (fun x y -> x == y)) trs in
    (* let _ = List.iter (fun tr ->
     *     printf "tr:%s\n" (Tree.layout string_of_int tr)
     *   ) trs in *)
    List.map (fun l -> V.T l) trs

  let randomgen_tree (fv: int list) =
    let ad = additional fv in
    let values = (ad :: fv) @ fv in
    let _ = printf "fv:%s\n" (IntList.to_string values) in
    let node a l r = Tree.Node (a, l, r) in
    let tree_gen =
      QCheck.Gen.((sized_size (int_bound 10)) @@ fix
                    (fun self n -> match n with
                       | 0 -> oneofl [Tree.Leaf]
                       | n ->
                         frequency
                           [1, oneofl [Tree.Leaf];
                            3, QCheck.Gen.map3 node (oneofl values)
                              (self (n/2)) (self (n/2))]
                    ))
    in
    let trs = QCheck.Gen.generate ~n:10 tree_gen in
    let trs = List.remove_duplicates (Tree.eq (fun x y -> x == y)) trs in
    (* let _ = List.iter (fun tr ->
     *     printf "tr:%s\n" (Tree.layout string_of_int tr)
     *   ) trs in *)
    List.map (fun l -> V.T l) trs

  let randomgen (fv: int list) (tp: Epr.SE.tp) =
    let module SE = Epr.SE in
    match tp with
    | T.IntList -> randomgen_list fv
    | T.IntTree -> randomgen_tree fv
    | _ -> raise @@ InterExn "randomgen: not a dt"


  let make_sample (title:title) (dt: V.t) (args: V.t list) =
    let vec = List.map (fun feature -> D.exec_feature feature dt args) title in
    {dt; args; vec}

  let cex_to_sample (args: V.t list) (vec: bool list) =
    {dt = V.NotADt; args; vec}

  let layout_sample {dt; args; vec} =
    sprintf "%s(%s) [%s]" (V.layout dt) (List.to_string V.layout args) (boollist_to_string vec)

  let classify_ (title: title) (_:vec list) (_:vec list) : D.feature D.t =
    let member0 = List.nth title 0 in
    let ord = List.nth title 2 in
    D.Node (ord, D.Leaf member0, D.T)

  let dt_to_dt title dt =
    let rec aux = function
      | F.Leaf {c_t; c_f} ->
        if (Float.abs c_t) < 1e-3 then D.F
        else if (Float.abs c_f) < 1e-3 then D.T
        else raise @@ InterExn (sprintf "Bad Dt Result(%f, %f)" c_t c_f)
      | F.Node ({split;if_t;if_f}) ->
        match List.nth_opt title split with
        | None -> raise @@ InterExn "Bad Dt Result"
        | Some p -> D.Node (p, aux if_t, aux if_f)
    in
    aux dt

  let classify title ~pos ~neg =
    let pos = List.map (fun s -> true, Array.of_list s.vec) pos in
    let neg = List.map (fun s -> false, Array.of_list s.vec) neg in
    let dt = F.make_dt ~samples:(Array.of_list (pos @ neg)) ~max_d:10 in
    let _ = F.print_tree' dt in
    dt_to_dt title dt

  let spec_classify title samples =
    let samples = List.map (fun (a, b) -> a, Array.of_list b) samples in
    let dt = F.make_dt ~samples:(Array.of_list samples) ~max_d:10 in
    let _ = F.print_tree' dt in
    dt_to_dt title dt

  open Z3

  let fixed_sample ctx l =
    Boolean.mk_and ctx (
      List.fold_left (fun cs (name, dt) ->
          match dt with
          | V.I i ->
            (Epr.SE.fixed_int_to_z3 ctx name i):: cs
          | V.B _ -> cs
          | _ ->
            (Epr.SE.fixed_dt_to_z3 ctx "list_member" name dt)::
            (Epr.SE.fixed_dt_to_z3 ctx "list_order" name dt)::
            cs
        ) [] l
    )

  let sample_constraint ctx fv l (s, e) =
    let c = fixed_sample ctx l in
    let geE a b = Epr.Atom (Epr.SE.Op (T.Bool, ">=", [a; b])) in
    let sz3, ez3 = map_double (fun x -> Epr.SE.Literal (T.Int, Epr.SE.L.Int x)) (s, e) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u -> l @ [geE u sz3; geE ez3 u]) [] fv)) in
    Boolean.mk_and ctx [interval;c]

  module SE = Epr.SE
  let sample_num = 2
  let start_size = 2
  open Printf

  let interval ctx exists_fv (s, e) =
    let (s', e') =
      map_double (fun x -> Epr.SE.Literal (T.Int, Epr.SE.L.Int x)) (s, e) in
    let name_to_var name = SE.Var (T.Int, name) in
    let geE a b = Epr.Atom (SE.Op (T.Bool, ">=", [a; b])) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u ->
             l @ [geE (name_to_var u) s'; geE e' (name_to_var u)]) [] exists_fv)) in
    interval

  let sample_constraint_over_dt ctx dtname l exists_fv (s, e) =
    let c = fixed_sample ctx l in
    let dt = SE.Var (T.IntList, dtname) in
    let u, v = SE.Var (T.Int, "u"), SE.Var (T.Int, "v") in
    let s', e' = SE.Literal (T.Int, SE.L.Int s), SE.Literal (T.Int, SE.L.Int e) in
    let geE a b = Epr.Atom (SE.Op (T.Bool, ">=", [a; b])) in
    let member l u = Epr.Atom (SE.Op (T.Bool, "list_member", [l; u])) in
    let head l u = Epr.Atom (SE.Op (T.Bool, "list_member", [l; u])) in
    let list_order l u v = Epr.Atom (SE.Op (T.Bool, "list_order", [l; u; v])) in
    let dt_c = ["u"; "v"], Epr.And [
        Epr.Implies (
          Epr.Not (Epr.And [geE u s';geE e' u]),
          Epr.Not (Epr.Or [member dt u; head dt u]));
        Epr.Implies (
          Epr.Not (Epr.And [geE u s';geE e' u;geE v s';geE e' v]),
          Epr.Not (list_order dt u v));
      ] in
    let name_to_var name = SE.Var (T.Int, name) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u ->
             l @ [geE (name_to_var u) s'; geE e' (name_to_var u)]) [] exists_fv)) in
    Boolean.mk_and ctx [c; interval;
                        Epr.forallformula_to_z3 ctx dt_c;
                       ]

  let get_sat_conj ctx vc spec_tab =
    let vc_nnf = Ast.to_nnf vc in
    let vc_dnf = Ast.to_dnf (Ast.remove_unsat_clause vc_nnf) in
    let rec aux = function
      | [] -> []
      | h :: t -> if fst @@ S.check ctx (Ast.to_z3 ctx h spec_tab)
        then aux t
        else
          let _ = printf "conj:%s\n" (Ast.layout h) in
          (* let _ = printf "conj:%s\n" (Ast.layout (Ast.application h spec_tab)) in *)
          let fv, dts, skolemize_conj = Ast.skolemize_conj (Ast.application h spec_tab) in
          let _ = printf "fv=[%s] dts=[%s]\n" (List.to_string (fun x -> x) fv)
              (List.to_string (fun x -> x) dts) in
          (* let _ = printf "conj:%s\n" (Ast.layout skolemize_conj) in *)
          let valid, _ = S.check ctx (Ast.to_z3 ctx skolemize_conj spec_tab) in
          if valid then raise @@ InterExn "get_sat_conj" else
            (fv, dts, skolemize_conj, h) :: (aux t)
    in
    match vc_dnf with
    | Or ps -> aux ps
    | _ -> raise @@ InterExn "get_sat_conj"

  let complement s len default =
    let vecs = List.choose_n_eq (fun a b -> a == b) [true;false] len in
    let vecs = List.filter_map (fun vec ->
        match List.find_opt (fun s -> List.eq (fun a b -> a == b) s.vec vec) s with
        | None -> Some vec
        | Some _ -> None
      ) vecs in
    let negs = List.map (fun vec -> cex_to_sample default vec) vecs in
    negs

  let additional_axiom ctx =
    let module E = Ast.E in
    let list_var name = SE.Var (T.IntList, name) in
    let int_var name = SE.Var (T.Int, name) in
    let head l u = E.Atom (SE.Op (T.Bool, "head", [l; u])) in
    let member l u = E.Atom (SE.Op (T.Bool, "member", [l; u])) in
    let list_order l u v = E.Atom (SE.Op (T.Bool, "list_order", [l; u; v])) in
    let l1    = list_var "l1" in
    let u    = int_var "u" in
    let v    = int_var "v" in
    let w    = int_var "w" in
    let axiom = (["l1"; "u"; "v"; "w"],
                 E.And [
                   (* E.Implies (list_order l1 u v, E.Not (head l1 v)); *)
                   E.Implies (head l1 u, member l1 u);
                   E.Implies (list_order l1 u v,
                              E.Or [E.And [head l1 u; member l1 v];
                                    E.And [head l1 w;list_order l1 w u]]);
                 ]
                ) in
    E.forallformula_to_z3 ctx axiom

  (* prevent loop forever *)
  let max_main_loop_times = 4

  type spec_title = string * int option * int list
  let make_int_title idx fv_idxs =
    List.filter_map (fun fv_idx ->
        if fv_idx == idx then None else
          Some ("==", None, [idx; fv_idx])) fv_idxs
  let make_inner_title fv_idxs =
    List.map (fun l -> "==", None, l) @@ List.combination_l fv_idxs 2
  let make_dt_title (tp, dt) fv_idxs =
    let aux info =
      let fvs_c = List.combination_l fv_idxs info.P.num_int in
      let fvs_c =
        if info.P.permu then
          List.concat (List.map (fun l -> List.permutation l) fvs_c)
        else fvs_c
      in
      List.map (fun fv_c -> (info.P.name, Some dt, fv_c)) fvs_c
    in
    let info = P.tp_to_preds tp in
    List.fold_left (fun r info -> r @ (aux info)) [] info
  let make_spec_var_assign (inptps, outptps) fv_num =
    let len1 = List.length inptps in
    let len2 = len1 + (List.length outptps) in
    let aux l base =  List.mapi (fun idx tp ->
        match tp with
        | T.Int | T.IntList | T.IntTree -> tp, idx + base
        | T.Bool -> raise @@ InterExn "make_spec_title:do not support"
      ) l in
    let inptps = aux inptps 0 in
    let outptps = aux outptps len1 in
    let fv_idxs = List.init fv_num (fun i -> i + len2) in
    inptps, outptps, fv_idxs
  let make_spec_title vartp fv_idxs=
    List.flatten @@ List.map (fun (tp, idx) ->
        if T.is_dt tp
        then make_dt_title (tp, idx) fv_idxs
        else make_int_title idx fv_idxs
      ) vartp

  let layout_spec_title title =
    List.fold_left (fun r (pred, dt, args) ->
        let args = List.map (fun i -> sprintf "x%i" i) args in
        let args =
          match dt with
          | None -> args
          | Some dt -> (sprintf "dt%i" dt) :: args
        in
        sprintf "%s [%s(%s)]" r pred (List.inner_layout args "," "")) "" title

  let make_target_title vartp fv_idxs =
    let aux info dtname fv_idxs =
      let fvs = List.sublist fv_idxs (0, info.P.num_int) in
      info.P.name, Some dtname, fvs
    in
    let p = List.map (fun (tp, idx) ->
        match tp with
        | T.Int -> ["==", None, [idx; List.nth fv_idxs 0]]
        | T.IntList | T.IntTree ->
            List.map (fun p -> aux p idx fv_idxs) (P.tp_to_preds tp)
        | T.Bool -> raise @@ InterExn "make_spec_title:do not support"
      ) vartp in
    List.flatten p

  let spec_title_filter spec_title vecs target =
    let extract_target (pred, dt, args) =
      match dt, args with
      | Some dt, _ -> pred, dt
      | None, h :: _ -> pred, h
      | _, _ -> raise @@ InterExn "spec_title_filter:extract_target"
    in
    let pred, var = extract_target target in
    let tmp = List.map (fun x ->
        let pred', var' = extract_target x in
        not ((String.equal pred pred') && (var == var'))
      ) spec_title in
    let spec_title' = List.filter_mapi (fun i x ->
        if List.nth tmp i then Some x else None
      ) spec_title in
    let indx = List.lookup (fun (pred, dt, args) (pred', dt', args') ->
        (String.equal pred pred') && (IntList.eq args args') &&
        (match dt, dt' with
         | None, None -> true
         | Some dt, Some dt' -> dt == dt'
         |_,_ -> false)
      ) target spec_title in
    let vecs' = List.map (fun one ->
        List.nth one indx, List.filter_mapi (fun i x ->
            if List.nth tmp i
            then Some x
            else None
          ) one ) vecs in
    spec_title', vecs'

  let spec_feature_apply (pred, dt, args) values =
    let args = List.map (fun i -> List.nth values i) args in
    let exec_eq args =
      match args with
      | [V.I a; V.I b] -> a == b
      | _ -> raise @@ InterExn "exec_eq" in
    match dt, pred with
    | None, "==" -> exec_eq args
    | Some dt, pred ->
      let dt = List.nth values dt in
      P.apply (pred, dt, args)
    | _ , _ -> raise @@ InterExn "spec_feature_apply"

  type classes = Pos | Neg | Unknown | Pending
  type data = (bool * (bool list)) list
  type sides =
    | Single of data
    | Double of data * data

  let print_data data =
    List.iter (fun (label, vec) ->
        printf "[%b]:%s\n" label (boollist_to_string vec)
      ) data

  let spec_infer ~progtp ~prog =
    let fv_num = 2 in
    let inptps, outptps, fv_idxs = make_spec_var_assign progtp fv_num in
    let args = (List.filter_map
                  (fun (tp, idx) -> match tp with
                     | T.Int -> Some idx
                     | _ -> None
                  ) (inptps @ outptps)) @ fv_idxs in
    let inp_title = make_spec_title inptps args in
    let outp_title = make_spec_title outptps args in
    let inner_title = make_inner_title args in
    let _ = printf "inp_title = %s\n" (layout_spec_title inp_title) in
    let _ = printf "outp_title = %s\n" (layout_spec_title outp_title) in
    let _ = printf "inner_title = %s\n" (layout_spec_title inner_title) in
    let spec_title = outp_title @ inp_title @ inner_title in
    let target = make_target_title outptps fv_idxs in
    let _ = printf "target = %s\n" (layout_spec_title target) in
    let make_inps inpvars =
      let intvars = List.filter_map (fun (tp, idx) ->
          match tp with
          | T.Int -> Some (tp, idx)
          | T.Bool -> raise @@ InterExn "make_inps"
          | _ -> None
        ) inpvars in
      let dtvars = List.filter_map (fun (tp, idx) ->
          if T.is_dt tp then Some (tp, idx) else None) inpvars in
      let int_num = fv_num + (List.length intvars) + 1 in
      let range = List.init int_num (fun i -> i) in
      let sample_one (dt, idx) =
        match dt with
        | T.Int -> idx, List.map (fun i -> V.I i) range
        | T.IntList -> idx, randomgen_list2 range
        | T.IntTree -> idx, randomgen_tree2 range
        | T.Bool -> raise @@ InterExn "sample_one"
      in
      let intsamples = match intvars with
        | (_, idx) :: t -> (idx, [V.I 0]) :: (List.map sample_one t)
        | [] -> [] in
      let dtsamples = List.map sample_one dtvars in
      let samples = (intsamples @ dtsamples) in
      let _, samples = List.split
          (List.sort (fun (a, _) (b, _) -> - (compare a b)) samples) in
      range, List.choose_list_list samples
    in
    let range, inps = make_inps inptps in
    let samples = List.filter_map (fun inp ->
        try Some (inp @ (prog inp)) with InterExn _ -> None) inps in
    (* let _ = List.iter (fun s ->
     *     printf "[%s]\n" (List.to_string V.layout s)) samples in *)
    let fvv = List.map (fun fv -> List.map (fun x -> V.I x) fv) @@
      List.choose_n_eq (fun x y -> x == y) range fv_num in
    let _ = List.iter (fun fv -> printf "fv:%s\n" (List.to_string V.layout fv)) fvv in
    let samples = List.map (fun (a, b) -> a @ b) @@ List.cross samples fvv in
    let vecs = List.map
        (fun x -> List.map (fun t -> spec_feature_apply t x) spec_title) samples in
    (* let _ = List.iter (fun vec ->
     *     printf "%s\n" (boollist_to_string vec)
     *   ) vecs in *)
    let make_arginfo inptps outptps fv_idxs =
      let m = IntMap.empty in
      let make_name = function
        | T.Int -> "x"
        | T.IntList -> "l"
        | T.IntTree -> "tr"
        | T.Bool -> "b"
      in
      let aux m vars =
        List.fold_left (fun m (tp, idx) ->
            IntMap.add idx {D.name = sprintf "%s%i" (make_name tp) idx;
                            D.tp = tp;
                            D.free = false} m
          ) m vars in
      let m = aux m inptps in
      let m = aux m outptps in
      List.fold_left (fun m idx ->
          IntMap.add idx {D.name = sprintf "u%i" idx;
                          D.tp = T.Int;
                          D.free = true} m) m fv_idxs
    in
    let infos = make_arginfo inptps outptps fv_idxs in
    let make_args_fv m =
      let args, fv = IntMap.fold (fun idx info (args, fv) ->
          if info.D.free
          then args, (idx,info.D.name) :: fv
          else (idx,info.D.name) :: args, fv
        ) m ([], []) in
      let _, args = List.split (List.sort (fun a b -> - (compare a b)) args) in
      let _, fv = List.split (List.sort (fun a b -> - (compare a b)) fv) in
      args, fv
    in
    let split_vecs vecs =
      let vecs = Array.of_list vecs in
      let len = Array.length vecs in
      let classes = Array.init len (fun _ -> Pending) in
      let if_two_side = ref false in
      let rec find (label, vec) i =
        if i >= len then false else
          let label', vec' = vecs.(i) in
          if (List.eq (fun x y -> x == y) vec' vec) && (label != label')
          then (if_two_side := true; true)
          else find (label, vec) (i+1)
      in
      let _ = Array.iteri (fun idx (label, vec) ->
          if find (label, vec) 0
          then Array.set classes idx Unknown
          else if label then Array.set classes idx Pos
          else Array.set classes idx Neg) vecs
      in
      if !if_two_side then
        let left = Array.to_list @@ Array.mapi
            (fun idx (_, vec) ->
               match classes.(idx) with
               | Pos -> (true, vec)
               | Neg -> (false, vec)
               | Unknown -> (true, vec)
               | Pending -> raise @@ InterExn "vecs_to_left_right"
            ) vecs in
        let right = Array.to_list @@ Array.mapi
            (fun idx (_, vec) ->
               match classes.(idx) with
               | Pos -> (true, vec)
               | Neg -> (false, vec)
               | Unknown -> (false, vec)
               | Pending -> raise @@ InterExn "vecs_to_left_right"
            ) vecs in
        Double (left, right)
      else
        Single (Array.to_list vecs)
    in
    let make_spec target =
      let title', vecs'= spec_title_filter spec_title vecs target in
      (* let _ = printf "title' = %s\n" (layout_spec_title title') in *)
      (* let _ = print_data vecs' in
       * let _ = printf "title' = %s\n" (layout_spec_title title') in *)
      let one_side vecs =
        Epr.simplify_ite @@ D.to_spec2 (spec_classify title' vecs) infos in
      let target_expr = D.feature_to_epr2 target
          (IntMap.map (fun info -> info.D.name) infos) in
      match split_vecs vecs' with
      | Single vecs' ->
        Epr.Iff (target_expr, one_side vecs')
      | Double (l, r) ->
        Epr.And [
          Epr.Implies (target_expr, one_side l);
          Epr.Implies (one_side r, target_expr);
        ]
    in
    let args, fv = make_args_fv infos in
    let spec = Epr.And (List.map (fun target -> make_spec target) target) in
    let spec = args, (fv, spec) in
    let _ = printf "spec:%s\n" (Ast.layout_spec spec) in
    [], ([],Epr.True)


  let axiom_infer ~ctx ~vc ~spectable ~pred_names ~dttp =
    (* TODO: handle literal integers... *)
    let _, vars = Ast.extract_variables vc in
    let dtnames = List.filter_map (fun (tp, name) ->
        if T.is_dt tp then Some name else None) vars in
    let intnames = List.filter_map (fun (tp, name) ->
        match tp with
        | T.Int -> Some name
        | _ -> None) vars in
    (* let _ = List.iter (fun name -> printf "var:%s\n" name) dtnames in *)
    let neg_vc_nnf = Ast.to_nnf (Ast.Not vc) in
    let neg_vc_nnf_applied = Ast.application neg_vc_nnf spectable in
    let exists_fv, neg_vc_skolemized = Ast.skolemize neg_vc_nnf_applied in
    let _ = printf "exists_fv:%s\nvc:%s\n"
        (List.to_string (fun x -> x) exists_fv) (Ast.vc_layout neg_vc_skolemized) in
    let counter = ref max_main_loop_times in
    (* TODO: increase number of fv automatically... *)
    let fv_num = 1 in
    let title = make_title pred_names fv_num in
    let _ = printf "%s\n" (layout_title title) in
    let neg_vc_with_ax axiom =
      Boolean.mk_and ctx [
        (* additional_axiom ctx; *)
        Ast.to_z3 ctx neg_vc_skolemized spectable
        ; Epr.forallformula_to_z3 ctx axiom] in
    let rec main_loop positives negatives axiom =
      let _ =
        if (!counter) <= 0 then
          raise @@ InterExn "main_loop: too many iterations"
        else counter:= (!counter) - 1 in
      let valid, _ = S.check ctx (neg_vc_with_ax axiom) in
      if valid then axiom else
        let range = (0, 3) in
        let constraints = interval ctx (intnames @ exists_fv) range in
        let _, m = S.check ctx (Boolean.mk_and ctx [constraints; neg_vc_with_ax axiom]) in
        let m = match m with None -> raise @@ InterExn "bad range" | Some m -> m in
        let _ = printf "model=\n%s\n" (Model.to_string m) in
        let int_to_se i = SE.Literal (T.Int, SE.L.Int i) in
        let get_interpretation ctx m title dtname args =
          let args = List.map int_to_se args in
          let title_b = List.map
              (fun feature -> D.feature_to_epr feature ~dtname:dtname ~fv:args) title in
          let title_z3 = List.map (fun b -> Epr.to_z3 ctx b) title_b in
          let feature_vec = List.map (fun z -> S.get_pred m z) title_z3 in
            printf "%s(%s):%s\n" dtname (List.to_string SE.layout args)
              (boollist_to_string feature_vec); feature_vec
          (* List.map (fun z -> S.get_pred m z) title_z3 *)
        in
        let all_args = List.choose_n_eq (fun x y -> x == y) (IntList.of_range range) fv_num in
        let all_args_vec dtname =
          List.combine all_args
            (List.map (fun args -> get_interpretation ctx m title dtname args) all_args) in
        let all_args_vec = List.flatten (List.map all_args_vec dtnames) in
        (* let _ = printf "num:%i\n" (List.length all_args_vec) in *)
        let booll_eq vec vec' = List.eq (fun x y -> x == y) vec vec' in
        let all_args_vec = List.remove_duplicates
            (fun (_, vec) (_, vec') -> booll_eq vec vec') all_args_vec in
        let _ = List.iter
            (fun (args, vec) -> printf "%s:%s\n"
                (IntList.to_string args) (boollist_to_string vec)) all_args_vec in
        let mk_positives positives args =
          let dts = randomgen args dttp in
          let samples = List.map
              (fun dt -> make_sample title dt (List.map (fun i -> V.I i) args)) dts in
          let positives = positives @ samples in
          List.remove_duplicates (fun p p' -> booll_eq p.vec p'.vec) positives
        in
        let update (positives, negatives) (args, vec) =
          let eq_that_vec p = booll_eq p.vec vec in
          match List.find_opt eq_that_vec positives with
          | Some _ -> positives, negatives
          | None ->
            let samples = mk_positives positives args in
            let aux negs =
              List.filter_map (fun n ->
                  match List.find_opt (fun p -> booll_eq p.vec n.vec) samples with
                  | Some _ -> None
                  | None -> Some n
                ) negs in
            let negatives =
              (cex_to_sample (List.map (fun i -> V.I i) args) vec) :: negatives in
            let positives =
              List.remove_duplicates (fun p p' -> booll_eq p.vec p'.vec) (samples @ positives)
            in
            positives, aux negatives
        in
        let positives, negatives =
          List.fold_left update (positives, negatives) all_args_vec in
        (* let _ = printf "title: %s\n" (layout_title title) in
         * let _ = List.iter (fun pos -> printf "pos:%s\n" (layout_sample pos)) positives in
         * let _ = List.iter (fun neg -> printf "neg:%s\n" (layout_sample neg)) negatives in *)
        let axiom = classify title ~pos:positives ~neg:negatives in
        let axiom = D.to_forallformula axiom ~dtname:"dt" in
        let axiom = Epr.forallformula_simplify_ite axiom in
        let _ = printf "axiom:%s\n" (Epr.layout_forallformula axiom) in
        let _ = printf "axiom:%s\n" (Expr.to_string (Epr.forallformula_to_z3 ctx axiom)) in
        main_loop positives negatives axiom
        (* raise @@ InterExn "zz" *)
    in
    main_loop [] [] ([], True)
end

module Syn = AxiomSyn(Dtree.Dtree)(Ml.FastDT.FastDT)
