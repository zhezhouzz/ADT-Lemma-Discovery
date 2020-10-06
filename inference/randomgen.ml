module type Randomgen = sig
  val gen: chooses:int list -> num:int -> tp:Tp.Tp.t -> Pred.Value.t list
  val gen_tpvars: tpvars:(Tp.Tp.t*string) list -> num: int -> fv_num:int -> int list * Pred.Value.t list list
end

module Randomgen : Randomgen = struct
  open Utils
  module V = Pred.Value
  module T = Tp.Tp

  let unique_gen gen num eq =
    let rec aux r =
      let trs = QCheck.Gen.generate ~n:num gen in
      let trs = List.remove_duplicates eq (r @ trs) in
      if List.length trs < num then aux trs else
         List.sublist trs (0, num)
    in
    aux []

  let randomgen_list (chooses: int list) (num: int) =
    let list_gen = QCheck.Gen.(list_size (int_bound 8) (oneofl chooses)) in
    List.map (fun l -> V.L l) @@ unique_gen list_gen num IntList.eq
    (* let s = QCheck.Gen.generate ~n:(2*num) list_gen in
     * let s = [] :: s in
     * let s = List.remove_duplicates IntList.eq s in
     * if List.length s < num then raise @@ InterExn "randomgen_list" else
     *   List.map (fun l -> V.L l) @@ List.sublist s (0, num) *)

  let randomgen_tree (chooses: int list) (num: int) =
    let _ = Printf.printf "chooses:%s\n" (IntList.to_string chooses) in
    let node a l r = Tree.Node (a, l, r) in
    let tree_gen =
      QCheck.Gen.((sized_size (int_bound 10)) @@ fix
                    (fun self n -> match n with
                       | 0 -> oneofl [Tree.Leaf]
                       | n ->
                         frequency
                           [1, oneofl [Tree.Leaf];
                            3, QCheck.Gen.map3 node (oneofl chooses)
                              (self (n/2)) (self (n/2))]
                    ))
    in
    List.map (fun l -> V.T l) @@ unique_gen tree_gen num (Tree.eq (fun x y -> x == y))

  let randomgen_labeled_tree gen (chooses: int list) (num: int) =
    let _ = Printf.printf "chooses:%s\n" (IntList.to_string chooses) in
    let node labal a l r = LabeledTree.Node (labal, a, l, r) in
    let tree_gen =
      QCheck.Gen.(
        let map4 f x y z k st = f (x st) (y st) (z st) (k st) in
        (sized_size (int_bound 10)) @@ fix
                    (fun self n -> match n with
                       | 0 -> oneofl [LabeledTree.Leaf]
                       | n ->
                         frequency
                           [1, oneofl [LabeledTree.Leaf];
                            3, map4 node gen (oneofl chooses)
                              (self (n/2)) (self (n/2))]
                    ))
    in
    unique_gen tree_gen num (LabeledTree.eq (fun x y -> x == y))

  let randomgen_labeled_treei chooses num =
    List.map (fun l -> V.TI l) @@
    randomgen_labeled_tree (QCheck.Gen.oneofl chooses) chooses num

  let randomgen_labeled_treeb chooses num =
    List.map (fun l -> V.TB l) @@
    randomgen_labeled_tree (QCheck.Gen.oneofl [true;false]) chooses num

  let gen ~chooses ~num ~tp =
    match tp with
    | T.Int -> List.map (fun i -> V.I i) chooses
    | T.IntList -> randomgen_list chooses num
    | T.IntTree -> randomgen_tree chooses num
    | T.IntTreeI -> randomgen_labeled_treei chooses num
    | T.IntTreeB -> randomgen_labeled_treeb chooses num
    | T.Bool -> [V.B true; V.B false]

  let gen_tpvars ~tpvars ~num ~fv_num =
    let intvars, dtvars, bvars =
      List.fold_lefti (fun (intvars, dtvars, bvars) idx (tp, _) ->
          if T.is_dt tp then intvars, (tp, idx) :: dtvars, bvars else
            match tp with
            | T.Int -> (tp, idx) :: intvars, dtvars, bvars
            | T.Bool -> intvars, dtvars, (tp, idx) :: bvars
            | _ -> raise @@ UndefExn "gen_tpvars"
        ) ([], [], []) tpvars in
    let _ =
      List.iter (fun (tp, idx) -> Printf.printf "tp(%s)|idx(%i)\n" (T.layout tp) idx) intvars in
    let _ =
      List.iter (fun (tp, idx) -> Printf.printf "tp(%s)|idx(%i)\n" (T.layout tp) idx) dtvars in
    let int_num = fv_num + (List.length intvars) + 1 in
    let chooses = List.init int_num (fun i -> i) in
    let bsamples = List.map (fun (tp, idx) ->
        idx, gen ~chooses:chooses ~num:num ~tp:tp) bvars in
    let intsamples = match intvars with
      | (_, idx) :: t ->
        (idx, [V.I 0]) :: (List.map (fun (tp, idx) ->
            idx, gen ~chooses:chooses ~num:num ~tp:tp) t)
      | [] -> [] in
    let dtsamples = List.map (fun (tp, idx) ->
        idx, gen ~chooses:chooses ~num:num ~tp:tp) dtvars in
    (* let _ = List.iter (fun tr ->
     *     Printf.printf "tr:%s\n" (V.layout tr)
     *   ) (snd (List.nth dtsamples 0)) in *)
    let _, samples = List.split
        (List.sort (fun (a, _) (b, _) -> (compare a b)) (intsamples @ dtsamples @ bsamples)) in
    chooses, List.choose_list_list_order samples
end
