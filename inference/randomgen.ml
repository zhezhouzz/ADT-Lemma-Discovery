module type Randomgen = sig
  val gen: chooses:int list -> num:int -> tp:Tp.Tp.t -> bound:int -> Pred.Value.t list
  val gen_tpvars: tpvars:(Tp.Tp.t*string) list -> num: int -> fv_num:int -> bound:int -> int list * Pred.Value.t list list
end

module Randomgen : Randomgen = struct
  open Utils
  module V = Pred.Value
  module T = Tp.Tp

  let unique_gen gen num eq =
    let rec aux r =
      let trs = QCheck.Gen.generate ~rand:(Random.State.make [|Random.int 100|]) ~n:num gen in
      (* let trs = QCheck.Gen.generate ~rand:(Random.get_state ()) ~n:num gen in *)
      let trs = List.remove_duplicates eq (r @ trs) in
      if List.length trs < num then aux trs else
         List.sublist trs (0, num)
    in
    aux []

  let randomgen_list (chooses: int list) (num: int) (bound: int) =
    let list_gen = QCheck.Gen.(list_size (int_bound bound) (oneofl chooses)) in
    let result = List.map (fun l -> V.L l) @@
      [] :: (unique_gen list_gen num IntList.eq) in
    (* let  _ = Printf.printf "list:\n";
     *   List.iter (fun l -> Printf.printf "%s\n" (V.layout l)) result in *)
    result

  let randomgen_tree (chooses: int list) (num: int) (bound: int) =
    (* let _ = Printf.printf "chooses:%s\n" (IntList.to_string chooses) in *)
    let node a l r = Tree.Node (a, l, r) in
    let tree_gen =
      QCheck.Gen.((sized_size (int_bound bound)) @@ fix
                    (fun self n -> match n with
                       | 0 -> oneofl [Tree.Leaf]
                       | n ->
                         frequency
                           [1, oneofl [Tree.Leaf];
                            3, QCheck.Gen.map3 node (oneofl chooses)
                              (self (n - 1)) (self (n - 1))]
                    ))
    in
    List.map (fun l -> V.T l) @@
    Tree.Leaf :: (unique_gen tree_gen num (Tree.eq (fun x y -> x == y)))

  let randomgen_labeled_tree gen (chooses: int list) (num: int) (bound: int) =
    (* let _ = Printf.printf "chooses:%s\n" (IntList.to_string chooses) in *)
    let node labal a l r = LabeledTree.Node (labal, a, l, r) in
    let tree_gen =
      QCheck.Gen.(
        let map4 f x y z k st = f (x st) (y st) (z st) (k st) in
        (sized_size (int_bound bound)) @@ fix
                    (fun self n -> match n with
                       | 0 -> oneofl [LabeledTree.Leaf]
                       | n ->
                         frequency
                           [1, oneofl [LabeledTree.Leaf];
                            3, map4 node gen (oneofl chooses)
                              (self (n - 1)) (self (n - 1))]
                    ))
    in
    unique_gen tree_gen num (LabeledTree.eq (fun x y -> x == y))

  let randomgen_labeled_treei chooses bound num =
    List.map (fun l -> V.TI l) @@
    LabeledTree.Leaf :: (randomgen_labeled_tree (QCheck.Gen.oneofl [0]) chooses num bound)

  let randomgen_labeled_treeb chooses bound num =
    List.map (fun l -> V.TB l) @@
    LabeledTree.Leaf :: (randomgen_labeled_tree (QCheck.Gen.oneofl [true;false]) chooses num bound)

  let gen ~chooses ~num ~tp ~bound =
    match tp with
    | T.Int -> List.map (fun i -> V.I i) chooses
    | T.IntList -> randomgen_list chooses num bound
    | T.IntTree -> randomgen_tree chooses num bound
    | T.IntTreeI -> randomgen_labeled_treei chooses num bound
    | T.IntTreeB -> randomgen_labeled_treeb chooses num bound
    | T.Bool -> [V.B true; V.B false]

  let gen_tpvars ~tpvars ~num ~fv_num ~bound =
    let intvars, dtvars, bvars =
      List.fold_lefti (fun (intvars, dtvars, bvars) idx (tp, _) ->
          if T.is_dt tp then intvars, (tp, idx) :: dtvars, bvars else
            match tp with
            | T.Int -> (tp, idx) :: intvars, dtvars, bvars
            | T.Bool -> intvars, dtvars, (tp, idx) :: bvars
            | _ -> raise @@ UndefExn "gen_tpvars"
        ) ([], [], []) tpvars in
    (* let _ =
     *   List.iter (fun (tp, idx) -> Printf.printf "tp(%s)|idx(%i)\n" (T.layout tp) idx) intvars in
     * let _ =
     *   List.iter (fun (tp, idx) -> Printf.printf "tp(%s)|idx(%i)\n" (T.layout tp) idx) dtvars in *)
    let int_num = fv_num + (List.length intvars) + 1 in
    let chooses = List.init int_num (fun i -> i) in
    let bsamples = List.map (fun (tp, idx) ->
        idx, gen ~chooses:chooses ~num:num ~tp:tp ~bound:bound) bvars in
    let intsamples = match intvars with
      | (_, idx) :: t ->
        (idx, [V.I 0]) :: (List.map (fun (tp, idx) ->
            idx, gen ~chooses:chooses ~num:num ~tp:tp ~bound:bound) t)
      | [] -> [] in
    let dtsamples = List.map (fun (tp, idx) ->
        idx, gen ~chooses:chooses ~num:num ~tp:tp ~bound:bound) dtvars in
    (* let _ = List.iter (fun tr ->
     *     Printf.printf "tr:%s\n" (V.layout tr)
     *   ) (snd (List.nth dtsamples 0)) in *)
    let _, samples = List.split
        (List.sort (fun (a, _) (b, _) -> (compare a b)) (intsamples @ dtsamples @ bsamples)) in
    chooses, List.choose_list_list_order samples
end
