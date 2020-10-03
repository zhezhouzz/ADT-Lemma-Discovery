module type Randomgen = sig
  val gen: chooses:int list -> num:int -> tp:Tp.Tp.t -> Pred.Value.t list
  val gen_tpvars: tpvars:(Tp.Tp.t*string) list -> num: int -> fv_num:int -> int list * Pred.Value.t list list
end

module Randomgen : Randomgen = struct
  open Utils
  module V = Pred.Value
  module T = Tp.Tp
  let randomgen_list (chooses: int list) (num: int) =
    let list_gen = QCheck.Gen.(list_size (int_bound 10) (oneofl chooses)) in
    let s = QCheck.Gen.generate ~n:(2*num) list_gen in
    let s = List.remove_duplicates IntList.eq s in
    if List.length s < num then raise @@ InterExn "randomgen_list" else
      List.map (fun l -> V.L l) @@ List.sublist s (0, num)

  let randomgen_tree (chooses: int list) (num: int) =
    (* let _ = printf "chooses:%s\n" (IntList.to_string values) in *)
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
    let trs = QCheck.Gen.generate ~n:(2*num) tree_gen in
    let trs = List.remove_duplicates (Tree.eq (fun x y -> x == y)) trs in
    (* let _ = List.iter (fun tr ->
     *     printf "tr:%s\n" (Tree.layout string_of_int tr)
     *   ) trs in *)
    if List.length trs < num then raise @@ InterExn "randomgen_tree" else
      List.map (fun l -> V.T l) @@ List.sublist trs (0, num)
  let gen ~chooses ~num ~tp =
    match tp with
    | T.Int -> List.map (fun i -> V.I i) chooses
    | T.IntList -> randomgen_list chooses num
    | T.IntTree -> randomgen_tree chooses num
    | T.Bool -> raise @@ UndefExn "gen"

  let gen_tpvars ~tpvars ~num ~fv_num =
    let intvars, dtvars =
      List.fold_lefti (fun (intvars, dtvars) idx (tp, _) ->
          if T.is_dt tp then intvars, (tp, idx) :: dtvars else
            match tp with
            | T.Int -> (tp, idx) :: intvars, dtvars
            | _ -> raise @@ UndefExn "gen_tpvars"
        ) ([], []) tpvars in
    let int_num = fv_num + (List.length intvars) + 1 in
    let chooses = List.init int_num (fun i -> i) in
    let intsamples = match intvars with
      | (_, idx) :: t ->
        (idx, [V.I 0]) :: (List.map (fun (tp, idx) ->
            idx, gen ~chooses:chooses ~num:num ~tp:tp) t)
      | [] -> [] in
    let dtsamples = List.map (fun (tp, idx) ->
        idx, gen ~chooses:chooses ~num:num ~tp:tp) dtvars in
    let _, samples = List.split
        (List.sort (fun (a, _) (b, _) -> - (compare a b)) (intsamples @ dtsamples)) in
    chooses, List.choose_list_list samples
end
