module type AxiomSyn = sig
  module D: Dtree.Dtree
  type vec = bool list
  type et = Preds.Pred.Element.t
  type sample = {dt: et; args: et list; vec: vec}
  type title = D.feature list
  val layout_title: title -> string
  val make_title: int -> title
  val make_sample: title -> et -> et list -> sample
  val cex_to_sample: et list -> vec -> sample
  val layout_sample: sample -> string
  val classify: title -> pos: sample list -> neg: sample list -> D.t
end

module AxiomSyn (D: Dtree.Dtree) (F: Ml.FastDT.FastDT) = struct
  module D = D
  module E = Preds.Pred.Element
  module P = Preds.Pred.Predicate
  open Utils
  open Printf
  type vec = bool list
  type sample = {dt: E.t; args: E.t list; vec: vec}
  type title = D.feature list

  let make_title fvs_num =
    let aux info =
      let _ = printf "%s(arglen = %i)\n" info.P.name info.P.num_int in
      let fvs_c = List.combination fvs_num info.P.num_int in
      List.map (fun fv_c -> (info.P.name, fv_c)) fvs_c
    in
    List.fold_left (fun r info -> r @ (aux info)) [] P.preds_info

  let layout_title (title: title) =
    List.fold_left (fun r pred -> sprintf "%s [%s]" r (D.layout_feature pred)) "" title

  let make_sample (title:title) (dt: E.t) (args: E.t list) =
    let vec = List.map (fun feature -> D.exec_feature feature dt args) title in
    {dt; args; vec}

  let cex_to_sample (args: E.t list) (vec: bool list) =
    {dt = E.NotADt; args; vec}

  let layout_sample {dt; args; vec} =
    sprintf "%s(%s) [%s]" (E.layout dt) (List.to_string E.layout args) (boollist_to_string vec)

  let classify_ (title: title) (_:vec list) (_:vec list) : D.t =
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
end

module Syn = AxiomSyn(Dtree.Dtree)(Ml.FastDT.FastDT)
