module type AxiomSyn = sig
  module D: Dtree.Dtree
  module E: Preds.Elem.Elem with type t = D.P.E.t
  type vec = bool list
  type sample = {dt: E.t; args: E.t list; vec: vec}
  type title = D.feature list
  val layout_title: title -> string
  val make_sample: title -> E.t -> E.t list -> sample
  val cex_to_sample: E.t list -> vec -> sample
  val layout_sample: sample -> string
  val classify: title -> pos: sample list -> neg: sample list -> D.t
end

module AxiomSyn (D: Dtree.Dtree): AxiomSyn = struct
  module D = D
  module E = D.P.E
  open Utils
  open Printf
  type vec = bool list
  type sample = {dt: E.t; args: E.t list; vec: vec}
  type title = D.feature list

  let layout_title (title: title) =
    List.fold_left (fun r pred -> sprintf "%s [%s]" r (D.layout_feature pred)) "" title

  let make_sample (title:title) (dt: E.t) (args: E.t list) =
    let vec = List.map (fun feature -> D.exec_feature feature dt args) title in
    {dt; args; vec}

  let cex_to_sample (args: E.t list) (vec: bool list) =
    {dt = E.NotADt; args; vec}

  let layout_sample {dt; args; vec} =
    sprintf "%s(%s) [%s]" (E.layout dt) (list_to_string E.layout args) (boollist_to_string vec)

  let classify_ (title: title) (_:vec list) (_:vec list) : D.t =
    let member0 = List.nth title 0 in
    let ord = List.nth title 2 in
    D.Node (ord, D.Leaf member0, D.T)

  let classify title ~pos ~neg =
    let pos = List.map (fun s -> s.vec) pos in
    let neg = List.map (fun s -> s.vec) neg in
    classify_ title pos neg
end
