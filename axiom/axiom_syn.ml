module AxiomSyn (P: Preds.Pred.Pred) = struct
  open Utils
  open Printf
  module E = P.E
  type vec = bool list
  type sample = {dt: E.t; args: E.t list; vec: vec}
  type feature = P.t * int list
  type title = feature list
  type result =
    | T
    | F
    | Atom of feature
    | Ite of feature * result * result

  let vartable = List.fold_left (fun m (k,v) ->
      IntMap.add k v m
    ) IntMap.empty [0, "u";1, "v";2, "w"]

  let layout_title (title: title) =
    let playout (pred, ids) =
      let args = List.map (fun id -> IntMap.find id vartable) ids in
      sprintf "%s(%s)" (P.layout pred) (list_to_string (fun x -> x) args)
    in
    List.fold_left (fun r pred -> sprintf "%s [%s]" r (playout pred)) "" title

  let feature_apply (pred, ids) (dt: E.t) (args: E.t list) =
    let lookup i =
      match List.nth_opt args i with
      | None -> raise @@ InterExn "feature_apply::lookup"
      | Some v -> v
    in
    P.apply (pred, dt, (List.map lookup ids))

  let make_sample (title:title) (dt: E.t) (args: E.t list) =
    let vec = List.map (fun feature -> feature_apply feature dt args) title in
    {dt; args; vec}

  let cex_to_sample (args: E.t list) (vec: bool list) =
    {dt = E.NotADt; args; vec}

  let layout_sample {dt; args; vec} =
    sprintf "%s(%s) [%s]" (E.layout dt) (list_to_string E.layout args) (boollist_to_string vec)

  let classify (title: title) (_:vec) : result =
    let member0 = List.nth title 0 in
    let ord = List.nth title 2 in
    Ite (ord, Atom member0, T)

  let result_apply (result:result) (dt: E.t) (args: E.t list) =
    let rec aux = function
      | T -> true
      | F -> false
      | Atom feature -> feature_apply feature dt args
      | Ite (feature, l, r) ->
        if feature_apply feature dt args
        then aux l
        else aux r
    in
    aux result
end
