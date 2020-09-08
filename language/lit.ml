module type Lit = sig
  include LitTree.LitTree
  type value = Preds.Pred.Element.t
  val exec: t -> value
end

module Lit (L: LitTree.LitTree): Lit = struct
  module P = Preds.Pred.Predicate
  module E = P.E
  include L
  type value = E.t
  let exec = function
    | Int i -> E.I i
    | Bool b -> E.B b
    | IntList il -> E.L il
    | IntTree it -> E.T it
end
