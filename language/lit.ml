module type Lit = sig
  include LitTree.LitTree
  type value = Pred.Value.t
  val exec: t -> value
end

module Lit (L: LitTree.LitTree): Lit = struct
  module P = Pred.Pred
  module V = Pred.Value
  include L
  type value = V.t
  let exec = function
    | Int i -> V.I i
    | Bool b -> V.B b
    | IntList il -> V.L il
    | IntTree it -> V.T it
end
