module type LitSemantic = sig
  include Lit.Lit
  module E: Preds.Elem.Elem
  type value = E.t
  val exec: t -> value
end

module LitSemantic (L: Lit.Lit) (E: Preds.Elem.Elem):
  LitSemantic with type E.t = E.t = struct
  module E = E
  include L
  type value = E.t
  let exec = function
    | Int i -> E.I i
    | Bool b -> E.B b
    | IntList il -> E.L il
    | IntTree it -> E.T it
end
