module type LitSemantic = sig
  include Lit.Lit
  type value
  val exec: t -> value
end

module LitSemantic (L: Lit.Lit) (E: Preds.Elem.Elem):
  LitSemantic with type value = E.t = struct
  include L
  type value = E.t
  let exec = function
    | Int i -> E.I i
    | Bool b -> E.B b
    | IntList il -> E.L il
    | IntTree it -> E.T it
end
