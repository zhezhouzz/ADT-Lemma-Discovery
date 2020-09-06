(* module type BexprSemantic = sig
 *   module B: Bexpr.Bexpr
 *   module P: Preds.Pred.Pred
 *   val fv: B.t -> string list
 *   val type_check : B.t -> (B.t * bool)
 *   val exec: B.t -> P.E.t list -> P.E.t
 * end *)
