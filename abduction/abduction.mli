(**
 * The main entry point for performing multiabduction as described in "Maximal
 * Specification Synthesis" by Albarghouthi et al.:
 * http://pages.cs.wisc.edu/~aws/papers/popl16.pdf
 *)

(**
 * Abduces maximal interpretations for function symbols appearing in a pre-
 * and post-condition but not present in an accompanying specification mapping.
 *
 * Accepts a precondition P, a postcondition Q, and a specification mapping M,
 * and returns an interpretation mapping M' of all function calls appearing P
 * and Q but not in M such that:
 *   P /\ M /\ M' |= Q  and
 *   P /\ M /\ M' |/= False
 *
 * The returned interpretations are guaranteed to be maximal up to Pareto
 * optimality. That is, it is impossible to weaken any of the abduced
 * specifications without strengthening another.
 *
 * If abduction could not be completed for any reason, returns a string
 * containing an error message.
 *)
val abduce : Z3.context ->
             Language.SpecAst.spec Utils.StrMap.t ->
             Language.SpecAst.t ->
             Language.SpecAst.t ->
             (Z3.Expr.expr Utils.StrMap.t, string) result
