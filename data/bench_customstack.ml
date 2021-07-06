module type Stack = sig
  type t
  val is_empty: t -> bool
  val push: int -> t -> t
  val top: t -> int
  val tail: t -> t
end

val concat: Stack.t -> Stack.t -> Stack.t

let rec concat (s1: Stack.t) (s2: Stack.t) : Stack.t =
  if Stack.is_empty s1 then s2
  else Stack.push (Stack.top s1) (concat (Stack.tail s1) s2)
