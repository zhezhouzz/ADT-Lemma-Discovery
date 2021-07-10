module type Stream = sig
  type t
  val nil: t
  val cons: int -> t -> t
  val liblazy: t -> t
  val libforce: t -> t
end

val reverse: Stream.t -> Stream.t -> Stream.t

let reverse (acc: Stream.t) (s: Stream.t) =
  Stream.liblazy (
    match s with
    | _ when (Stream.liblazy Stream.nil) -> Stream.libforce acc
    | _ when (Stream.liblazy (Stream.cons (hd: int) (tl: Stream.t))) ->
      Stream.libforce (reverse (Stream.liblazy (Stream.cons hd acc)) tl)
  )
