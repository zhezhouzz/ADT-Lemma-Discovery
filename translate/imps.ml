open Utils;;

let imps =
  ["Customstk", [
      `StackIsEmpty List.is_empty;
      `StackPush List.cons;
      `StackTop List.hd;
      `StackTail List.tl;
      `Concat (fun l1 l2 -> l1 @ l2);
    ] ]

let find name =
  snd @@ List.find "imp find" (fun (name', _) -> String.equal name' name) imps
