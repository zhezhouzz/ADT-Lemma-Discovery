open Utils;;

let imps =
  ["Customstk", [
      `StackIsEmpty List.is_empty;
      `StackPush List.cons;
      `StackTop List.hd;
      `StackTail List.tl;
      `Concat (fun l1 l2 -> l1 @ l2);
    ];
   "Bankersq", [
     `BankersqNil List.[];
     `BankersqCons List.cons;
     `BankersqLiblazy (fun x -> x);
     `BankersqLibforce (fun x -> x);
     `BankersqReverse List.rev;
     `BankersqConcat (fun l1 l2 -> l1 @ l2);
     `Snoc (fun lenf f lenr r x ->
         let snoc (lenf, f, lenr, r) x =
           let lenr = lenr + 1 in
           let r = x :: r in
           if lenr <= lenf then (lenf, f, lenr, r)
           else (lenf + lenr, f @ (List.rev r), 0, [])
         in
         snoc (lenf, f, lenr, r) x)
   ]
  ]

let find name =
  snd @@ List.find "imp find" (fun (name', _) -> String.equal name' name) imps
