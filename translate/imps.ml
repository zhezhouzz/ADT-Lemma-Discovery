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
   ];
   "Batchedq", [
     `BatchedqNil List.[];
     `BatchedqCons List.cons;
     `BatchedqRev List.rev;
     `BatchedqIsEmpty List.is_empty;
     `Tail (fun f r ->
         match f, r with
         | [], _ -> failwith "empty"
         | _ :: f, r ->
           if List.is_empty f then (List.rev r, f) else f, r
       )
   ];
   "Leftisthp", [
     `LeftisthpLeaf LabeledTree.Leaf;
     `LeftisthpTree (fun r x a b -> LabeledTree.Node (r, x, a, b));
     `LeftisthpMakeTree (fun x a b ->
         LabeledTree.(
           let rank = function Leaf -> 0 | Node (r, _, _ ,_) -> r in
           if rank a >= rank b
           then Node (rank b + 1, x, a, b)
           else Node (rank a + 1, x, b, a)
         )
       );
     `Merge (fun tree1 tree2 ->
         LabeledTree.(
           let rank = function Leaf -> 0 | Node (r,_,_,_) -> r in
           let makeT x a b =
             if rank a >= rank b then Node (rank b + 1, x, a, b)
             else Node (rank a + 1, x, b, a)
           in
           let rec merge tree1 tree2 =
             match tree1, tree2 with
             | tree1, Leaf -> tree1
             | Leaf, tree2 -> tree2
             | Node (_, x, a1, b1), Node (_, y, a2, b2) ->
               if x <= y then makeT x a1 (merge b1 tree2)
               else makeT y a2 (merge tree1 b2)
           in
           merge tree1 tree2)
       )
   ];
   "Rbset", [
     `RbsetLeaf LabeledTree.Leaf;
     `RbsetTree (fun (r: bool) a x b -> LabeledTree.Node (r, x, a, b));
     `Balance (fun (r: bool) tree1 x tree2 ->
         LabeledTree.(
           let balance = function
             | false, Node (true, y, Node (true, x, a, b), c), z, d
             | false, Node (true, x, a, Node (true, y, b, c)), z, d
             | false, a, x, Node (true, z, Node (true, y, b, c), d)
             | false, a, x, Node (true, y, b, Node (true, z, c, d)) ->
               Node (true, y, Node (false, x, a, b), Node (false, z, c, d))
             | a, b, c, d -> Node (a, c, b, d)
           in
           balance (r, tree1, x, tree2)
         )
       )
   ];
   "Splayhp", [
     `SplayhpLeaf Tree.Leaf;
     `SplayhpNode (fun a x b -> Tree.Node (x, a, b));
     `Partition (fun (pivot: int) (tr: int Tree.t) ->
         Tree.(
           let rec partition pivot : int Tree.t -> (int Tree.t) * (int Tree.t) = function
             | Leaf -> Leaf, Leaf
             | Node (x, a, b) as tr ->
               if x <= pivot then
                 match b with
                 | Leaf -> tr, Leaf
                 | Node (y, b1, b2) ->
                   if y <= pivot then
                     let small, big = partition pivot b2 in
                     Node (y, Node (x, a, b1), small), big
                   else
                     let small, big = partition pivot b1 in
                     Node (x, a, small), Node (y, big, b2)
               else
                 match a with
                 | Leaf -> Leaf, tr
                 | Node (y, a1, a2) ->
                   if y <= pivot then
                     let small, big = partition pivot a2 in
                     Node (y, a1, small), Node (x, big, b)
                   else
                     let small, big = partition pivot a1 in
                     small, Node (y, big, Node (x, a2, b))
           in
           partition pivot tr
         )
       )
   ];
   "Stream", [
     `StreamNil List.[];
     `StreamCons List.cons;
     `StreamLiblazy (fun x -> x);
     `StreamLibforce (fun x -> x);
     `Reverse (fun acc s -> acc @ (List.rev s))
   ];
   "Trie", [
     `TrieNil List.[];
     `TrieCons List.cons;
     `TrieLeaf Tree.Leaf;
     `TrieNode (fun l (x: int) r -> Tree.Node (x, l, r));
     `Ins (fun default i a m ->
         Tree.(
           let rec ins default i a m =
             match m with
             | Leaf ->
               (match i with
                | [] -> Node(a, Leaf, Leaf)
                | z :: i' ->
                  if z > 0
                  then Node(default, ins default i' a Leaf, Leaf)
                  else Node(default, Leaf, ins default i' a Leaf)
               )
             | Node(y, l, r) ->
               (match i with
                | [] -> Node(a, l, r)
                | z :: i' ->
                  if z > 0
                  then Node(y, ins default i' a l, r)
                  else Node(y, l, ins default i' a r)
               )
           in
           ins default i a m
         )
       )
   ];
   "Unbset", [
     `UnbsetLeaf Tree.Leaf;
     `UnbsetNode (fun a x b -> Tree.Node (x, a, b));
     `Insert (fun (x: int) tree3 ->
         Tree.(
           let rec insert x tree3 =
             match tree3 with
             | Leaf -> Node (x, Leaf, Leaf)
             | Node (y, tree1, tree2) ->
               if x < y then Node (x, insert y tree1, tree2)
               else if y < x then Node (y, tree1, insert x tree2)
               else Node (y, tree1, tree2)
           in
           insert x tree3
         )
       )
   ];
   "Uniquel", [
     `UniquelNil List.[];
     `UniquelCons List.cons;
     `SetAdd (fun a x ->
         let rec set_add a x =
           match x with
           | [] -> [a]
           | a1 :: x1 ->
             if a == a1 then a1 :: x1 else a1 :: (set_add a x1)
         in
         set_add a x
       )
   ];
  ]

let find name =
  snd @@ List.find (Printf.sprintf "imps cannot find(%s)" name) (fun (name', _) -> String.equal name' name) imps
