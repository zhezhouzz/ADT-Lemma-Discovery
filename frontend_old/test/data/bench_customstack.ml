let rec concat l1 l2 =
  if is_empty l1 then l2
  else push (stack_top l1) (concat (stack_tail l1) l2)
