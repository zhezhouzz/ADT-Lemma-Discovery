module FA = Frontend__Fast.Fast;;
module T = Tp.Tp;;
module A = Language.SpecAst;;
open Printf;;
open FA;;
open Utils;;
open Language.Helper;;
module Axiom = Inference.AxiomSyn;;
module Spec = Inference.SpecSyn;;
(* let snoc (lenf, f, lenr, r) x =
 *   let lenr = lenr + 1 in
 *   let r = lazy (Cons (x, r)) in
 *   if lenr <= lenf then (lenf, f, lenr, r)
 *   else (lenf + lenr, f ++ reverse r, 0, lazy Nil) *)
let make_lets l body =
  List.fold_right (fun (names, es) body ->
      Let(names, es, body)
    ) l body

let make_lets_one l body =
  List.fold_right (fun (name, es) body ->
      Let([name], es, body)
    ) l body
;;
let ast =
  ("snoc", [T.Int, "lenf"; T.IntList, "f"; T.Int, "lenr"; T.IntList, "r"; T.Int, "x";],
   make_lets
     [([T.Int, "lenr'"], App(T.Int, "plus", [T.Int, "lenr"; T.Int, "const1"]));
      ([T.IntList, "tmp0"], App(T.IntList, "cons", [T.Int, "x"; T.IntList, "r"]));
      ([T.IntList, "r'"], App(T.IntList, "lazy", [T.IntList, "tmp0"]));]
     (Ite(T.Int,
          App(T.Int, "le", [T.Int, "lenr'"; T.Int, "lenf'"]),
          Var [T.Int, "lenf"; T.IntList, "f"; T.Int, "lenr'"; T.IntList, "r'"],
          make_lets
            [[T.Int, "tmp1"], App(T.Int, "plus", [T.Int, "lenf"; T.Int, "lenr'"]);
             [T.IntList, "tmp5"], App(T.IntList, "reverse", [T.IntList, "r'"]);
             [T.IntList, "tmp2"], App(T.IntList, "concat", [T.IntList, "f"; T.IntList, "tmp5"]);
             [T.Int, "tmp3"], Lit (I 0);
             [T.IntList, "tmp6"], App(T.IntList, "nil", []);
             [T.IntList, "tmp4"], App(T.IntList, "lazy", [T.IntList, "tmp6"]);
            ]
            (Var [T.Int, "tmp1"; T.IntList, "tmp2"; T.Int, "tmp3"; T.IntList, "tmp4"])
         ))
  )
in
let vc = func_to_vc [T.Int, "x1"; T.IntList, "x2"; T.Int, "x3"; T.IntList, "x4"] ast in
let libcons = {name = "cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
            prog = function
              | [V.I h; V.L t] -> [V.L (h :: t)]
              | _ -> raise @@ InterExn "bad prog"
           } in
let libnil = {name = "nil"; intps = []; outtps = [T.IntList];
              prog = fun _ -> [V.L []]
               } in
let liblazy = {name = "lazy"; intps = [T.IntList]; outtps = [T.IntList];
                  prog = function
                    | [V.L l] -> [V.L l]
                    | _ -> raise @@ InterExn "bad prog"
                 } in
let libreverse = {name = "reverse"; intps = [T.IntList]; outtps = [T.IntList];
                  prog = function
                    | [V.L l] -> [V.L (List.rev l)]
                    | _ -> raise @@ InterExn "bad prog"
                 } in
let libconcat = {name = "concat"; intps = [T.IntList;T.IntList]; outtps = [T.IntList];
                  prog = function
                    | [V.L l1; V.L l2] -> [V.L (l1 @ l2)]
                    | _ -> raise @@ InterExn "bad prog"
                } in
let f, f', r, r' = map4 list_var ("f", "f'", "r", "r'") in
let spec_tab = predefined_spec_tab in
let spec_tab = add_spec spec_tab "snoc"
    ["lenf";"f";"lenr";"r";"x";"lenf'";"f'";"lenr'";"r'"] ["u"]
     (Iff(Or[list_member f u; list_member r u; int_eq u x],
             Or[list_member f' u; list_member r' u]
            ))
in
let spec_tab_add spec_tab {name;intps;outtps;prog} =
  StrMap.add name (Spec.infer ~progtp:(intps,outtps) ~prog:prog) spec_tab in
let spec_tab = List.fold_left spec_tab_add spec_tab
    [libcons;libnil;liblazy;libreverse;libconcat] in
let _ = printf "%s\n" (A.layout vc) in
let ctx =
   Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
 let _ = StrMap.iter (fun name spec ->
     printf "%s\n\n" (A.layout_spec_entry name spec)) spec_tab in
 let axiom = Axiom.infer ~ctx:ctx ~vc:vc ~spectable:spec_tab in
 let _ = printf "axiom:\n\t%s\n" (A.E.layout_forallformula axiom) in
 ();;
