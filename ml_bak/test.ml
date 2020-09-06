open FastDT;;
open Array;;
open Printf;;
let () =
  let boost_size = ref None in
  let bag_size   = ref None in
  let input_f    = ref None in
  let load_dt    = ref None in
  let max_d      = ref 10 in
  let rho        = ref 0. in
  let minfc      = ref 1 in
  let usage = "usage: FastDT [-boost #|-bag #] [-load dtfile] [-maxd (10)] [-rho (0)] [-minfc (1)] <data>\n" in
  let i  = ref 1 in
  let _I = length Sys.argv in
  while !i < _I do
    if      !i < _I-1 && Sys.argv.(!i) = "-boost" then ( boost_size := Some (int_of_string Sys.argv.(!i+1)) ; i := !i+2 )
    else if !i < _I-1 && Sys.argv.(!i) = "-bag"   then ( bag_size   := Some (int_of_string Sys.argv.(!i+1)) ; i := !i+2 )
    else if !i < _I-1 && Sys.argv.(!i) = "-load"  then ( load_dt    := Some (Sys.argv.(!i+1))               ; i := !i+2 )
    else if !i < _I-1 && Sys.argv.(!i) = "-maxd"  then ( max_d      := int_of_string   Sys.argv.(!i+1)      ; i := !i+2 )
    else if !i < _I-1 && Sys.argv.(!i) = "-rho"   then ( rho        := float_of_string Sys.argv.(!i+1)      ; i := !i+2 )
    else if !i < _I-1 && Sys.argv.(!i) = "-minfc" then ( minfc      := int_of_string   Sys.argv.(!i+1)      ; i := !i+2 )
    else if String.length Sys.argv.(!i) > 1 && String.get Sys.argv.(!i) 0 = '-' then failwith usage
    else ( input_f := Some Sys.argv.(!i); i := !i+1 )
  done;
  let input_f = match !input_f with None -> failwith usage | Some s -> s in
  (match !load_dt with
     None -> (
       let learn = 
         match !boost_size, !bag_size with
           None  , None   -> build_single_dt 
         | Some n, None   -> build_boosted_dt n
         | None  , Some n -> build_bagged_dt n
         | _ -> failwith "cannot specify both -boost and -bag" in
       eprintf "Loading data from %s...\n" input_f; flush stderr;
       let (_F,_Y,_W) = load_data !minfc input_f in
       let _ = printf "Y:"; Array.iter (fun y -> printf "%b " y) _Y; printf "\n" in
       let _ = printf "W:"; Array.iter (fun w -> printf "%f " w) _W; printf "\n" in
       let _ = printf "F:\n"; Array.iter (fun vec ->
           printf "dim = %i " (Bigarray.Array1.dim vec);
           printf "vec.{0} = %i " vec.{0};
           printf "vec.{1} = %i " vec.{1};
           (* printf "vec.{2} = %i " vec.{2}; *)
         )
           _F; printf "\n" in
       eprintf "%d examples, %d features\n" (length _Y) (length _F); flush stderr;
       eprintf "Building model...";
       let model = learn !max_d !rho 1e-6 input_f _F _Y _W in
       printf "%d\n" (length model);
       iter (fun (a,dt) -> printf "%g\n" a; print_tree stdout dt) model;
       eprintf "\n"; flush stderr;
     )
   | Some dt_file ->
     eprintf "Loading model from %s...\n" dt_file; flush stderr;
     let model = load_model dt_file in
     eprintf "Predicting on %s...\n" input_f; flush stderr;
     let error,sum_W = predict_file model input_f in
     eprintf "Error = %g / %g = %g\n" error sum_W (error /. sum_W);
     ()
  );
  ()


