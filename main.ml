
type var_type = int * int

type formula = 
    | Var of var_type
    | Top
    | Bot
    | Not of formula
    | And of formula * formula
    | Or of formula * formula
    | Imply of formula * formula
;;

let rec simpl = function
  | And(Bot, _) | And(_, Bot) -> (Bot, true)
  | Or(Top, _) | Or(_, Top) -> (Top, true)
  | And(Top, f) | And(f, Top)
  | Or(Bot, f) | Or(f, Bot)
  | Not(Not(f)) -> (f, true)
  | Not(Top) -> (Bot, true)
  | Not(Bot) -> (Top, true)
  | Imply(Bot, _) -> (Top, true)
  | Imply(Top, Bot) -> (Bot, true)

  | And(f1, f2) ->
    let (s1, r1), (s2, r2) = simpl f1, simpl f2 in
    (And(s1, s2), r1 || r2)
  | Or(f1, f2) -> 
    let (s1, r1), (s2, r2) = simpl f1, simpl f2 in
    (Or(s1, s2), r1 || r2)
  | Not(f) ->
    let (s, r) = simpl f in
    (Not(s), r)
  | Imply(f1, f2) ->
    let (s1, r1), (s2, r2) = simpl f1, simpl f2 in
    (Imply(s1, s2), r1 || r2)

  | f -> (f, false)
;;

let simplify f =
  let s = ref (simpl f) in
  while snd !s do s := simpl (fst !s) done;
  fst !s
;;

let rec subst f x g = match f with
  | v when v = x -> g
  | Not(f0) -> Not(subst f0 x g)
  | And(f1, f2) -> And(subst f1 x g, subst f2 x g)
  | Or(f1, f2) -> Or(subst f1 x g, subst f2 x g)
  | Imply(f1, f2) -> Imply(subst f1 x g, subst f2 x g)
  | _ -> f
;;


(* Affichage simple d'une formule pour debug *)
let rec string_of_formula ?(indent=0) f =
  let pad = String.make indent ' ' in
  match f with
  | Var (i, j) -> pad ^ Printf.sprintf "V(%d,%d)" i j
  | Top -> pad ^ "T"
  | Bot -> pad ^ "F"
  | Not f -> pad ^ "¬" ^ string_of_formula f
  | And (a, b) ->
      pad ^ "(AND\n"
      ^ string_of_formula ~indent:(indent+2) a ^ "\n"
      ^ string_of_formula ~indent:(indent+2) b ^ "\n"
      ^ pad ^ ")"
  | Or (a, b) ->
      pad ^ "(OR\n"
      ^ string_of_formula ~indent:(indent+2) a ^ "\n"
      ^ string_of_formula ~indent:(indent+2) b ^ "\n"
      ^ pad ^ ")"
  | Imply (a, b) ->
      pad ^ "(IMPLY\n"
      ^ string_of_formula ~indent:(indent+2) a ^ "\n"
      ^ string_of_formula ~indent:(indent+2) b ^ "\n"
      ^ pad ^ ")"
;;

let print_formulas l =
  List.iter (fun f -> print_endline (string_of_formula f)) l
;;


exception FormulaNotSATable


let rec quine f0 sigma vars =
  let (f, _) = simpl f0 in

  if f = Top then true else (
  if f = Bot then false else (

  if vars = [] then quine f sigma vars else (
  let x::v = vars in

  let f1 = subst f x Top in
  if quine f1 sigma v
  then (
    Hashtbl.add sigma x 1;
    true
  ) else (
    let f2 = subst f x Bot in
    if quine f2 sigma v then (
      Hashtbl.add sigma x 0;
      true
    )
    else false
  ))))
;;


type direction = Vertical | Horizontal;;

let combinations n blocks index d =
  let rec aux k blocks acc =
    match blocks with
    | [] ->
        (* Remplir le reste avec des 0 *)
        let f =
          let rec fill_zeros p f =
            if p = 0 then f
            else fill_zeros (p-1) (And(f, Not(Var(if d = Horizontal then (index, k + p - 1) else (k + p - 1, index)))))
          in
          fill_zeros (n - k) acc
        in
        [f]
    | t::bs ->
        let min_start = 0 in
        let max_start =
          if bs = [] then n - k - t
          else n - k - (List.fold_left (+) 0 bs) - (List.length bs) - t
        in
        let rec try_start i res =
          if i > max_start then res else
            let f0 =
              let rec fill_zeros k0 f =
                if k0 = 0 then f
                else fill_zeros (k0-1) (And(f, Not(Var(if d = Horizontal then (index, k + k0 - 1) else (k + k0 - 1, index)))))
              in
              fill_zeros i acc
            in
            let f1 =
              let rec fill_ones j f =
                if j = 0 then f
                else fill_ones (j-1) (And(f, Var(if d = Horizontal then (index, k + i + j - 1) else (k + i + j - 1, index))))
              in
              fill_ones t f0
            in
            let (f2, next_k) =
              if bs = [] then (f1, k + i + t)
              else (And(f1, Not(Var(if d = Horizontal then (index, k + i + t) else (k + i + t, index)))), k + i + t + 1)
            in
            let tails = aux next_k bs f2 in
            try_start (i+1) (tails @ res)
        in
        try_start min_start []
  in
  aux 0 blocks Top
;;



(* Lit un fichier et le convertit en une formule *)
let file_to_formula file_path =
  let file = open_in file_path in
  let line = input_line file in
  let (n, m) = Scanf.sscanf line "%d %d" (fun n m -> (n, m)) in

  let line_to_formula line index d =
    let l = String.split_on_char ' ' line in
    let int_l = List.map int_of_string l in
    let f_list = combinations (if d = Horizontal then m else n) int_l index d in
    List.fold_left (fun f1 f2 -> Or(f1, f2)) Bot f_list
  in

  let i = ref 0 in
  let rec read_l f =
    try
      if !i = n+m then raise End_of_file;
      Printf.printf "Reading line %d\n%!" (!i+1);
      let line = input_line file in
      let line_f =
        if !i < n
        then line_to_formula line !i Horizontal
        else line_to_formula line (!i - n) Vertical
      in
      incr i;
      read_l (And(f, line_f))
    with End_of_file -> f
  in
  let f = read_l Top in
  Printf.printf "Finished reading file.\n%!";
  close_in file;
  f, (n, m)
;;



let print_array a =
  Array.iter (fun row ->
    Array.iter (fun v -> Printf.printf "%d " v) row;
    print_newline ()
  ) a
;;

let f, (n, m) = file_to_formula "nonogram.txt" in

Printf.printf "Formula created.\n%!";

let vars = ref [] in
for i = 0 to n-1 do
  for j = 0 to m-1 do
    vars := Var((i,j))::!vars
  done;
done;

Printf.printf "Variables created, Quine starting...\n%!";


let sigma = Hashtbl.create 2048 in


let r = quine (simplify f) sigma !vars in

Printf.printf "Quine finished.\n%!";

if r then (
    Printf.printf "The formula is satisfiable.\n%!";
    let a = Array.init n (
      fun i -> Array.init m (
        fun j -> try Hashtbl.find sigma (Var((i,j))) with Not_found -> 0
        )
    ) in
    print_array a;
  )
else
  Printf.printf "The formula is not satisfiable.\n%!";

