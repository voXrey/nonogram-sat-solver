type direction = Vertical | Horizontal;;

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

exception FormulaNotSATable

(* Une simplification simple *)
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

(* Simplification complète *)
let simplify f =
  let s = ref (simpl f) in
  while snd !s do s := simpl (fst !s) done;
  fst !s
;;

(* Substitution *)
let rec subst f x g = match f with
  | v when v = x -> g
  | Not(f0) -> Not(subst f0 x g)
  | And(f1, f2) -> And(subst f1 x g, subst f2 x g)
  | Or(f1, f2) -> Or(subst f1 x g, subst f2 x g)
  | Imply(f1, f2) -> Imply(subst f1 x g, subst f2 x g)
  | _ -> f
;;

(* Algorithme de backtracking très simple pour trouver une valuation *)
let rec found_valuation f0 sigma vars =
  let (f, _) = simpl f0 in

  if f = Top then true else (
  if f = Bot then false else (

  if vars = [] then found_valuation f sigma vars else (
  let x::v = vars in

  let f1 = subst f x Top in
  if found_valuation f1 sigma v
  then (
    Hashtbl.add sigma x 1;
    true
  ) else (
    let f2 = subst f x Bot in
    if found_valuation f2 sigma v then (
      Hashtbl.add sigma x 0;
      true
    )
    else false
  ))))
;;

(* Permet de créer toutes les combinaisons de 0 et de 1 suivant les contraintes du nonogramme pour une ligne *)
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
  close_in file;
  f, (n, m)
;;

(* Afficher la solution *)
let print_solution sigma n m =
  let a = Array.init n (
      fun i -> Array.init m (
        fun j -> try Hashtbl.find sigma (Var((i,j))) with Not_found -> 0
        )
    )
  in
  Array.iter (fun row ->
    Array.iter (fun v -> Printf.printf "%d " v) row;
      print_newline ()
    ) a;
;;

(* Partie principale du programme *)
if Array.length Sys.argv <> 2 (* On s'assure que le programme fournisse le fichier d'entée *)
then exit 1;

let f, (n, m) = file_to_formula Sys.argv.(1) in

let vars = ref [] in
for i = 0 to n-1 do
  for j = 0 to m-1 do
    vars := Var((i,j))::!vars
  done;
done;

let sigma = Hashtbl.create 2048 in (* Contient notre solution *)
let r = found_valuation (simplify f) sigma !vars in

if r
then print_solution sigma n m
else exit 1;

exit 0;
