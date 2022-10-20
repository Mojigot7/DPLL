open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let rec simplifie l clauses =
  let rec aux l clauses res = (* on fait une fonction auxiliaire qui prend en plus une liste de liste vide au début *)
    match clauses with
    |[] -> res (* si il n'y a plus de clauses on renvoie la liste de liste res *)
    |s :: sl -> if List.mem l s then aux l sl res (* on vérifie si l est dans la liste si c'est le cas on continue sans rien ajouter à res *)
                else match s with (* sinon on regarde les éléments de la liste si on trouve -l on ajoute la liste à res sans l'élément -l sinon on ajoute toute la clause dans res *)
                      |[] -> res
                      |x :: sx -> if x = -l then aux l sl (sx :: res)
                                  else aux l sl ((x :: sx) :: res)
  in List.rev(aux l clauses []);; (* comme on ajoute les éléments à l'avant de la liste de liste il faut retourner la liste à l'envers *)

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  match clauses with
  | [] -> raise Not_found (*on ne peut pas verifier quelque chose de vide donc exception*)
  | l :: r -> if List.length l = 1 then List.hd(l) else unitaire r;;(*si la taille de la clause est de 1 alors il n'y a bien qu'un seul element et on le renvoie sinon on continue de parcourir*)
  
(*la fonction auxiliaire nettoye va servir a nettoyer la liste pour qu'il ne reste que les litteraux pur (s'il y en a plusieurs sinon au moins un).
  Elle prend un litteral, une liste de clause et une liste VIDE:
  - si l'element actuel est egal au litteral ou a la negation du litteral on continue de parcourir en rappelant recursivement la fonction
  - sinon on va rappeler la fonction mais en 3eme argument on mettra l'element actuel a vide
  - et si la liste est vide on renvoie juste la liste vide
   *)

let rec nettoye x list vide =
  match list with
  | [] -> vide
  | e :: r -> if (x == e || x == -e) then nettoye x r vide else nettoye x r (e :: vide);;

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  let rec aux2 l =
    match l with
    | [] -> raise (Failure "pas de litteral pur")
    | e :: r -> if not (List.mem (-e) r) then e else aux2 (nettoye e r []) (*si dans la liste on trouve la negation de l'element actuel alors il n'est pas pur sinon il est pur et alors il faut l'isoler pour pouvoir le renvoyer a la fin en resultat de la fonction*)
  in aux2 (List.flatten clauses);;(*concatener les litteraux qui seront pur s'il y en a plus d'un*)

pur [[1;3];[2];[-1;2];[-2;3];[-1;3]];; (*doit renvoyer 3*)
pur [[1;3];[2];[-1;2];[2;3];[-1;-3]];; (*doit renvoyer 2*)
pur [[1;3];[2];[-1;2];[-2;3];[-1;-3]];; (*doit renvoyer 'Failure "pas de litteral pur"' *)
(*pur [];; (*doit renvoyer 'Failure "pas de litteral pur"' *)*)

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation (* si il n'y a plus de clauses alors on termine et on renvoie l'interprétation correspondante *)
  else if List.mem [] clauses then None else (* si on a une clause vide dans la liste alors ce n'est pas satisfiable *) 
  let checkLitteral = (* fonction qui s'occupe de trouver un littéral unitaire ou pur *)
    try Some(unitaire clauses) with
    |Not_found -> try Some(pur clauses) with
                  |Failure(_) -> None
  in match checkLitteral with
  |None -> solveur_split clauses interpretation (* si on ne trouve pas de littéral seul ou pur on applique solveur_split qui simplifie les clauses littéral par littéral*)
  |Some(s) -> solveur_dpll_rec (simplifie s clauses) (s :: interpretation) (* sinon on rappelle la fonction dpll en simplifiant avec le littéral trouvé et on l'ajoute dans interprétation *)
(* tests *)
let () = print_modele (solveur_dpll_rec systeme [])
let () = print_modele (solveur_dpll_rec coloriage [])

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
