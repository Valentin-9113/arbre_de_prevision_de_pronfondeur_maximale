(** 
    Cette partie du programme NE DOIT EN AUCUN CAS √™tre modifi√©e sous peine
    de voir votre code ne pas passer les tests 
*)

let usage () =
  Format.fprintf
    Format.err_formatter
    "%s <options>

OPTIONS:
     -h : print this help and exit
     -o <file> : set output to <file>
     --output <file> : set output to <file>
     -ts <int> : set the size of the training set (default : 1000)
     --training-size <int> : set the size of the training set (default : 1000)
     -ds <int> : set the size of the testing data set (default : 10000)
     --training-size <int> : set the size of the testing data set (default : 10000)
     -md <int> : set the max tree depth (default : 10)
     --max-depth <int> : set the max tree depth (default : 10)
"
  Sys.argv.(0)
     
let parse_opts () =
  let rec parse l =
    match l with
    | "-h"::l ->
       let _ = usage () in
       exit 0
    | "-o"::output::l' | "--output"::output::l' ->
       ("output",output)::parse l'
    | "-ts"::size::l' | "--training-size"::size::l' ->
       (try
          let _ = int_of_string size in 
         ("training-size", size)::parse l'
       with Failure _ ->
             let _ = usage () in
             exit 127
       )     
    | "-ds"::size::l' | "--data-size"::size::l' ->
       (try
          let _ = int_of_string size in 
          ("data-size",size)::parse l'
       with Failure _ ->
             let _ = usage () in
             exit 127
       )
    | "-md"::size::l' | "--max-depth"::size::l' ->
       (try
          let _ = int_of_string size in 
          ("max-depth",size)::parse l'
       with Failure _ ->
             let _ = usage () in
             exit 127
       )
    | _::_ ->
       let _ = usage () in
       exit 127             
    | [] -> []
  in
  parse (List.tl (Array.to_list Sys.argv))

let raw_opts = parse_opts ()  
;;
         
(* Une position dans le plan est donn√©e par son abscisse et son ordonn√©e *)
type pos = { x : float; y : float; };;

(* Une couleur est donn√©e par ses trois composantes *)
type color = {r:int;g:int;b:int};;


(* Un ensemble de donn√©es sera repr√©sent√© ici
   par une liste de couple (pos,color).
   On pourra supposer qu'une position ne peut pas appara√Ætre deux fois
   dans cette liste
 *)
type 'a dataset = (pos*color) list;;

let red  = { r = 255; g = 0; b = 0};;
let blue = { r = 0; g = 0; b = 255};;
let white = { r = 255; g = 255; b = 255};;
let black = { r = 0; g = 0; b = 0};;


(* fonction de g√©n√©ration pour la courbe de racine carr√©e.
   La partie sous la courbe est en [blue], celle au dessus de la
   courbe est en [red]
 *)
let generate_sqrt p =
  if p.y*.p.y < p.x then blue else red ;;

(* fonction de g√©n√©ration pour un cercle.
   La partie dans le cercle  est en [blue], celle √† l'ext√©rieur
   est en [red]
 *)
let generate_circle p =
  let x = p.x -. 0.5 and y = p.y -. 0.5 in 
  if x*.x +. y*.y < 0.5*.0.5 then blue else red ;;
  
(** Début de la partie à implanter *) 

(* type [tree] des prédicteurs de couleur en fonction
   du type de donnée d'entrainement.
 *)
type tree = 
	|Leaf of color
	|Node of pos * tree * tree * tree * tree ;;



(*
val somme_couple : int * int -> int * int -> int * int = <fun>
@requires
@ensures : [somme_couple x y] renvoie la somme terme à terme de deux couple d'entier [x] et [y]
@raises
*)
let somme_couple x y = let (a,b)=x in
  let (c,d)=y in
  (a+c,b+d);;



(*
val compteur : ('a * color) list -> int * int = <fun>
@requires
@ensures : [compteur dataset] renvoie un couple d'entier (r,b) ou r est le nombre de point rouge et b le nombre de point bleu dans [dataset]
@raises
*)
let rec compteur dataset = match dataset with
|[]->(0,0)
|h::t-> let (_,color) = h in if color == red then somme_couple (1,0) (compteur t)
           else somme_couple (0,1) (compteur t);;



(*
val couleur_predominante : ('a * color) list -> color = <fun>
@requires
@ensures : [couleur_predominante dataset] renvoie la couleur prédomonante de [dataset]
@raises : renvoie red en cas d'égalité
*)
let couleur_predominante dataset = 
let (r,b)=compteur dataset in
if r<b then blue
else red;;


(*
val new_set : (pos * 'a) list -> pos -> pos -> (pos * 'a) list = <fun>
@requires : les coordonnées de [p1] doivent être plus petite que celles de [p2]
@ensures : [new_set dataset p1 p2] renvoie un dataset composé uniquement des points de [dataset] compris dans le carré dont le sommet en bas à gauche et p1 et dont le somment en haut à droite est p2
@raises
*)
let rec new_set dataset p1 p2 = match dataset with
| []->[]
| h::t->let (p,_)=h in if (p.x>=p1.x && p.x<p2.x && p.y>=p1.y && p.y<p2.y) then (h::new_set t p1 p2) 
                        else (new_set t p1 p2);;

(* [build_tree n training] retourne un prédicteur de profondeur maximale [n]
   sur le jeu d'entrainement [training]
 *)

(*
val build_tree : int -> (pos * color) list -> tree = <fun>
@requires
@ensures : [build_tree n training] retourne un prédicteur de profondeur maximale [n] sur le jeu d'entrainement [training]
@raises
*)
let build_tree prof training=
  let rec build_tree_aux n dataset x1 y1 x2 y2=
    match dataset with
    |[]->Leaf(blue)
    |set->if (n=0) then Leaf(couleur_predominante set) (*si on se trouve à la profondeur maximale*)
        else if (List.length set)<5 then Leaf(couleur_predominante set) (*si il y a 4 ou moins points à l'interieur du dataset*)
        else let (r,b)= compteur set in if (r==0) then Leaf(blue) else if (b==0) then Leaf(red) (*s'il n'y a pas de bleu/ pas de rouge dans la liste => pas besoin d'aller plus loin*)
        else Node({x=(x2+.x1)/.2.;y=(y1+.y2)/.2.},build_tree_aux (n-1) (new_set set {x=x1;y=(y1+.y2)/.2.} {x=(x2+.x1)/.2.;y=y2}) x1 ((y1+.y2)/.2.) ((x2+.x1)/.2.) y2, (*carré nord ouest*)
                                                  build_tree_aux (n-1) (new_set set {x=(x2+.x1)/.2.;y=(y1+.y2)/.2.} {x=x2;y=y2}) ((x2+.x1)/.2.) ((y1+.y2)/.2.) x2 y2, (*carré nord est*)
                                                  build_tree_aux (n-1) (new_set set {x=(x2+.x1)/.2.;y=y1} {x=x2;y=(y1+.y2)/.2.}) ((x2+.x1)/.2.) y1 x2 ((y1+.y2)/.2.), (*carré sud est*)
                                                  build_tree_aux (n-1) (new_set set {x=x1;y=y1} {x=(x2+.x1)/.2.;y=(y1+.y2)/.2.}) x1 y1 ((x2+.x1)/.2.) ((y1+.y2)/.2.)) (*carré sud ouest*)
  in
  build_tree_aux prof training 0. 0. 1. 1.;;


(*
@requires [pos] soit dans le carré délimiter par 
@ensures :[predict_color tree pos] prédit la couleur du point [pos] à l'aide du prédicteur [tree]
@raises
*)
let rec predict_color tree pos = 
  match tree with
  |Leaf(col)->col
  |Node(p,no,ne,se,so)->if (pos.x<=p.x) && (pos.y<=p.y) then predict_color so pos
                          else if (pos.x<=p.x) && (pos.y>=p.y) then predict_color no pos
                          else if (pos.x>=p.x) && (pos.y<=p.y) then predict_color se pos
                          else predict_color ne pos;;
                                    
(* [generate_using_function pos] retourne la couleur du point pos
   il vous est conseiller de tester vos résultats sur plusieurs générateurs
   il vous suffit simplement de changer la fonction de génération avant de
   recompiler/réévaluer le code
 *)                             
let generate_using_function = generate_sqrt ;;

(*
Si vous le souhaitez, vous pouvez changer les valeurs par d√©faut ici.

par exemple : pour prendre un jeu de données de taille 100 et d√©finir un fichier de sortie.
*)
let opts = ("training-size","100")::("output","image.ppm")::raw_opts

(*let opts = raw_opts*)
                        
                        
                        
(** fin de la partie à implanter
AUCUNE MODIFICATION NE DOIT √äTRE FAITE √Ä PARTIR DE CE COMMENTAIRE

Vous n'avez pas besoin de lire/comprendre cette partie du code
*)

let generate nb f  =
  let margin = 0.001 in
  List.init nb
    (fun _ ->
      let x = margin +. Random.float (1. -. 2. *. margin) in
      let y = margin +. Random.float (1. -. 2. *. margin) in
      let v = f {x;y} in
      ({x;y}, v)
    )


let ts =
  match List.assoc_opt "training-size" opts with
  | None -> 1000
  | Some s -> int_of_string s

let ds =
  match List.assoc_opt "data-size" opts with
  | None -> 10000
  | Some s -> int_of_string s
                        
let md =
  match List.assoc_opt "max-depth" opts with
  | None -> 10
  | Some s -> int_of_string s
  

let pnm h w tree testing_ds =
  let output = Array.make_matrix h w white in
  (* on commence par la couleur de fond *)
  Array.iteri
    (fun j line ->
      Array.iteri (fun i _ ->
          let x = float_of_int i /. float_of_int w in
          let y = float_of_int j /. float_of_int h in  
          let c = predict_color tree {x;y} in
          output.(h-j-1).(i) <- c
        )
        line
    )
    output;
  (* On imprime le vrai dataset *)
  List.iter
    (fun (pos,color) ->
      let j = h-1-int_of_float (pos.y*.float_of_int h) in
      let i = int_of_float (pos.x*.float_of_int w) in
      let color' = predict_color tree pos in
      output.(j).(i) <- if color=color' then white else black 
    )
    testing_ds;
  output
            
let output_graph h w tree testing_ds =
  match List.assoc_opt "output" opts with
  | None -> ()
  | Some output ->
     try
       let fd = open_out output in
       let fmt = Format.formatter_of_out_channel fd in
       let output = pnm h w tree testing_ds in   
       let _ = Format.fprintf fmt "P3@.%d %d@.255@." h w in
       let _ = Array.iter (Array.iter (fun color -> Format.fprintf fmt "%d %d %d@." color.r color.g color.b)) output in 
       let _ = Format.pp_print_flush fmt () in 
       close_out fd
     with Sys_error s ->
       let _ = Format.fprintf Format.err_formatter "%s@." s in
       exit 127
            
let main () = 
  let training_ds = generate ts generate_using_function in
  let testing_ds = generate ds generate_using_function in
  let tree = build_tree md training_ds in
  let nb_bad_prediction =
    List.fold_left
      (fun nb_bad_prediction (pos,color) -> 
        let color' = predict_color tree pos in
        if color = color'
        then nb_bad_prediction
        else nb_bad_prediction + 1
      )
      0
      testing_ds
  in
let _ =  Format.printf
"training-size = %d
test-size = %d
max-depth = %d
correctness = %03.1f%%@."
ts ds md (100.*.float_of_int (ds-nb_bad_prediction)/.float_of_int ds)
in
output_graph 400 400 tree testing_ds

let _ = main ()

