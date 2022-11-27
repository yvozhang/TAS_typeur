(* Typeur TAS *)
(* Author: zimeng zhang 21108900*)
(* Last edited:27/11/2022 *)
module MM = Map.Make (String);;
module SM = Set.Make(String);;

(****************************************** I. Syntaxe ******************************************)
(* Termes *)
(* 2.1.1 *)
type pterm = Var of string    (* variable *)
  | App of pterm * pterm      (* abstraction *)
  | Abs of string * pterm     (* application *)
(* 3.1.1 *)
  | Int of int                 (* entier natif *)
  | Add of pterm * pterm       (* addition *)  
  | Sub of pterm * pterm       (* soustration *)
  | List of pterm list         (* list native *)
  | Tete of pterm              (* La tête de la liste *)
  | Queue of pterm             (* La queue de la liste *)
  | Cons of pterm * pterm      (* Construire de la liste*)
  | IFZERO of pterm * pterm * pterm   (* Si la condition équale à 0, renvoie la première expression, sinon renvoie la deuxième expression *)
  | IFEMPTY of pterm * pterm * pterm  (* Si la condition est vide, renvoie la première expression, sinon renvoie la deuxième expression *)
  | Fix of string * pterm                     (* point fix qui défini une fonction récursive *)
  | Let of string * pterm *pterm      (* let, un exemple: let x = e1 in e2  *)
(* 4.1.1 *)
  | Ref of pterm ref           (* La création de région *)
  | DeRef of pterm             (* le d ́er ́ef ́erencement *)
  | Assign of pterm * pterm    (* L’assignement *)
  | Unit                       (* une valeur unit() *)
;;

(* pretty printer de termes *)
(* 2.1.2 *)     
let rec print_term (pt : pterm) : string =
  match pt with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ (print_term t) ^")" 
(* 3.1.2 *)  
    | Int n -> string_of_int n  
    | Add (t1, t2) -> "(" ^ (print_term t1) ^" + "^ (print_term t2) ^ ")"
    | Sub (t1, t2) -> "(" ^ (print_term t1) ^" - "^ (print_term t2) ^ ")"
    | List l -> "[" ^ String.concat "," (List.map print_term l) ^ "]"
    | Tete t -> "(tete " ^ (print_term t) ^ ")"
    | Queue q ->"(queue " ^ (print_term q) ^ ")"
    | Cons (c,l) ->"(cons " ^ print_term c ^ " " ^ print_term l ^ ")"
    | IFZERO (c,e1,e2) -> "(ifzero " ^ print_term c ^ " then " ^ print_term e1 ^ " else " ^ print_term e2 ^ ")"
    | IFEMPTY (c,e1,e2) -> "(ifempty " ^ print_term c ^ " then " ^ print_term e1 ^ " else " ^ print_term e2 ^ ")"
    | Fix (phi,m) -> "(fix (" ^ phi ^ "," ^ print_term m  ^ ")"
    | Let (v,e1,e2) -> "(let " ^ v ^ " = " ^ print_term e1 ^ " in " ^ print_term e2 ^ ")"
(* 4.1.2 *) 
    | Ref r -> "(ref " ^ print_term !r ^ ")"
    | DeRef d -> "(!" ^ print_term d ^ ")"
    | Assign(e1,e2) -> "(" ^ print_term e1 ^ ":=" ^ print_term e2 ^ ")"
    | Unit -> "unit()"
  ;;

(* Constructeurs *)
(* 2.1.3 *)
let createVar v = Var v;;
let createAbs v t = Abs(v,t);;
let createApp m n = App(m,n);;
(* 3.1.3 *)
let createInt i = Int i;;
let createAdd t1 t2 = Add(t1,t2);;
let createSub t1 t2 = Sub(t1,t2);;
let createList l = List l;;
let createTete t = Tete t;;
let createQueue q = Queue q;;
let createCons c l = Cons(c,l);;
let createIFZERO c e1 e2 = IFZERO(c,e1,e2);;
let createIFEMPTY c e1 e2 = IFEMPTY(c,e1,e2);;
let createFix f x = Fix (f,x);;
let createLet v e1 e2 = Let(v,e1,e2);;
(* 4.1.3 *)
let createRef r = Ref (ref r);;
let createDeRef d = DeRef d;;
let createAssign e1 e2 = Assign(e1,e2);;
let createUnit = Unit;;

(****************************************** II. Sémantique ******************************************)
(* 2.2.1 *)
(* générateur de noms frais de variables *)
let compteur_name : int ref = ref 0                    

let nouvelle_name () : string = compteur_name := !compteur_name + 1; 
  "V"^(string_of_int !compteur_name)

(* remplace les variables liées par les autre nouveux variables  *)
let rec substitue_v_name p new_v old_v =
  match p with
    Var v -> if v = old_v then Var new_v else p
  | App(v1,v2)  -> App(substitue_v_name v1 new_v old_v, substitue_v_name v2 new_v old_v)
  | Abs(v1, v2) -> if v1 = old_v then Abs(new_v,substitue_v_name v2 new_v old_v)
      else Abs(v1,substitue_v_name v2 new_v old_v)
  | _ -> p
;;
let rec alpha_convertit (p:pterm) = 
  match p with
    Var v -> Var v
  | App(p1,p2) -> App(alpha_convertit p1,alpha_convertit p2)
  | Abs(p1,p2) -> 
      let n_name = nouvelle_name() in 
      (Abs(n_name, substitue_v_name (alpha_convertit p2) n_name p1))
  | Let(v,e1,e2) -> Let(v,alpha_convertit e1,alpha_convertit e2)
  |_ -> p
;;

(* 2.2.2 *)
let rec substitue_variable old_term variable new_term = 
  match old_term with
    Var v -> if v = variable then new_term else old_term 
  | App(p1,p2) -> App(substitue_variable p1 variable new_term,substitue_variable p2 variable new_term )
  | Abs(p1,p2) -> if p1 = variable then old_term
                     else (Abs(p1, substitue_variable p2 variable new_term))
  | Add(p1,p2) -> Add(substitue_variable p1 variable new_term,substitue_variable p2 variable new_term)
  | Sub(p1,p2) -> Sub(substitue_variable p1 variable new_term,substitue_variable p2 variable new_term)
  | _ -> old_term
;;

(* 2.2.3 *)
let eval term = 
  match term with
    Var v -> Var v
  | Abs(v1,v2) -> Abs(v1,v2)
  | App(v1,v2) -> (match v1 with
                  Var v -> Var v
                | Abs(t1,t2) -> substitue_variable v1 t1 v2 
                | App(t1,t2) -> term
                |_ -> term)
  |_ -> term
;;
exception WrongType of string;;
(* 2.2.4 *)
let max_time=5.;;
exception Timeout of string;;
let rec reduit (e : pterm) = 
  let start = Sys.time () in
    let rec reduit_t e = 
      if Sys.time () -. start < max_time
      then (
        match e with
            App (Abs (v1,v2), e2) -> substitue_variable v2 v1 e2
          | App (e1,e2) -> let v1 = reduit_t e1 in
                              if v1 != e1 then reduit_t (App(v1,e2))
                              else App(e1,reduit_t e2) 
          | Abs (x,e) -> Abs (x,reduit_t e)
          | Var x -> Var x
          | Int x -> Int x
          | Add (x,y) -> (let a = reduit_t x and b = reduit_t y in 
                                            match (a,b) with 
                                                (Int x1, Int x2) -> Int (x1+x2)
                                              | (Var x1, Var x2) ->  Add(x,y)
                                              | (Var x1, Int x2) ->  Add(x,y)
                                              | (Int x1, Var x2) ->  Add(x,y) 
                                              | _ -> raise (WrongType("Wrong type add"))) 
          | Sub (x,y) -> (let a = reduit_t x and b = reduit_t y in 
                                            match (a,b) with 
                                                (Int x1, Int x2) -> Int (x1-x2)
                                              | _ -> raise (WrongType("Wrong type sub"))) 
          | Tete t -> (match t with 
                          List l -> List.hd l
                          |_ -> raise (WrongType("Wrong type")))
          | Queue q -> (match q with 
                          List l -> List (List.tl l)
                          |_ -> raise (WrongType("Wrong type")))
          | Cons(x,y) -> (match (x,y) with 
                          (a, List l) -> List (a::l)
                          |_ -> raise (WrongType("Wrong type"))) 
          | IFZERO(c,e1,e2) -> (let r = reduit_t c in 
                                  match r with
                                    Int a -> (if a = 0 then reduit_t e1 else reduit_t e2)
                                    | _ ->  raise (WrongType("Wrong type")) ) 
          | IFEMPTY(c,e1,e2) -> (match c with
                                 List l -> (match l with
                                                  []-> reduit_t e1 
                                                | _ -> reduit_t e2)
                               | _ ->  raise (WrongType("Wrong type")) )              
          | Fix (x,y) -> substitue_variable y x (Fix(x,y))
          | Let(v,e1,e2) -> reduit_t (substitue_variable e2 v (reduit_t e1))
          | _ -> e )
                            else raise (Timeout ("timeout")) in reduit_t e
                          ;;  


(* 2.2.4 *)

(*let rec reduit (e : pterm): pterm = 
    match e with
        App (Abs (v1,v2), e2) -> substitue_variable v2 v1 e2 
      | App (e1,e2) -> let v1 = reduit e1 in
                            if v1 != e1 then reduit (App(v1,e2))
                            else App(e1,reduit e2) 
      | Abs (x,e) -> Abs (x, reduit e)
      | Var x -> Var x
      | Int x -> Int x
      | Add (x,y) -> Add(reduit x, reduit y)
      | Sub (x,y) -> Sub(reduit x, reduit y)
      | Fix (x,y) -> substitue_variable y x (Fix(x,y))
      | Let(v,e1,e2) -> reduit (substitue_variable e2 v (reduit e1))
      | _ -> e
;; *)

(****************************************** III. Types ******************************************)
(* Types *)
(* 2.3.1 *) 
type ptype = 
    VarType of string 
  | ArrType of ptype * ptype 
(* 3.3.1 *)  
  | NatType 
  | ListeType of ptype 
  | AllType of SM.t * ptype
(* 4.3.1 *)
  | UnitType
  | RefType of ptype
;;



(* pretty printer de types*)
(* 2.3.2 *)
let rec print_type (t : ptype) : string =
  match t with
    VarType x -> x
  | ArrType (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
(* 3.3.2 *)  
  | NatType -> "Nat" 
  | ListeType t -> "[" ^ print_type t ^"]"
  | AllType (v,ty) -> "∀" ^ (String.concat "," (SM.elements v)) ^ "." ^ print_type ty
(* 4.3.2 *)
  | UnitType -> "unit"
  | RefType r -> "ref " ^ print_type r 
;;


(* Constructeurs *)
(* 2.3.3 *)
let createVarType t = VarType t;;
let createArrType t1 t2 = ArrType(t1,t2);;
(* 3.3.3 *)  
let createNatType t = NatType;;
let createListType t = ListeType t;;
let createAllType e1 e2 = AllType(e1,e2);;
(* 4.3.3 *)
let createUnitType = UnitType;;
let createRefType r = RefType r;;


(****************************************** IV. Génération d’équations ******************************************)
(* Environnements de typage *) 
type env = (string * ptype) list 
(* Listes d'équations *) 
type equa = (ptype * ptype) list

exception VarPasTrouve
exception RuntimeError of string;;

(* générateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0                    

let nouvelle_var () : string = compteur_var := !compteur_var + 1; 
  "T"^(string_of_int !compteur_var)

(* cherche le type d'une variable dans un environnement *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
    [] -> raise VarPasTrouve
  | (v1, t1)::q when v1 = v -> t1
  | (_, _):: q -> (cherche_type v q) 

(* genere des equations de typage à partir d'un terme *)  
(* 2.4 *)
let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with 
    Var v -> let tv : ptype = cherche_type v e in [(ty, tv)] 
  | App (t1, t2) -> let nv : string = nouvelle_var () in
      let eq1 : equa = genere_equa t1 (ArrType (VarType nv, ty)) e in
      let eq2 : equa = genere_equa t2 (VarType nv) e in
      eq1 @ eq2
  | Abs (x, t) -> let nv1 : string = nouvelle_var () 
      and nv2 : string = nouvelle_var () in
      (ty, ArrType (VarType nv1, VarType nv2))::(genere_equa t (VarType nv2) ((x, VarType nv1)::e))  
  (* 3.4 *)
  | Int _ -> [(ty, NatType)]
  | Add (t1, t2) -> let eq1 : equa = genere_equa t1 NatType e in
      let eq2 : equa = genere_equa t2 NatType e in
      (ty, NatType)::(eq1 @ eq2)
  | Sub (t1, t2) -> let eq1 : equa = genere_equa t1 NatType e in
      let eq2 : equa = genere_equa t2 NatType e in
      (ty, NatType)::(eq1 @ eq2)
  | List t -> let nv1 : string = nouvelle_var() in 
                    (ty,ListeType (VarType nv1))::(List.concat (List.map (function f -> genere_equa f (VarType nv1) e) t))
  | Tete t -> let nv1 : string = nouvelle_var() in
                    (ty,VarType nv1)::(genere_equa t (ListeType(VarType nv1)) e)
  | Queue t -> let nv1 : string = nouvelle_var() in
                    (ty,ListeType (VarType nv1))::(genere_equa t (ListeType(VarType nv1)) e)
  | Cons(t1,t2) -> let nv1 = nouvelle_var() in 
                        let l1 = genere_equa t1 (VarType nv1) e in
                                        let l2 = genere_equa t2 (ListeType(VarType nv1)) e in 
                                                (ty,(ListeType(VarType nv1)))::(l1 @ l2)
  | IFZERO(c,e1,e2) -> let eq1 = genere_equa c NatType e in
                            let eq2 = genere_equa e1 ty e in
                                  let eq3 = genere_equa e2 ty e in
                                      eq1 @ (eq2 @ eq3)
  | IFEMPTY(c,e1,e2) -> let nv = nouvelle_var() in 
                                let eq1 = genere_equa c (AllType(SM.singleton (print_type (VarType nv)),ListeType(VarType nv))) e in 
                                      let eq2 = genere_equa e1 ty e in 
                                            let eq3 = genere_equa e2 ty e in 
                                                  eq1 @ (eq2 @ eq3) 
  (* 4.4 *)
  | Ref r -> let nv = nouvelle_var() in 
                      (ty,(RefType(VarType nv)))::(genere_equa !r (VarType nv) e)
  | DeRef d -> let nv = nouvelle_var() in 
                      (ty,(VarType nv))::(genere_equa d (RefType(VarType nv)) e)
  | Assign(e1,e2) -> let nv = nouvelle_var() in
                              let eq1 = genere_equa e1 (RefType(VarType nv)) e in 
                                        let eq2 = genere_equa e2 (VarType nv) e in 
                                        (ty,UnitType)::(eq1 @ eq2)

  | _ -> raise (RuntimeError ("ERROR : Can't find this type"))

(* 3.4 *)

(****************************************** V. Unification ******************************************)
(* 2.5.1 *)
(* vérificateur d'occurence de variables *)  
let rec appartient_type (v : string) (t : ptype) : bool =
  match t with
    VarType v1 when v1 = v -> true
  | ArrType (t1, t2) -> (appartient_type v t1) || (appartient_type v t2) 
(* 3.5.1 *)
  | NatType -> false
  | ListeType l -> appartient_type v l
  | AllType(var,tp) -> if not (SM.mem v var) then appartient_type v tp else false
  | _ -> false

(* 2.5.2 *)
(* remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
    VarType v1 when v1 = v -> t0
  | VarType v2 -> VarType v2
  | ArrType(t1, t2) -> ArrType (substitue_type t1 v t0, substitue_type t2 v t0) 
(* 3.5.2 *)  
  | NatType -> NatType 
  | ListeType l -> ListeType (substitue_type l v t0)
  | AllType(var,ty) -> if not (SM.mem v var) then AllType(var,substitue_type ty v t0) else t
(* 4.5.2 *)
  | UnitType -> UnitType
  | RefType r -> RefType (substitue_type r v t0)
;;   

(* remplace une variable par un type dans une liste d'équations*)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e
;;

let barendregtisation var ty =
  let new_ty = ref ty in 
      SM.iter (function f -> let nv = VarType(nouvelle_var()) in new_ty:= substitue_type ty f nv) var; !new_ty
;;


  


(* 2.5.4 *)
exception Echec_unif of string      

(* zipper d'une liste d'équations *)
type equa_zip = equa * equa
  
(* rembobine le zipper *)
let rec rembobine (e : equa_zip) =
  match e with
    ([], _) -> e
  | (c::e1, e2) -> (e1, c::e2)

(* remplace une variable par un type dans un zipper d'équations *)
let substitue_type_zip (e : equa_zip) (v : string) (t0 : ptype) : equa_zip =
  match e with
    (e1, e2) -> (substitue_type_partout e1 v t0, substitue_type_partout e2 v t0)

(* trouve un type associé à une variable dans un zipper d'équation *)
let rec trouve_but (e : equa_zip) (but : string) = 
  match e with
    (_, []) -> raise VarPasTrouve
  | (_, (VarType v, t)::_) when v = but -> t
  | (_, (t, VarType v)::_) when v = but -> t 
  | (e1, c::e2) -> trouve_but (c::e1, e2) but 

(* résout un système d'équations *) 
let rec unification (e : equa_zip) (but : string) : ptype = 
  match e with 
    (* on a passé toutes les équations : succes *)
    (_, []) -> (try trouve_but (rembobine e) but with VarPasTrouve -> raise (Echec_unif "but pas trouvé"))
    (* equation avec but : on passe *)
  | (e1, (VarType v1, t2)::e2) when v1 = but ->  unification ((VarType v1, t2)::e1, e2) but
    (* deux variables : remplacer l'une par l'autre *)
  | (e1, (VarType v1, VarType v2)::e2) ->  unification (substitue_type_zip (rembobine (e1,e2)) v2 (VarType v1)) but
    (* une variable à gauche : vérification d'occurence puis remplacement *)
  | (e1, (VarType v1, t2)::e2) ->  if appartient_type v1 t2 then raise (Echec_unif ("occurence de "^ v1 ^" dans "^(print_type t2))) else  unification (substitue_type_zip (rembobine (e1,e2)) v1 t2) but
    (* une variable à droite : vérification d'occurence puis remplacement *)
  | (e1, (t1, VarType v2)::e2) ->  if appartient_type v2 t1 then raise (Echec_unif ("occurence de "^ v2 ^" dans " ^(print_type t1))) else  unification (substitue_type_zip (rembobine (e1,e2)) v2 t1) but 
    (* types fleche des deux cotes : on decompose  *)
  | (e1, (ArrType (t1,t2), ArrType (t3, t4))::e2) -> unification (e1, (t1, t3)::(t2, t4)::e2) but 
    (* types fleche à gauche pas à droite : echec  *)
  | (e1, (ArrType (_,_), t3)::e2) -> raise (Echec_unif ("type fleche non-unifiable avec "^(print_type t3)))     
    (* types fleche à droite pas à gauche : echec  *)
  | (e1, (t3, ArrType (_,_))::e2) -> raise (Echec_unif ("type fleche non-unifiable avec "^(print_type t3)))     
    (* types nat des deux cotes : on passe *)
  | (e1, (NatType, NatType)::e2) -> unification (e1, e2) but 
    (* types nat à gauche pas à droite : échec *)
  | (e1, (NatType, t3)::e2) -> raise (Echec_unif ("type entier non-unifiable avec "^(print_type t3)))     
    (* types à droite pas à gauche : échec *)
  | (e1, (t3, NatType)::e2) -> raise (Echec_unif ("type entier non-unifiable avec "^(print_type t3)))     
(* 3.5 *) 
    (* for all types, applique "barendregtisation" *)
  | (e1, (AllType(v1,t1), AllType(v2, t2))::e2) -> unification (e1, ((barendregtisation v1 t1),(barendregtisation v2 t2))::e2) but 
  | (e1, (AllType(v1,t1), t2)::e2) -> unification (e1, ((barendregtisation v1 t1),t2)::e2) but 
  | (e1, (t1, AllType(v2, t2))::e2) -> unification (e1, (t1,(barendregtisation v2 t2))::e2) but 
    (* ne sont pas les memes à gauche et à droite d’une équation, on échoue.*)
  | (e1, (t1, t2)::e2) -> raise (Echec_unif ("Les type ne sont pas les memes "))
(* 4.5 *)
  | (e1,(RefType t1,RefType t2)::e2) -> unification (e1,(t1,t2)::e2) but

(* enchaine generation d'equation et unification *)                                   
let inference (t : pterm) : string =
  let e : equa_zip = ([], genere_equa t (VarType "but") []) in
  try (let res = unification e "but" in
       (print_term t)^" ***TYPABLE*** avec le type "^(print_type res))
  with Echec_unif bla -> (print_term t)^" ***PAS TYPABLE*** : "^bla

  
















(* ***EXEMPLES*** *)  



(*
let alpha:pterm = alpha_convertit (Abs ("x", Abs ("y", Abs("x",Var "x"))))
let beta:pterm = alpha_convertit (Abs ("x", App (Var "y", Var "y")))
let sub_v:pterm = substitue_variable beta "y" (Abs ("z", Var "z"))*)

(* --------- 2.  λ-calcul simplement typé ----------- *)
(* ex_id = λx.x *)
let ex_id : pterm = Abs ("x", Var "x") 
let ex_id_reduit = reduit ex_id
let inf_ex_id : string = inference ex_id 
(* ex_k = λx.λy.x *)
let ex_k : pterm = Abs ("x", Abs ("y", Var "x")) 
let ex_k_reduit = reduit ex_k
let inf_ex_k : string = inference ex_k
(* ki = ex_k * ex_id*)
let ki:pterm = App(ex_k,ex_id)
let ki_alpha = alpha_convertit ki
let ki_reduit = reduit ki_alpha
let ki_inf = inference ki_reduit
(* ki = ex_k * ex_id * ex_id *)
let kii:pterm =App(App(ex_k,ex_id),ex_id)
let kii_alpha = alpha_convertit kii
let kii_reduit = reduit kii_alpha
let kii_inf = inference kii_reduit
(* ex_s = λx.λy.λz.xzyz *)
let ex_s : pterm = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
(*let ex_s_reduit = reduit ex_s*) 
let inf_ex_s : string = inference ex_s
(* ex_nat1 = (λx.(x+1))*3 *)
let ex_nat1 : pterm = App (Abs ("x", Add(Var "x", Int 1)), Int 3)
(*let ex_nat1_reduit = reduit ex_nat1*)
let inf_ex_nat1 : string = inference ex_nat1
(* ex_nat2 = λx.(x+x) *)
let ex_nat2 : pterm = Abs ("x", Add( Var "x", Var "x"))
let ex_nat2_reduit = reduit ex_nat2
let inf_ex_nat2 : string = inference ex_nat2
(* ex_omega = (λx.xx)(λy.yy) *)
let ex_omega : pterm = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))
let ex_omega_reduit = reduit ex_omega
let inf_ex_omega : string = inference ex_omega
(* ex_nat3 = ex_nat2 * ex_id *)
let ex_nat3 : pterm = App (ex_nat2, ex_id)
let ex_nat3_reduit = reduit ex_nat3
let inf_ex_nat3 : string = inference ex_nat3

(* --------- 3.  PCF ------------ *)
let ex_let = Let("add",Abs("x",Abs("y",Add(Var "x",Var "y"))),Let("add_5",App(Var "add",Int 5),Var "add_5"))
let e_let = Let("y",Var "z",Abs("x",App(Var "x",Var "y")))
let e_let_alpa = alpha_convertit e_let
(*let ex_let_reduit = reduit e_let_alpa*)
(*let ex_let_inf = inference ex_let_reduit*)
let ex_iz = IFZERO(Sub(Int 5,Int 4),Int 1,Int 2)
let ex_iz_reduit = reduit ex_iz
let ex_iz_inf = inference ex_iz
let ex_ie = IFEMPTY(Tete (List [Int 20]),Int 5, Tete(List []))
let ex_ie_inf = inference ex_ie
(* --------- 4. Traits Imperatifs  ------------ *)
let ex_ref = IFZERO(Ref (ref (Int 5)),Int 1,Int 2)
let ex_ref_inf = inference ex_ref
let r = App(Abs("x",Var "x"),Ref (ref (Int 2)))
let r_inf = inference r
let main () =
 (*
 print_endline(print_term alpha);
 print_endline(print_term beta);
 print_endline(print_term sub_v); *)
 print_endline "----------------------------------- 2. λ-calcul simplement typé ---------------------------------------------------";
 print_endline "Beta réduction pour I = λx.x :";
 print_endline(print_term ex_id_reduit);
 print_endline "Inférence de id=λx.x:";
 print_endline(inf_ex_id);
 print_endline "Beta réduction pour K = λx.λy.x :";
 print_endline(print_term ex_k_reduit);
 print_endline "Inférence de K = λx.λy.x :";
 print_endline(inf_ex_k);
 print_endline "Beta réduction pour KI :";
 print_endline(print_term ki_reduit);
 print_endline "Inférence de KI:";
 print_endline(ki_inf);
 print_endline "Beta réduction pour KI :";
 print_endline(print_term ki_reduit);
 print_endline "Inférence de KI:";
 print_endline(ki_inf);
 print_endline "Beta réduction pour KII :";
 print_endline(print_term kii_reduit);
 print_endline "Inférence de KII :";
 print_endline(kii_inf);
 print_endline "Beta réduction pour S = λx.λy.λz.xzyz :";
 print_endline "Inférence de S = λx.λy.λz.xzyz :";
 print_endline(inf_ex_s);
 print_endline "Beta réduction NAT1 = (λx.(x+1))*3 :";
 (*print_endline(print_term ex_nat1_reduit);*)
 print_endline "Inférence de NAT1 = (λx.(x+1))*3 :";
 print_endline(inf_ex_nat1);
 print_endline "Beta réduction NAT2 = λx.(x+x) :";
 print_endline(print_term ex_nat2_reduit);
 print_endline "Inférence de NAT2 = λx.(x+x) :";
 print_endline(inf_ex_nat2);
 print_endline "Beta réduction NAT3 = NAT2 * I :";
 print_endline(print_term ex_nat3_reduit);
 print_endline "Inférence de NAT3 = NAT2 * I :";
 print_endline(inf_ex_nat3);
 print_endline "Beta réduction NAT3 = NAT2 * I :";
 print_endline(print_term ex_nat3_reduit);
 print_endline "Inférence de NAT3 = NAT2 * I :";
 print_endline(inf_ex_nat3);
 print_endline "Beta réduction omega = (λx.xx)(λy.yy) :";
 print_endline(print_term ex_omega_reduit);
 print_endline "Inférence de omega = (λx.xx)(λy.yy) :";
 print_endline(inf_ex_nat3);
 print_endline "----------------------------------- 3. PCF ---------------------------------------------------";
 print_endline "Beta réduction pour ex_let:";
 (*print_endline(print_term ex_let_reduit);*)
 print_endline "Inférence de ex_let:";
 print_endline "Beta réduction pour ifzero:";
  print_endline(print_term ex_iz_reduit);
 print_endline "Inférence de ifzero:";
 print_endline(ex_iz_inf);
 
 print_endline "Beta réduction pour ifempty:";
 
 print_endline "Inférence de ifempty:";
 print_endline(ex_ie_inf);
 print_endline "----------------------------------- 4. Traits Imperatifs ---------------------------------------------------";
 print_endline "Inférence de ex_ref:";
 print_endline(ex_ref_inf);
 print_endline "Inférence de r:";
 print_endline(r_inf)
let _ = main ()