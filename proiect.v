Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.


(*-------------Tipuri Variabile si declarari Variabile-----------*)

Inductive Error :=
 | error_type : Error.

Inductive TypeNat :=
  | num : nat -> TypeNat
  | error_nat :TypeNat.

Scheme Equality for TypeNat.

Inductive TypeBool :=
  | boolean : bool -> TypeBool
  | error_bool : TypeBool.

Coercion num: nat >-> TypeNat.
Coercion boolean: bool >-> TypeBool.


Inductive Values :=
  | var_undecl : Values
  | var_assign : Values
  | default : Values
  | val_nat : TypeNat -> Values
  | val_bool : TypeBool -> Values.

Scheme Equality for Values.

(*Expresii aritmetice*)
Inductive AExp :=
  | avar: string -> AExp (* Var ~> string *)
  | anum: TypeNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp (* Multiplication *)
  | adiv: AExp -> AExp -> AExp (* Division *)
  | amod: AExp -> AExp -> AExp. (* Modulo *)

(* Expresii Booleene *)
Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp
  | blessthan : AExp -> AExp -> BExp
  | bgreaterthan : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.


Definition EnvGlobal := Values.
Definition EnvLocal := Values.



(*--------------------------Modelare Memorie-----------------------------*)


Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)
 
Scheme Equality for Mem.

(* Environment *)
Definition EnvMem := string -> Mem.

(* Memoria *)
Definition MemLayer := Mem -> Values.



(* Stack cu environmente pt a putea pastra valorile diferite ale variabilelor locale/globale*)
Definition Env_Stack := list EnvGlobal.


(* Initial, fiecare variabila are asignata o zona de memorie default *)
Definition MemDefault : EnvMem := fun x => mem_default.
   
Compute (MemDefault "z"). (* Variabila nu e inca declarta *)

(* fiecare variabila are initial asignata o valoare nedeclarata *)
Definition mem : MemLayer := fun x => var_undecl.

Definition update_env (env: EnvMem) (x: string) (n: Mem) : EnvMem :=
  fun y =>
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default)) (* verific daca environmentul in care e variabila nu are deja asignat un offset*)
      then
        n
      else
        (env y). 


Inductive Types :=
  | naturalType : Types
  | booleanType : Types
  | natural_vecType : Types
  | boolean_vecType : Types.
Scheme Equality for Types.

(*
Definition envMemAlloc : EnvMem := fun x => offset.
*)
Definition MemNat := Mem -> Types.
Definition envNat : MemNat := fun x => naturalType.

Compute ((update_env MemDefault "x" (offset 9)) "x").
Compute (MemDefault "x").

(*
Definition update_mem (env: MemNat) (offset: Mem) (n: Types) : MemNat :=
  fun y =>
      if (andb (Mem_beq offset y ) (Types_beq n (env y))) (* *)
      then
        n
      else
        (env y).


Compute (( update_mem  envNat (offset 9) naturalType) (offset 9)).
*)
(*
Compute (( update_mem  envNat (offset 9) (num 15)) (offset 9)). 
*)

Definition Env := string -> Mem.



Definition mlayer : MemLayer := fun x => var_undecl.

Definition env : Env := fun x => mem_default.



Compute (env "z"). (* The variable is not yet declared *)

(* Example of updating the environment, based on a specific memory offset *)
Compute ((update_env env "x" (offset 9)) "x").


Definition update_mem (layer: MemLayer) (x: Mem) (n: Values) : MemLayer :=
  fun y =>
    if( andb (Mem_beq x y) (Values_beq n (layer y)) ) (*sunt egale adresele si value diferit*)
    then
       (layer y)
    else
      n.

Compute ((update_mem mlayer (offset 9) (val_nat 5)) (offset 9)).



(*-------------------------------Vectori----------------------------*)


Inductive Vector :=
  | vec_decl : string -> nat -> Vector
  | vec_assign : string -> nat -> Values -> Vector.

Inductive Tipuri :=
  | vect : Vector -> Tipuri
  | variable : string -> Tipuri.

Definition VecMem := nat -> Mem. (* env pentru a retine in memorie marimea vectorului*)

Inductive Alloc_Vector :=
  | alloc_name : string -> Mem -> Alloc_Vector
  | alloc_val : Values -> Mem -> Alloc_Vector.

Inductive Vec_Type :=
  | undecl_vec : Vec_Type
  | default_vec : Vec_Type
  | empty_vec : Vec_Type
  | nat_vec : TypeNat -> Vec_Type
  | bool_vec : TypeBool ->Vec_Type.

Notation "A [ n ]" := (vec_decl A n )(at level 60).
Notation "A [ n ] = B" := (vec_assign A n B)(at level 61).

Definition EnvVect := Vector -> Vec_Type.

(* Initial, vectorii sunt nedeclarati in environment *)
Definition envVect : EnvVect := fun x => undecl_vec.
 
Check( "x" [10]). 

(*Check("x" [ 1 ] = (val_nat 5)).  *)




(* Statements *)
Inductive Stmt :=
  | var_decl: string -> Stmt (* declaratie pentru variabile *)
  | nat_decl_assign: string -> nat -> Stmt
  | bool_decl_assign: string -> bool ->Stmt
  | nat_decl: string -> Stmt
  | bool_decl: string ->Stmt
  | vector_decl: Vector ->Stmt
  | add_nat_vect: string -> nat -> AExp ->Stmt
  | add_bool_vect: string -> nat -> BExp ->Stmt
  | nat_assign : string -> AExp -> Stmt (* Assignment  pentru variabile de tip nat *)
  | bool_assign : string -> BExp -> Stmt (* Assignment pentru variabile de tip bool *)
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | forStmt : Stmt -> BExp -> Stmt -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt.


(*Notatii*)

(*Notatii pentru operatii cu expresii aritmetice *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

(* Notatii pentru operatii cu expresii Booleene*)
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bgreaterthan A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

(* Notatii pentru Statements *)
Notation "X <n= A" := (nat_assign X A)(at level 60).
Notation "X <b= A" := (bool_assign X A)(at level 60).
Notation "'LetVar' X " := (var_decl X )(at level 60).
Notation "'LetNat' X " := (nat_decl X )(at level 60).
Notation "'LetBool' X " := (bool_decl X )(at level 60).
Notation "X 'DecNat=' i" := (nat_decl_assign X i)(at level 60).
Notation "X 'DecBool=' i" := (bool_decl_assign X i)(at level 60).
Notation "X [ i ] <nv= B" := (add_nat_vect X i B) (at level 60).
Notation "X [ i ] <bv= B" := (add_bool_vect X i B) (at level 60).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'forr' ( A ; B ; C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation "'iff' ( A ) 'thenn' ( B ) 'elsee' ( C )" := (ifthenelse A B C)(at level 97).
Notation "'whilee' ( A ) { B }" := (while A B)(at level 97).

(*Coercions pentru constante si variabile*)

Coercion anum : TypeNat >-> AExp.
Coercion avar : string >-> AExp. 
Coercion bvar : string >->BExp.
Coercion vector_decl : Vector >-> Stmt.
Coercion var_decl : string >-> Stmt.

(*-----------------------------Exemple-----------------------------*)


Check("m" [ 5 ] <nv= 7).
Check("m" [ 5 ] <bv= bfalse).
 
Check( LetVar "x").
Check (LetNat "x").
Check("d" DecNat= 5).

Check ( "x" <n= (anum 5)).
Check ( "y" <b= btrue).

Compute ("x" <n= "x" +' 1).
Compute ("p" <n= 10).
Compute ("p" <n= 10 ;;
         "i" <n= 1;;
         "sum" <n= 0).
 
Compute ("y" <b= btrue).


Check
  "t" <n= 10 ;;
  "s" <n= 7;;
ifthenelse (2 <' 5)
           ("a" <n= 9)
           ("a" <n= 5).


Check btrue.
Check bfalse.
Check !' ("x" <' 10).
Check btrue &&' ("n" >' 0).

Check (
"a" [20] ;;
"cont" DecNat= 0 ;;
whilee ( "cont" <' 10) 
{ "a" [2] <nv= "cont" ;; "cont" <n= "cont" +' 1 }
).


Check (
LetNat "sum" ;;
LetBool "ok" ;;
"sum" <n= 10 ;;
( forr ( "i" <n= 0 ; "i" <' 10 ; "i" <n= "i" +' 1 )
             { "sum" <n= "sum" +' "i" } )
;;
iff ("sum" *' 2 >' 50)
thenn ( "sum" <n= 1 ;; "ok" <b= btrue)
elsee  ( "sum" <n= 2)
).




(*Environments*)

(*Environment ce face legatura intre numele variabilelor si tipul acestora*)
Definition Env := string -> Values.

(* Initial, toate variabilele sunt undeclared in environment *)
Definition env : Env := fun x => var_undecl.


Definition types_compatibility (t1 : Values) (t2 : Values) : bool :=
  match t1 with
    | var_undecl => match t2 with 
                     | var_undecl => true
                     | _ => false
                     end
    | var_assign => match t2 with
                     | var_assign => true
                     | _ => false
                    end
    | default => match t2 with 
                     | default => true
                     | _ => false
                     end
    | val_bool _x => match t2 with  (*daca am o var. de tip bool, verific ca i se atribuie/e utilizata in operatii cu alte bool*)
                     | val_bool _y => true
                     | _ => false
                     end
    | val_nat _x => match t2 with   (*la fel pt nat*)
                     | val_nat _y => true
                     | _ => false
                     end
  

  end. 




(*---------------------------Functia de Swap----------------------------*)

Compute (MemDefault "x").
(*
Definition Swap (a: string) (b: string) :=
 fun x =>
    if( andb ( ( EnvMem "a" ), (EnvMem "b")) )
    then update_env (envMem , "x", EnvMem "a")
         update_env (envMem , "a", EnvMem "b")
         update_env (envMem , "b", EnvMem "x")
    else
     val_error.


Notation " 'swap' (a,b) " := (Swap a b) (at level 80).
*)

(*-------------------------Algoritmul de sortare---------------------*)

(*
Fixpoint Sort ( envv: EnvVect ) (vect : Vector) : Vector :=
  fun y =>

 aici veific daca vectorul meu nu este gol si daca are mai mult de o valoare 
retinuta in el
  Apoi, daca cele 2 conditii sunt indeplinite ma folosesc de swap pentru a efectua sortarea
*)


(* Notatations used for the Big-Step semantics *)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).
 
Definition plus_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with 
    | error_nat, _ => error_nat
    | _, error_nat => error_nat 
    | natural, natural => natural
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | natural, natural => natural
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | natural, natural => natural
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | natural, natural => natural
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | natural, natural => natural
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

(* Big-Step semantics for arithmetic operations *)
Inductive aeval : AExp -> Env -> TypeNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | val_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_Nat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| multiplic : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_Nat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (sub_Nat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_Nat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mod_Nat i1 i2) ->
    a1 %'f a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).



Definition lt_Bool (n1 n2 : TypeNat) : TypeBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition not_Bool (n :TypeBool) : TypeBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_Bool (n1 n2 : TypeBool) : TypeBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.
 
Definition or_Bool (n1 n2 : TypeBool) : TypeBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.


(* Big-Step semantics for bool operations *)
Inductive beval : BExp -> Env -> TypeBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | val_bool x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_Bool i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_Bool i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_Bool i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_Bool i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').


Example substract_error : 1 -' 5 =[ env ]=> error_nat.
Proof.
  eapply substract.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Example boolean_operation : bnot (100 <' "n") ={ env }=> error_bool.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed. 


Definition update (env : Env) (x : string) (v : Values) : Env :=
 fun y =>
    if (eqb y x)  (*daca variabila x se gaseste prin environment, atunci updatez, daca nu, ramane la fel environmentul*)
    then
       (*variabila nu a fost declarata inca si valoarea pe care vreau sa o atribui nu e default*)
       if(andb (types_compatibility var_undecl (env y)) (negb (types_compatibility default v)))
        then var_undecl
       else
        (*variabila a fost doar declarata, acum avand tipul default si val de atribuit e tot default*)
          if(andb (types_compatibility var_undecl (env y)) (types_compatibility default v))
            then default
          else
              if(orb (types_compatibility default (env y)) (types_compatibility v (env y)))
                then v
              else var_assign (*daca valoarea de asignat nu are acelasi tip ca variabila*)
    else (env y).
 

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
 
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (val_nat i)) ->
   (x <n= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (val_nat i)) ->
    (x <n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma', 
   a ={ sigma }=> i ->
   sigma' = (update sigma x (val_bool i)) ->
   (x <b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (val_bool i)) ->
    (x <b= a) -{ sigma }-> sigma'
|e_nat_decl_assign: forall a i x sigma sigma',
    a =[sigma]=> i ->
    sigma' = (update sigma x (val_nat i)) ->
    (x <n= a) -{sigma }-> sigma'

| e_vector_decl: forall v i x sigma sigma',
    v =[sigma]=> i ->
    sigma' = (update sigma x (val_nat i)) ->
    (x <n= v) -{sigma}-> sigma'

| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').




 