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
  | bor : BExp -> BExp -> BExp
  | bequal : AExp -> AExp -> BExp.


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


Definition Env := string -> Mem.

Definition mlayer : MemLayer := fun x => var_undecl.

Definition env : Env := fun x => mem_default.



Compute (env "z"). (* Variabila nu e inca declarata *)
Compute ( env "x"). 

(* Examplu de update la memorie in functie de un offset *)
Compute ((update_env env "x" (offset 2)) "x").

Compute ((update_env env "z" (offset 5)) "z").

Definition update_mem (layer: MemLayer) (x: Mem) (n: Values) : MemLayer :=
  fun y =>
    if( andb (Mem_beq x y) (Values_beq n (layer y)) ) (*sunt egale adresele si value diferit*)
    then
       (layer y)
    else
      n.

Compute ((update_mem mlayer (offset 3) (val_nat 5)) (offset 3)).
Compute ((update_mem mlayer (offset 4) (val_nat 29)) (offset 4)).


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

(*update_env pentru vectori: imi incrementez offsetul astfel incat sa am loc in memorie cat dimensiunea vectorului  *)
 
Fixpoint update_env_vector (env: EnvMem) (x: string) (m: nat) (n: Mem) : EnvMem :=
match m with 
| 0 => env
| S m' => match n with
           | mem_default => env
           | offset of => (update_env_vector (update_env env x (offset (of+m'))) x m' (offset(of+1))) 
           end
end.

Compute ((update_env_vector env "x" 9 (offset 6)) "x").
Compute ((update_env_vector env "y" 10 (offset 15)) "x").

(* Statements *)
Inductive Stmt :=
  | var_decl: string -> Stmt (* declaratie pentru variabile *)
  | nat_decl_assign: string -> AExp -> Stmt
  | bool_decl_assign: string -> BExp ->Stmt
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
Notation "A =' B" := (bequal A B)(at level 70).

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




(* Configuration 
Inductive Config :=
   nat: last memory zone
     Env: environment
     MemLayer: memory layer
     Stack: stack 
  
  | config : nat -> Env -> MemLayer -> Config.*)


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
Definition EnvValues := string -> Values.

(* Initial, toate variabilele sunt undeclared in environment *)
Definition envValues : EnvValues := fun x => var_undecl.


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

Compute (types_compatibility (val_nat 5) (val_nat 8)).
Compute (types_compatibility (val_nat 5) (val_bool true)).
Compute (types_compatibility default (val_nat 118)).

Compute (MemDefault "x").

(* Notatations used for the Big-Step semantics *)
Reserved Notation "A =[ S , T ]=> N" (at level 30).
Reserved Notation "B ={ S , T }=> B'" (at level 70).
 
Definition plus_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with 
    | error_nat, _ => error_nat
    | _, error_nat => error_nat 
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_Nat (n1 n2 : TypeNat) : TypeNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end. 
   
(* Big-Step semantics for arithmetic operations *)
Inductive aeval : AExp -> EnvMem -> MemLayer -> TypeNat -> Prop :=
| const : forall n sigma phi, anum n =[ sigma , phi ]=> n
| var : forall v sigma phi, avar v =[ sigma , phi ]=>  match (phi (sigma v)) with
                                              | val_nat x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma phi n,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    n = (plus_Nat i1 i2) ->
    (a1 +' a2) =[ sigma , phi ]=> n
| multiplic : forall a1 a2 i1 i2 sigma phi n,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    n = (mul_Nat i1 i2) ->
    (a1 *' a2) =[ sigma , phi ]=> n
| substract : forall a1 a2 i1 i2 sigma phi n,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    n = (sub_Nat i1 i2) ->
    (a1 -' a2) =[ sigma , phi ]=> n
| division : forall a1 a2 i1 i2 sigma phi n,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    n = (div_Nat  i1 i2) ->
    (a1 /' a2) =[ sigma , phi ]=> n
| modulo : forall a1 a2 i1 i2 sigma phi n,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    n = (mod_Nat i1 i2) ->
    (a1 %' a2) =[ sigma , phi ]=> n
| s_to_val : forall s sigma phi,
             avar s =[ sigma , phi ]=> match (phi (sigma s)) with
                                   | val_nat s => s
                                   | _ => error_nat
                                   end
where "a =[ sigma , phi ]=> n" := (aeval a sigma phi n).
 
Compute ((update_env env "x" (offset 9)) "x").
Compute ((update_mem mlayer (offset 9) (val_nat 5)) (offset 9)).

Example ex0 : 5 =[ env , mlayer ]=> 5.
Proof.
 apply const.
Qed.

Example ex1 : (4 +' 4) =[ env , mlayer ]=> 8.
Proof.
 eapply add.
 apply const.
 apply const.
 simpl.
 reflexivity.
Qed.

Example ex2 : (3 *' 3) =[ env, mlayer ]=> 9.
Proof.
  eapply multiplic.
  apply const.
  apply const.
  simpl.
  reflexivity.
Qed.

Example ex3 : (1 -' 5) =[ env , mlayer ]=> error_nat.
Proof.
  eapply substract.
  apply const.
  apply const.
  simpl. 
  reflexivity.
Qed.

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

Definition equal_Bool (n1 n2 : TypeNat) : TypeBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.eqb v1 v2)
    end.

(* Big-Step semantics for bool operations *)
Inductive beval : BExp -> EnvMem -> MemLayer -> TypeBool -> Prop :=
| b_error: forall sigma phi, berror  ={ sigma , phi }=> error_bool
| b_true : forall sigma phi, btrue ={ sigma , phi }=> true
| b_false : forall sigma phi, bfalse ={ sigma , phi }=> false
| b_var : forall v sigma phi, bvar v ={ sigma , phi }=>  match (phi (sigma v)) with
                                                | val_bool x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma phi b,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    b = (lt_Bool i1 i2) ->
    a1 <' a2 ={ sigma , phi }=> b
| b_not : forall a1 i1 sigma phi b,
    a1 ={ sigma , phi }=> i1 ->
    b = (not_Bool i1) ->
    !'a1 ={ sigma , phi }=> b
| b_and : forall a1 a2 i1 i2 sigma phi b,
    a1 ={ sigma , phi }=> i1 ->
    a2 ={ sigma , phi }=> i2 ->
    b = (and_Bool i1 i2) ->
    (a1 &&' a2) ={ sigma , phi }=> b 
| b_or : forall a1 a2 i1 i2 sigma phi b,
    a1 ={ sigma , phi }=> i1 ->
    a2 ={ sigma , phi }=> i2 ->
    b = (or_Bool i1 i2) ->
    (a1 ||' a2) ={ sigma , phi }=> b 
| b_equal : forall a1 a2 i1 i2 sigma phi b,
    a1 =[ sigma , phi ]=> i1 ->
    a2 =[ sigma , phi ]=> i2 ->
    b = (equal_Bool i1 i2) ->
    (a1 =' a2) ={ sigma , phi }=> b
    
where "B ={ S , T }=> B'" := (beval B S T B').




Example ex4: bnot (100 <' "n") ={ env , mlayer }=> error_bool.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

Example ex5: (10 =' 5) &&' ( 8 =' 8) ={ env , mlayer }=> (boolean false).
Proof. 
 eapply b_and.
  eapply b_equal.
  apply const.
  apply const.
  simpl.
  reflexivity.
  eapply b_equal.
  apply const.
  apply const.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Reserved Notation "S -{ Sigma , Phi }-> Phi'" (at level 60).
 

Inductive eval : Stmt -> EnvMem -> MemLayer -> MemLayer -> Prop :=
| e_nat_decl: forall a i x sigma phi phi',
   a =[ sigma , phi ]=> i ->
   phi' = (update_mem phi (env x) var_undecl) ->
   (LetNat x) -{ sigma , phi }-> phi'
| e_nat_assign: forall a i x sigma phi phi',
    a =[ sigma , phi ]=> i ->
    phi' = (update_mem phi (env x) (val_nat i)) ->
    (x <n= a) -{ sigma , phi }-> phi'
| e_bool_decl: forall  a i x sigma phi phi',
   a ={ sigma , phi }=> i ->
   phi' = (update_mem phi (env x) var_undecl) ->
   (LetBool x) -{ sigma , phi }-> phi'

| e_bool_assign: forall  a i x sigma phi phi',
    a ={ sigma , phi }=> i ->
    phi' = (update_mem phi (env x) (val_bool i)) ->
    (x <b= a) -{ sigma , phi }-> phi'

|e_nat_decl_assign: forall a i x sigma phi phi',
    a =[ sigma , phi ]=> i ->
    phi' = (update_mem phi (env x) var_undecl) ->
    phi' = (update_mem phi (env x) (val_nat i)) ->
    (x DecNat= a) -{ sigma , phi }-> phi'

(*| e_vector_decl: forall v i x sigma sigma' phi,
    v =[ sigma , phi ]=> i ->
    phi' = (update_env_vector phi x (val_nat i)) ->
    (x <n= v) -{ sigma , phi}-> sigma' *)

| e_seq : forall s1 s2 sigma phi phi1 phi2,
    s1 -{ sigma , phi }-> phi1 ->
    s2 -{ sigma , phi1 }-> phi2 ->
    (s1 ;; s2) -{ sigma , phi }-> phi2
| e_if_then : forall b s sigma phi, 
    ifthen b s -{ sigma , phi }-> phi
  
| e_if_then_elsetrue : forall b s1 s2 sigma phi phi',
    b ={ sigma , phi }=> true ->
    s1 -{ sigma , phi }-> phi' ->
    ifthenelse b s1 s2 -{ sigma , phi }-> phi' 
| e_if_then_elsefalse : forall b s1 s2 sigma phi phi',
    b ={ sigma, phi }=> false ->
    s2 -{ sigma, phi }-> phi' -> 
    ifthenelse b s1 s2 -{ sigma , phi }-> phi' 
| e_whilefalse : forall b s sigma phi,
    b ={ sigma , phi }=> false ->
    while b s -{ sigma , phi }-> phi
| e_whiletrue : forall b s sigma phi phi',
    b ={ sigma , phi }=> true ->
    (s ;; while b s) -{ sigma , phi }-> phi' ->
    while b s -{ sigma , phi }-> phi'
where "s -{ sigma , phi }-> phi'" := (eval s sigma phi phi').


 
Example ex' : whilee ( "n" <' 3 ) { "n" <n= 3 } -{ env , mlayer }-> mlayer.
Proof.
  eapply e_whilefalse.
  eapply b_lessthan.
  - apply var.
  - apply const.
  - simpl. 
Qed.


 