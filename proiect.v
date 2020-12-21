Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.


(*-------------Tipuri Variabile si declarari Variabile-----------*)

Inductive Error :=
 | error_type : Error.

Inductive TypeNat :=
  | var_nat : TypeNat
  | num : nat -> TypeNat.

Inductive TypeBool :=
  | var_bool : TypeBool
  | boolean : bool -> TypeBool.

Coercion num: nat >-> TypeNat.
Coercion boolean: bool >-> TypeBool.


Inductive Values :=
  | var_undecl : Values
  | default : Values
  | val_nat : TypeNat -> Values
  | val_bool : TypeBool -> Values
  | val_error : Error -> Values.

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

(* Statements *)
Inductive Stmt :=
  | var_decl: string -> Stmt (* declaratie pentru variabile de tip nat *)
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
Notation "! A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

(* Notatii pentru Statements *)
Notation "X <n= A" := (nat_assign X A)(at level 60).
Notation "X <b= A" := (bool_assign X A)(at level 60).
Notation "'LetVar' X " := (var_decl X )(at level 60).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'forr' ( A ; B ; C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).



Check( LetVar "x").
Check ( "x" <n= (anum 5)).
Check ( "y" <b= btrue).

(*Coercions pentru constante si variabile*)

Coercion anum : TypeNat >-> AExp.
Coercion avar : string >-> AExp. (* Var ~> string *)
Coercion bvar : string >->BExp.


Check btrue.
Check bfalse.
Check ! ("x" <' 10).
Check btrue &&' ("n" >' 0).

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
    | default => match t2 with 
                     | default => true
                     | _ => false
                     end
    | val_bool _x => match t2 with  (*daca am o var. de tip bool, verific ca i se atribuie/e utilizata in operatii cu ate bool*)
                     | val_bool _y => true
                     | _ => false
                     end
    | val_nat _x => match t2 with   (*la fel pt nat*)
                     | val_nat _y => true
                     | _ => false
                     end
   | val_error _x => match t2 with 
                     | val_error _y => true
                     | _ => false
                     end
  

  end.


(*------------------------Modelare Memorie-----------------------------*)


Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem. (* offset which indicates the current number of memory zones *)

Scheme Equality for Mem.

(* Environment *)
Definition EnvMem := string -> Mem.

(* Memoria *)
Definition MemLayer := Mem -> Values.

(* Stack cu environmente pt a putea pastra valorile diferite ale variabilelor locale/globale*)
Definition Stack := list Env.

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

Definition envMem : EnvMem := fun x => mem_default.

(*Definition getOffset : string -> Mem  := fun x => EnvMem. *)

(*-------------------------------Vectori----------------------------*)

Inductive Vector :=
  | vec_decl : string -> nat -> Vector
  | vec_assign : string -> nat -> Values -> Vector.

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
Notation "A [ n ] <:= B" := (vec_assign A n B)(at level 61).

Definition EnvVect := Vector -> Vec_Type.

(* Initial, vectorii sunt nedeclarati in environment *)
Definition envVect : EnvVect := fun x => undecl_vec.

Check( "x" [10]).

(*Check("x" [ 1 ] = (val_nat 5)). *)



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
    if (

 aici veific daca vectorul meu nu este gol si daca are mai mult de o valoare 
retinuta in el
  Apoi, daca cele 2 conditii sunt indeplinite ma folosesc de swap pentru a efectua sortarea
*)
  







 