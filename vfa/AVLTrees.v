(** * Projeto de Topicos Avancados em Engenharia de Software *)

(* Equipe:

          - Nara Souza de Andrade (nsa2@cin.ufpe.br)
          - Sergio Machado de Arruda Filho (smaf2@cin.ufpe.br)
          - Tiago Sousa Carvalho (tsc2@cin.ufpe.br)

*)

(* ################################################################# *)
(** * Introduction *)

(** Esse projeto tem como objetivo apresentar uma implementacao funcional de \u00e1rvores AVL,
    al\u00e9m da an\u00e1lise de algumas de suas propriedades, juntamente com suas provas.
    Utilizaremos como base a implementacao de Binary Search Trees disponibilizada no
    Volume 3 - Verified Functional Algorithms. *)

From VFA Require Import SearchTree.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinIntDef.
From VFA Require Import Perm.



(* ################################################################# *)
(** * Implementation *)

(** Tendo como base as funcoes sobre arvore ja definidas no capitulo de
    Binary Search Trees (Volume 3 - Verified Functional Algorithms), iremos
    definir a funcao de balanceamento de uma arvore AVL. Mas antes, para
    facilitar a implementacao da funcao de balanceamento, vamos definir uma
    funcao que calcula a altura de uma arvore. Tambem iremos definir as funcoes
    rotateLeft e rotateRight.*)

Module AVL (Import I:Int).

Local Notation int := I.t.

Notation  "a <? b" := (I.ltb a b)
                          (at level 70) : Int_scope.

Fixpoint height {V : Type} (t : tree V) : int :=
  match t with
  | E => 0
  | T l k v r => 1 + (max (height l) (height r))
  end.

Definition rotateLeft {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => match r with 
                 |E => E 
                 | T l' x' v' r' => T (T E x v E) x' v' r'
                 end
  end.

Definition rotateRight {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => match l with 
                 |E => E 
                 | T l' x' v' r' => T l' x' v' (T E x v E)
                 end
  end.

Definition calcBalance {V : Type} (t : tree V) : int :=
  match t with
  | E => 0
  | T l x v r => I.sub (height r) (height l)
  end.

Definition balance {V : Type} (t : tree V) : tree V :=
  match t with
  | E => t
  | T l x v r => if 1 <? calcBalance t then 
                                       if calcBalance r <? 0 then rotateLeft (T l x v (rotateRight r)) 
                                                             else rotateLeft t
                 else if calcBalance t <? -(1) then 
                                               if 0 <? calcBalance l then rotateRight ( T (rotateLeft l) x v r) 
                                                                     else rotateRight t
                 else t
  end.


(** * Agora, definiremos a funcao de insert, que utilizar\u00e1 a funcao de balance sempre
      que uma insercao for realizada. *)

Fixpoint insert' {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if y >? x then balance (T (insert' x v l) y v' r)
                 else if x >? y then balance (T l y v' (insert' x v r))
                      else T l x v r
  end.

End AVL.

(* 2021-08-08 *)