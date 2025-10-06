(*
  OpenCog-inspired Atomspace for OCoq-dL
  
  This module implements an Atomspace-like knowledge representation
  system optimized for differential dynamic logic formulas and proofs.
  It provides cognitive reasoning capabilities for automated theorem proving.
*)

Require Export syntax.symbol.
Require Export syntax.expressions.
Require Export String.
Require Export Coq.Lists.List.
Export List.ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qminmax.
Require Import Coq.Reals.Reals.

(** Atom types for OpenCog-style knowledge representation *)
Inductive AtomType : Type :=
| ConceptNode    : AtomType  (* Represents concepts/classes *)
| PredicateNode  : AtomType  (* Represents predicates/relations *)
| VariableNode   : AtomType  (* Represents variables *)
| NumberNode     : AtomType  (* Represents numerical values *)
| ListLink       : AtomType  (* Represents lists/sequences *)
| EvaluationLink : AtomType  (* Represents predicate evaluations *)
| ImplicationLink: AtomType  (* Represents logical implications *)
| AndLink        : AtomType  (* Represents conjunctions *)
| OrLink         : AtomType  (* Represents disjunctions *)
| NotLink        : AtomType  (* Represents negations *)
| ForAllLink     : AtomType  (* Represents universal quantification *)
| ExistsLink     : AtomType  (* Represents existential quantification *)
| BoxLink        : AtomType  (* Represents dL box modality *)
| DiamondLink    : AtomType  (* Represents dL diamond modality *)
| ODELink        : AtomType  (* Represents ODE systems *)
| ProofLink      : AtomType  (* Represents proof structures *)
.

(** Truth values with confidence intervals for probabilistic reasoning *)
Record TruthValue : Type := mkTruthValue {
  strength : Q;      (* Truth strength [0,1] *)
  confidence : Q;    (* Confidence level [0,1] *)
}.

(** Atom structure with truth values and metadata *)
Inductive Atom : Type := mkAtom {
  atom_id : nat;
  atom_type : AtomType;
  atom_name : string;
  atom_outgoing : list Atom;  (* Outgoing connections *)
  atom_tv : TruthValue;       (* Truth value *)
  atom_dL_formula : option Formula;  (* Associated dL formula *)
  atom_dL_program : option Program;  (* Associated dL program *)
  atom_dL_term : option Term;        (* Associated dL term *)
}.

(** Atomspace - the knowledge base *)
Record Atomspace : Type := mkAtomspace {
  atoms : list Atom;
  next_id : nat;
}.

(** Helper functions for truth value operations *)
Definition tv_true : TruthValue := mkTruthValue (1#1) (1#1).
Definition tv_false : TruthValue := mkTruthValue (0#1) (1#1).
Definition tv_unknown : TruthValue := mkTruthValue (1#2) (0#1).

Definition tv_and (tv1 tv2 : TruthValue) : TruthValue :=
  mkTruthValue 
    (Qmin (strength tv1) (strength tv2))
    (Qmin (confidence tv1) (confidence tv2)).

Definition tv_or (tv1 tv2 : TruthValue) : TruthValue :=
  mkTruthValue 
    (Qmax (strength tv1) (strength tv2))
    (Qmin (confidence tv1) (confidence tv2)).

Definition tv_not (tv : TruthValue) : TruthValue :=
  mkTruthValue 
    (Qminus (1#1) (strength tv))
    (confidence tv).

(** Helper function to convert KAssignable to string *)
Fixpoint kassignable_to_string (x : KAssignable) : string :=
  match x with
  | KAssignVar (variable s) => s
  | KAssignDiff y => (kassignable_to_string y) ++ "'"
  end.

(** Simple string conversion for natural numbers *)
Fixpoint string_of_nat (n : nat) : string :=
  match n with
  | O => "0"
  | S n' => "S(" ++ string_of_nat n' ++ ")"
  end.

(** Convert dL formulas to atoms - simplified version *)
Definition formula_to_atom (f : Formula) (id : nat) : Atom :=
  match f with
  | KFtrue => mkAtom id ConceptNode "true" [] tv_true (Some f) None None
  | KFfalse => mkAtom id ConceptNode "false" [] tv_false (Some f) None None
  | KFand l r => 
      mkAtom id AndLink "and" [] tv_unknown (Some f) None None
  | KFor l r => 
      mkAtom id OrLink "or" [] tv_unknown (Some f) None None
  | KFnot child => 
      mkAtom id NotLink "not" [] tv_unknown (Some f) None None
  | KFimply l r => 
      mkAtom id ImplicationLink "implies" [] tv_unknown (Some f) None None
  | KFbox prog child => 
      mkAtom id BoxLink "box" [] tv_unknown (Some f) None None
  | KFdiamond prog child => 
      mkAtom id DiamondLink "diamond" [] tv_unknown (Some f) None None
  | KFgreaterEqual l r =>
      mkAtom id PredicateNode ">==" [] tv_unknown (Some f) None None
  | _ => mkAtom id ConceptNode "unknown_formula" [] tv_unknown (Some f) None None
  end.

(** Convert dL programs to atoms - simplified version *)
Definition program_to_atom (p : Program) (id : nat) : Atom :=
  match p with
  | KPassign x e =>
      mkAtom id ConceptNode "assign" [] tv_unknown None (Some p) None
  | KPtest cond =>
      mkAtom id ConceptNode "test" [] tv_unknown None (Some p) None
  | KPchoice l r =>
      mkAtom id ConceptNode "choice" [] tv_unknown None (Some p) None
  | KPcompose l r =>
      mkAtom id ConceptNode "compose" [] tv_unknown None (Some p) None
  | KPloop child =>
      mkAtom id ConceptNode "loop" [] tv_unknown None (Some p) None
  | KPodeSystem ode constraint =>
      mkAtom id ODELink "ode_system" [] tv_unknown None (Some p) None
  | _ => mkAtom id ConceptNode "unknown_program" [] tv_unknown None (Some p) None
  end.

(** Convert dL terms to atoms - simplified version *)
Definition term_to_atom (t : Term) (id : nat) : Atom :=
  match t with
  | KTnumber (KTNnat n) => mkAtom id NumberNode (string_of_nat n) [] tv_true None None (Some t)
  | KTnumber (KTNreal r) => mkAtom id NumberNode "real" [] tv_true None None (Some t)
  | KTread x => mkAtom id VariableNode (kassignable_to_string x) [] tv_true None None (Some t)
  | KTplus l r =>
      mkAtom id ConceptNode "plus" [] tv_unknown None None (Some t)
  | KTminus l r =>
      mkAtom id ConceptNode "minus" [] tv_unknown None None (Some t)
  | KTtimes l r =>
      mkAtom id ConceptNode "times" [] tv_unknown None None (Some t)
  | KTdifferential child =>
      mkAtom id ConceptNode "differential" [] tv_unknown None None (Some t)
  | _ => mkAtom id ConceptNode "unknown_term" [] tv_unknown None None (Some t)
  end.

(** Convert ODEs to atoms - simplified version *)
Definition ode_to_atom (ode : ODE) (id : nat) : Atom :=
  match ode with
  | ODEatomic (ODEsing x e) =>
      mkAtom id ConceptNode "ode_sing" [] tv_unknown None None None
  | ODEprod l r =>
      mkAtom id ConceptNode "ode_prod" [] tv_unknown None None None
  | _ => mkAtom id ConceptNode "unknown_ode" [] tv_unknown None None None
  end.

(** Add atom to atomspace *)
Definition add_atom (atomspace_arg : Atomspace) (a : Atom) : Atomspace :=
  mkAtomspace (a :: (atoms atomspace_arg)) (S (next_id atomspace_arg)).

(** Find atoms by type *)
Definition find_atoms_by_type (atomspace_arg : Atomspace) (target_type : AtomType) : list Atom :=
  filter (fun a => 
    match atom_type a with 
    | ConceptNode => match target_type with ConceptNode => true | _ => false end
    | PredicateNode => match target_type with PredicateNode => true | _ => false end
    | ImplicationLink => match target_type with ImplicationLink => true | _ => false end
    | _ => false 
    end) (atoms atomspace_arg).

(** Create empty atomspace *)
Definition empty_atomspace : Atomspace := mkAtomspace [] 0.

(** Add dL formula to atomspace *)
Definition add_formula (atomspace_arg : Atomspace) (f : Formula) : Atomspace :=
  let atom := formula_to_atom f (next_id atomspace_arg) in
  add_atom atomspace_arg atom.

(** Add dL program to atomspace *)
Definition add_program (atomspace_arg : Atomspace) (p : Program) : Atomspace :=
  let atom := program_to_atom p (next_id atomspace_arg) in
  add_atom atomspace_arg atom.