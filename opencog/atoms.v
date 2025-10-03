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
Record Atom : Type := mkAtom {
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
Definition tv_true : TruthValue := mkTruthValue 1 1.
Definition tv_false : TruthValue := mkTruthValue 0 1.
Definition tv_unknown : TruthValue := mkTruthValue (1#2) 0.

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
    (1 - (strength tv))
    (confidence tv).

(** Convert dL formulas to atoms *)
Fixpoint formula_to_atom (f : Formula) (id : nat) : Atom :=
  match f with
  | KFtrue => mkAtom id ConceptNode "true" [] tv_true (Some f) None None
  | KFfalse => mkAtom id ConceptNode "false" [] tv_false (Some f) None None
  | KFand l r => 
      let left_atom := formula_to_atom l (id + 1) in
      let right_atom := formula_to_atom r (id + 2) in
      mkAtom id AndLink "and" [left_atom; right_atom] tv_unknown (Some f) None None
  | KFor l r => 
      let left_atom := formula_to_atom l (id + 1) in
      let right_atom := formula_to_atom r (id + 2) in
      mkAtom id OrLink "or" [left_atom; right_atom] tv_unknown (Some f) None None
  | KFnot child => 
      let child_atom := formula_to_atom child (id + 1) in
      mkAtom id NotLink "not" [child_atom] tv_unknown (Some f) None None
  | KFimply l r => 
      let left_atom := formula_to_atom l (id + 1) in
      let right_atom := formula_to_atom r (id + 2) in
      mkAtom id ImplicationLink "implies" [left_atom; right_atom] tv_unknown (Some f) None None
  | KFbox prog child => 
      let prog_atom := program_to_atom prog (id + 1) in
      let child_atom := formula_to_atom child (id + 2) in
      mkAtom id BoxLink "box" [prog_atom; child_atom] tv_unknown (Some f) None None
  | KFdiamond prog child => 
      let prog_atom := program_to_atom prog (id + 1) in
      let child_atom := formula_to_atom child (id + 2) in
      mkAtom id DiamondLink "diamond" [prog_atom; child_atom] tv_unknown (Some f) None None
  | KFgreaterEqual l r =>
      let left_atom := term_to_atom l (id + 1) in
      let right_atom := term_to_atom r (id + 2) in
      mkAtom id PredicateNode ">==" [left_atom; right_atom] tv_unknown (Some f) None None
  | _ => mkAtom id ConceptNode "unknown_formula" [] tv_unknown (Some f) None None
  end

(** Convert dL programs to atoms *)
with program_to_atom (p : Program) (id : nat) : Atom :=
  match p with
  | KPassign x e =>
      let var_atom := mkAtom (id + 1) VariableNode (kassignable_to_string x) [] tv_true None None (Some (KTread x)) in
      let term_atom := term_to_atom e (id + 2) in
      mkAtom id ConceptNode "assign" [var_atom; term_atom] tv_unknown None (Some p) None
  | KPtest cond =>
      let cond_atom := formula_to_atom cond (id + 1) in
      mkAtom id ConceptNode "test" [cond_atom] tv_unknown None (Some p) None
  | KPchoice l r =>
      let left_atom := program_to_atom l (id + 1) in
      let right_atom := program_to_atom r (id + 2) in
      mkAtom id ConceptNode "choice" [left_atom; right_atom] tv_unknown None (Some p) None
  | KPcompose l r =>
      let left_atom := program_to_atom l (id + 1) in
      let right_atom := program_to_atom r (id + 2) in
      mkAtom id ConceptNode "compose" [left_atom; right_atom] tv_unknown None (Some p) None
  | KPloop child =>
      let child_atom := program_to_atom child (id + 1) in
      mkAtom id ConceptNode "loop" [child_atom] tv_unknown None (Some p) None
  | KPodeSystem ode constraint =>
      let ode_atom := ode_to_atom ode (id + 1) in
      let constraint_atom := formula_to_atom constraint (id + 2) in
      mkAtom id ODELink "ode_system" [ode_atom; constraint_atom] tv_unknown None (Some p) None
  | _ => mkAtom id ConceptNode "unknown_program" [] tv_unknown None (Some p) None
  end

(** Convert dL terms to atoms *)
with term_to_atom (t : Term) (id : nat) : Atom :=
  match t with
  | KTnumber (KTNnat n) => mkAtom id NumberNode (string_of_nat n) [] tv_true None None (Some t)
  | KTnumber (KTNreal r) => mkAtom id NumberNode "real" [] tv_true None None (Some t)
  | KTread x => mkAtom id VariableNode (kassignable_to_string x) [] tv_true None None (Some t)
  | KTplus l r =>
      let left_atom := term_to_atom l (id + 1) in
      let right_atom := term_to_atom r (id + 2) in
      mkAtom id ConceptNode "plus" [left_atom; right_atom] tv_unknown None None (Some t)
  | KTminus l r =>
      let left_atom := term_to_atom l (id + 1) in
      let right_atom := term_to_atom r (id + 2) in
      mkAtom id ConceptNode "minus" [left_atom; right_atom] tv_unknown None None (Some t)
  | KTtimes l r =>
      let left_atom := term_to_atom l (id + 1) in
      let right_atom := term_to_atom r (id + 2) in
      mkAtom id ConceptNode "times" [left_atom; right_atom] tv_unknown None None (Some t)
  | KTdifferential child =>
      let child_atom := term_to_atom child (id + 1) in
      mkAtom id ConceptNode "differential" [child_atom] tv_unknown None None (Some t)
  | _ => mkAtom id ConceptNode "unknown_term" [] tv_unknown None None (Some t)
  end

(** Convert ODEs to atoms *)
with ode_to_atom (ode : ODE) (id : nat) : Atom :=
  match ode with
  | ODEatomic (ODEsing x e) =>
      let var_atom := mkAtom (id + 1) VariableNode (kassignable_to_string x) [] tv_true None None (Some (KTread x)) in
      let term_atom := term_to_atom e (id + 2) in
      mkAtom id ConceptNode "ode_sing" [var_atom; term_atom] tv_unknown None None None
  | ODEprod l r =>
      let left_atom := ode_to_atom l (id + 1) in
      let right_atom := ode_to_atom r (id + 2) in
      mkAtom id ConceptNode "ode_prod" [left_atom; right_atom] tv_unknown None None None
  | _ => mkAtom id ConceptNode "unknown_ode" [] tv_unknown None None None
  end.

(** Helper function to convert KAssignable to string *)
Fixpoint kassignable_to_string (x : KAssignable) : string :=
  match x with
  | KAssignVar (variable s) => s
  | KAssignDiff y => (kassignable_to_string y) ++ "'"
  end.

(** Add atom to atomspace *)
Definition add_atom (as : Atomspace) (a : Atom) : Atomspace :=
  mkAtomspace (a :: (atoms as)) (S (next_id as)).

(** Find atoms by type *)
Definition find_atoms_by_type (as : Atomspace) (at : AtomType) : list Atom :=
  filter (fun a => match atom_type a with at => true | _ => false end) (atoms as).

(** Create empty atomspace *)
Definition empty_atomspace : Atomspace := mkAtomspace [] 0.

(** Add dL formula to atomspace *)
Definition add_formula (as : Atomspace) (f : Formula) : Atomspace :=
  let atom := formula_to_atom f (next_id as) in
  add_atom as atom.

(** Add dL program to atomspace *)
Definition add_program (as : Atomspace) (p : Program) : Atomspace :=
  let atom := program_to_atom p (next_id as) in
  add_atom as atom.