(* Inductive Definitions and QuickChick generators for Palamedes RQ2. Tested with Coq 8.20 *)

From QuickChick Require Import QuickChick.

(* STLC, longer setup *)

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Inductive term : Type :=
| Const : nat -> term
| Id : nat -> term
| App : term -> term -> term
| Abs : term -> term.

Definition env := list type.

Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (cons tau env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (cons tau' env) (S x) tau.

Inductive typing : env -> term -> type -> Prop :=
| TId :
    forall e x tau,
      bind e x tau ->
      typing e (Id x) tau
| TConst :
    forall e n,
      typing e (Const n) N
| TAbs :
    forall e t tau1 tau2,
      typing (cons tau1 e) t tau2 ->
      typing e (Abs t) (Arrow tau1 tau2)
| TApp :
    forall e t1 t2 tau1 tau2,
      typing e t1 (Arrow tau1 tau2) ->
      typing e t2 tau1 ->
      typing e (App t1 t2) tau2.

Derive Arbitrary for type.
Derive Show for term.
Derive Show for type.
Instance dec_type (t1 t2 : type) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive Generator for (fun x => bind env x tau).
Derive Generator for (fun t => typing env t tau).

(* Sample (genST (fun e => typing nil e (Arrow N N ))). *)

Inductive scoped : env -> term -> Prop :=
| SId :
    forall e x tau,
      bind e x tau ->
      scoped e (Id x)
| SConst :
    forall e n,
      scoped e (Const n)
| SAbs :
    forall e t,
      scoped (cons N e) t ->
      scoped e (Abs t)
| SApp :
    forall e t1 t2,
      scoped e t1 ->
      scoped e t2 ->
      scoped e (App t1 t2).

Derive Generator for (fun t => scoped env t).

(* Sample (genST (fun e => scoped nil e)). *)
