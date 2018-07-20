Require compiler.util.Common.

Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).

Local Notation "'bind!' x <- a | y ; f" :=
  (match a with
   | x => f
   | _ => y
   end)
    (right associativity, at level 60, x pattern, only parsing).

Local Notation "'bind!' x <- a ; f" :=
  (match a with
   | x => f
   | _ => a
   end)
    (right associativity, at level 60, x pattern, only parsing).

Class ImpParameters :=
  {
    mword : Type;
    mword_nonzero : mword -> bool;

    varname : Type;
    funname : Type;
    actname : Type;
    bopname : Type;
    mem : Type;

    varmap_functions : compiler.util.Map.MapFunctions varname mword;

    interp_binop : bopname -> mword -> mword -> mword;
    load : mword -> mem -> option mword;
    store : mword -> mword -> mem -> option mem;
  }.
Global Existing Instance varmap_functions.
Definition varmap {p:ImpParameters} : Type := Map.map varname mword.

Section Imp.
  Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpParameters}.

  Inductive expr  : Type :=
  | ELit(v: mword)
  | EVar(x: varname)
  | EOp(op: bopname) (e1 e2: expr)
  | ELoad (addr: expr).

  Inductive stmt :=
  | SStore(addr val: expr)
  | SSet(x: varname)(e: expr)
  | SIf(cond: expr)(bThen bElse: stmt)
  | SWhile(cond: expr)(body: stmt)
  | SSeq(s1 s2: stmt)
  | SSkip
  | SCall(binds: list varname)(f: funname)(args: list expr)
  | SIO(binds: list varname)(io : actname)(args: list expr).

  Context (x : varname) (e : expr).

  Delimit Scope bedrock_var with bedrock_var.

  Delimit Scope bedrock_expr with bedrock_expr.
  Notation "(uintptr_t) v 'ULL'" := (ELit v)
   (at level 1, no associativity, format "(uintptr_t) v 'ULL'") : bedrock_expr.
  Notation "*(uintptr_t*) e" := (ELoad e)
   (at level 1, no associativity, format "*(uintptr_t*) e") : bedrock_expr.

  Delimit Scope bedrock_stmt with bedrock_stmt.
  Notation "'/*skip*/'" := SSkip
    : bedrock_stmt.
  Notation "x = e" := (SSet x%bedrock_var e%bedrock_expr)
    : bedrock_stmt.
  Notation "c1 ; c2" := (SSeq c1%bedrock_stmt c2%bedrock_stmt)
    (at level 76, right associativity, c2 at level 76, format "'[v' c1 ; '//' c2 ']'") : bedrock_stmt.
  Notation "x = e" := (SSet x%bedrock_var e%bedrock_expr)
    : bedrock_stmt.
  Notation "'if' ( e ) { c1 } 'else' { c2 }" := (SIf e%bedrock_expr c1%bedrock_stmt c2%bedrock_stmt)
   (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  {  '/  ' c1 '/' }  'else'  {  '/  ' c2 '/' } ']'") : bedrock_stmt.
  Notation "'if' ( e ) { c }" := (SIf e%bedrock_expr c%bedrock_stmt SSkip)
   (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  {  '/  ' c '/' } ']'") : bedrock_stmt.
  Notation "'while' ( e ) { c }" := (SWhile e%bedrock_expr c%bedrock_stmt)
   (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  {  '/  ' c '/' } ']'") : bedrock_stmt.

  (* -fwrapv -- because we will implement signed multiplication by cast-mul-uncast and it will need to have defined behavior *)
  (* -fno-strict-aliasing -- because we treat all pointers as if they were in the same memory space, but the caller might be passing us separately malloc-ed pointers *)
  Check (
    x = *(uintptr_t*)e;
    if (ELit _) {
      /*skip*/;
      /*skip*/;
      (while (e) {
         x = *(uintptr_t*)e;
         x = *(uintptr_t*)e;
         x = *(uintptr_t*)e
      });
      /*skip*/;
      /*skip*/
    } else {
     /*skip*/
    }
         )%bedrock_stmt.
End Imp.