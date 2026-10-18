module

public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public meta import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public meta import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# ML-KEM on x86-64: the control flow and the stack pointer of the top-level functions with 16-bit polynomials

As `s4_ctl` and `s4_sp` (`Sample4Impl.lean`), for code that also calls the
16-bit sampler `c` of an implementation `v` (`S : S16Ok c`) and the K-PKE
functions (`hK : KpkeOk L`): their calls are taken from `S` and `hK`, before
any part is evaluated, so the kernel evaluates neither the samplers' code
nor the K-PKE functions'.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v` or `c`, or a part of the
top-level functions that calls the K-PKE functions: the kernel evaluates
only the parts that call neither the samplers nor the K-PKE functions. -/
elab "closed16_in " v:ident c:ident : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  for x in [v, c] do
    let e ← elabTerm x none
    if g.containsFVar e.fvarId! then throwError "the goal mentions {e}"
  let calls := [``Impl.MlKem.X86_64.kemKeyGen16, ``Impl.MlKem.X86_64.kemEncapsH16,
    ``Impl.MlKem.X86_64.kemDecaps16, ``Impl.MlKem.X86_64.Top16.kgTail, ``Impl.MlKem.X86_64.Top16.kgRest,
    ``Impl.MlKem.X86_64.Top16.encRest, ``Impl.MlKem.X86_64.Top16.encrypt,
    ``Impl.MlKem.X86_64.Kem.kpkeKgAt, ``Impl.MlKem.X86_64.Kem.kpkeEncAt, ``Impl.MlKem.X86_64.Kem.kpkeDecAt,
    ``Impl.MlKem.X86_64.kpkeKg, ``Impl.MlKem.X86_64.kpkeEnc, ``Impl.MlKem.X86_64.kpkeDec]
  if (g.find? fun e => e.isConst && calls.contains e.constName!).isSome then
    throwError "the goal calls the K-PKE functions"

open Lean Meta Elab Tactic in
/-- Puts the code `X` of a goal `f X = true` in weak head normal form, if
that is a `block`, `seq`, `ite` or `call`, so that a lemma about each applies with
reducible transparency: a failed `apply` at default transparency would
evaluate `f` on code it does not match, the K-PKE functions' included. -/
elab "code_whnf" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (_, lhs, rhs) := t.eq? | throwError "not an equation"
  let lhs := lhs.consumeMData
  let .app f x := lhs | throwError "not an application"
  let x' ← whnf x
  unless [``Code.block, ``Code.seq, ``Code.ite, ``Code.call].contains x'.getAppFn.constName do
    throwError "not a `block`, `seq`, `ite` or `call`"
  replaceMainGoal [← g.replaceTargetDefEq (← mkEq (.app f x') rhs)]

/-- `ctlOk` of a top-level function with 16-bit polynomials. -/
tactic_template "s16_ctl " v:ident c:ident S:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($hK).kg.ctl | with_reducible exact ($hK).enc.ctl
    | with_reducible exact ($hK).dec.ctl | with_reducible exact ($S).mxcsr
    | (closed16_in $v $c; decide +kernel) | (code_whnf; closed16_in $v $c; decide +kernel)
    | with_reducible exact ($v).prfs_ctl _ _ _ _ | with_reducible exact ($v).arith.cbd16.ctl
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite)
    | (code_whnf; with_reducible apply ctlOk_call)))

/-- That a top-level function with 16-bit polynomials never writes the stack pointer. -/
tactic_template "s16_sp " v:ident c:ident S:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($hK).kg.sp | with_reducible exact ($hK).enc.sp
    | with_reducible exact ($hK).dec.sp | with_reducible exact ($S).spSafe
    | (closed16_in $v $c; exact Code.all_of_allInstrs (by decide +kernel))
    | (code_whnf; closed16_in $v $c; exact Code.all_of_allInstrs (by decide +kernel))
    | with_reducible exact ($v).prfs_sp _ _ _ _ | with_reducible exact ($v).arith.cbd16.sp
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite)
    | (code_whnf; with_reducible apply all_call)))

end VG.Proof.MlKem.X86_64
