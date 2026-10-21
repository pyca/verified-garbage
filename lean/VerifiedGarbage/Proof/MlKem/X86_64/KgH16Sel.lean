module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16CT
import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.KgH16CT
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16Tail
import VerifiedGarbage.Proof.MlKem.X86_64.KgH16Rows

/-!
# ML-KEM-768 on x86-64: key generation of each implementation

An implementation `v` with the fragments that absorb `m` blocks of `H`'s
sponge (`Callee4.batchHM16`) runs ML-KEM-768's key generation hashing `ek`
in the rows (`kemKeyGenH16`); any other, `kemKeyGenSel` (`Sel16.lean`).
`kgh_ctl` and `kgh_sp` take the control flow and the stack pointer of the
calls of `vg_mlkem768_kpke_keygen_ntt` and `vg_mlkem768_kpke_keygen_row` from
their proofs (`KgRowsOk`), and of the fragments from theirs (`BatchHMOk16`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v`, `b` or `p`, or a part that
calls the halves of K-PKE key generation: the kernel evaluates only the
parts that call neither the samplers nor those functions. -/
elab "closedH_in " v:ident b:ident p:ident : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  for x in [v, b, p] do
    let e ← elabTerm x none
    if g.containsFVar e.fvarId! then throwError "the goal mentions {e}"
  let calls := [``Impl.MlKem.X86_64.kemKeyGenH16, ``Impl.MlKem.X86_64.KeyGenH16.rows,
    ``Impl.MlKem.X86_64.KeyGenH16.nttAt, ``Impl.MlKem.X86_64.KeyGenH16.rowAt,
    ``Impl.MlKem.X86_64.Kem.kgNttAt, ``Impl.MlKem.X86_64.Kem.kgRowAt,
    ``Impl.MlKem.X86_64.KpkeKgRows.kgNtt, ``Impl.MlKem.X86_64.KpkeKgRows.kgRow]
  if (g.find? fun e => e.isConst && calls.contains e.constName!).isSome then
    throwError "the goal calls the halves of K-PKE key generation"

/-- `ctlOk` of key generation hashing `ek` in the rows, of the implementation
`v` with the fragments `b` (`B`) and `p` (`P`), calling the halves of K-PKE
key generation (`hR : KgRowsOk L`). -/
tactic_template "kgh_ctl " v:ident b:ident p:ident B:ident P:ident hR:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B _ (by decide)).ctl | with_reducible exact ($P).ctl
    | with_reducible exact ($hR).ntt.ctl | with_reducible exact ($hR).row.ctl
    | (closedH_in $v $b $p; decide +kernel) | (code_whnf; closedH_in $v $b $p; decide +kernel)
    | with_reducible exact ($v).prfs_ctl _ _ _ _ | with_reducible exact ($v).arith.cbd16.ctl
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite)
    | (code_whnf; with_reducible apply ctlOk_call)))

/-- That key generation hashing `ek` in the rows never writes the stack pointer. -/
tactic_template "kgh_sp " v:ident b:ident p:ident B:ident P:ident hR:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($B _ (by decide)).sp | with_reducible exact ($P).sp
    | with_reducible exact ($hR).ntt.sp | with_reducible exact ($hR).row.sp
    | (closedH_in $v $b $p; exact Code.all_of_allInstrs (by decide +kernel))
    | (code_whnf; closedH_in $v $b $p; exact Code.all_of_allInstrs (by decide +kernel))
    | with_reducible exact ($v).prfs_sp _ _ _ _ | with_reducible exact ($v).arith.cbd16.sp
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite)
    | (code_whnf; with_reducible apply all_call)))

open KeyGenH in
theorem keyGenHSel_verified (hR : KgRowsOk kem768w.L) (v : Sample4Impl) (WH : KgH16Wf kem768w) (T : KgH16T kem768w)
    (hK : KpkeOk kem768w.L) (W16 : KeyGen16.Kg16Wf kem768w) (W : KeyGen.KgWf kem768w.L) {k : Contract isa}
    (hk : (keyGenK kem768w.L).Implies k)
    (hctlH : ∀ (b : Nat → Prog isa) (p : Prog isa), (∀ m ≤ 3, BatchHMOk16 m (b m)) → BatchPOk16 p →
      ctlOk (kemKeyGenH16 kem768w v.callee b p) = true)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemKeyGen16 kem768w v.callee (n, c)) = true)
    (hctl : ctlOk (kemKeyGen kem768w.L v.callee) = true) :
    Verified X86_64.target (kemKeyGenHSel v.callee) k := by
  unfold kemKeyGenHSel
  match hb : v.callee.batchHM16, hpb : v.callee.batchP16 with
  | some b, some p =>
    exact Verified.of_correct (kemKeyGenH16_correct hR v WH hb hpb (hctlH b p (v.batchHM16 b hb) (v.batchP16 p hpb)))
      (kemKeyGenH16_ct hR v WH T hb hpb) hk
  | none, _ => exact keyGenSel_verified (n := kem768w.L.scr) (Nat.le_refl _) hK v W16 W hk hctl16 hctl
  | some _, none => exact keyGenSel_verified (n := kem768w.L.scr) (Nat.le_refl _) hK v W16 W hk hctl16 hctl

/-- No instruction of `kemKeyGenHSel c` writes the stack pointer, if none of
the functions it may run does. -/
theorem keyGenHSel_sp (v : Sample4Impl) {q : Instr → Bool}
    (hH : ∀ (b : Nat → Prog isa) (p : Prog isa), (∀ m ≤ 3, BatchHMOk16 m (b m)) → BatchPOk16 p →
      (kemKeyGenH16 kem768w v.callee b p).all q = true)
    (h : (kemKeyGenSel kem768w v.callee).all q = true) : (kemKeyGenHSel v.callee).all q = true := by
  unfold kemKeyGenHSel
  match hb : v.callee.batchHM16, hpb : v.callee.batchP16 with
  | some b, some p => exact hH b p (v.batchHM16 b hb) (v.batchP16 p hpb)
  | none, _ => exact h
  | some _, none => exact h

end VG.Proof.MlKem.X86_64
