module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs

/-!
# `vg_rsa_recover_primes` on PPC64LE: the entry

`RArgs s0 t`: the pointers and lengths the entry keeps. `entry_ok`: the
entry saves the registers, sets up `w` and the stride, and keeps them.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (entry save)

/-- The pointers and lengths the entry keeps. -/
structure RArgs (s0 t : State) : Prop where
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = s0.gpr .r9
  r27 : t.gpr .r27 = s0.gpr .r10
  r28 : t.gpr .r28 = PPC64LE.stackArg s0 0
  r22 : t.gpr .r22 = PPC64LE.stackArg s0 1

/-- The registers `RArgs` is about. -/
abbrev argKeep : List Reg := [.r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28]

theorem RArgs.of_keep {s0 t u : State} (h : RArgs s0 t) {rs : List Reg} (k : Keep rs t u)
    (hr : ∀ r ∈ argKeep, r ∉ rs := by decide) : RArgs s0 u := by
  have e : ∀ r ∈ argKeep, u.gpr r = t.gpr r := fun r hr' => k.gpr r (hr r hr')
  exact ⟨(e _ (by decide)).trans h.r21, (e _ (by decide)).trans h.r23, (e _ (by decide)).trans h.r24,
    (e _ (by decide)).trans h.r25, (e _ (by decide)).trans h.r26, (e _ (by decide)).trans h.r27,
    (e _ (by decide)).trans h.r28, (e _ (by decide)).trans h.r22⟩

/-- The registers the entry changes. -/
abbrev entryRegs : List Reg :=
  [.r0, .r9, .r10, .r11, .r12, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- After the entry. -/
structure REnt (s0 t : State) : Prop where
  base : RBase s0 t
  args : RArgs s0 t
  r29 : t.gpr .r29 = BitVec.ofNat 64 (ww (kK s0))
  r30 : t.gpr .r30 = BitVec.ofNat 64 (KeyWorkspace.S (ww (kK s0)))
  mem : t.mem = rEntryMem s0
  keep : Keep entryRegs s0 t

theorem entry_ok {s0 : State} (h : rvP.pre s0) : WP isa (.block entry) s0 (REnt s0) := by
  have hp := rv_kpre h
  have h8 : (s0.gpr .r8).toNat ≤ 1024 := hp.k1024
  rw [← List.append_nil entry]
  simp only [entry, List.append_assoc]
  refine save_ok h fun s m e11 esp k1 => ?_
  have e8 : s.gpr .r8 = s0.gpr .r8 := k1.gpr _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = rvB s0 ∧ t.mem = s.mem) (by prun [e11, BitVec.add_zero])
    (by decide)) fun s₁ ⟨⟨a31, m1⟩, k2⟩ => ?_
  have e8' : s₁.gpr .r8 = s0.gpr .r8 := (k2.gpr _ (by decide)).trans e8
  refine wOf_ok (rd := .r29) (by decide) (by rw [e8']; exact h8) ?_
  rw [e8']
  refine strideOf_ok (rd := .r30) (rs := .r29) (w := ww (kK s0)) (by decide) (by simp [gpr_write]) ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r21, .r23, .r24, .r25, .r26, .r27]
    (Q := fun t => (t.gpr .r21 = s0.gpr .r3 ∧ t.gpr .r23 = s0.gpr .r5 ∧ t.gpr .r24 = s0.gpr .r7 ∧
      t.gpr .r25 = s0.gpr .r8 ∧ t.gpr .r26 = s0.gpr .r9 ∧ t.gpr .r27 = s0.gpr .r10) ∧ t.mem = s₁.mem)
    (by prun [k2.gpr .r3 (by decide), k2.gpr .r5 (by decide), k2.gpr .r7 (by decide), e8',
      k2.gpr .r9 (by decide), k2.gpr .r10 (by decide), k1.gpr .r3 (by decide), k1.gpr .r5 (by decide),
      k1.gpr .r7 (by decide), k1.gpr .r9 (by decide), k1.gpr .r10 (by decide), BitVec.add_zero]) (by decide))
    fun s₂ ⟨⟨⟨a21, a23, a24, a25, a26, a27⟩, m2⟩, k3⟩ => ?_
  have K : Keep (.r30 :: .r29 :: .r31 :: entryRegs) s0 s₂ :=
    (((k1.trans k2).trans ((Keep.write _ _ _).trans (Keep.write _ _ _))).trans k3).mono
  have hsp : s₂.sp = s0.sp := K.sp
  have hrd : s₂.rd = s0.rd := K.rd
  refine hp.stackArg_ok hrd hsp (r := .r28) (by decide) (by decide) (by decide) ?_
  refine hp.stackArg_ok (s := s₂.write .r28 _) hrd hsp (r := .r22) (by decide) (by decide) (by decide)
    (WP.block_nil ?_)
  have m3 : s₂.mem = rEntryMem s0 := by rw [m2]; exact m1.trans m
  have r31' : s₂.gpr .r31 = rvB s0 := by rw [k3.gpr _ (by decide)]; simpa [gpr_write] using a31
  have b2 : RBase s0 s₂ := ⟨h, hsp, K.lr, hrd, K.wr, by rw [m3]; exact Outs.refl _ _ _, r31'⟩
  have sa0 := b2.stackArg (i := 0) (by decide)
  have b3 := b2.of_regs (Keep.write s₂ .r28 (PPC64LE.stackArg s₂ 0)) rfl
  have sa1 := b3.stackArg (i := 1) (by decide)
  have e29 : s₂.gpr .r29 = BitVec.ofNat 64 (ww (kK s0)) := by rw [k3.gpr _ (by decide)]; simp [gpr_write]
  have e30 : s₂.gpr .r30 = BitVec.ofNat 64 (KeyWorkspace.S (ww (kK s0))) := by
    rw [k3.gpr _ (by decide)]; simp [gpr_write]
  refine ⟨b3.of_regs (Keep.write _ _ _) rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, m3,
    (K.trans ((Keep.write _ _ _).trans (Keep.write _ _ _))).mono⟩
  rotate_left 7
  · simp only [gpr_write, ite_true]; exact sa1
  all_goals simp only [gpr_write, reduceCtorEq, ite_false, ite_true, sa0, a21, a23, a24, a25, a26, a27, e29, e30]

end VG.Proof.Rsa.PPC64LE.Recover
