module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCck
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkMain
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcEntry
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkPre

/-!
# `vg_rsa_check_crt_key` on PPC64LE: correctness

As `KcCkMain.lean`: `cck_correct`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Impl.Rsa.PPC64LE.Keys (seqs)

/-- What the moves of `vg_rsa_check_crt_key` establish. -/
def CckM (u v : State) : Prop :=
  v.gpr .r14 = u.gpr .r3 ∧ v.gpr .r15 = u.gpr .r4 ∧ v.gpr .r18 = u.gpr .r7 ∧ v.gpr .r19 = u.gpr .r8 ∧
    v.gpr .r20 = u.gpr .r9 ∧ v.gpr .r21 = u.gpr .r10

theorem cck_moves (u : State) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves ++ ([.addi .r7 .r5 0,
        .addi .r8 .r6 0] : List Instr))) u fun v =>
      (CckM u v ∧ v.mem = u.mem ∧ v.gpr .r7 = u.gpr .r5 ∧ v.gpr .r8 = u.gpr .r6) ∧
        Keep [.r14, .r15, .r18, .r19, .r20, .r21, .r7, .r8] u v := by
  refine WP.keep _ ?_ (by decide)
  prun [VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves, CckM]
  simp only [BitVec.add_zero, and_self]

/-- Every register the function changes before the restore. -/
abbrev cckAll : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21,
    .r22, .r23, .r24, .r26, .r29, .r30, .r31]

/-- What holds before the restore. -/
def CckDone (s0 t : State) : Prop :=
  KBase (cckB s0) (cckZ s0) s0 t ∧ t.gpr .r3 = BitVec.ofNat 64 (if cckOk s0 then 1 else 0) ∧ Keep cckAll s0 t

theorem cckOk_of_e {s0 : State}
    (h : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)) = false) :
    cckOk s0 = false := by
  simp [cckOk, Spec.Rsa.checkCrtKey, Spec.Rsa.crtKeyValid, h]

theorem cckOk_of_n {s0 : State}
    (h : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0))) (kK s0) = false) :
    cckOk s0 = false := by
  simp only [cckOk, Spec.Rsa.checkCrtKey, Spec.Rsa.crtKeyValid, len_bytes]
  simp [kK] at h
  simp [h]

/-- `vg_rsa_check_crt_key`'s stack arguments into `r22`, `r23` and `r26`. -/
theorem cck_stk {s0 t : State} (hp : KPre s0 (cckB s0) (cckZ s0) (kK s0) 6 8)
    (b : KBase (cckB s0) (cckZ s0) s0 t) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.CheckCrtKey.stk) t fun u => (u.mem = t.mem ∧
      u.gpr .r22 = PPC64LE.stackArg s0 0 ∧ u.gpr .r23 = PPC64LE.stackArg s0 2 ∧
      u.gpr .r26 = PPC64LE.stackArg s0 4) ∧ Keep [.r22, .r23, .r26] t u := by
  have sa : ∀ i < 8, PPC64LE.stackArg t i = PPC64LE.stackArg s0 i := fun i hi => b.stackArg hp hi
  simp only [VG.Impl.Rsa.PPC64LE.CheckCrtKey.stk, List.append_assoc]
  rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r26 4)]
  refine hp.stackArg_ok b.rd b.sp (r := .r22) (by decide) (by decide) (by decide) ?_
  refine hp.stackArg_ok (s := t.write .r22 _) b.rd b.sp (r := .r23) (by decide) (by decide) (by decide) ?_
  refine hp.stackArg_ok (s := (t.write .r22 _).write .r23 _) b.rd b.sp (r := .r26) (by decide) (by decide)
    (by decide) (WP.block_nil ?_)
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.write, ↓reduceIte]; exact sa 0 (by decide)
  · simp only [State.write, ↓reduceIte]; exact sa 2 (by decide)
  · simp only [State.write, ↓reduceIte]; exact sa 4 (by decide)
  · exact (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

theorem cck_correct (s0 : State) (h : cckP.pre s0) :
    ∃ tr t, Exec isa VG.Impl.Rsa.PPC64LE.CheckCrtKey.code s0 tr t ∧ abiPreserved s0 t ∧ cckP.post s0 t := by
  show WP isa VG.Impl.Rsa.PPC64LE.CheckCrtKey.code s0 fun t => abiPreserved s0 t ∧ cckP.post s0 t
  have hp := cck_kpre h
  obtain ⟨-, hrd, -, dn, de, -, -, -, -, -, -, wn, -, -, -, -, -, -, -, ⟨hk, hk'⟩, e1, e2, -⟩ := id h
  have hk1 : (s0.gpr .r6).toNat ≤ 1024 := by omega
  unfold VG.Impl.Rsa.PPC64LE.CheckCrtKey.code fn
  refine WP.seq (WP.mono (entry_ok hp (by decide) cck_moves (by decide) rfl (CrtValues.ofNat_toNat64 _) e1
    hk1 (by rw [hrd]; simp) de) fun t1 ⟨u, v, ku, ⟨m14, m15, m18, m19, m20, m21⟩, kv, b1, h24, h26, k1⟩ => ?_)
  refine WP.seq (WP.mono (Q := CckDone s0) ?_ fun t ⟨bt, t3, kt⟩ => ?_)
  · refine WP.ite (t1.gpr .r26 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · -- `e` is not valid.
      have hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip
          (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)) = false := by
        rw [h26] at hz
        cases e : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))
        · rfl
        · rw [e] at hz; simp at hz
      refine WP.mono (ret0_ok t1) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨b1.of_regs kt tm, by rw [t3, cckOk_of_e hev]; rfl,
        (k1.trans kt).mono⟩
    · -- `e` is valid.
      have hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip
          (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat)) = true := by
        rw [h26] at hz
        cases e : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r5) (s0.gpr .r6).toNat))
        · rw [e] at hz; simp at hz
        · rfl
      refine WP.seq (WP.mono (cck_stk hp b1) fun t2 ⟨⟨m2, a22, a23, a26⟩, k2⟩ => ?_)
      have b2 := b1.of_regs k2 m2
      have R : CckRegs s0 t2 := ⟨by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m14, ku.gpr _ (by decide)],
        by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m15, ku.gpr _ (by decide)],
        by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m18, ku.gpr _ (by decide)],
        by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m19, ku.gpr _ (by decide)],
        by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m20, ku.gpr _ (by decide)],
        by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m21, ku.gpr _ (by decide)], a22, a23, a26⟩
      -- `n`.
      refine WP.seq ?_
      unfold nCheck
      refine WP.seq (WP.mono (CrtValues.mv2_ok (s := t2) (d₁ := .r9) (d₂ := .r10) (a := .r14) (b := .r15) (by decide)
        (by decide) (by decide) (by decide)) fun t3 ⟨⟨u9, u10, m3⟩, k3⟩ => ?_)
      have b3 := b2.of_regs k3 m3
      have wn' : (s0.gpr .r3).toNat + kK s0 ≤ 2 ^ 64 := wn
      have hc : ∀ i < kK s0, (⟨s0.gpr .r3, kK s0⟩ : Region).Contains (off (s0.gpr .r3) i) 1 := fun i hi =>
        Offset.contains_base _ (by omega) (by omega)
      refine WP.mono (CrtValues.check_ok (N := s0.gpr .r3) (k := kK s0)
        (nb := Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0))
        (by rw [u9, R.r14]; simp [off]) (by rw [u10, R.r15]; exact CrtValues.ofNat_toNat64 _) hk hk'
        (len_bytes _ _ _)
        (fun i hi => ⟨_, List.mem_append_left _ (by rw [b3.rd, hrd]; simp), hc i hi⟩)
        (fun i hi => by
          rw [b3.frame _ (CrtValues.past_of_disjoint dn (hc i hi))]; simp [Spec.Rsa.bytesAt, off]))
        fun t4 ⟨hv, m4, k4⟩ => ?_
      have b4 := b3.of_regs k4 m4
      refine WP.ite (t4.gpr .r0 == 0) (eval_zero _ _) (fun hz0 => ?_) (fun hz0 => ?_)
      · have hmv := hv.mp (by simpa using hz0)
        have R4 := (R.of_keep k3).of_keep k4
        have h24' : t4.gpr .r24 = t1.gpr .r24 := by
          rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide)]
        rw [h24] at h24'
        refine WP.mono (cck_valid h b4 R4 h24' hmv hev) fun t ⟨bt, t3', kt⟩ => ⟨bt, t3', ?_⟩
        exact ((((k1.trans k2).trans k3).trans k4).trans kt).mono
      · have hmv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0)))
            (kK s0) = false := by
          cases e : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r3) (kK s0))) (kK s0)
          · rfl
          · have := hv.mpr e; simp [this] at hz0
        refine WP.mono (ret0_ok t4) fun t ⟨⟨t3', tm⟩, kt⟩ => ⟨b4.of_regs kt tm, by rw [t3', cckOk_of_n hmv]; rfl,
          ((((k1.trans k2).trans k3).trans k4).trans kt).mono⟩
  · -- The restore.
    refine WP.mono (restore_ok bt hp.wr hp.nowrap (by have := hp.zk; omega)) fun u' ⟨⟨u14, u15, u16, u17, u18,
      u19, u20, u21, u22, u23, u24, u26, u29, u30, u31, um⟩, ku'⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · have K := kt.trans ku'
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;>
        first | exact K.gpr _ (by decide) | with_reducible assumption
    · rw [ku'.sp, kt.sp]
    · rw [ku'.lr, kt.lr]
    · show (u'.gpr .r3).setWidth 32 = _
      rw [ku'.gpr _ (by decide), t3]
      change (BitVec.ofNat 64 (if cckOk s0 then 1 else 0)).setWidth 32 = if cckOk s0 then 1 else 0
      cases cckOk s0 <;> rfl

end VG.Proof.Rsa.PPC64LE.KeyCheck
