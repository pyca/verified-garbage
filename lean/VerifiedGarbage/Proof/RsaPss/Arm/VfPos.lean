module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfScan
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.VfScan
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the scan's result

The scan's registers (`scanSet_vp`); then `acc` takes in that `DB`'s first
nonzero byte is `0x01` and, if a salt length is expected, that the salt after
it has that length (`acc2`), and its index goes to its slot (`pos_vp`); then
the flags of `any_salt_len = 0` (`anySet_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- What the scan keeps. -/
abbrev Kd (P : EP) (τ : State) (m : Mem) : Prop :=
  Ka h P τ m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- The scan's registers. -/
theorem scanSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (U0 h P) (.block scanSet)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun τ s ⟨hc, hk, hd, hh⟩ => ?_
  have hw : WP isa (.block scanSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = BitVec.ofNat 32 0 ∧
      t.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧ t.gpr .r4 = BitVec.ofNat 32 0 ∧ t.gpr .r5 = BitVec.ofNat 32 0 ∧
      t.gpr .r6 = BitVec.ofNat 32 0 - 1 ∧ t.gpr .r7 = BitVec.ofNat 32 0 := by
    prun [scanSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.2.2.1.2.1,
      hk.2.2.1.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show 0 < 2 ^ 16 by decide),
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r4, r5, r6, r7⟩ =>
    ⟨hc.regs rd wr sp m, m ▸ ⟨hk, hd, hh⟩, hk.2.1, ⟨by rw [r0, Nat.add_zero], r1, by rw [lr, Nat.sub_zero], ?_, ?_, ?_, r7⟩⟩
  · rw [r4]; simp only [pzJ, Nat.not_lt_zero, ite_false]
  · rw [r5]; simp only [vzJ, Nat.not_lt_zero, ite_false]; rfl
  · rw [r6]; simp only [nfJ, Nat.not_lt_zero, ite_false]; decide

/-- `[any_salt_len ≠ 0]`. -/
abbrev anyW (P : EP) : BitVec 32 := if P.any = 0 then 0 else 1

/-- The index of `DB`'s first nonzero byte, 0 if none. -/
abbrev pzF (P : EP) (τ : State) : Nat := pzJ h P τ (dbN h P)

/-- `acc` after the scan. -/
abbrev acc2 (P : EP) (τ : State) : BitVec 32 :=
  (accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32) ||| nfJ h P τ (dbN h P) >>> 31)) |||
    ((BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^ BitVec.ofNat 32 P.slt) &&& (anyW P - 1))

/-- What the paths after the scan keep. -/
abbrev K2 (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    (∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
    m.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzF h P τ) ∧
    m.readW ((P.lay h.D).fr sAcc) 32 = acc2 h P τ

theorem posChk_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r12])
    (.block posChk) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `acc` and `pos` to their slots. -/
theorem pos_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s)
      (.seq (.block posSet) (.block posChk))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P) ∧
      s.gpr .r4 = BitVec.ofNat 32 (pzF h P τ) ∧ s.gpr .r5 = (vzJ h P τ (dbN h P)).setWidth 32 ∧
      s.gpr .r6 = nfJ h P τ (dbN h P) ∧
      s.gpr .r1 = accW P τ ∧ s.gpr .r2 = BitVec.ofNat 32 (dbN h P) ∧ s.gpr .r3 = BitVec.ofNat 32 P.slt ∧
      s.gpr .r8 = anyW P ∧ s.gpr .r12 = P.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hf, hs⟩ => ?_)
    (VP.taint _ posChk_cert (fun _ _ _ _ h₁ h₂ r hr => ?_)
      fun τ s ⟨⟨hc, hk, hf⟩, r4, r5, r6, r1, r2, r3, r8, r12⟩ => ?_)
  · have hi := hk.1.1
    obtain ⟨a7, ra7, va7⟩ := argAt hi hc.st (j := 7) (by decide)
    replace va7 : s.mem.readW ((P.lay h.D).fr (arg 7)) 32 = BitVec.ofNat 32 P.slt := va7
    have hw : WP isa (.block posSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r4 = BitVec.ofNat 32 (pzF h P τ) ∧ t.gpr .r5 = (vzJ h P τ (dbN h P)).setWidth 32 ∧
        t.gpr .r6 = nfJ h P τ (dbN h P) ∧
        t.gpr .r1 = accW P τ ∧ t.gpr .r2 = BitVec.ofNat 32 (dbN h P) ∧ t.gpr .r3 = BitVec.ofNat 32 P.slt ∧
        t.gpr .r8 = anyW P ∧ t.gpr .r12 = P.B := by
      prun [posSet, sp0, ld, hc.st.sp, a7, ra7, va7, arg_lt, hc.aFr hg, hc.rFr hg, hk.1.2.2.2, hk.1.2.2.1.2.2.1,
        hk.1.2.2.1.2.2.2, hs.r4, hs.r5, hs.r6]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t4, t5, t6, t1, t2, t3, t8, t12⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hk, hf⟩, t4, t5, t6, t1, t2, t3, t8, t12⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2]
  · have hi := hk.1.1
    have hw : WP isa (.block posChk) s fun t =>
        t.mem = (s.mem.writeW ((P.lay h.D).fr sPos) (BitVec.ofNat 32 (pzF h P τ))).writeW ((P.lay h.D).fr sAcc)
          (acc2 h P τ) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [posChk, st, r1, r2, r3, r4, r5, r6, r8, r12, slotAt hi (d := sAcc) (by decide),
        slotAt hi (d := sPos) (by decide), hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide),
        hc.st.inFr (d := sPos) (n := 4) (by show sPos + 4 ≤ frameBytes; decide), dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR (P.lay h.D) sPos, slotR (P.lay h.D) sAcc] s.mem t.mem := by
      rw [m]
      exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
    obtain ⟨σ', ok⟩ := hg.ok
    have kk : ∀ d, d + 4 ≤ frameBytes → (d + 4 ≤ sAcc ∨ sPos + 4 ≤ d) →
        t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 := fun d hd hd' => by
      rw [m, slot_ww _ _ hd (by decide) (by unfold sAcc sPos at hd'; unfold sAcc; omega),
        slot_ww _ _ hd (by decide) (by unfold sAcc sPos at hd'; unfold sPos; omega)]
    have kb : ∀ o, o + 1 ≤ oRsa → t.mem (sa P.scr o) = s.mem (sa P.scr o) := fun o ho =>
      fr _ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hg.slot ok (o := o) (n := 1) (by omega) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
        · exact (hg.slot ok (o := o) (n := 1) (by omega) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
    obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
    have e1 : oEm = 1024 := rfl
    have e2 : oRsa = 8192 := rfl
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, hf,
      ⟨by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.1, by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.1,
        by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.2.1,
        by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.2.2⟩,
      fun i hi' => by rw [kb _ (by omega)]; exact hk.2.1 i hi',
      fun i hi' => by rw [kb _ (by omega)]; exact hk.2.2 i hi', ?_, by rw [m, Mem.readW_writeW_self32]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-- The flags of `any_salt_len = 0`. -/
theorem anySet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) (.block anySet)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.z = decide (P.any = 0)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk⟩ => ?_
  have hw : WP isa (.block anySet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (P.any = 0) := by
    prun [anySet, sp0, ld, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.2.2.1.2.2.2]
    by_cases e : P.any = 0#32 <;> simp [e]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, z⟩

end VG.Proof.RsaPss.Arm.Vf
