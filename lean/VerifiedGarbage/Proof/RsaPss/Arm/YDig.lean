module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Spec.RsaPss

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS on ARMv7: `Y` cleared, and the digest after 8 zeros

`yDig_vp`: `yDig` clears `Y` and copies the digest (argument `j`, `hLen`
bytes of a buffer the body only reads) after its first 8 bytes, as both
signing and verification begin `M' = 0x00 ×8 ‖ mHash ‖ salt`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.RsaPkcs1Sig.Arm (argOff)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- `Y`'s bytes after its first `o`, zero. -/
abbrev YZ (scr : BitVec 32) (o : Nat) (m : Mem) : Prop := ∀ i < 2048 - o, m (sa scr (oY + o + i)) = 0

theorem yDig_vp (hg : Geo L scr) {j : Nat} {dgP : BitVec 32} (hj21 : j < 21) (hj : j < L.argv.length)
    (hv : L.argv.getD j 0 = dgP) (hD : RBuf L dgP h.D)
    (hsepD : ∀ o n, o + n ≤ oRsa → Region.Disjoint ⟨State.addr dgP, h.D⟩ (sR scr o n))
    {dl : State → List Byte} (hdl : ∀ σ, (dl σ).length = h.D)
    (hro : ∀ σ s, Ctx L scr σ s → ∀ i < h.D, s.mem (byteAt dgP i) = (dl σ).getD i 0)
    {X : State → Mem → Prop} (hX : ∀ σ m m', X σ m → Frame [sR scr oY 2048] m m' → X σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem)
      (yDig h.H j)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧
        ∀ i < 2048, s.mem (sa scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ dl σ).getD i 0) := by
  have hDl : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have hD0 := h.D_pos
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  have hoff : argOff frameBytes j < 4096 := by unfold argOff frameBytes; split <;> omega
  have hX' : ∀ σ m m' o n, X σ m → oY ≤ o → o + n ≤ oY + 2048 → Frame [sR scr o n] m m' → X σ m' :=
    fun σ m m' o n hx h₁ h₂ hf => hX σ m m' hx (Frame.sub hf fun r hr => ⟨sR scr oY 2048, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ h₁ h₂⟩)
  show VP _ (.seq (.block clrY) (.seq Impl.Bignum.Arm.maskBytes (.seq (.block (cpDig h.H j))
    Impl.Bignum.Arm.copyBytes))) _
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oY ∧
      s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 2048)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hx⟩ => ?_)
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ ∀ i < 2048, s.mem (byteAt (scr + BitVec.ofNat 32 oY) i) = 0)
      (zero_vp (hg.wbuf (o := oY) (n := 2048) (by decide) (by decide)) (by decide)
        fun σ m m' hx hf => hX σ m m' hx (by rwa [hg.addr (by decide)] at hf))
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ (X σ s.mem ∧ (∀ i < 8, s.mem (sa scr (oY + i)) = 0) ∧
        YZ scr (8 + h.D) s.mem) ∧ s.gpr .r0 = scr + BitVec.ofNat 32 (oY + 8) ∧ s.gpr .r1 = dgP ∧
        s.gpr .lr = BitVec.ofNat 32 h.D ∧ ∀ i < h.D, s.mem (byteAt dgP i) = (dl σ).getD i 0)
      (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hx, hz⟩ => ?_)
      ((copy_vp (hg.wbuf (o := oY + 8) (n := h.D) (by pomega) hD0) hD
        (by rw [hg.addr (by pomega)]; exact hsepD _ _ (by pomega)) hD0 (f := fun σ i => (dl σ).getD i 0)
        (Inv := fun σ m => X σ m ∧ (∀ i < 8, m (sa scr (oY + i)) = 0) ∧ YZ scr (8 + h.D) m)
        fun σ m m' ⟨hx, h8, hz⟩ hf => ?_).mono (fun _ _ h => h) fun σ s ⟨hc, ⟨hx, h8, hz⟩, hy⟩ =>
          ⟨hc, hx, fun i hi => ?_⟩)))
  · have hw : WP isa (.block clrY) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oY ∧ t.gpr .r2 = 0 ∧ t.gpr .lr = BitVec.ofNat 32 2048 := by
      prun [clrY, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oY < 2 ^ 16 by decide), movw_val (show 2048 < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2, lr⟩ => ⟨hc.regs rd wr sp m, m ▸ hx, r0, r2, lr⟩
  · have a := ok.addrB (d := argOff frameBytes j) (by
      have := Lay.argOff_lt (L := L) (j := j) (by have := ok.nargs; omega); rw [hg.F] at this ⊢; omega)
    have rd : InRegions (s.rd ++ s.wr) (L.fr (argOff frameBytes j)) 4 := by
      rw [hc.st.rd, hc.st.wr]; have := hc.st.ok.arg_read hj; rwa [Lay.argA, hg.F] at this
    have v : s.mem.readW (L.fr (argOff frameBytes j)) 32 = dgP := by
      have := hc.st.arg hj; rwa [Lay.argA, hg.F, hv] at this
    have hw : WP isa (.block (cpDig h.H j)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oY + 8) ∧ t.gpr .r1 = dgP ∧
        t.gpr .lr = BitVec.ofNat 32 h.D := by
      prun [cpDig, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a, rd, v, hoff,
        movw_val (show oY + 8 < 2 ^ 16 by decide), movw_val (show dig h.H < 2 ^ 16 by show h.D < 2 ^ 16; omega)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨hc.regs rd wr sp m, ⟨m ▸ hx, fun i hi => ?_, fun i hi => ?_⟩,
      r0, r1, lr, fun i hi => m ▸ hro σ s hc i hi⟩
    · rw [m, ← hg.byteAt_scr (by pomega)]; exact hz i (by omega)
    · rw [m, show oY + (8 + h.D) + i = oY + (8 + h.D + i) by omega, ← hg.byteAt_scr (by pomega)]
      exact hz _ (by omega)
  · rw [hg.addr (by pomega)] at hf
    refine ⟨hX' σ m m' _ _ hx (by pomega) (by pomega) hf, sbytes_keep hf (fun r hr => ?_) (by pomega) h8,
      sbytes_keep hf (fun r hr => ?_) (by pomega) hz⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)
  · rw [RsaPss.getD_app]
    simp only [RsaPss.zeros_length]
    by_cases h1 : i < 8
    · rw [ite_eq_left h1, RsaPss.zeros_getD]; exact h8 i h1
    rw [ite_eq_right h1]
    by_cases h2 : i < 8 + h.D
    · rw [← hy (i - 8) (by omega), hg.byteAt_scr (by pomega), show oY + 8 + (i - 8) = oY + i by omega]
    · rw [getD_ge (by rw [hdl]; omega), show oY + i = oY + (8 + h.D) + (i - (8 + h.D)) by omega]
      exact hz _ (by omega)

end VG.Proof.RsaPss.Arm
