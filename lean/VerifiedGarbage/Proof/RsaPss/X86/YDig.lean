module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: `Y` with the digest

`yDig_vp`: `yDig` clears `Y` and copies the digest (argument `j`, `hLen`
bytes of a buffer the body only reads) after its first 8 bytes, as both
signing and verification begin `M' = 0x00 ×8 ‖ mHash ‖ salt`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPkcs1Sig.X86 (argOff)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- `Y`'s bytes after its first `o`, zero. -/
abbrev YZ (scr : BitVec 32) (o : Nat) (m : Mem) : Prop := ∀ i < 2048 - o, m (sa scr (oY + o + i)) = 0

theorem yDig_vp (hg : Geo L scr) {j : Nat} (hcert : TaintOk [.esp, .ebp] (.block (cpDig h.H j)))
    (hj : j < L.argv.length) {dgP : BitVec 32} (hv : L.argv.getD j 0 = dgP) (hD : RBuf L dgP h.D)
    (hsepD : ∀ o n, o + n ≤ oRsa → Region.Disjoint ⟨dgP.setWidth 64, h.D⟩ (sR scr o n))
    {dl : State → List Byte} (hdl : ∀ σ, (dl σ).length = h.D)
    (hro : ∀ σ s, Ctx L scr σ s → ∀ i < h.D, s.mem (byteAt dgP i) = (dl σ).getD i 0)
    {X : State → Mem → Prop} (hX : ∀ σ m m', X σ m → Frame [sR scr oY 2048] m m' → X σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem)
      (yDig h.H j)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧
        ∀ i < 2048, s.mem (sa scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ dl σ).getD i 0) := by
  have hDl : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega
  have eD : h.H.D = h.D := rfl
  have hD0 := h.D_pos
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  have hX' : ∀ σ m m' o n, X σ m → oY ≤ o → o + n ≤ oY + 2048 → Frame [sR scr o n] m m' → X σ m' :=
    fun σ m m' o n hx h₁ h₂ hf => hX σ m m' hx (Frame.sub hf fun r hr => ⟨sR scr oY 2048, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ h₁ h₂⟩)
  show VP _ (.seq (.block (clrArgs oY 2048)) (.seq zeroLoop (.seq (.block (cpDig h.H j))
    Impl.Bignum.X86.copyBytes))) _
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .esi = scr + BitVec.ofNat 32 oY ∧
      s.gpr .ecx = BitVec.ofNat 32 2048 ∧ s.gpr .eax = 0)
    (VP.taint [.esp, .ebp] clrY2048_taint (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx⟩ => ?_)
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ ∀ i < 2048, s.mem (byteAt (scr + BitVec.ofNat 32 oY) i) = 0)
      (zero_vp (hg.wbuf (o := oY) (n := 2048) (by decide) (by decide)) (by decide)
        fun σ m m' hx hf => hX σ m m' hx (by rwa [hg.scrA (by decide)] at hf))
    (VP.seq (G := fun σ s => Ctx L scr σ s ∧ (X σ s.mem ∧ (∀ i < 8, s.mem (sa scr (oY + i)) = 0) ∧
        YZ scr (8 + h.D) s.mem) ∧ s.gpr .ebx = scr + BitVec.ofNat 32 (oY + 8) ∧ s.gpr .esi = dgP ∧
        s.gpr .ecx = BitVec.ofNat 32 h.D ∧ ∀ i < h.D, s.mem (byteAt dgP i) = (dl σ).getD i 0)
      (VP.taint [.esp, .ebp] hcert (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hx, hz⟩ => ?_)
      ((copy_vp (hg.wbuf (o := oY + 8) (n := h.D) (by pomega) hD0) hD
        (by rw [hg.scrA (by pomega)]; exact hsepD _ _ (by pomega)) hD0 (f := fun σ i => (dl σ).getD i 0)
        (Inv := fun σ m => X σ m ∧ (∀ i < 8, m (sa scr (oY + i)) = 0) ∧ YZ scr (8 + h.D) m)
        fun σ m m' ⟨hx, h8, hz⟩ hf => ?_).mono (fun _ _ h => h) fun σ s ⟨hc, ⟨hx, h8, hz⟩, hy⟩ =>
          ⟨hc, hx, fun i hi => ?_⟩)))
  · simp only [clrArgs, atS, addi, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => wp_movi fun t4 u4 => WP.block_nil ?_
    refine ⟨(((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide)
      (by decide)).upd u4 (by decide) (by decide), by rw [u4.mem, u3.mem, u2.mem, u1.mem]; exact hx, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u4.other, u3.other, u2.gpr, u1.gpr, hc.ebp]
    · rw [u4.other _ (by decide), u3.gpr]
    · rw [u4.gpr]; rfl
  · simp only [cpDig, atS, addi, ld, mi, Impl.RsaPkcs1Sig.X86.stk, List.cons_append, List.nil_append]
    refine hc.wp_arg hg hj (by decide) (by decide) fun t1 c1 u1 => wp_mov fun t2 u2 => wp_addi fun t3 u3 =>
      wp_movi fun t4 u4 => WP.block_nil ?_
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨((c1.upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)).upd u4 (by decide) (by decide),
      ⟨m4 ▸ hx, fun i hi => ?_, fun i hi => ?_⟩, ?_, ?_, ?_, fun i hi => m4 ▸ hro σ s hc i hi⟩
    · rw [m4, ← hg.byteAt_scr (by pomega)]; exact hz i (by omega)
    · rw [m4, show oY + (8 + h.D) + i = oY + (8 + h.D + i) by omega, ← hg.byteAt_scr (by pomega)]
      exact hz _ (by omega)
    · simp (disch := decide) only [u4.other, u3.gpr, u2.gpr, u1.other, hc.ebp]
    · simp (disch := decide) only [u4.other, u3.other, u2.other, u1.gpr, hv]
    · rw [u4.gpr]
  · rw [hg.scrA (by pomega)] at hf
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

end VG.Proof.RsaPss.X86
