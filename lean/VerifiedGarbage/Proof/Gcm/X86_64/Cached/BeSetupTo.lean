module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.BeSetup
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The setup of the counters added to as bytes, out of place (`readyTo_be`) -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.StitchZH (beSetup)
open VG.Proof.Gcm.X86_64 (beFour)
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode cb pp pR oR in_sub)
open VG.Proof.Gcm.X86_64.StitchZ (AInv R10 IdxOk idxR BeConsts sixteen)
open VG.Proof.Gcm.X86_64.StitchZTo (ReadyTo AInvTo)
open VG.Spec.Gcm (Block)

/-- `StitchZH.ready_be`, out of place. -/
theorem readyTo_be {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) {off : Nat} (hx : IdxOk off [oR s₀, pR s₀] s₀)
    {P : Nat → Nat → Block} {s : State} (hR : ReadyTo s₀ P s) :
    WP isa (.block (beSetup off)) s fun t => ReadyTo s₀ P t true ∧ HKeep s t := by
  have hwp := hp.wrap_p
  have hr11 : s.gpr .r11 = pp s₀ := hR.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  have hsp : s.gpr .rsp = s₀.gpr .rsp := hR.gpr .rsp (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hi, hI, hd⟩ := hx
  have c896 : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 896) (128 / 8) := Offset.contains_base _ (by omega) (by omega)
  have c912 : (pR s₀).Contains (pp s₀ + BitVec.ofNat 64 912) (128 / 8) := Offset.contains_base _ (by omega) (by omega)
  have fr : Frame [pR s₀] s.mem
      ((s.mem.writeW (pp s₀ + BitVec.ofNat 64 896) beFour).writeW (pp s₀ + BitVec.ofNat 64 912) sixteen) :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c896).writeW (List.mem_singleton_self _) _ c912
  have hi₁ : ((s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW (s.gpr .r11 + BitVec.ofNat 64 912)
      sixteen).readW (s.gpr .rsp + BitVec.ofNat 64 off) 32 = (cb s₀).extractLsb' 0 32 := by
    rw [hr11, hsp, fr.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd _ (by simp)) (show 32 / 8 < 2 ^ 64 by decide),
      hR.a.frame.readW (Region.contains_self _ _) hd (show 32 / 8 < 2 ^ 64 by decide)]
    exact hi
  refine WP.mono (WP.hkeep (is := beSetup off) rfl (StitchZH.beSetup_ok off s
    (by rw [hr11, hR.a.wr]; exact in_sub hp.p_in (by omega)) (by rw [hr11, hR.a.wr]; exact in_sub hp.p_in (by omega))
    (by rw [hsp, hR.a.rd, hR.a.wr]; exact hI) hi₁)) fun t ⟨⟨g10, m, g, z, rd, wr⟩, hh⟩ => ⟨?_, hh⟩
  rw [hr11] at m
  have ft : Frame [pR s₀] s.mem t.mem := by rw [m]; exact fr
  have hA : AInvTo s₀ 0 t true :=
    ⟨hR.a.le, fun l hl => by rw [z _ (by decide) l hl]; exact hR.a.ctr l hl,
      fun l hl => by rw [z _ (by decide) l hl]; exact hR.a.msk l hl,
      fun l hl => by rw [z _ (by decide) l hl]; exact hR.a.inc l hl,
      by rw [g _ (by decide)]; exact hR.a.rdi, by rw [g _ (by decide)]; exact hR.a.rsi,
      ⟨by rw [g10]; simp only [idxR, BitVec.ofNat_eq_ofNat, BitVec.add_zero],
        by rw [m]; exact ⟨by
          rw [Mem.readW_writeW_sep (Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by decide)]
          exact Mem.readW_writeW_self _ _ 16 _ (by decide), Mem.readW_writeW_self _ _ 16 _ (by decide)⟩⟩,
      by rw [g _ (by decide)]; exact hR.a.r8,
      hR.a.frame.trans (ft.sub fun r hr => ⟨pR s₀, by simp, fun a ha => by
        simp only [List.mem_singleton] at hr; subst hr; exact ha⟩),
      fun k hk => absurd hk (Nat.not_lt_zero _),
      by rw [rd]; exact hR.a.rd, by rw [wr]; exact hR.a.wr⟩
  have keepLow : ∀ o, o + 16 ≤ 896 →
      t.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 = s.mem.readW (pp s₀ + BitVec.ofNat 64 o) 128 := fun o ho => by
    rw [m, Mem.readW_writeW_sep (Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by decide)]
  exact ⟨hA, by rw [g _ (by decide)]; exact hR.rdx, by rw [g _ (by decide)]; exact hR.rax,
    fun r h1 h2 h3 h4 => by rw [g r h4]; exact hR.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepLow _ (by omega)]; exact hR.pw k hk l hl,
    fun l hl => by rw [z _ (by decide) l hl]; exact hR.m1 l hl,
    by rw [z _ (by decide) 0 (by decide)]; exact hR.y,
    fun l h1 h4 => by rw [z _ (by decide) l h4]; exact hR.y1 l h1 h4⟩

end VG.Proof.Gcm.X86_64.StitchZHTo
