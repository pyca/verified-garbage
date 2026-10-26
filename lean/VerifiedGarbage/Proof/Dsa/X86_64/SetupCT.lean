module

import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupChoice
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.CrtMath

/-! # Constant-time Montgomery constants for padded DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The count and index used to initialize a constant are public. -/
def SmallHead (L : Lay) (s : State) : Prop :=
  GoodL L s ∧ s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rcx = 0

/-- Clearing an array and setting its low word has no value-dependent trace. -/
theorem small_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .r8 (.mem (hdr (sArr a)))]) hc).isSome = true) :
    RelCT isa (Two GoodL) (Arithmetic.small a 1) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHead) [.rdi] pins_good (by taint_decide) ?_) ?_
  · intro L s hg
    refine WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t =>
      t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rcx = 0 ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨⟨h12, hcx, hm⟩, hk⟩ =>
        ⟨⟨⟨hg.1.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, h12, hcx⟩
    xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.hdr.hw,
      hg.1.scr.ld (show 8 * sW + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega)]
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r8 = off L.B (slot L.w a) ∧
    t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rcx = 0) [.rdi]
    (fun L s t hs ht => pins_good L s t hs.1 ht.1) hT ?_)
    (two_taint [.r8, .r12, .rcx] (pins_of (fun (L : Lay) r =>
      if r = .r8 then off L.B (slot L.w a) else if r = .r12 then BitVec.ofNat 64 L.w else 0)
      (by intro L s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide))
  intro L s ⟨hg, h12, hcx⟩
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off L.B (slot L.w a)) ?_ rfl)
    fun t ⟨h8, hk⟩ => ⟨h8, (hk.gpr (by decide)).trans h12, (hk.gpr (by decide)).trans hcx⟩
  xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.hdr.harr a ha,
    hg.1.scr.ld (show 8 * sArr a + 8 ≤ L.Z by
      have := hdr_lt_slot L.w 8 (show sArr a < 32 by unfold sArr; omega); have := hg.2; omega)]

/-- Bounds and the public modulus needed by constants setup. -/
def SetupPre (p : ProductPublic) (s : State) : Prop :=
  ModCtx s p.layout.B p.layout.Z p.layout.w p.layout.minv p.modulus ∧
    p.layout.w ≤ 48 ∧ 1 < p.modulus ∧ p.modulus % 2 = 1

/-- Initializing one array retains the setup precondition. -/
theorem setup_one {a : Nat} (ha : a < 8) (han : a ≠ aN)
    {p : ProductPublic} {s : State} (h : SetupPre p s) :
    WP isa (Arithmetic.small a 1) s fun t =>
      SetupPre p t ∧ wv t.mem p.layout.B (slot p.layout.w a) p.layout.w = 1 := by
  refine WP.mono (one_ok h.1.good p.fits p.lower p.upper ha) fun t ⟨ht, hv, hf, _⟩ => ?_
  have hz : p.layout.B.toNat + slot p.layout.w 8 ≤ 2 ^ 64 := by
    have := h.1.good.scr.nowrap; have := p.fits; omega
  have hnot : aN ∉ [a] := by simpa using Ne.symm han
  refine ⟨⟨⟨ht, (hf.wv_of_not_mem (by decide) hnot hz).trans h.1.modulus, ?_⟩, h.2⟩, hv⟩
  rw [hf.word0_of_not_mem (by decide) hnot hz (by have := p.lower; omega)]
  exact h.1.inverse

/-- Setup's doubling loop has a public count even when the modulus is padded. -/
theorem doublingR2_ct : RelCT isa (Two SetupPre) Arithmetic.doublingR2 (fun _ _ => True) := by
  unfold Arithmetic.doublingR2 seqs
  refine RelCT.seq (two_post (Ψ := fun p s => SetupPre p s ∧
    wv s.mem p.layout.B (slot p.layout.w aR2) p.layout.w = 1)
    (two_map (fun p : ProductPublic => p.layout) (fun p _ h => ⟨h.1.good, p.fits⟩)
      (small_ct (a := aR2) (by decide) (by taint_decide)))
    (fun _ _ h => setup_one (by decide) (by decide) h)) ?_
  refine RelCT.seq (two_piece (Ψ := fun p s => SetupPre p s ∧
    wv s.mem p.layout.B (slot p.layout.w aR2) p.layout.w = 1 ∧
    s.gpr .rcx = BitVec.ofNat 64 (128 * p.layout.w)) [.rdi]
    (fun p s t hs ht => pins_good p.layout s t ⟨hs.1.1.good, p.fits⟩ ⟨ht.1.1.good, p.fits⟩)
    (by taint_decide) ?_) ?_
  · intro p s ⟨h, hv⟩
    refine WP.mono (r2Count_ok h.1.good p.fits) fun t ⟨ht, hcx, hm, _⟩ => ?_
    exact ⟨⟨⟨ht, hm ▸ h.1.modulus, hm ▸ h.1.inverse⟩, h.2⟩, hm ▸ hv, hcx⟩
  exact (two_map (fun p : ProductPublic => (⟨p.layout, 128 * p.layout.w⟩ : DblPub))
    (fun p s ⟨h, hv, hcx⟩ => ⟨⟨h.1.good, p.fits⟩, p.lower, p.upper,
      by change 1 ≤ 128 * p.layout.w; have := p.lower; omega,
      by change 128 * p.layout.w < 2 ^ 31; have := h.2.1; omega, hcx,
      by rw [hv, h.1.modulus]; exact h.2.2.1⟩)
    (doubles_ct (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

/-- Registers whose values determine the setup test's address. -/
def SetupRegs (p : ProductPublic) (s : State) : Prop :=
  SetupPre p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.layout.w ∧
    s.gpr .r10 = off p.layout.B (slot p.layout.w aN)

/-- The branch depends only on the public modulus and storage width. -/
def SetupTested (p : ProductPublic) (s : State) : Prop :=
  SetupRegs p s ∧ s.zf = some (decide (p.modulus / 2 ^ (64 * (p.layout.w - 1)) = 0))

theorem constants_ct (M : Mont) : RelCT isa (Two SetupPre)
    (Arithmetic.constants M.mm) (fun _ _ => True) := by
  unfold Arithmetic.constants
  refine RelCT.seq (two_post (Ψ := SetupPre)
    (two_map (fun p : ProductPublic => p.layout) (fun p _ h => ⟨h.1.good, p.fits⟩)
      (small_ct (a := aOne) (by decide) (by taint_decide)))
    (fun _ _ h => WP.mono (setup_one (by decide) (by decide) h) fun _ ht => ht.1)) ?_
  refine RelCT.seq (two_piece (Ψ := SetupRegs) [.rdi]
    (fun p s t hs ht => pins_good p.layout s t ⟨hs.1.good, p.fits⟩ ⟨ht.1.good, p.fits⟩)
    (by taint_decide) ?_) ?_
  · intro p s h
    exact WP.mono (setupBases_ok h.1.good p.fits) fun t ⟨hg, h12, h10, hm, _⟩ =>
      ⟨⟨⟨hg, hm ▸ h.1.modulus, hm ▸ h.1.inverse⟩, h.2⟩, h12, h10⟩
  refine RelCT.seq (two_piece (Ψ := SetupTested) [.r10, .r12] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.2.2.trans ht.2.2.symm
    · exact hs.2.1.trans ht.2.1.symm
  · intro p s ⟨h, h12, h10⟩
    refine WP.mono (setupTest_ok h.1.good p.fits p.lower h.1.modulus h12 h10)
      fun t ⟨hz, hm, hk⟩ => ⟨⟨?_, (hk.gpr (by decide)).trans h12, (hk.gpr (by decide)).trans h10⟩, hz⟩
    exact ⟨⟨⟨h.1.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.1.good.rdi,
      hm ▸ h.1.good.hdr⟩, hm ▸ h.1.modulus, hm ▸ h.1.inverse⟩, h.2⟩
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · exact two_map id (fun _ _ ⟨⟨⟨h, _, _⟩, _⟩, _⟩ => h) doublingR2_ct
  · refine two_map (fun p : ProductPublic => (⟨p.layout, p.modulus⟩ : R2Pub)) ?_ (R2w.choice_ct M)
    rintro p s ⟨⟨⟨h, h12, h10⟩, hz⟩, hc⟩
    simp only [eval, hz, Option.some.injEq, decide_eq_false_iff_not] at hc
    refine ⟨⟨h.1.good, p.fits⟩, p.lower, ?_, h.1.modulus, h.1.inverse, h12, h10, h.2.2.2, ?_⟩
    · change p.layout.w < 2 ^ 30
      have := h.2.1; omega
    · change 2 ^ (64 * (p.layout.w - 1)) ≤ p.modulus
      by_contra hl
      exact hc (Nat.div_eq_of_lt (by omega))

end VG.Proof.Dsa.X86_64
