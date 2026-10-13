module

public import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant-time Montgomery constants for padded DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The count and index used to initialize a constant are public. -/
def SmallHead (L : Lay) (s : State) : Prop :=
  GoodL L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x13 = 0

/-- Clearing an array and setting its low word has no value-dependent trace. -/
theorem small_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x8 (sArr a), movi .x7 0]) hc).isSome = true) :
    RelCT isa (Two GoodL) (Arithmetic.small a 1) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHead) [.x0] pins_good (by taint_decide) ?_) ?_
  · intro L s hg
    refine WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
      fun t ⟨⟨h12, hcx, hm⟩, hk⟩ =>
        ⟨⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩, h12, hcx⟩
    brun [hg.1.x0, hdr_enc (show sW < 32 by decide), hg.1.hdr.hw,
      hg.1.scr.ld (show 8 * sW + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega)]
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x8 = off L.B (slot L.w a) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.gpr .x7 = 0) [.x0]
    (fun L s t hs ht => pins_good L s t hs.1 ht.1) hT ?_)
    (two_taint [.x8, .x12, .x13, .x7] (fun L s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide))
  intro L s ⟨hg, h12, hcx⟩
  refine WP.mono (WP.keep [.x8, .x7] (Q := fun t => t.gpr .x8 = off L.B (slot L.w a) ∧ t.gpr .x7 = 0) ?_ rfl rfl rfl)
    fun t ⟨⟨h8, h7⟩, hk⟩ => ⟨h8, (hk.gpr .x12 (by decide)).trans h12, (hk.gpr .x13 (by decide)).trans hcx, h7⟩
  brun [hg.1.x0, hdr_enc (show sArr a < 32 by unfold sArr; omega), hg.1.hdr.harr a ha,
    hg.1.scr.ld (show 8 * sArr a + 8 ≤ L.Z by
      have := hdr_lt_slot L.w 8 (show sArr a < 32 by unfold sArr; omega); have := hg.2; omega)]

theorem small256_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x8 (sArr a), movi .x7 0]) hc).isSome = true) :
    RelCT isa (Two GoodL) (Arithmetic.small a 256) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHead) [.x0] pins_good (by taint_decide) ?_) ?_
  · intro L s hg
    refine WP.mono (WP.keep [.x12, .x9, .x13] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
      fun t ⟨⟨h12, hcx, hm⟩, hk⟩ =>
        ⟨⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩, h12, hcx⟩
    brun [hg.1.x0, hdr_enc (show sW < 32 by decide), hg.1.hdr.hw,
      hg.1.scr.ld (show 8 * sW + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega)]
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x8 = off L.B (slot L.w a) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = 0 ∧ t.gpr .x7 = 0) [.x0]
    (fun L s t hs ht => pins_good L s t hs.1 ht.1) hT ?_)
    (two_taint [.x8, .x12, .x13, .x7] (fun L s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide))
  intro L s ⟨hg, h12, hcx⟩
  refine WP.mono (WP.keep [.x8, .x7] (Q := fun t => t.gpr .x8 = off L.B (slot L.w a) ∧ t.gpr .x7 = 0) ?_ rfl rfl rfl)
    fun t ⟨⟨h8, h7⟩, hk⟩ => ⟨h8, (hk.gpr .x12 (by decide)).trans h12, (hk.gpr .x13 (by decide)).trans hcx, h7⟩
  brun [hg.1.x0, hdr_enc (show sArr a < 32 by unfold sArr; omega), hg.1.hdr.harr a ha,
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
    s.gpr .x13 = BitVec.ofNat 64 (128 * p.layout.w)) [.x0]
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

theorem constants_ct : RelCT isa (Two SetupPre)
    Arithmetic.constants (fun _ _ => True) := by
  unfold Arithmetic.constants
  refine RelCT.seq (two_post (Ψ := SetupPre)
    (two_map (fun p : ProductPublic => p.layout) (fun p _ h => ⟨h.1.good, p.fits⟩)
      (small_ct (a := aOne) (by decide) (by taint_decide)))
    (fun _ _ h => WP.mono (setup_one (by decide) (by decide) h) fun _ ht => ht.1)) doublingR2_ct

end VG.Proof.Dsa.AArch64
