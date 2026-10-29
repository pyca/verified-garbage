module
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Initializing one in a public workspace, whatever its `-m⁻¹` -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- The count and index used to initialize a constant are public. -/
def SmallHeadW (L : Ws) (s : State) : Prop :=
  GoodW L s ∧ s.gpr .x12 = BitVec.ofNat 64 L.w ∧ s.gpr .x13 = BitVec.ofNat 64 0

/-- `x12 := w`, `x9 := 1`, `x13 := 0` before `setWord`. -/
theorem smallHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [ldh .x12 sW, movi .x9 1, movi .x13 0]) s fun u =>
      (u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x9 = BitVec.ofNat 64 1 ∧
        u.gpr .x13 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) ∧ Keep [.x9, .x12, .x13] s u := by
  refine WP.keep [.x9, .x12, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  brun [hg.x0, hdr_enc (show sW < 32 by decide), hg.hdr.hw,
    hg.scr.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)]

/-- Clearing an array and setting its low word has no value-dependent trace. -/
theorem smallW_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block [ldh .x8 (sArr a), movi .x7 0]) hc).isSome = true) :
    RelCT isa (Two GoodW) (Arithmetic.small a 1) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHeadW) [.x0] pins_goodW (by taint_decide) ?_) ?_
  · rintro L s ⟨minv, hg⟩
    exact WP.mono (smallHead_ok hg.1 hg.2) fun t ⟨⟨h12, _, h13, hm⟩, hk⟩ =>
      ⟨⟨minv, ⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩,
        h12, h13⟩
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x8 = off L.B (slot L.w a) ∧
    t.gpr .x12 = BitVec.ofNat 64 L.w ∧ t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.gpr .x7 = 0) [.x0]
    (fun L s t hs ht => pins_goodW L s t hs.1 ht.1) hT ?_)
    (two_taint [.x8, .x12, .x13, .x7] (pins_of (fun (L : Ws) r =>
      if r = .x8 then off L.B (slot L.w a) else if r = .x12 then BitVec.ofNat 64 L.w else 0)
      (by intro L s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2.1
          · exact h.2.2.2)) (by taint_decide))
  rintro L s ⟨h, h12, h13⟩
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  refine WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off L.B (slot L.w a) ∧ t.gpr .x7 = 0)
    ?_ rfl rfl rfl)
    fun t ⟨⟨h8, h7⟩, hk⟩ => ⟨h8, (hk.gpr .x12 (by decide)).trans h12, (hk.gpr .x13 (by decide)).trans h13, h7⟩
  brun [hg.x0, hdr_enc (sArr_lt ha), hl (sArr a) (sArr_lt ha), hg.hdr.harr a ha]

end VG.Proof.Dsa.AArch64
