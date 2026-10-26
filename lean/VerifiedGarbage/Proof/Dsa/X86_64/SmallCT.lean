module

public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Initializing one with a public workspace and secret modulus -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The count and index used to initialize a constant are public. -/
def SmallHeadW (L : Ws) (s : State) : Prop :=
  GoodW L s ∧ s.gpr .r12 = BitVec.ofNat 64 L.w ∧ s.gpr .rcx = 0

/-- Clearing an array and setting its low word has no value-dependent trace. -/
theorem smallW_ct {a : Nat} (ha : a < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .r8 (.mem (hdr (sArr a)))]) hc).isSome = true) :
    RelCT isa (Two GoodW) (Arithmetic.small a 1) (fun _ _ => True) := by
  unfold Arithmetic.small
  refine RelCT.seq (two_piece (Ψ := SmallHeadW) [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · rintro L s ⟨minv, hg⟩
    refine WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t =>
      t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rcx = 0 ∧ t.mem = s.mem) ?_ rfl)
      fun t ⟨⟨h12, hcx, hm⟩, hk⟩ =>
        ⟨⟨minv, ⟨hg.1.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, h12, hcx⟩
    xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.hdr.hw,
      hg.1.scr.ld (show 8 * sW + 8 ≤ L.Z by have := hdr_lt_slot L.w 8 (show sW < 32 by decide); have := hg.2; omega)]
  rw [setWord_eq]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r8 = off L.B (slot L.w a) ∧
    t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rcx = 0) [.rdi]
    (fun L s t hs ht => pins_goodW L s t hs.1 ht.1) hT ?_)
    (two_taint [.r8, .r12, .rcx] (pins_of (fun (L : Ws) r =>
      if r = .r8 then off L.B (slot L.w a) else if r = .r12 then BitVec.ofNat 64 L.w else 0)
      (by intro L s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide))
  rintro L s ⟨⟨minv, hg⟩, h12, hcx⟩
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off L.B (slot L.w a)) ?_ rfl)
    fun t ⟨h8, hk⟩ => ⟨h8, (hk.gpr (by decide)).trans h12, (hk.gpr (by decide)).trans hcx⟩
  xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.hdr.harr a ha,
    hg.1.scr.ld (show 8 * sArr a + 8 ≤ L.Z by
      have := hdr_lt_slot L.w 8 (show sArr a < 32 by unfold sArr; omega); have := hg.2; omega)]


end VG.Proof.Dsa.X86_64
