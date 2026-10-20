module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # The prepared round never changes its caller's saved stack words -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.RsaKeyGen.X86_64.Candidate

theorem core_ranges_fit {B : Addr} {Z w : Nat} (h : MrDims B Z w) :
    ∀ r ∈ coreRanges w, r.1 + r.2 ≤ Z := by
  intro r hr
  obtain hr | hr := List.mem_append.mp hr
  · have he := tabRanges_lt w r hr
    have hm := VG.Proof.Bignum.slot_mono w (by decide : aE ≤ aRm1)
    have hx := h.x
    omega_arith
  · exact Nat.le_trans (expRanges_low w r hr) h.z

theorem core_frame {B : Addr} {Z w : Nat} {m m' : Mem} (h : MrDims B Z w)
    (hf : Frm B (coreRanges w) m m') : Frame [⟨B, Z⟩] m m' := by
  intro x hx
  have hn := hx ⟨B, Z⟩ (List.mem_singleton_self _)
  have hz : Z ≤ ofs B x := by
    simp only [Region.Contains, ofs] at hn ⊢
    omega_arith
  exact hf x fun r hr => Or.inr (Nat.le_trans (core_ranges_fit h r hr) hz)

end VG.Proof.MillerRabin.X86_64
