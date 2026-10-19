module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native p-width branch matches the specification's guard -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Bignum.X86_64

theorem candidateWidth_ok {s : State} {B pp : Addr} {Z w len p : Nat}
    (h : Ws s B Z w) (hptr : word s.mem B 160 = pp)
    (hlen : 0 < len) (hbound : p < 256 ^ len)
    (hbytes : Spec.Rsa.bytesAt s.mem pp len = Spec.Dsa.encodeBE len p)
    (hrd : InRegions (s.rd ++ s.wr) pp 1) :
    WP isa (.block Impl.Dsa.X86_64.Generation.candidateWidth) s fun t =>
      t.cf = some (decide (p < 2 ^ (8 * len - 1))) ∧ t.mem = s.mem ∧ Keep [.rsi, .rax] s t := by
  have hfirst : s.mem pp = (Spec.Dsa.encodeBE len p).getD 0 0 := by
    rw [← hbytes]
    simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hlen]
  have he := VG.Proof.Dsa.Generation.candidate_firstByte hlen hbound
  rw [← hfirst] at he
  refine WP.mono (WP.keep [.rsi, .rax] (Q := fun t =>
      t.cf = some (decide (p < 2 ^ (8 * len - 1))) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.candidateWidth, State.ea, hdr, hdrOff, at0, h.rdi,
      show BitVec.ofInt 64 0 = 0#64 by rfl, BitVec.add_zero,
      h.scr.ld (d := 160) (by have := h.h256; omega), hptr, hrd]
    simp only [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (s.mem pp).isLt (by decide : 2 ^ 8 < 2 ^ 64))]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact he) rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
