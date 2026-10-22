module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Omega

/-! Bounds for calls sharing the dynamic Montgomery context. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Dynamic

theorem montgomery_offsets {n o a b : Nat} (hn : 0 < n) (hn' : n ≤ 48)
    (ho : o < 9) (ha : a < 9) (hb : b < 9) (ho0 : o ≠ 0) :
    VG.Proof.Bignum.X86.RtCall.Offs montgomeryBytes n (slot n 0) 0
      montgomeryScratch (slot n o) (slot n a) (slot n b) := by
  have bo := slot_bound (n := n) ho
  have ba := slot_bound (n := n) ha
  have bb := slot_bound (n := n) hb
  have so := slot_le (n := n) (i := 0) (j := o) (by omega)
  have oh := slot_header n o
  simp only [contextBytes, slot, stride] at bo ba bb so oh ⊢
  constructor <;>
    (try simp only [montgomeryBytes, montgomeryScratch, VG.Spec.Rsa.MontMul.scratchBytes,
      VG.Spec.Rsa.MontMul.Apart]) <;> omega

end VG.Proof.Dsa.X86.Generation
