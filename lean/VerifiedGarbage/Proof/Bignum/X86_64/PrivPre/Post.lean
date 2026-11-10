module

public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_private_precompute` on x86-64: `pre`'s words

`pre`'s words, from the four parts `out` writes, each word and-ed with the
mask (`wordsAt_out`): the four values' words if the mask is set, and zeros
otherwise.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.Proof.Bignum

theorem wordsAt_append (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.wordsAt m p (a + b) =
      Spec.Rsa.wordsAt m p a ++ Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [Offset.add_add, Nat.mul_add]

/-- A part of `pre`, word by word. -/
theorem seg_eq {m : Mem} {D : Addr} {e n : Nat} {f : Nat → BitVec 64}
    (h : ∀ i < n, word m D (e + 8 * i) = f i) :
    Spec.Rsa.wordsAt m (D + BitVec.ofNat 64 e) n = (List.range n).map f := by
  refine List.map_congr_left fun i hi => ?_
  rw [Offset.add_add]
  exact h i (List.mem_range.mp hi)

theorem and_mask (x : BitVec 64) (c : Bool) : x &&& mask c = if c then x else 0 := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes]; rfl

/-- `pre`'s words, from its four parts. -/
theorem wordsAt_out {m : Mem} {D : Addr} {w wp wq : Nat} {M : Bool} {VN VR VP VQ : Nat}
    (hN : ∀ i < w, word m D (8 * i) = BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M)
    (hR : ∀ i < w, word m D (8 * w + 8 * i) = BitVec.ofNat 64 (VR / 2 ^ (64 * i)) &&& mask M)
    (hP : ∀ i < wp, word m D (16 * w + 8 * i) = BitVec.ofNat 64 (VP / 2 ^ (64 * i)) &&& mask M)
    (hQ : ∀ i < wq, word m D (16 * w + 8 * wp + 8 * i) = BitVec.ofNat 64 (VQ / 2 ^ (64 * i)) &&& mask M) :
    Spec.Rsa.wordsAt m D (2 * w + wp + wq) = if M then
      Spec.Rsa.toWords VN w ++ Spec.Rsa.toWords VR w ++ Spec.Rsa.toWords VP wp ++ Spec.Rsa.toWords VQ wq
    else List.replicate (2 * w + wp + wq) 0 := by
  rw [show 2 * w + wp + wq = w + w + wp + wq by omega, wordsAt_append, wordsAt_append, wordsAt_append]
  have h0 : Spec.Rsa.wordsAt m D w = (List.range w).map fun i => BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M := by
    have := seg_eq (m := m) (D := D) (e := 0) (n := w) (f := fun i => BitVec.ofNat 64 (VN / 2 ^ (64 * i)) &&& mask M)
      (fun i hi => by rw [Nat.zero_add]; exact hN i hi)
    simpa using this
  have eP : 8 * (w + w) = 16 * w := by omega
  have eQ : 8 * (w + w + wp) = 16 * w + 8 * wp := by omega
  rw [eP, eQ]
  rw [h0, seg_eq (f := fun i => BitVec.ofNat 64 (VR / 2 ^ (64 * i)) &&& mask M) hR,
    seg_eq (f := fun i => BitVec.ofNat 64 (VP / 2 ^ (64 * i)) &&& mask M) hP,
    seg_eq (f := fun i => BitVec.ofNat 64 (VQ / 2 ^ (64 * i)) &&& mask M) hQ]
  cases M
  · simp only [and_mask, Bool.false_eq_true, ↓reduceIte, List.map_const', List.length_range,
      List.replicate_append_replicate]
  · simp only [and_mask, ↓reduceIte, Spec.Rsa.toWords]

end VG.Proof.Bignum.X86_64.PrivPre
