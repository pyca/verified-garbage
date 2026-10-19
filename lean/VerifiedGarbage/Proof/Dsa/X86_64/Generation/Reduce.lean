module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Subtract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Increment
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native remainder subtraction and increment implement p reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum
open VG.Proof.Dsa.Generation VG.Proof.MlKem.X86_64

theorem reduceRemainder_ok {s : State} {B : Addr} {Z w dst src rem x q : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hval : wv s.mem B (slot w src) w = x)
    (hrem : wv s.mem B (slot w rem) (w + 1) = x % (2 * q)) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.subtractRemainder dst src rem)
      (.block (Impl.Dsa.X86_64.Generation.incrementEven dst))) s fun t =>
      wv t.mem B (slot w dst) w = x + 1 - x % (2 * q) ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep [.r12, .r9, .rbp, .r8, .r10, .rsi, .rax, .r14, .rbx] s t := by
  have hmod := Nat.mod_le x (2 * q)
  have hbound : x < 2 ^ (64 * w) := hval ▸ wv_lt s.mem B (slot w src) w
  have hrem' : wv s.mem B (slot w rem) w = x % (2 * q) := by
    rw [wv_low_of_lt (Nat.le_succ w) (by rw [hrem]; omega), hrem]
  refine WP.seq (WP.mono (subtractRemainder_ok h hd hx hr hdx hdr
    (by rw [hval, hrem']; exact hmod)) fun u ⟨hu, ho, ku⟩ => ?_)
  rw [hval, hrem'] at hu
  have hf : Frm B [(slot w dst, 8 * w)] s.mem u.mem := Frm.of_outside ho (by simp)
  have hwu := h.congr hf
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot w dst (8 * w))
    ku (by decide)
  have he : wv u.mem B (slot w dst) w % 2 = 0 := by
    rw [hu]
    have hm := Nat.mod_add_div x (2 * q)
    have hv : x - x % (2 * q) = 2 * q * (x / (2 * q)) := by omega
    rw [hv]
    simp [Nat.mul_assoc]
  refine WP.mono (incrementEven_ok hwu hd he) fun t ⟨ht, hot, kt⟩ => ?_
  refine ⟨?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [ht, hu, pReduction_sub]
  · intro a ha
    rw [hot a (by have := h.w1; omega), ho a ha]

end VG.Proof.Dsa.X86_64.Generation
