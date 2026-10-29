module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Close
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
/-! # Native remainder subtraction and increment implement p reduction -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Subtract.lean`, which only this module imported.
section

/-! Reuse RSA's array subtraction for the candidate's division remainder. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

theorem subtractRemainder_ok {s : State} {B : Addr} {Z w dst src rem : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hle : wv s.mem B (slot w rem) w ≤ wv s.mem B (slot w src) w) :
    WP isa (seqs (subA dst src rem)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w src) w - wv s.mem B (slot w rem) w ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (subA_ok h hd hx hr (.inr hdx) hdr) fun t ⟨hv, ho, _, _, _, hk⟩ => ?_
  refine ⟨?_, ho, hk.mono (by decide)⟩
  have hxlt := wv_lt s.mem B (slot w src) w
  have holt := wv_lt t.mem B (slot w dst) w
  cases hc : (!t.c) <;> rw [hc] at hv <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Increment.lean`, which only this module imported.
section

/-! The even candidate difference can be incremented without carry propagation. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

private theorem low_word {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w = (word m B e).toNat + 2 ^ 64 * wv m B (e + 8) (w - 1) := by
  have h := wv_add m B e 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at h
  simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul, Nat.mul_one] using h

theorem incrementEven_ok {s : State} {B : Addr} {Z w dst : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (heven : wv s.mem B (slot w dst) w % 2 = 0) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.incrementEven dst)) s fun t =>
      wv t.mem B (slot w dst) w = wv s.mem B (slot w dst) w + 1 ∧
      Outside B (slot w dst) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have sd := h.sl hd
  have hw : 1 ≤ w := by have := h.w1; omega
  unfold Impl.Dsa.AArch64.Generation.incrementEven
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, hm₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok dst .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11)
    fun s₂ ⟨⟨h16, hm₂, _⟩, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem =
    s.mem.writeW (off B (slot w dst)) (word s.mem B (slot w dst) + 1))
    (by brun [h16, hs₂.ld (d := slot w dst) (by omega), hs₂.st (d := slot w dst) (by omega), hm₂, hm₁]; rfl)
    rfl rfl rfl) fun t ⟨hm, k₃⟩ => ?_
  have ho : Outside B (slot w dst) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega)
  refine ⟨?_, ho, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have e₀ := low_word (m := s.mem) (B := B) (e := slot w dst) hw
  have e₁ := low_word (m := t.mem) (B := B) (e := slot w dst) hw
  have hu := ho.wv (d := slot w dst + 8) (k := w - 1) (Or.inr (by omega)) (by omega)
  have hv : word t.mem B (slot w dst) = word s.mem B (slot w dst) + 1 := by
    rw [hm, word_writeW_self]
  have hlo := (word s.mem B (slot w dst)).isLt
  rw [e₀] at heven
  have hb : (word s.mem B (slot w dst)).toNat + 1 < 2 ^ 64 := by omega
  rw [e₁, hu, hv, BitVec.toNat_add, Nat.mod_eq_of_lt (by simpa using hb), e₀]
  change (word s.mem B (slot w dst)).toNat + 1 + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) =
    (word s.mem B (slot w dst)).toNat + 2 ^ 64 * wv s.mem B (slot w dst + 8) (w - 1) + 1
  omega_using []

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.Generation VG.Proof.MlKem.AArch64

private theorem low_of_lt {m : Mem} {B : Addr} {e v w : Nat} (hv : v ≤ w)
    (h : wv m B e w < 2 ^ (64 * v)) : wv m B e v = wv m B e w := by
  have e1 := wv_add m B e v (w - v)
  rw [show v + (w - v) = w by omega] at e1
  have hz : wv m B (e + 8 * v) (w - v) = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (e + 8 * v) (w - v)) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * wv m B (e + 8 * v) (w - v) := Nat.le_mul_of_pos_right _ h0
      omega
  rw [e1, hz]; simp

theorem reduceRemainder_ok {s : State} {B : Addr} {Z w dst src rem x q : Nat}
    (h : Ws s B Z w) (hd : dst < 16) (hx : src < 16) (hr : rem < 16)
    (hdx : dst ≠ src) (hdr : dst ≠ rem)
    (hval : wv s.mem B (slot w src) w = x)
    (hrem : wv s.mem B (slot w rem) (w + 1) = x % (2 * q)) :
    WP isa (.seq (seqs (subA dst src rem))
      (.block (Impl.Dsa.AArch64.Generation.incrementEven dst))) s fun t =>
      wv t.mem B (slot w dst) w = x + 1 - x % (2 * q) ∧
      Outside B (slot w dst) (8 * w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hmod := Nat.mod_le x (2 * q)
  have hbound : x < 2 ^ (64 * w) := hval ▸ wv_lt s.mem B (slot w src) w
  have hrem' : wv s.mem B (slot w rem) w = x % (2 * q) := by
    rw [low_of_lt (Nat.le_succ w) (by rw [hrem]; omega), hrem]
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

end VG.Proof.Dsa.AArch64.Generation
