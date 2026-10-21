module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Product
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Prime products use the shared paired native multiplication loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep S arr arr_disj)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def productScalars : List Nat := [128, 132, 136, 140, 144, 148, 152]

theorem primeProduct_ok {s : State} {B : Addr} {Z n out a b k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (ho : out < 32) (ha : a < 32) (hb : b < 32) (oa : out ≠ a) (ob : out ≠ b)
    (boundA : num s.mem B n a < 2 ^ (32 * k)) (boundB : num s.mem B n b < 2 ^ (32 * k)) :
    WP isa (primeProduct out a b) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [out] productScalars s.mem t.mem ∧
      num t.mem B n out = num s.mem B n a * num s.mem B n b ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have sa := arr_disj (w := n) oa
  have sb := arr_disj (w := n) ob
  have head := h.hdr_le
  have L : ProductGeometry Z k k (arr n out) (arr n a) (arr n b) := by
    refine ⟨⟨positive, positive, even, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals simp only [S, VG.Proof.Rsa.X86.Keys.arr, VG.Impl.Rsa.X86.Keys.hdr] at *
    all_goals omega
  have nk : n / 2 = k := by omega
  have L' : ProductGeometry Z (Width.prime.words n) (Width.prime.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr out).offset n) ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr a).offset n) ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr b).offset n) := by
    simpa only [Width.words, VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, nk] using L
  have A := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : k ≤ n) boundA
  have Bv := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : k ≤ n) boundB
  have bound : val32 s.mem B (arr n a) k * val32 s.mem B (arr n b) k < 2 ^ (32 * n) := by
    have lt := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_left (val32 s.mem B (arr n a) k) (Nat.le_of_lt (val32_lt s.mem B (arr n b) k)))
      (Nat.mul_lt_mul_of_pos_right (val32_lt s.mem B (arr n a) k) (Nat.two_pow_pos (32 * k)))
    rw [show 32 * n = 32 * k + 32 * k by omega, Nat.pow_add]
    exact lt
  refine WP.mono (product_ok h L') fun t ⟨ht, O, V, K⟩ => ?_
  simp only [Width.words, VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, Width.words, nk] at O V
  have value : val32 t.mem B (arr n out) (n + 2) =
      val32 s.mem B (arr n a) k * val32 s.mem B (arr n b) k := by
    simpa only [width, Nat.two_mul, Nat.add_assoc] using V
  refine ⟨ht, ?_, ?_, K⟩
  · intro x hx
    apply O x
    intro r hr
    simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h0 := hx (128, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h1 := hx (132, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h2 := hx (136, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h3 := hx (140, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h4 := hx (144, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h5 := hx (148, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      have h6 := hx (152, 4) (by simp [VG.Proof.Rsa.X86.Keys.ranges, productScalars])
      simp only at *
      omega
    · have H := hx (arr n out, S n) (by simp [VG.Proof.Rsa.X86.Keys.ranges])
      simpa only [S, width, Nat.two_mul, Nat.add_assoc] using H
  · have low := VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : n ≤ n + 2)
      (by rw [value]; exact bound)
    change val32 t.mem B (arr n out) n = _
    rw [low, value, A, Bv]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
