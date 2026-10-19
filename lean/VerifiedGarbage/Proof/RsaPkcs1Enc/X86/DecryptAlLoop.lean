module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptAlStep
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Bytes
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Cast5.X86.Run

/-! # Fold all 128 alternative-length candidates without secret branches -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc
open VG.Proof.Cast5.X86 (wp_countdown)

def alFold (k : Nat) (CL : List Byte) (j : Nat) : Nat := (List.range j).foldl (altStep k CL) 0

def AlPrefix (s0 : State) (p : BitVec 32) (k j : Nat) (s : State) : Prop :=
  Keeps [.eax, .edx, .edi, .esi, .ecx] s0 s ∧ s.mem = s0.mem ∧
  s.gpr .esi = p + BitVec.ofNat 32 (2 * j) ∧
  s.gpr .edi = BitVec.ofNat 32 (alFold k (Spec.Rsa.bytesAt s0.mem (byteAddr p) 256) j)

theorem alLoop_ok {s : State} {p : BitVec 32} {k : Nat}
    (lower : 64 ≤ k) (upper : k ≤ 1024) (fit : p.toNat + 256 ≤ 2 ^ 32)
    (read : ∀ i < 256, InRegions (s.rd ++ s.wr) (byteAddr p + BitVec.ofNat 64 i) 1)
    (src : s.gpr .esi = p) (selected : s.gpr .edi = 0)
    (mask : s.gpr .ebx = BitVec.ofNat 32 (bitMask (k - 11)))
    (limit : s.gpr .ebp = BitVec.ofNat 32 (k - 11)) (count : s.gpr .ecx = BitVec.ofNat 32 128) :
    WP isa alLoop s fun t => Keeps [.eax, .edx, .edi, .esi, .ecx] s t ∧ t.mem = s.mem ∧
      t.gpr .edi = BitVec.ofNat 32 (Spec.RsaPkcs1Enc.altLength k (Spec.Rsa.bytesAt s.mem (byteAddr p) 256)) := by
  refine wp_countdown (cnt := .ecx) (by decide : 128 < 2 ^ 32) (by decide : 0 < 128)
    (AlPrefix s p k) ?_ ?_ ?_ count
  · intro i hi t ⟨K, M, srcT, selectedT⟩ _
    have ptr0 : t.ea ⟨.esi, 0⟩ = byteAddr p + BitVec.ofNat 64 (2 * i) := by
      change byteAddr (t.gpr .esi + BitVec.ofNat 32 0) = _
      rw [BitVec.add_zero, srcT, byteAddr_add (by omega)]
    have ptr1 : t.ea ⟨.esi, 1⟩ = (byteAddr p + BitVec.ofNat 64 (2 * i)) + 1 := by
      change byteAddr (t.gpr .esi + BitVec.ofNat 32 1) = _
      rw [srcT, BitVec.add_assoc, ← BitVec.ofNat_add, byteAddr_add (by omega), ← Offset.add_add]
      rfl
    refine WP.mono (alBody_ok (byteAddr p + BitVec.ofNat 64 (2 * i)) lower upper ptr0 ptr1
      (by rw [K.2.1, K.2.2]; exact read (2 * i) (by omega))
      (by rw [K.2.1, K.2.2]; exact read (2 * i + 1) (by omega))
      ((K.1 .ebx (by decide)).trans mask) ((K.1 .ebp (by decide)).trans limit)) ?_
    rintro u ⟨Mu, Ku, selectedU, srcU, countU, zfU⟩
    refine ⟨⟨K.trans Ku, Mu.trans M, ?_, ?_⟩, countU, zfU⟩
    · rw [srcU, srcT, BitVec.add_assoc]
      change p + (BitVec.ofNat 32 (2 * i) + BitVec.ofNat 32 2) = _
      rw [← BitVec.ofNat_add]
      congr 2
      omega
    · have byte0 : t.mem (byteAddr p + BitVec.ofNat 64 (2 * i)) =
          (Spec.Rsa.bytesAt s.mem (byteAddr p) 256).getD (2 * i) 0 := by
        rw [M, bytesAt_getD (by omega : 2 * i < 256)]
      have byte1 : t.mem ((byteAddr p + BitVec.ofNat 64 (2 * i)) + 1) =
          (Spec.Rsa.bytesAt s.mem (byteAddr p) 256).getD (2 * i + 1) 0 := by
        rw [M, bytesAt_getD (by omega : 2 * i + 1 < 256), ← Offset.add_add]
        rfl
      rw [selectedU, byte0, byte1, selectedT]
      unfold alFold
      rw [foldl_range_succ, altStep_candidate]
      split <;> rfl
  · intro t ⟨K, M, _, result⟩
    exact ⟨K, M, result⟩
  · exact ⟨Keeps.refl _ _, rfl, by simpa only [Nat.mul_zero, BitVec.ofNat_zero, BitVec.add_zero] using src, selected⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
