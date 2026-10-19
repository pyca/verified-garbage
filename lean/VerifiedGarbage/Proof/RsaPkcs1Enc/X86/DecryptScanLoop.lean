module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptScanStep
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Bytes
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Cast5.X86.Run

/-! # Scan every encoded-message byte and retain its first separator -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc (firstZero bytesAt_getD)
open VG.Proof.Cast5.X86 (wp_countdown)

def ScanPrefix (s0 : State) (p : BitVec 32) (k j : Nat) (s : State) : Prop :=
  Keeps [.eax, .edx, .ebp, .ebx, .edi, .esi, .ecx] s0 s ∧ s.mem = s0.mem ∧
  s.gpr .esi = p + BitVec.ofNat 32 (2 + j) ∧ s.gpr .edi = BitVec.ofNat 32 (2 + j) ∧
  s.gpr .ebx = BitVec.ofNat 32 (firstZero (Spec.Rsa.bytesAt s0.mem (byteAddr p) k) (2 + j)).isSome.toNat ∧
  s.gpr .ebp = BitVec.ofNat 32 ((firstZero (Spec.Rsa.bytesAt s0.mem (byteAddr p) k) (2 + j)).getD 0)

theorem scanLoop_ok {s : State} {p : BitVec 32} {k : Nat}
    (lower : 64 ≤ k) (upper : k ≤ 1024) (fit : p.toNat + k ≤ 2 ^ 32)
    (read : ∀ i < k, InRegions (s.rd ++ s.wr) (byteAddr p + BitVec.ofNat 64 i) 1)
    (src : s.gpr .esi = p + BitVec.ofNat 32 2) (index : s.gpr .edi = 2)
    (found : s.gpr .ebx = 0) (separator : s.gpr .ebp = 0)
    (count : s.gpr .ecx = BitVec.ofNat 32 (k - 2)) :
    WP isa scanLoop s fun t =>
      Keeps [.eax, .edx, .ebp, .ebx, .edi, .esi, .ecx] s t ∧ t.mem = s.mem ∧
      t.gpr .ebx = BitVec.ofNat 32 (firstZero (Spec.Rsa.bytesAt s.mem (byteAddr p) k) k).isSome.toNat ∧
      t.gpr .ebp = BitVec.ofNat 32 ((firstZero (Spec.Rsa.bytesAt s.mem (byteAddr p) k) k).getD 0) := by
  refine wp_countdown (cnt := .ecx) (by omega) (by omega) (ScanPrefix s p k) ?_ ?_ ?_ count
  · intro j hj t ⟨K, M, srcT, indexT, foundT, sepT⟩ _
    have pos : 2 + j < k := by omega
    have byte : t.mem (byteAddr (t.gpr .esi)) =
        (Spec.Rsa.bytesAt s.mem (byteAddr p) k).getD (2 + j) 1 := by
      rw [M, srcT, byteAddr_add (by omega), bytesAt_getD pos]
    refine WP.mono (scanBody_ok t (byteAddr (t.gpr .esi))
      (by change (t.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _; simp only [BitVec.add_zero]; rfl)
      (by rw [srcT, byteAddr_add (by omega), K.2.1, K.2.2]; exact read (2 + j) pos)) ?_
    rintro u ⟨Mu, sepU, foundU, indexU, srcU, countU, zfU, Ku⟩
    have step := Word32.scan_step (Spec.Rsa.bytesAt s.mem (byteAddr p) k) (i := 2 + j) (by omega)
    refine ⟨⟨K.trans Ku, Mu.trans M, ?_, ?_, ?_, ?_⟩, countU, zfU⟩
    · rw [srcU, srcT, BitVec.add_assoc]
      change p + (BitVec.ofNat 32 (2 + j) + BitVec.ofNat 32 1) = _
      rw [← BitVec.ofNat_add]
      simp only [Nat.add_assoc]

    · rw [indexU, indexT]
      change BitVec.ofNat 32 (2 + j) + BitVec.ofNat 32 1 = _
      rw [← BitVec.ofNat_add]
      simp only [Nat.add_assoc]

    · rw [foundU, foundT, byte]
      simpa only [zbit, Nat.add_assoc] using step.2
    · rw [sepU, sepT, foundT, indexT, byte]
      simpa only [zbit, Nat.add_assoc] using step.1
  · intro t ⟨K, M, _, _, F, S⟩
    rw [show 2 + (k - 2) = k by omega] at F S
    exact ⟨K, M, F, S⟩
  · refine ⟨Keeps.refl _ _, rfl, ?_, ?_, ?_, ?_⟩
    · exact src
    · exact index
    · change s.gpr .ebx = 0
      exact found
    · change s.gpr .ebp = 0
      exact separator

end VG.Proof.RsaPkcs1Enc.X86.Dec
