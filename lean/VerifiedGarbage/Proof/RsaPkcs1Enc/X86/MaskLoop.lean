module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.MaskStep
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopy

/-! # Mask the entire ciphertext while preserving the return bit -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (writeBytes_out bytesAt_take_succ)
open VG.Impl.RsaPkcs1Enc.X86
open VG.Proof.Cast5.X86 (wp_countdown)

def masked (s : State) (k : Nat) : List Byte :=
  (Spec.Rsa.bytesAt s.mem (byteAddr (s.gpr .esi)) k).map fun b => b &&& (s.gpr .edx).setWidth 8

def MaskedPrefix (s0 : State) (k i : Nat) (s : State) : Prop :=
  Keeps [.eax, .esi, .ecx] s0 s ∧
  s.mem = writeBytes s0.mem (byteAddr (s0.gpr .esi)) ((masked s0 k).take i) ∧
  s.gpr .esi = s0.gpr .esi + BitVec.ofNat 32 i

theorem maskLoop_ok {s : State} {k : Nat} (positive : 0 < k) (bound : k ≤ 1024)
    (fit : (s.gpr .esi).toNat + k ≤ 2 ^ 32)
    (write : ∀ i < k, InRegions s.wr (byteAddr (s.gpr .esi + BitVec.ofNat 32 i)) 1)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa maskLoop s fun t => Keeps [.eax, .esi, .ecx] s t ∧
      t.mem = writeBytes s.mem (byteAddr (s.gpr .esi)) (masked s k) := by
  have length : (masked s k).length = k := by simp [masked, bytesAt_length]
  refine wp_countdown (cnt := .ecx) (by omega) positive (MaskedPrefix s k) ?_ ?_ ?_ count
  · intro i hi t ⟨kt, mt, pt⟩ _
    have current : t.mem (byteAddr (t.gpr .esi)) =
        s.mem (byteAddr (s.gpr .esi) + BitVec.ofNat 64 i) := by
      rw [mt, pt, byteAddr_add (by omega)]
      apply writeBytes_out _ _ _ _ i ?_ (by simp only [List.length_take, length]; omega)
      intro j hj eq
      have same := (BitVec.add_right_inj _).mp eq
      have nums := congrArg BitVec.toNat same
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at nums
      omega
    have writable : InRegions t.wr (byteAddr (t.gpr .esi)) 1 := by rw [pt, kt.2.2]; exact write i hi
    refine WP.mono (maskStep_ok t (byteAddr (t.gpr .esi))
      (by change (t.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _; simp only [BitVec.add_zero]; rfl)
      writable) ?_
    rintro u ⟨mu, pu, cu, zu, ku⟩
    refine ⟨⟨kt.trans ku, ?_, ?_⟩, cu, zu⟩
    · rw [mu, current, kt.1 .edx (by decide), mt, pt, byteAddr_add (by omega)]
      have next : (masked s k).take (i + 1) = (masked s k).take i ++
          [s.mem (byteAddr (s.gpr .esi) + BitVec.ofNat 64 i) &&& (s.gpr .edx).setWidth 8] := by
        simp only [masked, ← List.map_take]
        rw [bytesAt_take_succ _ _ hi, List.map_append]
        rfl
      rw [next, writeBytes_snoc _ _ _ _ (by simp [length]; omega)]
      simp only [List.length_take, length, Nat.min_eq_left (by omega : i ≤ k)]
    · rw [pu, pt, BitVec.add_assoc]
      change s.gpr .esi + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
      rw [← BitVec.ofNat_add]
  · intro t ht
    unfold MaskedPrefix at ht
    rw [List.take_of_length_le (by rw [length])] at ht
    exact ⟨ht.1, ht.2.1⟩
  · exact ⟨Keeps.refl _ _, by simp [writeBytes_nil], by simp⟩

end VG.Proof.RsaPkcs1Enc.X86
