module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Public constants do not change the native RSA arithmetic schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.RsaKeyGen.X86.Key

theorem constant_words_check (o x : Nat) : ∀ k,
    taint.checkBlock (zeroTaint true) ((List.range k).flatMap fun j =>
      if x >>> (32 * j) % 2 ^ 32 = 0 then []
      else [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * j)))), .store (sc (o + 4 * j)) .eax]) =
        some (zeroTaint true)
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      VG.Proof.Mont.X86.Dynamic.check_append (M := isa) taint (zeroTaint true),
      constant_words_check o x k]
    change taint.checkBlock (zeroTaint true)
      (if x >>> (32 * k) % 2 ^ 32 = 0 then []
       else [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * k)))), .store (sc (o + 4 * k)) .eax]) = _
    split
    · rfl
    · rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (zeroTaint true) = true from rfl)]
      change taint.checkBlock (zeroTaint true) [.mov .eax (.imm 0), .store (sc 0) .eax] = _
      rfl

theorem constArray_public (n j x : Nat) : KeyPublic (constArray n j x) := by
  let out := VG.Impl.Rsa.X86.Keys.slot n j
  let hint : VG.Taint.Hint VG.X86.Taint.T := .seq (zeroTaint true) (zerosHint true) (.block [])
  have words : VG.Taint.check taint (zeroTaint true)
      (.block ((List.range (n + 2)).flatMap fun i =>
        if x >>> (32 * i) % 2 ^ 32 = 0 then []
        else [.mov .eax (.imm (BitVec.ofNat 32 (x >>> (32 * i)))), .store (sc (out + 4 * i)) .eax]))
      (.block []) = some (zeroTaint true) := constant_words_check out x (n + 2)
  refine ⟨hint, zeroTaint true, ?_, by decide +kernel⟩
  exact exponent_check_seq taint (zeros_check true out (n + 2)) (by decide +kernel) words

end VG.Proof.RsaKeyGen.X86.Key
