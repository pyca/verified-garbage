module

import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-! # Read a certified prime/inverse pair from the shared static -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.TrialTable32 VG.Proof.RsaKeyGen.TrialTable32

theorem table_words {m : Mem} {p : Addr} {i : Nat} (bound : i < 1024)
    (read : m.readW p 64 = BitVec.ofNat 64 (entry i)) :
    m.readW p 32 = BitVec.ofNat 32 (tabEntry i) ∧
    m.readW (p + BitVec.ofNat 64 4) 32 = inverse (BitVec.ofNat 32 (tabEntry i)) := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_lo, read, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (entry_bound bound), Nat.shiftRight_zero,
      entry_low bound, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
        have := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2; omega)]
  · apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Rc2.Word32.readW64_hi, read, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (entry_bound bound), Nat.shiftRight_eq_div_pow,
      entry_high bound, Nat.mod_eq_of_lt (inverse (BitVec.ofNat 32 (tabEntry i))).isLt]

end VG.Proof.RsaKeyGen.X86.Sieve
