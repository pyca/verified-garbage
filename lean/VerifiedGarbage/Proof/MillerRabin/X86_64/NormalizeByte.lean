module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
import VerifiedGarbage.Proof.Framework.Omega

/-! # Only bookkeeping bytes change during normalization -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.Proof.Bignum VG.Impl.Bignum
open VG.Impl.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate

theorem normalized_byte (m : Mem) (B x : Addr) (w : Nat)
    (hx : ∀ j ∈ bookkeeping.map (·.1), ofs B x < 8 * j ∨ 8 * j + 8 ≤ ofs B x) :
    normalizedMem m B w x = m x := by
  have hk : ∀ j ∈ bookkeeping.map (·.1), j < 32 := by
    simp only [bookkeeping, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    rintro j (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide
  have h : ∀ j ∈ bookkeeping.map (·.1), ∀ (m' : Mem) (v : BitVec 64),
      (m'.writeW (off B (8 * j)) v) x = m' x := fun j hj m' v =>
    writeW_outside m' B v (by have := hk j hj; omega_arith) x (hx j hj)
  simp only [normalizedMem, zeroWords, List.foldl_cons, List.foldl_nil]
  rw [h kI (by simp [bookkeeping]), h kChecks (by simp [bookkeeping]), h kRandLen (by simp [bookkeeping]),
    h kRand (by simp [bookkeeping]), h kUsedP (by simp [bookkeeping]), h kOut (by simp [bookkeeping]),
    h kUsed (by simp [bookkeeping]), h kLen (by simp [bookkeeping])]

end VG.Proof.MillerRabin.X86_64
