module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.CrtExp

/-! # Equality masks for supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem widthMask_ok {s : State} {n value : Nat}
    (hn : n < 2 ^ 31) (hv : value < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 value) :
    WP isa (.block (Checks.widthMask n)) s fun t =>
      t.gpr .rax = mask (decide (value = n)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn64 : n < 2 ^ 64 := by omega
  have he : (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0 ↔ value = n := by
    change (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0#64 ↔ value = n
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hn64] using h'
    · intro h; rw [h]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = mask (decide (value = n)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold Checks.widthMask
  xrun [h8, sx_ofNat hn, show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl]
  change mask (decide ((BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n).toNat < 1)) = _
  rw [mask_lt_one, decide_eq_decide.mpr he]

end VG.Proof.Dsa.X86_64
