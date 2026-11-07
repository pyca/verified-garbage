module

public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
public import VerifiedGarbage.Proof.Ecdsa.Contract
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.Framework.Sig

/-! # A concrete witness for the comb signing contract -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86

/-- The tables at `0x100000`, over `satMem`. The bound, `151552`, is `8 * p256W.length`
(`p256W_length`) as a literal: as the product, the kernel would evaluate the tables' length
in every definitional check of the bound. -/
@[irreducible] def combSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 151552 then constMem 0x100000 p256W a else satMem a

theorem combSatMem_held : ∀ i < p256W.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 := by
  intro i hi
  have hl := p256W_length
  have hm : combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 p256W).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold combSatMem
    rw [e, ite_eq_left (show 8 * i + j < 151552 by omega)]
  exact hm.trans (constMem_held 0x100000 p256W (by omega) i hi)

def combSatState : State := { satState with
  mem := combSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x100000, 151552⟩]
  syms := fun _ => 0x100000 }

theorem combSat_arg (j : Nat) (hj : j < 5) : arg combSatState j = arg satState j := by
  have outside : ∀ j < 5, ∀ b < 4,
      151552 ≤ (argAddr satState j + BitVec.ofNat 64 b - 0x100000).toNat := by decide
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change combSatMem (argAddr satState j + BitVec.ofNat 64 b) = satMem (argAddr satState j + BitVec.ofNat 64 b)
  unfold combSatMem
  rw [ite_eq_right (by have := outside j hj b (by omega); omega)]

end VG.Proof.Ecdsa.X86
