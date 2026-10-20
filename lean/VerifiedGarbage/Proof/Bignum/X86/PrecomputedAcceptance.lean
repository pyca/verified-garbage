module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Bignum.X86.PublicSetup
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
public import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.P256Red
public import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Mont.X86.PowerLoop
public import VerifiedGarbage.Proof.Mont.X86.PowerTwo
public import VerifiedGarbage.Proof.Mont.X86.RedRow
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.RowW
public import VerifiedGarbage.Proof.Mont.X86.SparseShift
public import VerifiedGarbage.Proof.Mont.X86.Step
public import VerifiedGarbage.Proof.Mont.X86.WordOps


/-! # Boolean meaning of the packed-key acceptance mask -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

def precomputedAccepted (m r : Nat) : Bool := decide (1 < m ∧ r < m ∧ m % 2 = 1)

theorem precomputedAcceptance {m r : Nat} {low : BitVec 32} (L : m % 2 ^ 32 = low.toNat) :
    (if r < m then BitVec.allOnes 32 else 0) &&&
      (if 1 < m then BitVec.allOnes 32 else 0) &&& (low &&& 1) =
      BitVec.ofNat 32 (precomputedAccepted m r).toNat := by
  have parity : (low &&& 1).toNat = m % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega
  by_cases R : r < m <;> by_cases M : 1 < m
  · simp only [R, M, ite_true, BitVec.and_allOnes, BitVec.allOnes_and]
    apply BitVec.eq_of_toNat_eq
    rw [parity]
    unfold precomputedAccepted
    by_cases O : m % 2 = 1 <;> simp [M, R, O] <;> omega
  · simp [precomputedAccepted, R, M]
  · simp [precomputedAccepted, R, M]
  · simp [precomputedAccepted, R, M]

end VG.Proof.Bignum.X86.PublicContext
