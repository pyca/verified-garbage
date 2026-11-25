module

public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SHA-3 on AArch64: absorbing whole blocks

The contract of the functions that absorb all of the data's whole blocks at
once (`Callee.blocks`), and what a block's words XORed into the lanes are.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Blocks

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt keccakF xorBytes bytesAt rates)
open VG.Proof.Sha3 (laneAddr)

/-! ## Words -/

/-- The first `n` words at `p` XORed into the state. -/
def xorWords (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => A[i] ^^^ if i.val < n then m.readW (laneAddr p i.val) 64 else 0

theorem xorWords_get (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n j : Nat) (hj : j < 25) :
    (xorWords A m p n)[j] = A[j] ^^^ if j < n then m.readW (laneAddr p j) 64 else 0 := by
  simp only [xorWords, Vector.getElem_ofFn, Fin.getElem_fin]

theorem xorWords_get! (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) {j : Nat} (hj : j < 25) :
    (xorWords A m p n)[j]! = A[j]! ^^^ if j < n then m.readW (laneAddr p j) 64 else 0 := by
  rw [getElem!_eq _ hj, xorWords_get _ _ _ _ _ hj, getElem!_eq _ hj]

theorem xorWords_zero (A : Spec.Sha3.State) (m : Mem) (p : Addr) : xorWords A m p 0 = A := by
  apply Vector.ext
  intro i hi
  rw [xorWords_get _ _ _ _ _ hi]; simp

theorem xorWords_eq (A : Spec.Sha3.State) (m : Mem) (p : Addr) (n : Nat) :
    xorWords A m p n = xorBytes A (bytesAt m p (8 * n)) := by
  refine ext_bytes fun j hj => ?_
  rw [byteOf_xorBytes _ _ hj, byteOf_eq' _ hj, byteOf_eq' _ hj, xorWords_get _ _ _ _ _ (by omega), BitVec.extractLsb'_xor]
  congr 1
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : j / 8 < n
  · rw [ite_eq_left h, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [Mem.readW, BitVec.setWidth_eq, Mem.extractLsb'_read _ _ (show j % 8 < 64 / 8 by omega), BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.div_add_mod]
  · rw [ite_eq_right h, List.getElem?_eq_none (by simp; omega)]
    simp

/-! ## The contract -/

/-- `n` blocks of `r` bytes at `p` absorbed. -/
def absorbed (r : Nat) (m : Mem) (p : Addr) (A : Spec.Sha3.State) (n : Nat) : Spec.Sha3.State :=
  (List.range n).foldl (fun S i => keccakF (xorBytes S (bytesAt m (p + BitVec.ofNat 64 (r * i)) r))) A

theorem absorbed_succ (r : Nat) (m : Mem) (p : Addr) (A : Spec.Sha3.State) (n : Nat) :
    absorbed r m p A (n + 1) =
      keccakF (xorBytes (absorbed r m p A n) (bytesAt m (p + BitVec.ofNat 64 (r * n)) r)) := by
  simp only [absorbed, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `absorbBlocks(state = x0, rate = x1, data = x2, len = x3, scratch = x4) -> x0`: absorbs whole
blocks of the `len` bytes at `data`, at least one, and returns the number of bytes left. -/
def blocksK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 200⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      (s.gpr .x1).toNat ∈ rates ∧ (s.gpr .x1).toNat ≤ (s.gpr .x3).toNat
  post s s' :=
    ∃ n, 0 < n ∧ (s.gpr .x1).toNat * n ≤ (s.gpr .x3).toNat ∧
      s'.gpr .x0 = BitVec.ofNat 64 ((s.gpr .x3).toNat - (s.gpr .x1).toNat * n) ∧
      stateAt s'.mem (s.gpr .x0) = absorbed (s.gpr .x1).toNat s.mem (s.gpr .x2) (stateAt s.mem (s.gpr .x0)) n
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The test whether a block is left: `x ≥ r`, for `x < 2 ^ 64` and `r ≤ 168`, as the sign of `x - r`
tells where `x < 2 ^ 63`. -/
theorem sign_sub (x r : BitVec 64) (hr : r.toNat ≤ 168) (h : (x - r) >>> 63 = 0) : r.toNat ≤ x.toNat := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow, show (0 : BitVec 64).toNat = 0 from rfl] at this
  have := x.isLt
  omega

end VG.Proof.Sha3.AArch64.Blocks
