module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorMask
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorScan
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Block

/-! The 32-entry scan of a 128-byte column block consumes every row and
leaves the selected block in the eight accumulators. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (innerWide)

/-- What the 128-byte scan keeps from its start `s` after row `j`; the digit
(`x5`), the mask's sources (`x7`, `x8`) and the stride (`x6`) are `s`'s. -/
structure WScanInv (s : State) (base : Addr) (stride v j : Nat) (t : State) : Prop where
  mem : t.mem = s.mem
  keep : Keep [.x9, .x14, .x16] s t
  ptr : t.gpr .x16 = base + BitVec.ofNat 64 (stride * j)
  value : ∀ i < 8, t.v (acc i) = if v < j then
    s.mem.read (base + BitVec.ofNat 64 (stride * v + 16 * i)) 16 else 0

theorem wscanStep_ok {s t : State} {base : Addr} {stride v j : Nat}
    (hj : j < 32) (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (32 - v)) (h7 : s.gpr .x7 = BitVec.allOnes 64)
    (h8 : s.gpr .x8 = 0) (hI : WScanInv s base stride v j t)
    (h14 : t.gpr .x14 = BitVec.ofNat 64 (32 - j))
    (hld : ∀ j < 32, ∀ i < 8,
      InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (stride * j + 16 * i)) 16) :
    WP isa (.block (innerWide ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      WScanInv s base stride v (j + 1) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff]
  refine WP.mono (innerWide_ok hj hv h14
    (by rw [hI.keep.gpr .x5 (by decide)]; exact h5)
    (by rw [hI.keep.gpr .x7 (by decide)]; exact h7)
    (by rw [hI.keep.gpr .x8 (by decide)]; exact h8) (fun i hi => by
    rw [hI.keep.rd, hI.keep.wr, hI.ptr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hld j hj i hi)) fun a ⟨⟨ha, hp, hm⟩, ka⟩ => ?_
  refine WP.mono (decVector_ok a) fun u ⟨⟨hu, hum, huv⟩, ku⟩ => ?_
  refine ⟨⟨hum.trans (hm.trans hI.mem), ((hI.keep.trans ka).trans ku).mono (by decide),
    ?_, ?_⟩, hu.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x14 (by decide)))⟩
  · rw [ku.gpr .x16 (by decide), hp, hI.ptr, hI.keep.gpr .x6 (by decide), hs,
      BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one]
  · intro i hi
    rw [huv, ha i hi, hI.mem, hI.ptr, BitVec.add_assoc, ← BitVec.ofNat_add, hI.value i hi]
    by_cases he : j = v
    · subst j
      simp only [ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
    · have heq : v < j + 1 ↔ v < j := by omega
      simp only [he, ite_false, heq]

/-- Exact 32-row scan of a 128-byte block. -/
theorem wscan_ok {s : State} {base : Addr} {stride v : Nat}
    (hv : v < 32) (hs : s.gpr .x6 = BitVec.ofNat 64 stride)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (32 - v)) (h7 : s.gpr .x7 = BitVec.allOnes 64)
    (h8 : s.gpr .x8 = 0)
    (hc : s.gpr .x14 = BitVec.ofNat 64 32) (h0 : WScanInv s base stride v 0 s)
    (hld : ∀ j < 32, ∀ i < 8,
      InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (stride * j + 16 * i)) 16) :
    WP isa (countLoop .x14 innerWide) s (WScanInv s base stride v 32) := by
  unfold countLoop
  exact wp_countdown (by decide) (by decide) (fun j => WScanInv s base stride v j)
    (fun j hj t hI h14 => wscanStep_ok hj hv hs h5 h7 h8 hI h14 hld) h0 hc

end VG.Proof.Bignum.AArch64.WindowVector
