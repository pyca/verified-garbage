module

public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Endian conversion of ordinary disjoint byte buffers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

theorem reverse_source_addr (src : BitVec 32) {n i : Nat}
    (fit : src.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    State.addr (src + BitVec.ofNat 32 (n - 1) - BitVec.ofNat 32 i) =
      State.addr src + BitVec.ofNat 64 (n - 1 - i) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
    Offset.ofNat_sub_ofNat (by omega)]
  exact addr_add (by omega)

/-- Standard readable/writable, nonoverlapping buffers discharge all loop conditions. -/
theorem reverseCtx_of_regions (s : State) (src dst : BitVec 32) {n : Nat}
    (hn : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32)
    (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) n)
    (write : InRegions s.wr (State.addr dst) n)
    (sep : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩) :
    ReverseCtx s (src + BitVec.ofNat 32 (n - 1)) dst n := by
  have ds (j : Nat) (hj : j < n) := addr_add (a := dst) (k := j) (by omega)
  have sc (i : Nat) (hi : i < n) :
      (⟨State.addr src, n⟩ : Region).Contains (State.addr src + BitVec.ofNat 64 (n - 1 - i)) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have dc (j : Nat) (hj : j < n) :
      (⟨State.addr dst, n⟩ : Region).Contains (State.addr dst + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [reverse_source_addr src srcFit hi]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · intro j hj
    rw [ds j hj]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · intro i hi j hj he
    rw [reverse_source_addr src srcFit hi, ds j hj] at he
    exact sep _ (he ▸ sc i hi) (dc j hj)
  · intro i hi j hj he
    rw [ds i hi, ds j hj] at he
    have e := congrArg (fun a => (a - State.addr dst).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64)] using e

theorem ReverseInv.frame {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (inv : ReverseInv s0 src dst n i s) (fit : dst.toNat + n ≤ 2 ^ 32) :
    Frame [⟨State.addr dst, n⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj he
  apply ha ⟨State.addr dst, n⟩ (by simp)
  rw [he, addr_add (by have := inv.index; omega)]
  exact Offset.contains_base _ (by have := inv.index; omega) (by have := inv.index; omega)

end VG.Proof.Bignum.Arm
