module

public import VerifiedGarbage.Proof.Bignum.Arm.CopyBytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Copying of ordinary disjoint byte buffers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

/-- Standard readable/writable, nonoverlapping buffers discharge all loop conditions. -/
theorem copyCtx_of_regions (s : State) (src dst : BitVec 32) {n : Nat}
    (hn : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32)
    (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) n)
    (write : InRegions s.wr (State.addr dst) n)
    (sep : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩) :
    CopyCtx s src dst n := by
  have ds (j : Nat) (hj : j < n) := addr_add (a := dst) (k := j) (by omega)
  have sc (i : Nat) (hi : i < n) :
      (⟨State.addr src, n⟩ : Region).Contains (State.addr src + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have dc (j : Nat) (hj : j < n) :
      (⟨State.addr dst, n⟩ : Region).Contains (State.addr dst + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [addr_add (by omega)]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · intro j hj
    rw [ds j hj]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · intro i hi j hj he
    rw [addr_add (by omega), ds j hj] at he
    exact sep _ (he ▸ sc i hi) (dc j hj)
  · intro i hi j hj he
    rw [ds i hi, ds j hj] at he
    have e := congrArg (fun a => (a - State.addr dst).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64)] using e

theorem CopyInv.frame {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (inv : CopyInv s0 src dst n i s) (fit : dst.toNat + n ≤ 2 ^ 32) :
    Frame [⟨State.addr dst, n⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj he
  apply ha ⟨State.addr dst, n⟩ (by simp)
  rw [he, addr_add (by have := inv.index; omega)]
  exact Offset.contains_base _ (by have := inv.index; omega) (by have := inv.index; omega)

theorem copied_read (m m' : Mem) (p q : Addr) (n : Nat)
    (bytes : ∀ j < n, m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j)) :
    m'.read q n = m.read p n := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have first := bytes 0 (by omega)
    simp only [BitVec.add_zero] at first
    rw [first, ih]
    intro j hj
    have h := bytes (j + 1) (by omega)
    simpa only [Offset.add_ofNat_succ] using h

theorem CopyInv.read {s0 s : State} {src dst : BitVec 32} {n : Nat}
    (inv : CopyInv s0 src dst n n s)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32) :
    s.mem.read (State.addr dst) n = s0.mem.read (State.addr src) n := by
  apply copied_read
  intro j hj
  have h := inv.copied j hj
  rw [addr_add (by omega), addr_add (by omega)] at h
  exact h

end VG.Proof.Bignum.Arm
