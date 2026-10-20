module

public import VerifiedGarbage.Proof.Bignum.X86.CopyBytes
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset

/-! # Byte copying of ordinary disjoint byte buffers -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86


/-- Standard readable/writable, nonoverlapping buffers discharge all loop conditions. -/
theorem copyCtx_of_regions (s : State) (src dst : BitVec 32) {n : Nat}
    (hn : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32)
    (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) n)
    (write : InRegions s.wr (byteAddr dst) n)
    (sep : Region.Disjoint ⟨byteAddr src, n⟩ ⟨byteAddr dst, n⟩) :
    CopyCtx s src dst n := by
  have ds (j : Nat) (hj : j < n) := byteAddr_add (a := dst) (k := j) (by omega)
  have sc (i : Nat) (hi : i < n) :
      (⟨byteAddr src, n⟩ : Region).Contains (byteAddr src + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have dc (j : Nat) (hj : j < n) :
      (⟨byteAddr dst, n⟩ : Region).Contains (byteAddr dst + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [byteAddr_add (by omega)]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · intro j hj
    rw [ds j hj]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · intro i hi j hj he
    rw [byteAddr_add (by omega : src.toNat + i < 2 ^ 32), ds j hj] at he
    exact sep _ (he ▸ sc i hi) (dc j hj)
  · intro i hi j hj he
    rw [ds i hi, ds j hj] at he
    have e := congrArg (fun a => (a - byteAddr dst).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64)] using e

theorem CopyInv.frame {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (inv : CopyInv s0 src dst n i s) (fit : dst.toNat + n ≤ 2 ^ 32) :
    Frame [⟨byteAddr dst, n⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj he
  apply ha ⟨byteAddr dst, n⟩ (by simp)
  rw [he, byteAddr_add (by have := inv.index; omega)]
  exact Offset.contains_base _ (by have := inv.index; omega) (by have := inv.index; omega)

end VG.Proof.Bignum.X86
