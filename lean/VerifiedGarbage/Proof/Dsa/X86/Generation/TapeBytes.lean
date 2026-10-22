module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessTape
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Bignum.CopyOctets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Read individual seed bytes from the same bounded external-tape representation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Bignum.X86

theorem WitnessTape.byte_read {s : State} {base : Addr} {bytes i : Nat}
    {sp src : BitVec 32} {r : List Byte} (T : WitnessTape base bytes sp src r s) (hi : i < r.length) :
    InRegions (s.rd ++ s.wr) (off (byteAddr src) i) 1 := by
  apply Covers.one (T.read (by intro h; rw [h] at hi; simp at hi))
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := T.fit; omega)⟩

theorem WitnessTape.byte_value {s : State} {base : Addr} {bytes i : Nat}
    {sp src : BitVec 32} {r : List Byte} (T : WitnessTape base bytes sp src r s) (hi : i < r.length) :
    s.mem (off (byteAddr src) i) = r.getD i 0 := by
  rw [← T.data, VG.Proof.Bignum.bytesAt_getD _ _ hi]

theorem WitnessTape.byte_apart {s : State} {base : Addr} {bytes i d count j : Nat}
    {sp src : BitVec 32} {r : List Byte} (T : WitnessTape base bytes sp src r s)
    (hi : i < r.length) (hj : j < count) (fit : d + count ≤ bytes) (small : bytes < 2 ^ 64) :
    off (byteAddr src) i ≠ off (off base d) j := by
  intro eq
  apply T.workspace (off (byteAddr src) i)
    (Offset.contains_base _ (by omega) (by have := T.fit; omega))
  rw [eq, off, off, Offset.add_add]
  exact Offset.contains_base base (by omega) (by omega)

end VG.Proof.Dsa.X86.Generation
