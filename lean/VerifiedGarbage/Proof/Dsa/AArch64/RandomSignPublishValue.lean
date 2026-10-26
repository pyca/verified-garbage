module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublish
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Published consumption, preserved signature bytes, and erased nonce bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem random_publish_used (m : Mem) (B : Addr) :
    (randomPublishMem m B).readW (word m B Random.oUsedPtr) 64 = word m B Random.oUsed :=
  Mem.readW_writeW_self64 _ _ _

theorem random_writeW_bytes {m : Mem} {p dst : Addr} {n : Nat} (v : BitVec 64)
    (hsep : Mem.Sep p n dst 8) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW dst v) p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply Mem.write_apply
  apply hsep
  rw [Mem.sub_ofNat_toNat _ (by have := List.mem_range.mp hi; omega)]
  exact List.mem_range.mp hi

theorem random_publish_output {m : Mem} {B p : Addr} {n : Nat}
    (hframe : (⟨p, n⟩ : Region).Disjoint ⟨B, Random.frameBytes⟩)
    (hused : Mem.Sep p n (word m B Random.oUsedPtr) 8) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (randomPublishMem m B) p n = Spec.Rsa.bytesAt m p n := by
  unfold randomPublishMem
  rw [random_writeW_bytes _ hused hn]
  exact random_private_bytes (InScr.of_outside (random_clear_outside _ _) (by decide)) hframe (Nat.le_of_lt hn)

theorem random_publish_nonce_zero {m : Mem} {B : Addr}
    (hsep : Mem.Sep (off B Random.oNonce) 32 (word m B Random.oUsedPtr) 8) (i : Nat) (hi : i < 32) :
    randomPublishMem m B (off B (200 + i)) = 0 := by
  unfold randomPublishMem
  have he : off B (200 + i) = off B Random.oNonce + BitVec.ofNat 64 i := by
    simp only [off, Random.oNonce, BitVec.ofNat_add, BitVec.add_assoc]
  have hout : ¬(off B (200 + i) - word m B Random.oUsedPtr).toNat < 8 := by
    apply hsep
    rw [he, Mem.sub_ofNat_toNat _ (by omega)]
    exact hi
  exact (Mem.write_apply hout).trans (random_clear_byte _ _ i hi)

end VG.Proof.Dsa.AArch64
