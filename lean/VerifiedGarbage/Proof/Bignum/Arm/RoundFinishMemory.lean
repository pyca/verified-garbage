module

public import VerifiedGarbage.Proof.Bignum.Arm.RoundMeta
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The three finishing stores update only the high word and loop state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

def finishMem (mem : Mem) (base : Addr) (top tmp : Nat) : Mem :=
  ((mem.writeW (off base top) (0 : BitVec 32)).writeW (off base (tmp + 16))
    (mem.readW (off base (tmp + 16)) 32 + 4)).writeW (off base (tmp + 20))
    (mem.readW (off base (tmp + 20)) 32 - 1)

theorem finish_meta {mem : Mem} {base : BitVec 32} {size top tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 32 ≤ size) (htmp : tmp = top + 12)
    (hdr : RoundMeta mem base tmp a b mod acc n i inv) (hi : i < n) :
    RoundMeta (finishMem mem (State.addr base) top tmp) base tmp a b mod acc n (i + 1) inv := by
  have hb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    rw [VG.Proof.X25519.Arm.addr_toNat]
    exact nowrap
  have stable (d : Nat) (hd : d + 4 ≤ 32) (sep : d + 4 ≤ 16 ∨ 24 ≤ d) :
      (finishMem mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + d)) 32 =
        mem.readW (off (State.addr base) (tmp + d)) 32 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem mem (State.addr base) top tmp) (State.addr base) (tmp + d) =
      w32 mem (State.addr base) (tmp + d)
    rw [finishMem, w32_write_ne hb (by omega) (by omega) (by omega),
      w32_write_ne hb (by omega) (by omega) (by omega),
      w32_write_ne hb (by omega) (by omega) (by omega)]
  have ap : (finishMem mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 16)) 32 =
      mem.readW (off (State.addr base) (tmp + 16)) 32 + 4 := by
    apply BitVec.eq_of_toNat_eq
    change w32 (finishMem mem (State.addr base) top tmp) (State.addr base) (tmp + 16) = _
    rw [finishMem, w32_write_ne hb (by omega) (by omega) (by omega), w32_write_self]
  have count : (finishMem mem (State.addr base) top tmp).readW (off (State.addr base) (tmp + 20)) 32 =
      mem.readW (off (State.addr base) (tmp + 20)) 32 - 1 := by
    rw [finishMem, Mem.readW_writeW_self32]
  refine ⟨(stable 0 (by decide) (by decide)).trans hdr.count,
    (stable 4 (by decide) (by decide)).trans hdr.bPtr,
    (stable 8 (by decide) (by decide)).trans hdr.mPtr,
    (stable 12 (by decide) (by decide)).trans hdr.inverse, ?_, ?_,
    (stable 28 (by decide) (by decide)).trans hdr.accPtr⟩
  · rw [ap, hdr.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, hdr.remaining]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1

theorem finish_value {mem : Mem} {base : Addr} {size acc top tmp n : Nat}
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : tmp + 24 ≤ size)
    (htop : top = acc + 4 * (n + 1)) (htmp : tmp = top + 12) :
    val32 (finishMem mem base top tmp) base acc (n + 2) = val32 mem base acc (n + 1) ∧
      Outs base [(acc, 4 * (n + 2)), (tmp + 16, 8)] mem (finishMem mem base top tmp) := by
  have k1 := writeW32_outside mem base (d := top) (0 : BitVec 32) (by omega)
  have k2 := writeW32_outside (mem.writeW (off base top) (0 : BitVec 32)) base (d := tmp + 16)
    (mem.readW (off base (tmp + 16)) 32 + 4) (by omega)
  have k3 := writeW32_outside ((mem.writeW (off base top) (0 : BitVec 32)).writeW
    (off base (tmp + 16)) (mem.readW (off base (tmp + 16)) 32 + 4)) base (d := tmp + 20)
    (mem.readW (off base (tmp + 20)) 32 - 1) (by omega)
  have low1 := k1.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have low2 := k2.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have low3 := k3.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have hi2 := k2.w32 (d := top) (by omega) (by omega)
  have hi3 := k3.w32 (d := top) (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [show n + 2 = (n + 1) + 1 by omega, val32_succ, finishMem, low3, low2, low1,
      ← htop, hi3, hi2, w32_write_self]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · exact (Outs.of_outside (k1.mono (o' := acc) (n' := 4 * (n + 2)) (by omega) (by omega)) (by simp)).trans
      ((Outs.of_outside (k2.mono (o' := tmp + 16) (n' := 8) (by omega) (by omega)) (by simp)).trans
        (Outs.of_outside (k3.mono (o' := tmp + 16) (n' := 8) (by omega) (by omega)) (by simp)))

end VG.Proof.Bignum.Arm
