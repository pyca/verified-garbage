module

public import VerifiedGarbage.Proof.Bignum.Arm.WideProductNext
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Product-loop controls change only their dedicated header slots -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

theorem wideProductNext_memory {m m' : Mem} {base : Addr} {ap op : BitVec 32} {c : Nat}
    (mem : m' = ((m.writeW (off base 128) (ap + 4)).writeW
      (off base 136) (op + 4)).writeW (off base 140) (BitVec.ofNat 32 (c - 1))) :
    Outside base 128 16 m m' ∧
      m'.readW (off base 128) 32 = ap + 4 ∧
      m'.readW (off base 136) 32 = op + 4 ∧
      m'.readW (off base 140) 32 = BitVec.ofNat 32 (c - 1) ∧
      m'.readW (off base 132) 32 = m.readW (off base 132) 32 ∧
      m'.readW (off base 144) 32 = m.readW (off base 144) 32 := by
  have a := writeW32_outside m base (d := 128) (ap + 4) (by decide)
  have b := writeW32_outside (m.writeW (off base 128) (ap + 4)) base (d := 136) (op + 4) (by decide)
  have c' := writeW32_outside ((m.writeW (off base 128) (ap + 4)).writeW (off base 136) (op + 4))
    base (d := 140) (BitVec.ofNat 32 (c - 1)) (by decide)
  have outside : Outside base 128 16 m m' := by
    rw [mem]
    exact (a.mono (by decide) (by decide)).trans
      ((b.mono (by decide) (by decide)).trans (c'.mono (by decide) (by decide)))
  refine ⟨outside, ?_, ?_, ?_, ?_, outside_read32 outside (by decide) (by decide)⟩
  · rw [mem, outside_read32 c' (d := 128) (by decide) (by decide),
      outside_read32 b (d := 128) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, outside_read32 c' (d := 136) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, Mem.readW_writeW_self32]
  · rw [mem, outside_read32 c' (d := 132) (by decide) (by decide),
      outside_read32 b (d := 132) (by decide) (by decide),
      outside_read32 a (d := 132) (by decide) (by decide)]

end VG.Proof.Bignum.Arm
