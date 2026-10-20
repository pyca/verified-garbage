module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The Montgomery loop's temporary state and its preservation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

structure RoundMeta (mem : Mem) (base : BitVec 32) (tmp a b mod acc n i : Nat) (inv : BitVec 32) : Prop where
  count : mem.readW (off (State.addr base) tmp) 32 = BitVec.ofNat 32 n
  bPtr : mem.readW (off (State.addr base) (tmp + 4)) 32 = base + BitVec.ofNat 32 b
  mPtr : mem.readW (off (State.addr base) (tmp + 8)) 32 = base + BitVec.ofNat 32 mod
  inverse : mem.readW (off (State.addr base) (tmp + 12)) 32 = inv
  aPtr : mem.readW (off (State.addr base) (tmp + 16)) 32 = base + BitVec.ofNat 32 (a + 4 * i)
  remaining : mem.readW (off (State.addr base) (tmp + 20)) 32 = BitVec.ofNat 32 (n - i)
  accPtr : mem.readW (off (State.addr base) (tmp + 28)) 32 = base + BitVec.ofNat 32 acc

theorem RoundMeta.congr {mem mem' : Mem} {base : BitVec 32} {tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (h : RoundMeta mem base tmp a b mod acc n i inv)
    (eq : ∀ d, d + 4 ≤ 32 → mem'.readW (off (State.addr base) (tmp + d)) 32 =
      mem.readW (off (State.addr base) (tmp + d)) 32) :
    RoundMeta mem' base tmp a b mod acc n i inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eq 0 (by decide)).trans h.count
  · exact (eq 4 (by decide)).trans h.bPtr
  · exact (eq 8 (by decide)).trans h.mPtr
  · exact (eq 12 (by decide)).trans h.inverse
  · exact (eq 16 (by decide)).trans h.aPtr
  · exact (eq 20 (by decide)).trans h.remaining
  · exact (eq 28 (by decide)).trans h.accPtr

theorem RoundMeta.of_outside {mem mem' : Mem} {base : BitVec 32}
    {tmp a b mod acc n i o len : Nat} {inv : BitVec 32}
    (h : RoundMeta mem base tmp a b mod acc n i inv) (outside : Outside (State.addr base) o len mem mem')
    (sep : tmp + 32 ≤ o ∨ o + len ≤ tmp) (fit : tmp + 32 ≤ 2 ^ 64) :
    RoundMeta mem' base tmp a b mod acc n i inv :=
  h.congr fun d hd => outside_read32 outside (by omega) (by omega)

end VG.Proof.Bignum.Arm
