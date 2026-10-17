module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCompareArgs
public import VerifiedGarbage.Proof.Bignum.Arm.EqualBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exact branchless equality of the factor product and padded modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtCompareInput (base : BitVec 32) (size o a b w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  fit : 244 ≤ size
  subtraction : SubCtx s base size o a b (4 * w + 2)
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  output : s.mem.readW (off (State.addr base) 236) 32 = base + BitVec.ofNat 32 o
  first : s.mem.readW (off (State.addr base) 232) 32 = base + BitVec.ofNat 32 a
  second : s.mem.readW (off (State.addr base) 240) 32 = base + BitVec.ofNat 32 b
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem crt_compareProduct_ok (s : State) {base : BitVec 32} {size o a b w : Nat}
    (h : CrtCompareInput base size o a b w s) :
    WP isa compareProduct s fun t =>
      t.gpr .r11 = (if val32 s.mem (State.addr base) a (4 * w + 2) =
        val32 s.mem (State.addr base) b (4 * w + 2) then 1 else 0) ∧
      Outside (State.addr base) o (4 * (4 * w + 2)) s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [compareProduct, WP.seq_iff]
  refine WP.mono (crt_compareArgs_ok s h.workspace h.fit h.ptr h.count h.output h.first h.second) ?_
  rintro u ⟨ptrU, aU, bU, countU, memU, restU⟩
  have ctx : SubCtx u base size o a b (4 * w + 2) :=
    ⟨h.subtraction.nowrap, h.subtraction.outFits, h.subtraction.aFits, h.subtraction.bFits,
      h.subtraction.sepA, h.subtraction.sepB, by rw [restU.wr]; exact h.subtraction.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (equalBuffers_ok u ctx (by omega) ptrU aU bU countU) ?_
  rintro v ⟨value, outside, restV⟩
  rw [memU] at value outside
  have frame := outside_workspace outside h.subtraction.outFits
  have rest : Rest roundClobbers s v := (restU.mono (by simp [roundClobbers])).trans restV
  refine WP.mono (restoreBase_ok v (by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead)
    (saved_base_kept frame h.stackSep h.saved rest.sp)) ?_
  rintro t ⟨ptrT, memT, restT⟩
  exact ⟨(restT.gpr .r11 (by simp)).trans value, by rw [memT]; exact outside,
    by rw [memT]; exact frame, ptrT, rest.trans (restT.mono (by simp [roundClobbers]))⟩

end VG.Proof.Bignum.Arm
