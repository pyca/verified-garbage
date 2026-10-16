module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.Block
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 and Poly1305 together (x86-64): the data tail's overlapping loads

`padBig` (8 to 15 bytes) and `padMid` (4 to 7) load the last `t` bytes at
`Q` in two loads within them that overlap, and shift the second past the
bytes the first holds: their results as reads of memory, which `CT.lean`
turns into the bytes' little-endian value.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.TailLoad

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- `Q + t - d`, the address of the last `d` of the `t` bytes at `Q`. -/
theorem ea_last {Q : Addr} {t d : Nat} (hd : d ≤ t) (ht : t < 2 ^ 64) :
    Q + BitVec.ofNat 64 t * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-(d : Int)) =
      Q + BitVec.ofNat 64 (t - d) := by
  rw [BitVec.mul_one, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- The shift count both cases compute in `rcx` (`mov ecx, c; sub ecx, edx;
shl ecx, 3`), as `shr r9, cl` reads it: `8 * (c - t)`. -/
theorem count_val (c : BitVec 32) {t : Nat} (hc : c.toNat < 2 ^ 28) (ht : t ≤ c.toNat) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 c) - BitVec.setWidth 32 (BitVec.ofNat 64 t))) <<< 3)).toNat % 64 =
      8 * (c.toNat - t) % 64 := by
  have ht' : t < 2 ^ 32 := by omega
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show c.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c.toNat < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega), Nat.mod_eq_of_lt ht']
  omega

theorem padBig_ok {s : State} {Q : Addr} {t : Nat} (h8 : 8 ≤ t) (ht : t < 16) (hrsi : s.gpr .rsi = Q)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 t) (hin0 : InRegions (s.rd ++ s.wr) Q 8)
    (hin1 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 (t - 8)) 8) :
    WP isa (.block padBig) s fun s' =>
      s'.gpr .rax = s.mem.readW Q 64 ∧
      s'.gpr .r9 = s.mem.readW (Q + BitVec.ofNat 64 (t - 8)) 64 >>> 8 >>> (8 * (15 - t)) ∧
      (∀ q, q ≠ .rax → q ≠ .r9 → q ≠ .rcx → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  have e0 : Q + BitVec.ofInt 64 ((0 : Nat) : Int) = Q := by simp
  have e8 : Q + BitVec.ofNat 64 t * 1#64 + BitVec.ofInt 64 (-8) = Q + BitVec.ofNat 64 (t - 8) := by
    have := ea_last (Q := Q) (d := 8) h8 (by omega); simpa using this
  apply WP.of_runBlock
  simp only [padBig, tailLast8, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.ea, hrsi, hrdx, e0, e8, State.load64, hin0, hin1, ↓reduceIte, Option.bind_some, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq,
    execShift, execAlu32, execShift32, execShiftCl, State.setReg32, VarShiftOp.eval,
    RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags,
    Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, Nat.reduceSub]
  rw [count_val 15 (by decide) (by simp; omega), show BitVec.toNat (15 : BitVec 32) = 15 from rfl,
    Nat.mod_eq_of_lt (show 8 * (15 - t) < 64 by omega)]
  exact ⟨trivial, rfl, fun q h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

theorem padMid_ok {s : State} {Q : Addr} {t : Nat} (h4 : 4 ≤ t) (ht : t < 8) (hrsi : s.gpr .rsi = Q)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 t) (hin0 : InRegions (s.rd ++ s.wr) Q 4)
    (hin1 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 (t - 4)) 4) :
    WP isa (.block padMid) s fun s' =>
      s'.gpr .rax = (s.mem.readW Q 32).setWidth 64 +
        ((s.mem.readW (Q + BitVec.ofNat 64 (t - 4)) 32).setWidth 64 >>> (8 * (8 - t)) <<< 32) ∧
      s'.gpr .r9 = 0 ∧
      (∀ q, q ≠ .rax → q ≠ .r9 → q ≠ .rcx → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  have e0 : Q + BitVec.ofInt 64 ((0 : Nat) : Int) = Q := by simp
  have e4 : Q + BitVec.ofNat 64 t * 1#64 + BitVec.ofInt 64 (-4) = Q + BitVec.ofNat 64 (t - 4) := by
    have := ea_last (Q := Q) (d := 4) h4 (by omega); simpa using this
  apply WP.of_runBlock
  simp only [padMid, tailLast4, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.ea, hrsi, hrdx, e0, e4, State.load32, hin0, hin1, ↓reduceIte, Option.bind_some, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq,
    execAlu, execShift, execAlu32, execShift32, execShiftCl, State.setReg32, VarShiftOp.eval,
    RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags,
    Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, Nat.reduceSub]
  rw [count_val 8 (by decide) (by simp; omega), show BitVec.toNat (8 : BitVec 32) = 8 from rfl,
    Nat.mod_eq_of_lt (show 8 * (8 - t) < 64 by omega), BitVec.xor_self, BitVec.setWidth_zero]
  exact ⟨rfl, rfl, fun q h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

end VG.Proof.ChaCha20Poly1305.X86_64.TailLoad
