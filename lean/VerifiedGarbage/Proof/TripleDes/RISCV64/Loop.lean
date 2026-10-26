module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.RoundBody
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The sixteen rounds of a pass

`roundsLoop_ok`: the loop of rounds, from the pass's first key at
`keyAddr base direction 0`, `kstep` bytes on each round.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

/-- The key step of a pass, in `kstep`. -/
def stepVal (direction : Direction) : BitVec 64 :=
  BitVec.ofInt 64 (if direction = .encrypt then 8 else -8)

theorem keyAddr_step (base : Addr) (direction : Direction) (j : Nat) (hj : j < 15) :
    keyAddr base direction j + stepVal direction = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega)
  · change base + BitVec.ofNat 64 (8 * (15 - j)) + -BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (15 - (j + 1)))
    rw [← BitVec.sub_eq_add_neg, Offset.add_ofNat_sub _ (by omega)]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega)

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr lReg = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr rReg = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.gpr cnt = BitVec.ofNat 64 n
  pointer : s.gpr kp = keyAddr base direction (16 - n)
  stp : s.gpr kstep = stepVal direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  mem : s.mem = origin.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr lReg = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr rReg = (roundPrefix keys direction 16 v).2.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  mem : s.mem = origin.mem

/-- What the rounds need of the pass's keys: readable, aligned, and the
pass's round keys. -/
structure KeysAt (keys : DesSchedule) (direction : Direction) (base : Addr) (s : State) :
    Prop where
  read : ∀ j < 16, InRegions (s.rd ++ s.wr) (keyAddr base direction j) 8
  al : ∀ j < 16, (keyAddr base direction j).toNat % 8 = 0
  keys : ∀ j < 16, (s.mem.readW (keyAddr base direction j) 64).setWidth 48 =
    roundKey keys direction j

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hready : FeiReady origin) (hkeys : KeysAt keys direction base origin)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance)) s (fun s' =>
      (isa.eval (.nonzero cnt) s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval (.nonzero cnt) s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hreadyS : FeiReady s := hready.congr (hs.regs sb (by decide)) hs.wr hs.mem
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr kp) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hkeys.read _ hj
  have halS : (s.gpr kp).toNat % 8 = 0 := by rw [hs.pointer]; exact hkeys.al _ hj
  have hk : (s.mem.readW (s.gpr kp) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer, hs.mem]
    exact hkeys.keys _ hj
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, sp, mem, regs⟩ :=
    roundStep_ok s _ _ (s.mem.readW (s.gpr kp) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hreadyS hreadS halS hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr lReg = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr rReg = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : s'.mem = origin.mem := mem.trans hs.mem
  have hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, (regs kstep (by decide)).trans hs.stp,
        rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, hs.stp, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hready : FeiReady origin)
    (hl : origin.gpr lReg = v.1.setWidth 64) (hr : origin.gpr rReg = v.2.setWidth 64)
    (hptr : origin.gpr kp = keyAddr base direction 0)
    (hcount : origin.gpr cnt = BitVec.ofNat 64 16)
    (hstep : origin.gpr kstep = stepVal direction)
    (hkeys : KeysAt keys direction base origin) :
    WP isa (.loop (.block (roundBody ++ roundAdvance)) (.nonzero cnt))
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance))
    (c := .nonzero cnt) (Q := LoopPost keys direction origin v)
    (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hready hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, hstep, rfl, rfl, rfl,
    fun _ _ => rfl, rfl⟩

end VG.Proof.TripleDes.RISCV64
