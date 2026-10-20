module

public import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.ControlMemory

/-! Exact controller stores made by ARMv7 initialization. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm
open VG.Proof.Mont (off)

theorem clearController_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa clearController s fun t =>
      t.gpr .r0 = 0 ∧ t.mem = controlMem s.mem (State.addr base) (fun _ => 0) := by
  have write (d : Nat) (hd : d ≤ 28) :
      InRegions s.wr (State.addr base + BitVec.ofNat 64 d) 4 := by
    exact h.write (by omega)
  have write0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [BitVec.add_zero] using write 0 (by decide)
  have addr (d : Nat) (hd : d ≤ 28) :
      State.addr (base + BitVec.ofNat 32 d) = State.addr base + BitVec.ofNat 64 d :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  unfold clearController controlMem controlSlots Spill.saveMem
  ffrun [ptr, write0, write 0 (by decide), write 4 (by decide), write 8 (by decide), write 12 (by decide),
    write 16 (by decide), write 20 (by decide), write 24 (by decide), write 28 (by decide),
    BitVec.add_zero, off, Spill.saveMem, addr 4 (by decide), addr 8 (by decide),
    addr 12 (by decide), addr 16 (by decide), addr 20 (by decide), addr 24 (by decide), addr 28 (by decide)]

def keyInitValues (k : BitVec 32) : Reg → BitVec 32
  | .r0 | .r2 => 128
  | .r4 | .r6 => k
  | _ => 0

theorem keyInitializeState_ok (s : State) {base : BitVec 32}
    (h : Workspace s base 128) (ptr : s.gpr .r0 = base) :
    WP isa KeyGeneration.initializeState s fun t =>
      t.gpr .r0 = 1 ∧ t.mem = controlMem s.mem (State.addr base) (keyInitValues (s.gpr .r1)) := by
  have write (d : Nat) (hd : d ≤ 28) :
      InRegions s.wr (State.addr base + BitVec.ofNat 64 d) 4 := h.write (by omega)
  have write0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [BitVec.add_zero] using write 0 (by decide)
  have addr (d : Nat) (hd : d ≤ 28) :
      State.addr (base + BitVec.ofNat 32 d) = State.addr base + BitVec.ofNat 64 d :=
    VG.Arm.addr_add (by have := h.nowrap; omega)
  unfold KeyGeneration.initializeState controlMem controlSlots Spill.saveMem
  ffrun [ptr, write0, write 4 (by decide), write 8 (by decide), write 12 (by decide),
    write 16 (by decide), write 20 (by decide), write 24 (by decide), write 28 (by decide),
    BitVec.add_zero, off, Spill.saveMem, keyInitValues,
    addr 4 (by decide), addr 8 (by decide), addr 12 (by decide), addr 16 (by decide),
    addr 20 (by decide), addr 24 (by decide), addr 28 (by decide)]

def parameterInitValues (bits : BitVec 32) : Reg → BitVec 32
  | .r0 => (bits * bits) <<< 6
  | .r1 => (bits * bits) >>> 26
  | .r2 => (bits + 7) >>> 3
  | .r4 => ((bits + 7) >>> 3) + (((bits + 7) >>> 3) <<< 15)
  | .r6 => ((bits + 7) >>> 3) <<< 9
  | _ => 0

end VG.Proof.Ffdh.Arm
