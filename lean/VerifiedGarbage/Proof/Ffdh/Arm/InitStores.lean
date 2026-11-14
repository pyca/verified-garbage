module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rc2.PairMem
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.Impl.Ffdh.Arm.Init
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Ffdh.Arm.ControlMemory`, which only this module used -/

section

/-! The shared 64-bit FFDH controller encoded with native 32-bit stores. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont

def controlSlots : List (Reg × Nat) :=
  [(.r0, 0), (.r1, 4), (.r2, 8), (.r3, 12),
   (.r4, 16), (.r5, 20), (.r6, 24), (.r7, 28)]

def controlMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : Mem :=
  Spill.saveMem m B g controlSlots

theorem controlMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    Spill.Saved (controlMem m B g) B g controlSlots :=
  Spill.saveMem_saved B g m controlSlots (by decide : Spill.Slots 0 32 controlSlots)

theorem controlMem_words (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    Spec.Rsa.wordsAt (controlMem m B g) B 4 =
      [g .r1 ++ g .r0, g .r3 ++ g .r2, g .r5 ++ g .r4, g .r7 ++ g .r6] := by
  have h := controlMem_saved m B g
  have wordPair (d : Nat) (lo hi : Reg)
      (low : (lo, d) ∈ controlSlots) (high : (hi, d + 4) ∈ controlSlots) :
      (controlMem m B g).readW (off B d) 64 = g hi ++ g lo := by
    rw [VG.Proof.Rc2.Word32.read64_pair]
    have a : (controlMem m B g).readW (off B d) 32 = g lo := h (lo, d) low
    have b : (controlMem m B g).readW (off B (d + 4)) 32 = g hi := h (hi, d + 4) high
    rw [show off B d + BitVec.ofNat 64 4 = off B (d + 4) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add], b, a]
  change [(controlMem m B g).readW (off B 0) 64,
    (controlMem m B g).readW (off B 8) 64,
    (controlMem m B g).readW (off B 16) 64,
    (controlMem m B g).readW (off B 24) 64] = _
  rw [wordPair 0 .r0 .r1 (by decide) (by decide),
    wordPair 8 .r2 .r3 (by decide) (by decide),
    wordPair 16 .r4 .r5 (by decide) (by decide),
    wordPair 24 .r6 .r7 (by decide) (by decide)]

end VG.Proof.Ffdh.Arm

end

end


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
    exact h.write (by omega_using [hd])
  have write0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [BitVec.add_zero] using write 0 (by decide)
  have addr (d : Nat) (hd : d ≤ 28) :
      State.addr (base + BitVec.ofNat 32 d) = State.addr base + BitVec.ofNat 64 d :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [hd, this])
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
      InRegions s.wr (State.addr base + BitVec.ofNat 64 d) 4 := h.write (by omega_using [hd])
  have write0 : InRegions s.wr (State.addr base) 4 := by
    simpa only [BitVec.add_zero] using write 0 (by decide)
  have addr (d : Nat) (hd : d ≤ 28) :
      State.addr (base + BitVec.ofNat 32 d) = State.addr base + BitVec.ofNat 64 d :=
    VG.Arm.addr_add (by have := h.nowrap; omega_using [hd, this])
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
