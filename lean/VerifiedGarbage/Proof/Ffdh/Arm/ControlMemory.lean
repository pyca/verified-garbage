module

public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rc2.PairMem

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
