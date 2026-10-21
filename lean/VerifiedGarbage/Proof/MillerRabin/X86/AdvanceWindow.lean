module

import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.Counter
import VerifiedGarbage.Proof.MillerRabin.X86.ShiftWindow
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Advance the exponent word and count down its eight public windows -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def advanceWindow : List Instr :=
  [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .store (slot sValue) .eax, .mov .eax (.mem (slot sWindows)),
    .alu .sub .eax (.imm 1), .store (slot sWindows) .eax]

theorem advanceWindow_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32)
    (count : s.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q) :
    WP isa (.block advanceWindow) s fun t =>
      t.mem.readW (off g.W sValue) 32 = s.gpr .eax <<< 4 ∧
      w32 t.mem g.W sWindows = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outs g.W [(sValue, 4), (sWindows, 4)] s.mem t.mem ∧ Keeps [.eax] s t ∧ Context g t := by
  have header := v.headerFit
  have fitV : sValue + 4 ≤ g.L := by unfold sValue; omega
  change WP isa (.block ([.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)] ++
    [.store (slot sValue) .eax, .mov .eax (.mem (slot sWindows)),
      .alu .sub .eax (.imm 1), .store (slot sWindows) .eax])) s _
  refine WP.block_append (WP.mono (doubleFour_ok s) fun a ⟨AX, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := sValue) (by omega))
    (ws_write Ca.ws (y := 0 + sValue) (n := 4) (by omega)) fun b B => ?_
  have Ov : Outside g.W sValue 4 a.mem b.mem := by
    rw [B.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)
  have Cb := Ca.keepScalar (B.keeps []) (by decide) Ov (by unfold scratchWord sValue; simp)
  have oldCount : b.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q := by
    have unchanged := BitVec.eq_of_toNat_eq (Ov.w32 (d := sWindows)
      (by unfold sValue sWindows; omega) (by unfold sWindows; decide))
    rw [unchanged, Ma, count]
  refine WP.mono (counterDown_ok v Cb sWindows q (by unfold scratchWord sWindows; simp)
    positive bound oldCount) fun t ⟨Count, Z, Ow, Kw, Ct⟩ => ?_
  have O₁ : Outs g.W [(sValue, 4), (sWindows, 4)] s.mem b.mem := by
    rw [Ma] at Ov
    exact Outs.of_outside Ov (by simp)
  refine ⟨?_, Count, Z, O₁.trans (Outs.of_outside Ow (by simp)),
    (Ka.widen (B.keeps [])).trans Kw, Ct⟩
  have unchanged := BitVec.eq_of_toNat_eq (Ow.w32 (d := sValue)
    (by unfold sValue sWindows; omega) (by unfold sValue; decide))
  rw [unchanged, B.mem, Nat.zero_add, Mem.readW_writeW_self32, AX]

end VG.Proof.MillerRabin.X86
