module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.MillerRabin.X86.WindowBits
import VerifiedGarbage.Proof.MillerRabin.X86.AdvanceWindow
import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame

/-! # A complete window end updates secret data and a public countdown -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def windowWrites : List (Nat × Nat) := [(sFlag, 4), (sValue, 4), (sWindows, 4)]

theorem windowEnd_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (eq1 : s.mem.readW (off g.W sEq1) 32 = BitVec.ofNat 32 E1.toNat)
    (eq2 : s.mem.readW (off g.W sEq2) 32 = BitVec.ofNat 32 E2.toNat)
    (flag : s.mem.readW (off g.W sFlag) 32 = BitVec.ofNat 32 F.toNat)
    (count : s.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      w32 t.mem g.W sFlag =
        (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = 0 then F else E1 || E2).toNat ∧
      t.mem.readW (off g.W sValue) 32 = s.mem.readW (off g.W sValue) 32 <<< 4 ∧
      w32 t.mem g.W sWindows = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      Outs g.W windowWrites s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t ∧ Context g t := by
  have header := v.headerFit
  have fitF : sFlag + 4 ≤ g.L := by unfold sFlag; omega
  change WP isa (.block (windowEnd.take 12 ++ .store (slot sFlag) .ecx :: advanceWindow)) s _
  refine WP.block_append (WP.mono (windowBits_ok v C E1 E2 F eq1 eq2 flag)
    fun a ⟨AX, Flag, Ma, Ka⟩ => ?_)
  have Ca := C.keepMem Ka (by decide) Ma
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := sFlag) (by omega))
    (ws_write Ca.ws (y := 0 + sFlag) (n := 4) (by omega)) fun b B => ?_
  have Of : Outside g.W sFlag 4 a.mem b.mem := by
    rw [B.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)
  have Cb := Ca.keepScalar (B.keeps []) (by decide) Of (by unfold scratchWord sFlag; simp)
  have oldCount : b.mem.readW (off g.W sWindows) 32 = BitVec.ofNat 32 q := by
    have unchanged := BitVec.eq_of_toNat_eq (Of.w32 (d := sWindows)
      (by unfold sFlag sWindows; omega) (by unfold sWindows; decide))
    rw [unchanged, Ma, count]
  refine WP.mono (advanceWindow_ok v Cb q positive bound oldCount)
    fun t ⟨Value, Count, Z, Ot, Kt, Ct⟩ => ?_
  have O₁ : Outs g.W windowWrites s.mem b.mem := by
    rw [Ma] at Of
    exact Outs.of_outside Of (by simp [windowWrites])
  have O₂ : Outs g.W windowWrites b.mem t.mem := Ot.mono (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> simp [windowWrites])
  refine ⟨?_, ?_, Count, Z, O₁.trans O₂, (Ka.widen (B.keeps [])).widen Kt, Ct⟩
  · have preserved := (WorkspaceFrame.of_outs Cb.ws.nowrap Ot).read32 fitF (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> left <;> decide)
    change (t.mem.readW (off g.W sFlag) 32).toNat = _
    rw [preserved, B.mem, Nat.zero_add, Mem.readW_writeW_self32]
    exact Flag
  · rw [Value, B.gpr, AX]

end VG.Proof.MillerRabin.X86
