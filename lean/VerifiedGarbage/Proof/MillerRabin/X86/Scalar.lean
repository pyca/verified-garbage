module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Reads and stores of the round's permitted scratch header words -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem Context.readScalar {g : Geometry} {s : State} (C : Context g s)
    (d : Nat) (fit : d + 4 ≤ g.L) :
    readSrc s (.mem (slot d)) = some (s.mem.readW (off g.W d) 32) := by
  simpa only [slot, VG.Impl.MillerRabin.X86.at_, VG.Impl.Mont.X86.at_, Nat.zero_add] using readSrc_ptr C.ws C.base (d := d) (by omega)

theorem Context.readScalarAfter {g : Geometry} {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs) (mem : t.mem = s.mem)
    (d : Nat) (fit : d + 4 ≤ g.L) :
    readSrc t (.mem (slot d)) = some (s.mem.readW (off g.W d) 32) := by
  have Ct := C.keepMem K base mem
  simpa only [mem] using Ct.readScalar d fit

theorem scalarStore_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (d : Nat) (scratch : scratchWord d) (r : Reg) :
    WP isa (.block [.store (slot d) r]) s fun t =>
      t.mem.readW (off g.W d) 32 = s.gpr r ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [] s t ∧ Context g t := by
  have bound : d + 4 ≤ g.L := by
    have := v.headerFit
    unfold scratchWord at scratch
    omega
  refine wp_storeS (ea_ptr C.ws C.base (d := d) (by omega))
    (ws_write C.ws (y := 0 + d) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have O : Outside g.W d 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; omega)
  refine ⟨?_, O, T.keeps [], C.keepScalar (T.keeps []) (by decide) O scratch⟩
  rw [T.mem, Nat.zero_add, Mem.readW_writeW_self32]

end VG.Proof.MillerRabin.X86
