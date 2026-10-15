module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.Stream

/-! # Installing the public byte-source pointer for scalar reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem streamSource_ok {s : State} {base : Addr} {size n m : Nat}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (p : Pointer) :
    WP isa (.block (Core.pointer p ++ [.store (sc sourcePointer) .esi])) s fun t =>
      Context n m base size t ∧ t.mem.readW (off base sourcePointer) 32 = pointerValue base s p ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps [.esi] s t := by
  refine WP.block_append (WP.mono (pointer_ok h.scr hz p) fun u ⟨Pu, Ku, Mu⟩ => ?_)
  have su := h.scr.of_keeps Ku (by decide)
  have hsize : 24 ≤ size := by have : 8256 ≤ size := hz; omega
  refine wp_storeS (su.ea (d := sourcePointer) (by change 20 < size; omega))
    (su.write (d := sourcePointer) (n := 4) (by change 24 ≤ size; omega)) fun t mt => WP.block_nil ?_
  have Kt := Ku.trans (mt.keeps _)
  have Ot : Outside base sourcePointer 4 s.mem t.mem := by
    rw [mt.mem, Mu]
    exact writeW32_outside _ _ _ (by have := h.scr.nowrap; change 20 + 4 ≤ 2 ^ 64; decide)
  have hmod := slot_header n 0
  have hwhole := slot_header n 9
  change 64 ≤ contextBytes n at hwhole
  refine ⟨h.outside_keep Kt (by decide) (by decide) Ot (.inr (by change 24 ≤ slot n 0; omega))
    (by decide), ?_, Ot.mono (o' := 0) (n' := contextBytes n) (by decide) (by simp only [sourcePointer, Nat.zero_add]; omega), Kt⟩
  rw [mt.mem, Mem.readW_writeW_self32, Pu]

end VG.Proof.Dsa.X86
