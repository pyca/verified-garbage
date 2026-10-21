module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath

/-! # The secret digit chooses a mask without choosing an address -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem maskIndex_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (j : Nat) (index : j < 16) :
    WP isa (.block (maskIndex j)) s fun t =>
      t.mem.readW (off g.W sEq1) 32 =
        (if (s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j then BitVec.allOnes 32 else 0#32) ∧
      Outside g.W sEq1 4 s.mem t.mem ∧ Keeps [.eax, .ecx] s t ∧ Context g t := by
  unfold maskIndex
  refine wp_movS (readSrc_ptr C.ws C.base (d := sValue) (by have := v.headerFit; unfold sValue; omega))
    fun a A _ => wp_shr (by decide) fun b B _ => ?_
  refine wp_logicS (.inr rfl) rfl fun c D => wp_subS rfl fun d E _ => ?_
  refine wp_shr (by decide) fun e F _ => wp_movS rfl fun f G _ => wp_subS rfl fun h H _ => ?_
  have K : Keeps [.eax, .ecx] s h :=
    ((((((A.keeps.mono (by decide)).widen B.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen G.keeps).widen H.keeps
  have Ch := C.keepMem K (by decide) (by rw [H.mem, G.mem, F.mem, E.mem, D.mem, B.mem, A.mem])
  refine wp_storeS (ea_ptr Ch.ws Ch.base (d := sEq1) (by have := v.headerFit; unfold sEq1; omega))
    (ws_write Ch.ws (y := 0 + sEq1) (n := 4) (by have := v.headerFit; unfold sEq1; omega))
    fun t T => WP.block_nil ?_
  have M : h.mem = s.mem := by rw [H.mem, G.mem, F.mem, E.mem, D.mem, B.mem, A.mem]
  have O : Outside g.W sEq1 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add, M]
    exact writeW32_outside _ _ _ (by have := C.ws.nowrap; have := v.headerFit; unfold sEq1; omega)
  have Kt : Keeps [.eax, .ecx] s t := K.widen (T.keeps [])
  refine ⟨?_, O, Kt, C.keepScalar Kt (by decide) O (by unfold scratchWord sEq1; simp)⟩
  rw [T.mem, Nat.zero_add, Mem.readW_writeW_self32, H.gpr, G.gpr, G.other .eax (by decide),
    F.gpr, E.gpr, D.gpr, B.gpr, A.gpr, Nat.zero_add]
  change 0#32 - ((((s.mem.readW (off g.W sValue) 32 >>> 28) ^^^ BitVec.ofNat 32 j) - 1) >>> 31) = _
  exact digitMask _ index

end VG.Proof.MillerRabin.X86
