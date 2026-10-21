module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext

/-! # Install the public descending source pointer in the caller-owned frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem pointerInit_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent : Nat} {s : State}
    (C : ArrayContext g candidate exponent s) :
    WP isa (.block (pointerInit g.n g.src)) s fun t =>
      ArrayContext g candidate exponent t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer 0 ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold pointerInit
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have stack := C.stack.keep K (by decide)
  have value : b.gpr .eax = g.pointer 0 := by
    rw [B.gpr, A.gpr, C.workspace]
    change _ = g.workspace + BitVec.ofNat 32 (g.src + 4 * (g.n - 1)) - 0#32
    rw [BitVec.sub_zero]
  refine wp_storeS (stack.address 0 (by decide))
    (VG.Proof.Mont.X86.Rt.ws_write stack.ws (y := 0) (n := 4) (by decide)) fun t T => WP.block_nil ?_
  have Mt : t.mem = s.mem.writeW (off (g.sp.setWidth 64) 0) (g.pointer 0) := by
    rw [T.mem, B.mem, A.mem, value]
  have Ot : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem := by
    rw [Mt]
    exact (writeW32_outside _ _ _ (by decide)).mono (by decide) (by decide)
  have Kt := K.widen (T.keeps [])
  refine ⟨C.keepFrame v Kt (by decide) (by decide) (arrayStackFrame Ot), ?_, Ot, Kt⟩
  rw [Mt, Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.Mod64
