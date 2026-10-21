module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext

/-! # Move the public source pointer to the preceding native word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem previousWord_ok {g : ArrayGeometry} {s : State} {i : Nat}
    (C : Sieve.StackContext g.sp s)
    (pointer : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i) :
    WP isa (.block previousWord) s fun t =>
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer (i + 1) ∧
      Outside (g.sp.setWidth 64) 0 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold previousWord
  refine wp_movS (C.read 0 (by decide)) fun a A _ => wp_subS rfl fun b B _ => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have next : b.gpr .eax = g.pointer (i + 1) := by
    rw [B.gpr, A.gpr, pointer]
    unfold ArrayGeometry.pointer
    rw [BitVec.sub_sub]
    change _ - (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  have stack := C.keep K (by decide)
  refine wp_storeS (stack.address 0 (by decide))
    (VG.Proof.Mont.X86.Rt.ws_write stack.ws (y := 0) (n := 4) (by decide)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, Mem.readW_writeW_self32, next]
  · rw [T.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.RsaKeyGen.X86.Mod64
