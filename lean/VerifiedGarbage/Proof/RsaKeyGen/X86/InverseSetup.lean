module

import VerifiedGarbage.Proof.RsaKeyGen.X86.InverseLift
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete the prepared workspace's 64-bit negative inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.RsaKeyGen.X86.InverseLift

theorem setup_ok {s : State} {base : Addr} {size mo inv : Nat}
    (scratch : Scr s base size) (modulus : mo + 8 ≤ size) (slot : inv + 8 ≤ size)
    (inverse : (w32 s.mem base mo * w32 s.mem base inv + 1) % 2 ^ 32 = 0) :
    WP isa (.block (setup mo inv)) s fun t =>
      ((w32 s.mem base mo + 2 ^ 32 * w32 s.mem base (mo + 4)) *
        (w32 s.mem base inv + 2 ^ 32 * w32 t.mem base (inv + 4)) + 1) % 2 ^ 64 = 0 ∧
      Outside base (inv + 4) 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_movS (readSrc_sc Sa (by omega)) fun b B _ => ?_
  have Kb : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_movS (readSrc_sc Sb (by omega)) fun c C _ => ?_
  have lo : c.gpr .ebx = s.mem.readW (off base mo) 32 := by
    rw [C.other .ebx (by decide), B.other .ebx (by decide), A.gpr]
  have hi : c.gpr .esi = s.mem.readW (off base (mo + 4)) 32 := by
    rw [C.other .esi (by decide), B.gpr, A.mem]
  have ix : c.gpr .ecx = s.mem.readW (off base inv) 32 := by
    rw [C.gpr, B.mem, A.mem]
  refine WP.block_append (WP.mono (inverse_ok c (by rw [lo, ix]; exact inverse)) fun d ⟨value, mem, Kd⟩ => ?_)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.widen C.keeps).widen Kd
  have Sd := scratch.of_keeps K (by decide)
  refine wp_storeS (Sd.ea (by omega)) (Sd.write (by omega)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self]
    rw [Kd.1 .ecx (by decide), lo, hi, ix] at value
    exact value
  · rw [T.mem, mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

end VG.Proof.RsaKeyGen.X86.InverseLift
