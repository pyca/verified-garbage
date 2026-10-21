module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayCount
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayPrevious

/-! # The complete public control update preserves the candidate and exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem advance_ok {g : ArrayGeometry} (v : g.Valid) {candidate exponent i q : Nat} {s : State}
    (C : ArrayContext g candidate exponent s) (positive : 0 < q) (bound : q < 2 ^ 32)
    (pointer : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i)
    (count : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 q) :
    WP isa (.block advance) s fun t =>
      ArrayContext g candidate exponent t ∧
      t.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer (i + 1) ∧
      t.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (q - 1) ∧
      t.zf = some (decide (q - 1 = 0)) ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold advance
  refine WP.block_append (WP.mono (previousWord_ok C.stack pointer) fun a ⟨P, Oa, Ka⟩ => ?_)
  have Ca := C.keepFrame v Ka (by decide) (by decide)
    (arrayStackFrame (Oa.mono (by decide) (by decide)))
  have countA : a.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 q :=
    (BitVec.eq_of_toNat_eq (Oa.w32 (d := 4) (by decide) (by decide))).trans count
  refine WP.mono (countDown_ok Ca.stack positive bound countA) fun t ⟨N, Z, Ot, Kt⟩ => ?_
  refine ⟨Ca.keepFrame v Kt (by decide) (by decide) (arrayStackFrame (Ot.mono (by decide) (by decide))),
    ?_, N, Z, (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), Ka.trans Kt⟩
  exact (BitVec.eq_of_toNat_eq (Ot.w32 (d := 0) (by decide) (by decide))).trans P

end VG.Proof.RsaKeyGen.X86.Mod64
