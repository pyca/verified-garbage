module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessOdd
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.LowUpdate32
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The native range comparison sees x with bit zero set and then restores x -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessOdd
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessOdd

theorem mark_ok {s : State} {base : Addr} {size src n : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : src + 4 * n ≤ size) :
    WP isa (.block (mark src)) s fun t =>
      val32 t.mem base src n = val32 s.mem base src n + (1 - val32 s.mem base src n % 2) ∧
      t.gpr .esi = s.mem.readW (off base src) 32 ∧ Outside base src 4 s.mem t.mem ∧ Keeps [.eax, .esi] s t := by
  unfold mark
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => wp_movS rfl fun b B _ => wp_orS rfl fun c C => ?_
  have K : Keeps [.eax, .esi] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have Sc := scratch.of_keeps K (by decide)
  refine wp_storeS (Sc.ea (by omega)) (Sc.write (by omega)) fun t T => WP.block_nil ?_
  have O : Outside base src 4 s.mem t.mem := by
    rw [T.mem, C.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have low : w32 t.mem base src = w32 s.mem base src ||| 1 := by
    rw [T.mem, w32_write_self, C.gpr, B.gpr, A.gpr, BitVec.toNat_or]
    rfl
  refine ⟨val32_low_or_one positive (by have := scratch.nowrap; omega) O low, ?_, O, K.widen (T.keeps [])⟩
  rw [(T.keeps []).1 .esi (by decide), C.other .esi (by decide), B.other .esi (by decide), A.gpr]

theorem restore_ok {s original : State} {base : Addr} {size src n : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : src + 4 * n ≤ size) (O : Outside base src 4 original.mem s.mem)
    (saved : s.gpr .esi = original.mem.readW (off base src) 32) :
    WP isa (.block (restore src)) s fun t =>
      val32 t.mem base src n = val32 original.mem base src n ∧
      Outside base src 4 original.mem t.mem ∧ Keeps [] s t := by
  unfold restore
  refine wp_storeS (scratch.ea (by omega)) (scratch.write (by omega)) fun t T => WP.block_nil ?_
  have Ot : Outside base src 4 s.mem t.mem := by
    rw [T.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have low : w32 t.mem base src = w32 original.mem base src := by rw [T.mem, w32_write_self, saved]
  exact ⟨val32_restore_low positive (by have := scratch.nowrap; omega) (O.trans Ot) low, O.trans Ot, T.keeps []⟩

end VG.Proof.RsaKeyGen.X86.WitnessOdd
