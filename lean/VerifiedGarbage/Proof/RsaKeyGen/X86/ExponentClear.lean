module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Zero top sentinels supply the incoming bits for fixed masked halving -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem clearTops_ok {s : State} {base : Addr} {size n src out : Nat} (scratch : Scr s base size)
    (srcFit : src + 4 * (n + 1) ≤ size) (outFit : out + 4 * (n + 1) ≤ size)
    (sep : src + 4 * (n + 1) ≤ out) :
    WP isa (.block (clearTops n src out)) s fun t =>
      w32 t.mem base (src + 4 * n) = 0 ∧ w32 t.mem base (out + 4 * n) = 0 ∧
      t.gpr .ecx = cmask true ∧
      Outs base [(src + 4 * n, 4), (out + 4 * n, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold clearTops
  refine wp_movS rfl fun a A _ => ?_
  have Sa := scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by omega)) (Sa.write (by omega)) fun b B => ?_
  have Kb : Keeps [.eax] s b := A.keeps.widen (B.keeps [])
  have Sb := scratch.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write (by omega)) fun c C => wp_movS rfl fun t T _ => WP.block_nil ?_
  have Mb : b.mem = s.mem.writeW (off base (src + 4 * n)) (0#32) := by
    rw [B.mem, A.mem, A.gpr]
    rfl
  have Mc : c.mem = b.mem.writeW (off base (out + 4 * n)) (0#32) := by
    rw [C.mem, (B.keeps []).1 .eax (by decide), A.gpr]
    rfl
  have Os : Outside base (src + 4 * n) 4 s.mem b.mem := by
    rw [Mb]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  have Oo : Outside base (out + 4 * n) 4 b.mem c.mem := by
    rw [Mc]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)
  refine ⟨?_, ?_, T.gpr, ?_, ((Kb.mono (by decide : ∀ r : Reg, r ∈ [.eax] → r ∈ [.eax, .ecx])).widen (C.keeps [])).widen T.keeps⟩
  · rw [T.mem, Oo.w32 (by omega) (by have := scratch.nowrap; omega), Mb, w32_write_self]
    rfl
  · rw [T.mem, Mc, w32_write_self]
    rfl
  · rw [T.mem]
    exact (Outs.of_outside Os (List.mem_cons_self ..)).trans
      (Outs.of_outside Oo (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

end VG.Proof.RsaKeyGen.X86.Exponent
