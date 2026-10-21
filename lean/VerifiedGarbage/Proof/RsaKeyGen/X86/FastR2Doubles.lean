module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Seed
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

/-! # The short doubling phase computes 2^n R modulo the candidate -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont VG.Impl.RsaKeyGen.X86.FastR2

theorem doubles_ok {s : State} {base : Addr} {size m acc out : Nat} {M : Mod}
    (scratch : Scr s base size) (modulus : Modulus M size m s.mem base)
    (layout : OpLay M size acc out out out)
    (apart : out + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ out)
    (bound : M.n ≤ 64) (odd : m % 2 = 1) (top : 2 ^ (64 * M.n - 1) ≤ m) :
    WP isa (doubles M acc out) s fun t =>
      wordsVal t.mem base out M.n = 2 ^ M.n * 2 ^ (64 * M.n) % m ∧
      Modulus M size m t.mem base ∧
      Outs base [(out, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem t.mem ∧
      Keeps powerClob s t := by
  refine WP.seq (WP.mono (seed_ok scratch modulus.n0 layout.o_le) fun a ⟨Va, Oa, Ka⟩ => ?_)
  refine WP.seq (wp_movS rfl fun b B _ => WP.block_nil ?_)
  have Kb : Keeps powerClob s b := (Ka.mono (by decide)).widen B.keeps
  have Mb : Modulus M size m b.mem base := by
    refine ⟨modulus.n0, modulus.mo, modulus.tmp, modulus.sep, ?_⟩
    rw [B.mem, wordsVal_eq_val32,
      Oa.val32 (by omega) (by have := scratch.nowrap; have := modulus.mo; omega), ← wordsVal_eq_val32]
    exact modulus.val
  refine WP.mono (doubleLoop_ok (scratch.of_keeps Kb (by decide)) Mb layout apart
    (by rw [B.mem, Va]; exact seed_lt modulus.n0 odd top) (by omega) (by omega) B.gpr)
    fun t T => ?_
  refine ⟨?_, T.modulus, ?_, Kb.trans T.keeps⟩
  · rw [T.value, B.mem, Va, ← Nat.pow_add, ← Nat.pow_add]
    have npos := modulus.n0
    rw [show M.n + 1 + (64 * M.n - 1) = M.n + 64 * M.n by omega]
  · have Oab : Outside base out (8 * M.n) s.mem b.mem := B.mem ▸ Oa
    exact (Outs.of_outside Oab (List.mem_cons_self ..)).trans T.mem

end VG.Proof.RsaKeyGen.X86.FastR2
