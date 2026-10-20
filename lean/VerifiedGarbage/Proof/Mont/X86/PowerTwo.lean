module
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Montgomery-domain setup using public modular doublings -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

/-- `powerTwo` computes powers of two without a division instruction or a
special-form modulus. In particular, `bits = 128*n` prepares Montgomery R². -/
theorem powerTwo_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} {m acc out bits : Nat} (hm : Modulus M size m s.mem base)
    (hl : OpLay M size acc out out out)
    (ho : out + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ out)
    (hm1 : 1 < m) (hb : 0 < bits) (hb32 : bits < 2 ^ 32) :
    WP isa (VG.Impl.Mont.X86.Dynamic.powerTwo M acc out bits) s fun t =>
      wordsVal t.mem base out M.n = 2 ^ bits % m ∧ wordsVal t.mem base out M.n < m ∧
      Modulus M size m t.mem base ∧
      Outs base [(out, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem t.mem ∧
      Keeps powerClob s t := by
  unfold VG.Impl.Mont.X86.Dynamic.powerTwo
  refine WP.seq (WP.mono (one_ok hs hm.n0 hl.o_le) fun u ⟨O, V, K⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v uv _ => WP.block_nil ?_)
  have kv : Keeps powerClob s v := (K.mono (by decide)).widen uv.keeps
  have hv := hs.of_keeps kv (by decide)
  have vv : wordsVal v.mem base out M.n = 1 := by rw [uv.mem, V]
  have mv : Modulus M size m v.mem base := by
    refine ⟨hm.n0, hm.mo, hm.tmp, hm.sep, ?_⟩
    rw [uv.mem, wordsVal_eq_val32, O.val32 (by omega) (by have := hs.nowrap; have := hm.mo; omega),
      ← wordsVal_eq_val32, hm.val]
  refine WP.mono (doubleLoop_ok hv mv hl ho (by rw [vv]; exact hm1) hb hb32 uv.gpr) fun t I => ?_
  refine ⟨?_, I.lt, I.modulus, ?_, kv.trans I.keeps⟩
  · rw [I.value, vv, Nat.mul_one]
  · have ov : Outside base out (8 * M.n) s.mem v.mem := uv.mem ▸ O
    exact (Outs.of_outside ov (by simp)).trans I.mem

end VG.Proof.Mont.X86.Dynamic
