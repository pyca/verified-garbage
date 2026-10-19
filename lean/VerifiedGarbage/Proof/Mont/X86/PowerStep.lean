module
public import VerifiedGarbage.Impl.Mont.X86.Power
public import VerifiedGarbage.Proof.Mont.X86.DynamicOps

import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A modular doubling with a public countdown -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

/-- Arithmetic registers and the public loop count. -/
def powerClob : List Reg := [.esi, .eax, .ebx, .ecx, .edx, .ebp]

/-- A modular-doubling iteration, including its loop condition and frame. -/
theorem doubleStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} {m acc out k : Nat} (hm : Modulus M size m s.mem base)
    (hl : OpLay M size acc out out out)
    (ho : out + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ out)
    (hv : wordsVal s.mem base out M.n < m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 k) :
    WP isa (VG.Impl.Mont.X86.Dynamic.doubleStep M acc out) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (k - 1) ∧ t.zf = some (decide (k = 1)) ∧
      wordsVal t.mem base out M.n = 2 * wordsVal s.mem base out M.n % m ∧
      Modulus M size m t.mem base ∧
      Outs base [(out, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem t.mem ∧
      Keeps powerClob s t := by
  unfold VG.Impl.Mont.X86.Dynamic.doubleStep
  refine WP.seq (WP.mono (add_ok hs hm hl (by omega)) fun u ⟨K, V, _⟩ => ?_)
  have count : u.gpr .esi = BitVec.ofNat 32 k := (K.gpr .esi (by decide)).trans hc
  have modU := hm.keep hs hl ho K
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have mt : t.mem = u.mem := ft.mem.trans uv.mem
  have et : t.gpr .esi = BitVec.ofNat 32 (k - 1) := by
    rw [ft.gpr, uv.gpr, count, counter_sub hk32 hk]
  refine ⟨et, ?_, ?_, mt ▸ modU, mt ▸ K.mem,
    ((OpKeep.keeps K).mono (by decide) |>.widen uv.keeps).widen (ft.keeps powerClob)⟩
  · rw [zt, uv.gpr, count, counter_sub hk32 hk, counter_zero hk32 hk]
  · rw [mt, V, Nat.two_mul]

end VG.Proof.Mont.X86.Dynamic
