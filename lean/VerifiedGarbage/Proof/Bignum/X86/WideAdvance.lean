module

public import VerifiedGarbage.Proof.Mont.X86.Loop

/-! # Advance a public schoolbook row counter -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem wideAdvance_ok {s : State} {i N : Nat}
    (hi : i < N) (hN : 4 * N < 2 ^ 32)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) :
    WP isa (.block [.alu .add .ebp (.imm 4), .mov .edx (.reg .edi),
      .alu .add .edx (.imm (BitVec.ofNat 32 (4 * N))), .alu .cmp .ebp (.reg .edx)]) s fun t =>
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = N)) ∧ t.mem = s.mem ∧ Keeps [.ebp, .edx] s t := by
  refine wp_addS rfl fun u U _ => ?_
  refine wp_movS rfl fun v V _ => ?_
  refine wp_addS rfl fun w W _ => ?_
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  have K : Keeps [.ebp, .edx] s t := ((U.keeps.mono (by decide)).widen V.keeps |>.widen W.keeps).trans (T.keeps _)
  have P : t.gpr .ebp = s.gpr .ebp + 4 := by
    rw [T.gpr, W.other _ (by decide), V.other _ (by decide), U.gpr]
  have Q : w.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (4 * N) := by
    rw [W.gpr, V.gpr, U.other _ (by decide)]
  have Pw : w.gpr .ebp = s.gpr .ebp + 4 := by
    rw [W.other _ (by decide), V.other _ (by decide), U.gpr]
  refine ⟨?_, ?_, T.mem.trans (W.mem.trans (V.mem.trans U.mem)), K⟩
  · rw [P, K.1 _ (by decide), hp, row_ebp]
  · rw [Z, Pw, Q, hp, row_zf _ hi hN]

end VG.Proof.Bignum.X86
