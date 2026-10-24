module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Ed448.WnafWide.Word
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! One bounded arithmetic step of the public signed recoder. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide
open VG.Proof.X448.AArch64 (Keeps)

private theorem half_enc (wide : Bool) : half wide < 4096 := by cases wide <;> decide
private theorem radix_enc (wide : Bool) : radix wide < 4096 := by cases wide <;> decide
private theorem half_word (wide : Bool) :
    (BitVec.ofNat 16 (half wide)).setWidth 64 = BitVec.ofNat 64 (half wide) := by cases wide <;> rfl
private theorem mask_word (wide : Bool) :
    (BitVec.ofNat 16 (radix wide-1)).setWidth 64 = BitVec.ofNat 64 (radix wide-1) := by cases wide <;> rfl

theorem digitStep_ok (wide : Bool) {s : State} {bits c : Nat}
    (hb : bits < radix wide) (hc : c ≤ radix wide)
    (h4 : s.gpr .x4 = BitVec.ofNat 64 bits)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 (bits%2))
    (h6 : s.gpr .x6 = BitVec.ofNat 64 c) :
    WP isa (.block (digitStep wide)) s fun u =>
      u.gpr .x7 = BitVec.ofInt 64 (localDigit wide bits c) ∧
      u.gpr .x6 = BitVec.ofNat 64 (carryNext wide bits c) ∧
      Keeps [.x4,.x6,.x7,.x8,.x9] s u ∧ u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [digitStep, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    half_enc, radix_enc, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, RegUpd.zf_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    CondCode.holds, h4, h5, h6, half_word, mask_word, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · have he := WnafWide.rawDigit_ok wide hb hc
    simpa only [WnafWide.rawDigit, BitVec.ofNat_add, show (BitVec.setWidth 64 (1 : BitVec 16)) = 1 from rfl, show (BitVec.setWidth 64 (0 : BitVec 16)) = 0 from rfl] using he
  · have he := WnafWide.rawCarry_ok wide hb hc
    simpa only [WnafWide.rawDigit, BitVec.ofNat_add, show (BitVec.setWidth 64 (1 : BitVec 16)) = 1 from rfl, show (BitVec.setWidth 64 (0 : BitVec 16)) = 0 from rfl] using he
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Ed448.AArch64.Sparse
