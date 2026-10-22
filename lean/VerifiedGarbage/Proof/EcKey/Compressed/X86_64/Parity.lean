module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Tag
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! # Select and check the canonical root's parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

private theorem xor_low_mask (x y : BitVec 64) :
    0 - ((x ^^^ y) &&& 1) = mask (x.toNat % 2 ≠ y.toNat % 2) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, mask]

theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.X86_64.QY + 8 ≤ size) (ht : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.parityMask c)) s fun s' =>
      s'.gpr .rcx = mask (sv c base s Impl.Ecdh.X86_64.QY % 2 ≠
        (word s.mem base (c.sl D)).toNat % 2) ∧ Keeps [.rdx, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.X86_64.parityMask, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, readSrc32, execAlu, Option.map_some, Option.bind_some, State.load64,
    State.setReg32, ea_sc, hs.rdi, ld_sc hs hy, ld_sc hs ht,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change (0 : BitVec 64) - ((word s.mem base (c.sl Impl.Ecdh.X86_64.QY) ^^^
      word s.mem base (c.sl D)) &&& 1) = _
    rw [xor_low_mask, slot_parity _ _ _ _ hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .rcx = mask P) :
    WP isa (.block [.mov .rdx (.reg .rcx), .alu .xor .rdx (.imm (-1))]) s fun s' =>
      s'.gpr .rdx = mask (¬ P) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [h]
    by_cases hp : P <;> simp [mask, hp]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.EcKey.Compressed.X86_64
