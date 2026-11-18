module

public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Spec.Gcm.Bitsliced
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# What `vg_ghash`'s `prep` writes, without its algebra

Untrusted: everything here is checked by Lean. `prep` (`Impl/Gcm/RISCV64.lean`)
writes, from the hash subkey at `HP`, the 36 doublewords GHASH's integer
multiplications read at `FP`: class `j` of operand `i`, as
`Spec/Gcm/Bitsliced.lean` states them (`ghashOperand`, `ghashClass`).
`PrepLaw` states it, `Law.lean` proves it; as with `GhashLaw`, code that runs
`prep` outside `vg_ghash` (`vg_aes_gcm_bitslice`) takes it as a hypothesis,
so that it does not import the algebra of `Proof/Gcm/Poly.lean`.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64 VG.Impl.Gcm.RISCV64

/-- The registers `prep` writes. -/
def prepWrites : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .a7, .a6, .s4]

/-- `prep`, from the hash subkey at `HP` (readable) to the 36 doublewords at
`FP` (writable and 8-byte aligned). -/
class PrepLaw : Prop where
  ok : ∀ s, InRegions (s.rd ++ s.wr) (s.gpr HP) 16 →
    (∀ k < 36, (s.gpr FP + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 ∧
      InRegions s.wr (s.gpr FP + BitVec.ofNat 64 (8 * k)) 8) →
    WP isa (.block prep) s fun t =>
      (∀ i < 9, ∀ j < 4, t.mem.readW (s.gpr FP + BitVec.ofNat 64 (8 * (4 * i + j))) 64 =
        Spec.Gcm.ghashOperand (Spec.Gcm.blockAt s.mem (s.gpr HP)) i &&& Spec.Gcm.ghashClass j) ∧
      (∀ r, r ∉ prepWrites → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr FP, 288⟩] s.mem t.mem

end VG.Proof.Gcm.RISCV64
