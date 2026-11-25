module

public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Spec.Gcm.Bitsliced
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# What `prep` writes

Untrusted: everything here is checked by Lean. `prep`
(`Impl/Gcm/RISCV64.lean`) writes the key's 36 doublewords
(`Spec/Gcm/Bitsliced.lean`). `PrepLaw` says so, and `Law.lean` proves it: code
that also runs `prep` takes it as a hypothesis, not to import its algebra.
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64

open VG VG.RISCV64
open VG.Impl.Gcm.RISCV64 (HP FP prep)

/-- The registers `prep` writes. -/
def prepWrites : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .a7]

class PrepLaw : Prop where
  ok : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr HP) 16 →
    (∀ k < 36, (s.gpr FP + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 ∧
      InRegions s.wr (s.gpr FP + BitVec.ofNat 64 (8 * k)) 8) →
    WP isa (.block prep) s fun t =>
      (∀ i < 9, ∀ j < 4, t.mem.readW (s.gpr FP + BitVec.ofNat 64 (8 * (4 * i + j))) 64 =
        Spec.Gcm.ghashOperand (Spec.Gcm.blockAt s.mem (s.gpr HP)) i &&& Spec.Gcm.ghashClass j) ∧
      (∀ r, r ∉ prepWrites → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr FP, 288⟩] s.mem t.mem

end VG.Proof.Gcm.RISCV64
