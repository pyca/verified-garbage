module
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks

import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase

/-!
# RSASSA-PSS verification on x86-64: the taint checks of the pieces that do
not depend on the hash function
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The first block of `anyArgs`. -/
def any1 : List Instr :=
  [.mov .rax (.mem (arg 1)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)), .alu .test .rax (.reg .rax)]

/-- The prologue of `shift`. -/
def shiftPro : List Instr :=
  [.mov .rax (.mem (sp sPos)), .alu .add .rax (.imm 1), .store (sp sA) .rax, .mov32 .rax (.imm 1),
    .store (sp sD) .rax, .mov32 .rax (.imm 10), .store (sp sJ) .rax]

theorem anyArgs_eq : anyArgs = .seq (.block any1)
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)])) := rfl

theorem shift_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) :
    shift H = .seq (.block shiftPro) (.loop (.seq (shiftPass H) (.block nextPass)) .ne) := rfl

/-- The checks. -/
structure VFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (verifyPrologue ++ n0)) hc).isSome
    = true
  fail : ∃ hc, (taint.check (pT 1 [] []) verifyFail hc).isSome = true
  any1 : ∃ hc, (taint.check (pT 1 [] []) (.block any1) hc).isSome = true
  anyT : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))]) hc).isSome = true
  anyE : ∃ hc, (taint.check (pT 1 [] [])
    (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)]) hc).isSome = true
  dbPub : ∃ hc, (taint.check (pT 1 [17, 18, 19, 20, 21, 22, 26, 38] [.rax])
    (.seq (.block dbSlots) (.block pubArgs)) hc).isSome = true
  acc0 : ∃ hc, (taint.check (pT 1 [17, 21, 23, 25, 26] []) (.block acc0) hc).isSome = true
  clearTop : ∃ hc, (taint.check (pT 1 [23] []) (.block clearTop) hc).isSome = true
  posScan : ∃ hc, (taint.check (pT 1 [23, 24] []) posScan hc).isSome = true
  shiftPro : ∃ hc, (taint.check (pT 1 [] []) (.block shiftPro) hc).isSome = true
  nextPass : ∃ hc, (taint.check (pT 1 [] []) (.block nextPass) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 1 [] []) (.block restoreRegs) hc).isSome = true

theorem vFixed : VFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64
