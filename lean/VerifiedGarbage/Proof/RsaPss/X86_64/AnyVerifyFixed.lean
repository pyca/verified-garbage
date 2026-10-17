module

public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
meta import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: the taint checks of the new pieces

The prologue, the checks of the encoding's length and of the salt's with
`hLen` from its slot, `anyArgs`' first block (its arguments moved) and the
load of the digest's hash function's selector do not depend on the hash
functions: they are checked once.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64

/-- The first block of `anyArgs`. -/
def any1A : List Instr :=
  [.mov .rax (.mem (arg 3)), .store (sp sSlen) .rax, .mov32 .rax (.mem (arg 2)), .alu .test .rax (.reg .rax)]

theorem anyArgs_eqA : AnyHash.anyArgs = .seq (.block any1A)
    (.ite .e (.block [.mov32 .rax (.imm 0), .store (sp sAny) .rax, .mov .rdx (.mem (sp sSlen))])
      (.block [.mov32 .rax (.imm 1), .store (sp sAny) .rax, .mov32 .rdx (.imm 0)])) := rfl

/-- The checks. -/
structure VFixedA : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    (.block (AnyHash.verifyPrologue ++ n0)) hc).isSome = true
  emLen : ∃ hc, (taint.check (pT 1 [15, 17] [.rax]) (.seq (.block smear) emLenAny) hc).isSome = true
  any1 : ∃ hc, (taint.check (pT 1 [] []) (.block any1A) hc).isSome = true
  salt : ∃ hc, (taint.check (pT 1 [15, 17, 26] [.rdx]) (.block (([.mov .rax (.mem (sp sK)),
    .mov .r8 (.mem (sp sLo)), .alu .sub .rax (.reg .r8)] : List Instr) ++ saltFitsAny)) hc).isSome = true
  selH : ∃ hc, (taint.check (pT 1 [47] []) (.block [.mov .rax (.mem (sp sHsel))]) hc).isSome = true

theorem vFixedA : VFixedA :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64.Any
