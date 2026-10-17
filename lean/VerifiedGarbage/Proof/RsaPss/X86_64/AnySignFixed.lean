module

public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
meta import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSASSA-PSS signing with the hash functions as arguments on x86-64: the taint checks of the new pieces

The prologue, the checks of the encoding's length with `hLen` from its slot
and the load of the digest's hash function's selector do not depend on the
hash functions: they are checked once.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.RsaPss.X86_64

/-- The checks. -/
structure SFixedA : Prop where
  pro : ∃ hc, (taint.check (pT 2 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (AnyHash.signPrologue ++ n0)) hc).isSome
    = true
  emLen : ∃ hc, (taint.check (pT 2 [15, 17] [.rax]) (.seq (.block smear) emLenAny) hc).isSome = true
  salt : ∃ hc, (taint.check (pT 2 [15, 40] [.rax])
    (.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFitsAny)) hc).isSome = true
  selH : ∃ hc, (taint.check (pT 2 [47] []) (.block [.mov .rax (.mem (sp sHsel))]) hc).isSome = true

theorem sFixedA : SFixedA :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64.Any
