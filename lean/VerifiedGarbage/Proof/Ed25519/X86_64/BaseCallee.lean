import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase

/-!
# The base-point multiplications the Ed25519 functions call

`EdBase bs`: `bs` is a body of `vg_ed25519_scalar_base`, correct and constant
time for its contract, and its every instruction keeps `rsp` (the calls need
both) in one level of calls: those of `scalarBase_precomputed` (each field
multiplication) and `scalarBase_ifma`. Public-key derivation and signing are
proven once for any of them.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

class EdBase (bs : Prog isa) : Prop where
  ok : ∀ s, scalarBaseLocal.pre s →
    ∃ t s', Exec isa bs s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s'
  ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub bs
  instrs : bs.allInstrs (fun i => !VG.X86_64.Taint.clobbers i .rsp && !isa.writesSp i) = true
  depth : bs.depth ≤ 1

instance {fld : Arith} [EdArith fld] [X25519.X86_64.DivstepInv] : EdBase (scalarBase_precomputed fld) :=
  ⟨scalarBase_precomputed_ok, scalarBase_precomputed_ct, by fld_lit_decide, by fld_lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_ifma :=
  ⟨Ifma.scalarBase_ifma_ok, Ifma.scalarBase_ifma_ct, by lit_decide, by lit_decide⟩

end VG.Proof.Ed25519.X86_64
