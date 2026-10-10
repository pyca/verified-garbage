import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx

/-!
# The base-point multiplications the Ed25519 functions call

`EdBase bs`: `bs` is a body of `vg_ed25519_scalar_base`, correct and constant
time for its contract (for states whose buffers are apart from the 8 bytes below
`rsp`, where its call of `vg_gf25519_r64_invert` stores its return address),
and its every instruction keeps `rsp` (the calls need both) in one level of
calls: those of `scalarBase_precomputed` (each field
multiplication), `scalarBase_adx` and `scalarBase_ifma`. Public-key derivation and signing are
proven once for any of them.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

/-- The 8 bytes below `rsp = B + 8`, where a call from it stores its return address. -/
theorem hole_add8 (B : Addr) : hole (B + BitVec.ofNat 64 8) = ⟨B, 8⟩ := by
  simp only [hole]
  rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.add_sub_cancel]

class EdBase (bs : Prog isa) : Prop where
  ok : ∀ s, scalarBaseLocal.clear.pre s →
    ∃ t s', Exec isa bs s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s'
  ct : ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub bs
  instrs : bs.allInstrs (fun i => !VG.X86_64.Taint.clobbers i .rsp && !isa.writesSp i) = true
  depth : bs.depth ≤ 1

instance {fld : Arith} [EdArith fld] [X25519.X86_64.DivstepInv] : EdBase (scalarBase_precomputed fld) :=
  ⟨scalarBase_precomputed_ok, scalarBase_precomputed_ctC, by fld_lit_decide, by fld_lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_adx :=
  ⟨scalarBase_adx_ok, scalarBase_adx_ct, by lit_decide, by lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_ifma :=
  ⟨Ifma.scalarBase_ifma_ok, Ifma.scalarBase_ifma_ct, by lit_decide, by lit_decide⟩

end VG.Proof.Ed25519.X86_64
