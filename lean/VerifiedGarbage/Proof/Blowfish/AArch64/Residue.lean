module

public import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public meta import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public import VerifiedGarbage.Impl.Residue.AArch64
public meta import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registration needs it, and it imports the proof of the key schedule, which the residue analysis would otherwise be built with

/-!
# Blowfish on AArch64: the key schedule returns without secret residue

`expandKeyCleared` is `expandKey`, then what it leaves secret cleared: the
registers that held the key and the schedule's last words. The residue
analysis for two runs that leak the same (`RTaintCT.noResidue_of_verified`)
proves it leaves nothing secret: the initial table it reads through
`adrSym`, at an address the two runs need not share, it reads at the same
address in both.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

abbrev expandKeyCleared : Prog isa :=
  Impl.Residue.AArch64.withClears [.x6, .x8, .x13]
    [.v0, .v1, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v28, .v29, .v30, .v31] none Impl.Blowfish.AArch64.expandKey

theorem expandKeyCleared_verified : Verified target expandKeyCleared
    (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts)) :=
  Clears.Verified.withClears_of expandKey_verified
    (fun {s u u'} h hm hx => by
      have hm' : (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts).mem u' =
          (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts).mem u := hm
      have hx' : (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts).ret u' =
          (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts).ret u := hx
      revert h
      simp only [Spec.Blowfish.expandKeyContract, Sig.contract]
      split
      · exact id
      · rw [hm', hx']; exact id)
    (by decide)

theorem expandKeyCleared_noResidue :
    NoResidue expandKeyCleared (Spec.Blowfish.expandKeyContract (AArch64.abi.withConsts Impl.Blowfish.AArch64.initConsts)) 0 :=
  RTaintCT.noResidue_of_verified expandKeyCleared_verified ⟨_, by taint_decide_ct⟩

end VG.Proof.Blowfish.AArch64
