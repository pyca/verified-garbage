module

public import VerifiedGarbage.Proof.EcKey.X86.CombStagesCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
import VerifiedGarbage.Proof.EcKey.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.X86.CombStagesCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.EcKey.X86.CombMain
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFacts
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFinishCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # The public-key comb function, including its static-address prefix -/

@[expose] public section

namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (Args.publicKey)

def pkCombCode : Prog isa := Impl.EcKey.X86.Cfg.publicKeyComb p256Comb
materialize_code pkCombCode

/-- No instruction writes `esp`, and the calls use 24 bytes of stack. -/
theorem pkComb_sp : SpOk pkCombCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem pkComb_body_sp : SpOk (.seq p256Comb.gMul (.seq p256Comb.pPow (Impl.EcKey.X86.Cfg.middle p256Comb))) 24 :=
  (SpOk.right (a := p256Comb.tableAddr) pkComb_sp).right

theorem pkComb_spG : SpOk p256Comb.gMul 24 := pkComb_body_sp.left

theorem pkComb_spP : SpOk p256Comb.pPow p256Comb.stk := pkComb_body_sp.right.left

theorem pkComb_spO : SpOk (pkOps p256Comb) p256Comb.stk := by
  have h := pkComb_body_sp.right.right
  rw [middle_split] at h
  exact (SpOk.split _ _ _ h).1

theorem pkComb_ok (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) {s₀ : State} (hp : PkCombPre p256Comb s₀) :
    WP isa pkCombCode s₀ fun s' => abiPreserved s₀ s' ∧ PkPost p256Comb s₀ s' :=
  publicKeyComb_ok (d := p256d) (p256Comb_ok hI) hC (p256Comb_tables hC) rfl p256Comb_shape
    ⟨pkComb_spG, pkComb_spP, pkComb_spO⟩ hp

theorem pkComb_ct (hC : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    ConstantTime isa (PkCombPre p256Comb) (PkCombPub p256d) pkCombCode :=
  publicKeyComb_ct (d := p256d) (p256Comb_ok hI) hC (p256Comb_tables hC) rfl p256Comb_shape
    (p256Comb_gMul hC hI) p256PkCT pkComb_spG

end VG.Proof.EcKey.X86
