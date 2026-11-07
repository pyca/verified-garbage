module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Correct
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Entry
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on ARMv7: verified

The entry `vg_mldsa*_sign`, a call of the kernel with no prepared
polynomials (`Entry.lean`), is verified against `signContract`, including
the first failing polynomial permitted by its rejection leakage.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying `signContract`'s precondition: `scratch` at `0x10000`, on the stack. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 0x3100 | .r3 => 0x4000
    | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x80002 then 1 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩, ⟨0x80000, 4⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signE_implies_of {p : Params} (hsat : ∃ s, (signContract p Arm.abi entryStack).pre s) :
    (signE p false entryStack).Implies (signContract p Arm.abi entryStack) where
  pre := by
    intro s h
    sig_pre [signContract, signSig, signE, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, hsp4, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, -, n1, n2, n3, n4, n5⟩ := h
    simp only [Nat.mul_comm (scratchWords p) 8] at hwr d2 d4 d6 d7 d9 k5 n5
    exact ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp, hsp4,
      fun h => absurd h (by decide)⟩
  post := by
    intro s s' _ h
    sig_post [signContract, signSig, signE, signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32]
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContract, signSig, signE, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, hb, h0, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hsp, hb⟩
  sat := hsat

theorem signE_implies {p : Params} (h3 : Ok3 p) :
    (signE p false entryStack).Implies (signContract p Arm.abi entryStack) := by
  refine signE_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using signSat mlDsa44
  · sig_implies_sat [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using signSat mlDsa65
  · sig_implies_sat [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using signSat mlDsa87

/-- `vg_mldsa*_sign` against the contract `sign_message` calls it with. -/
theorem signE_verified {p : Params} (h3 : Ok3 p) :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims p) (signE p false entryStack) :=
  ⟨entry_correct h3 false, entry_ct h3 false, (signE_implies h3).sat_left⟩

theorem sign_verified {p : Params} (h3 : Ok3 p) :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims p) (signContract p Arm.abi entryStack) :=
  Verified.of_correct (entry_correct h3 false) (entry_ct h3 false) (signE_implies h3)

theorem sign44_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims mlDsa44) (signContract mlDsa44 Arm.abi entryStack) :=
  sign_verified (.inl rfl)

theorem sign65_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims mlDsa65) (signContract mlDsa65 Arm.abi entryStack) :=
  sign_verified (.inr (.inl rfl))

theorem sign87_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims mlDsa87) (signContract mlDsa87 Arm.abi entryStack) :=
  sign_verified (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.Sign
