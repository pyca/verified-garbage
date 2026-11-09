module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Entry
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Entry
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA verification on 32-bit ARM: verified

The entry `vg_mldsa*_verify`, a call of the kernel with no prepared
polynomials (`Entry.lean`), is verified against `verifyContract` with 52
bytes of stack.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa

/-- A state satisfying `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, KeyGen.scrLen p⟩]

theorem verifyE_implies_of {p : Params} (hsat : ∃ s, (verifyContract p Arm.abi entryStack).pre s) :
    (verifyE p false entryStack).Implies (verifyContract p Arm.abi entryStack) where
  pre := by
    intro s h
    sig_pre [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, fun h => absurd h (by decide)⟩
  post := by
    intro s s' _ h
    sig_post [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32]
    exact h
  pub := by
    intro s₁ s₂ _ _ hpub
    sig_pub [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    obtain ⟨e12, e3⟩ := List.append_inj (Proof.MlDsa.KeyGen.leakBytes_inj hl)
      (by simp only [List.length_append, Proof.MlKem.bytesAt_length])
    obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [Proof.MlKem.bytesAt_length])
    exact ⟨hsp, h0, h1, h2, h3, e1, e2, e3⟩
  sat := hsat

theorem verifyE_implies {p : Params} (h3 : Ok3 p) :
    (verifyE p false entryStack).Implies (verifyContract p Arm.abi entryStack) := by
  refine verifyE_implies_of ⟨verifySat p, ?_⟩
  rcases h3 with rfl | rfl | rfl <;>
  sig_sat_check [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySat]

/-- `vg_mldsa*_verify` against the contract `verify_message` calls it with. -/
theorem verifyE_verified {p : Params} (h3 : Ok3 p) :
    Verified Arm.target (verify prims p) (verifyE p false entryStack) :=
  ⟨entry_correct h3 false, entry_ct h3 false, (verifyE_implies h3).sat_left⟩

theorem verify_verified {p : Params} (h3 : Ok3 p) :
    Verified Arm.target (verify prims p) (verifyContract p Arm.abi entryStack) :=
  Verified.of_correct (entry_correct h3 false) (entry_ct h3 false) (verifyE_implies h3)

theorem verify44_verified : Verified Arm.target verify44 (verifyContract mlDsa44 Arm.abi 52) :=
  verify_verified (.inl rfl)

theorem verify65_verified : Verified Arm.target verify65 (verifyContract mlDsa65 Arm.abi 52) :=
  verify_verified (.inr (.inl rfl))

theorem verify87_verified : Verified Arm.target verify87 (verifyContract mlDsa87 Arm.abi 52) :=
  verify_verified (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.Verify
