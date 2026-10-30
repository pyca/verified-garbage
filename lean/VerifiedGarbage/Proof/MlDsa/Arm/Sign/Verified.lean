module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Correct
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on ARMv7: verified

`vg_mldsa{44,65,87}_sign` (`sign prims p`) is verified against
`signContractT`: `signContract` with `signLeakT`
(`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`, which tags what each iteration of the loop leaks after its `c̃` with the
check that rejected it. The contract's `signLeak` also says at which
polynomial; two runs that agree on it agree on `signLeakT`
(`signContract_pubT`), so `signContractT_narrow` moves the proof to
`signContract`, against which `sign*_verified'` state it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `signContract`, with `signLeakT` for `signLeak`. -/
def signContractT (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeakT p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

/-- A state satisfying `signContractT`'s precondition: `scratch` at `0x10000`, on the stack. -/
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

theorem signK_implies_of {p : Params} (hsat : ∃ s, (signContractT p Arm.abi signStack).pre s) :
    (signK p signStack).Implies (signContractT p Arm.abi signStack) where
  pre := by
    intro s h
    sig_pre [signContractT, signSig, signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, -, hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, -, n1, n2, n3, n4, n5⟩ := h
    simp only [Nat.mul_comm (scratchWords p) 8] at hwr d2 d4 d6 d7 d9 k5 n5
    exact ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩
  post := by
    intro s s' _ h
    sig_post [signContractT, signSig, signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32]
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [signContractT, signSig, signK, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, hb, h0, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : Ok3 p) :
    (signK p signStack).Implies (signContractT p Arm.abi signStack) := by
  refine signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [signContractT, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using signSat mlDsa44
  · sig_implies_sat [signContractT, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using signSat mlDsa65
  · sig_implies_sat [signContractT, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] [signSat]
      using signSat mlDsa87

theorem sign_verified {p : Params} (h3 : Ok3 p) :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims p) (signContractT p Arm.abi signStack) :=
  Verified.of_correct (sign_correct prims_ok h3) (sign_ct prims_ok h3) (signK_implies h3)

/-- From `signContractT` to `signContract`: two runs that agree on what
`signContract` takes as public agree on what `signContractT` does
(`signContract_pubT`). -/
theorem signContractT_narrow {c : Prog Arm.target.isa} {p : Params} {stack : Nat}
    (h : Verified Arm.target c (signContractT p Arm.abi stack)) :
    Verified Arm.target c (signContract p Arm.abi stack) :=
  h.of_narrow id (fun _ s => s) (fun _ h => h) (fun _ _ _ _ e => e) (fun _ _ _ _ _ ha hq => ⟨ha, hq⟩)
    (fun _ _ _ _ hp => Sign.signContract_pubT hp) h.2.2

theorem sign44_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims mlDsa44) (signContract mlDsa44 Arm.abi signStack) :=
  signContractT_narrow <| sign_verified (.inl rfl)

theorem sign65_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims mlDsa65) (signContract mlDsa65 Arm.abi signStack) :=
  signContractT_narrow <| sign_verified (.inr (.inl rfl))

theorem sign87_verified' :
    Verified Arm.target (Impl.MlDsa.Arm.Sign.sign prims mlDsa87) (signContract mlDsa87 Arm.abi signStack) :=
  signContractT_narrow <| sign_verified (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.Sign
