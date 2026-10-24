module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
public import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Contract
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.Main
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Contract
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
meta import VerifiedGarbage.Proof.EcKey.PPC64LE.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# brainpoolP256r1 public keys on PPC64LE: `Verified`

`pk_ppc`: from `publicKey_ok`, for brainpoolP256r1's configuration; `pk_ct`: the
time depends only on `out`, `d` and `scratch` (`taint_decide` on the code's
literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE.BrainpoolP256r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : pkPPC.pre s) : PkPre brainpoolp256r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem post_of {s s' : State} (h : PkPost brainpoolp256r1 s s') : pkPPC.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 65 = List.replicate 65 0
  revert h
  generalize hq : pk s.mem (s.gpr .r4) = q
  rw [show Spec.EcKey.publicKey brainpoolp256r1.C (dk brainpoolp256r1 s) = pk s.mem (s.gpr .r4) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_ppc (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (s : State) (hs : pkPPC.pre s) :
    ∃ t s', Exec isa Impl.EcKey.PPC64LE.publicKeyBrainpoolP256r1 s t s' ∧ abiPreserved s s' ∧ pkPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := publicKey_ok brainpoolp256r1_ok (by decide) hL (pre_of hs)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem pk_ct : ConstantTime isa pkPPC.pre pkPPC.pub Impl.EcKey.PPC64LE.publicKeyBrainpoolP256r1 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩]

theorem pk_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified PPC64LE.target Impl.EcKey.PPC64LE.publicKeyBrainpoolP256r1 (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract PPC64LE.abi) :=
  Verified.of_correct (pk_ppc hL) pk_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [pkPPC, pk, Spec.BrainpoolP256r1.curve] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, pkPPC, pk, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

end VG.Proof.EcKey.PPC64LE.BrainpoolP256r1
