module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Contract
public import VerifiedGarbage.Impl.Ecdh.P256.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Contract
meta import VerifiedGarbage.Impl.Ecdh.P256.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over P-256 on PPC64LE: `Verified`

`ecdh_ppc`: from `exchange_ok`, for P-256's configuration; `ecdh_ct`: the
time depends only on `out`, `d`, `peer` and `scratch` (`taint_decide` on the
code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : ecdhPPC.pre s) : EPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p256 s s') : ecdhPPC.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 32 = z
    | none => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 32 = List.replicate 32 0
  revert h
  generalize hq : ex s.mem (s.gpr .r4) (s.gpr .r5) = q
  rw [show Spec.Ecdh.exchange p256.C (dk p256 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) (1 + 2 * p256.C.len)) = ex s.mem (s.gpr .r4) (s.gpr .r5) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_ppc (hL : Weierstrass.Law Spec.P256.curve) (s : State) (hs : ecdhPPC.pre s) :
    ∃ t s', Exec isa exchangeP256 s t s' ∧ abiPreserved s s' ∧ ecdhPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := exchange_ok p256_ok (by decide) (by decide) hL (pre_of hs)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhPPC.pre ecdhPPC.pub exchangeP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5, h6⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 65⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified PPC64LE.target exchangeP256 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst PPC64LE.abi) :=
  Verified.of_correct (ecdh_ppc hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [ecdhPPC, ex, Spec.P256.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

end VG.Proof.Ecdh.PPC64LE
