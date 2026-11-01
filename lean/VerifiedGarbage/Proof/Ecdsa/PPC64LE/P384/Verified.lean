module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Contract
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over P-384 on PPC64LE: `Verified`

`sign_ppc`: from `sign_ok`, for P-384's configuration; `sign_ct`: the time
depends only on the pointers (`taint_decide` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P384

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : signPPC.pre s) : Pre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost p384 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 96 = Spec.Ecdsa.encode Spec.P384.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 96 = List.replicate 96 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith p384.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) p384.C.len))
      (Spec.Ecdsa.hashToInt p384.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) p384.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) p384.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

theorem sign_ppc (hL : Weierstrass.Law Spec.P384.curve) (s : State) (hs : signPPC.pre s) :
    ∃ t s', Exec isa signP384 s t s' ∧ abiPreserved s s' ∧ signPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok p384_ok (by decide) hL (pre_of hs)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem sign_ct : ConstantTime isa signPPC.pre signPPC.pub signP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5, h6, h7⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 48⟩, ⟨0x4000, 48⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x8000, 8192⟩]

theorem sign_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified PPC64LE.target signP384 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst PPC64LE.abi) :=
  Verified.of_correct (sign_ppc hL) sign_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.P384.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P384.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }

end VG.Proof.Ecdsa.PPC64LE.P384
