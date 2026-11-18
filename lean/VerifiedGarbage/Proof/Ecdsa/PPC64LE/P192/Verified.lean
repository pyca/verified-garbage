module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Main
meta import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P192
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.P192
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Ecdsa.Generic
meta import VerifiedGarbage.Spec.P192
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdsa.PPC64LE.P192.Contract`, which only this module used -/

section

/-!
# ECDSA signatures over P-192 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P192.inst` for PPC64LE, by name:
`vg_ecdsa_p192_sign(out, d, digest, k, scratch)`, with the arguments in
`r3`–`r7` and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P192

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P192.curve (ofBytes (bytesAt m d 24)) (hashToInt Spec.P192.curve (bytesAt m digest 24))
    (ofBytes (bytesAt m k 24))

def signPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 48⟩
    let d : Region := ⟨s.gpr .r4, 24⟩
    let digest : Region := ⟨s.gpr .r5, 24⟩
    let k : Region := ⟨s.gpr .r6, 24⟩
    let scratch : Region := ⟨s.gpr .r7, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .r3).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 24 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 48 = encode Spec.P192.curve rs
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7

end VG.Proof.Ecdsa.PPC64LE.P192

end

end

/-!
# ECDSA signatures over P-192 on PPC64LE: `Verified`

`sign_ppc`: from `sign_ok`, for P-192's configuration; `sign_ct`: the time
depends only on the pointers (`taint_decide` on the code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.P192

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : signPPC.pre s) : Pre p192 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem post_of {s s' : State} (h : SignPost p192 s s') : signPPC.post s s' := by
  unfold SignPost at h
  show match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 48 = Spec.Ecdsa.encode Spec.P192.curve rs
    | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) 48 = List.replicate 48 0
  revert h
  generalize hq : sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) = q
  rw [show Spec.Ecdsa.signWith p192.C (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r4) p192.C.len))
      (Spec.Ecdsa.hashToInt p192.C (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) p192.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .r6) p192.C.len)) = sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
    from rfl, hq]
  rcases q with _ | rs <;> exact id

theorem sign_ppc (hL : Weierstrass.Law Spec.P192.curve) (s : State) (hs : signPPC.pre s) :
    ∃ t s', Exec isa signP192 s t s' ∧ abiPreserved s s' ∧ signPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok p192_ok (by decide) hL (pre_of hs)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem sign_ct : ConstantTime isa signPPC.pre signPPC.pub signP192 :=
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
  rd := [⟨0x2000, 24⟩, ⟨0x3000, 24⟩, ⟨0x4000, 24⟩]
  wr := [⟨0x1000, 48⟩, ⟨0x8000, 8192⟩]

theorem sign_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified PPC64LE.target signP192 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P192.inst PPC64LE.abi) :=
  Verified.of_correct (sign_ppc hL) sign_ct
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P192.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P192.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P192.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P192.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
        simp only [signPPC, sig, Spec.P192.curve] at h
        revert h
        generalize Spec.Ecdsa.signWith _ _ _ _ = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.P192.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P192.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P192.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
          Spec.P192.curve, Spec.Ecdsa.scratchWords, signPPC, sig, PPC64LE.abi, PPC64LE.argRegs]
          [satState] using satState }

end VG.Proof.Ecdsa.PPC64LE.P192
