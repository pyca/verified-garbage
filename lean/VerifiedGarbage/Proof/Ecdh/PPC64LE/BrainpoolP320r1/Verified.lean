module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1.Window
import VerifiedGarbage.Proof.Ecdh.PPC64LE.VerifiedAll
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.Spec.BrainpoolP320r1
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Ecdh
meta import VerifiedGarbage.Spec.BrainpoolP320r1
meta import VerifiedGarbage.TCB.PPC64LE.Isa
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ecdh.PPC64LE.BrainpoolP320r1.Contract`, which only this module used -/

section

/-!
# ECDH over brainpoolP320r1 on PPC64LE: the contract the proof is written against

The facts of `Spec.Ecdh.Instance.exchangeContract` for brainpoolP320r1 on PPC64LE, by
name: `vg_ecdh_brainpoolp320r1(out, d, peer, scratch)`, with the arguments in `r3`–`r6`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.BrainpoolP320r1

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP320r1.curve (ofBytes (bytesAt m d 40)) (bytesAt m peer 81)

def ecdhPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 40⟩
    let d : Region := ⟨s.gpr .r4, 40⟩
    let peer : Region := ⟨s.gpr .r5, 81⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r3).toNat + 40 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 40 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 81 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 40 = z
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 40 = List.replicate 40 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdh.PPC64LE.BrainpoolP320r1

end

end

/-!
# ECDH over brainpoolP320r1 on PPC64LE: `Verified`

`win_mulPowOk`: `[d]P` by the four-bit windows
for any `a` (`Proof/Ecdsa/PPC64LE/BrainpoolP320r1/Window.lean`), then `Z^(p-2)` by its addition chain, leaves
what ECDH's last stage needs (`LadPost`),
by `Win.mulPowOk` (`Proof/Ecdh/PPC64LE/VerifiedAll.lean`) on the curve's kit.
`ecdh_ppc`: from `exchangeWith_ok`,
for brainpoolP320r1's configuration; `ecdh_ct`: the
time depends only on `out`, `d`, `peer` and `scratch` (`taint_decide` on the
code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.BrainpoolP320r1

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : ecdhPPC.pre s) : EPre brainpoolp320r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost brainpoolp320r1 s s') : ecdhPPC.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 40 = z
    | none => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 40 = List.replicate 40 0
  revert h
  generalize hq : ex s.mem (s.gpr .r4) (s.gpr .r5) = q
  rw [show Spec.Ecdh.exchange brainpoolp320r1.C (dk brainpoolp320r1 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) (1 + 2 * brainpoolp320r1.C.len)) = ex s.mem (s.gpr .r4) (s.gpr .r5) from rfl, hq]
  rcases q with _ | z <;> exact id

/-- The windows, then the addition chain, meet `MulPowOk`. -/
theorem win_mulPowOk (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (s₀ : State) :
    MulPowOk brainpoolp320r1 s₀ (WindowA.Cfg.mul brainpoolp320r1 PX PY B3P) :=
  Win.mulPowOk Proof.Ecdsa.PPC64LE.Window.BrainpoolP320r1.kit (.inr ⟨rfl, rfl⟩) (by decide) hL s₀

theorem ecdh_ppc (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) (s : State) (hs : ecdhPPC.pre s) :
    ∃ t s', Exec isa exchangeBrainpoolP320r1 s t s' ∧ abiPreserved s s' ∧ ecdhPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := exchangeWith_ok brainpoolp320r1_ok hL (pre_of hs) (win_mulPowOk hL s)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhPPC.pre ecdhPPC.pub exchangeBrainpoolP320r1 :=
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
  rd := [⟨0x2000, 40⟩, ⟨0x3000, 81⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Verified PPC64LE.target exchangeBrainpoolP320r1 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP320r1.inst PPC64LE.abi) :=
  Verified.of_correct (ecdh_ppc hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP320r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP320r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [ecdhPPC, ex, Spec.BrainpoolP320r1.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP320r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP320r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP320r1.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

end VG.Proof.Ecdh.PPC64LE.BrainpoolP320r1
