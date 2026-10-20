module

import VerifiedGarbage.Proof.RsaPss.Arm.VfMain
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
public import VerifiedGarbage.Proof.RsaPss.Arm.VfChk
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`), the result as the shared
contract states it, and a state that meets it (`verify_sat_<hash>`):
`vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling a precomputed public
operation `c`, is verified (`verify_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm

variable (h : PssHash)

/-- The code, calling `c`. -/
abbrev verifyCode (c : PdImpl) : Prog isa := verifyPrecomputed h.H c.name c.code

theorem entered_state {s : State} (hs : (spec h.G).pre s) :
    S h (ep s) (entered frameBytes s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  rw [h.glen] at hi
  exact ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (hs : (spec h.G).pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, reduceClassify,
    Loc.val] at hs
  exact hs.1

theorem code_ok (c : PdImpl) {s : State} (hs : (spec h.G).pre s) :
    WP isa (verifyCode h c) s fun t => abiPreserved s t ∧ (spec h.G).post s t := by
  have hsp := spec_sp h hs
  have hin := in_of_pre hs
  rw [h.glen] at hin
  have st := entered_state h hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hsp; omega
  refine WP.mono (wrap_ok (by decide) (by omega) (W := ((ep s).lay h.D).W)
    (Q := fun r _ => Res h (ep s) (entered frameBytes s) r) (fun r hr => ?_)
    (WP.mono ((body_vq h (ep s) c).1 _ _ st) fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 36) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).DIG h.D, (ep s).SIG, (ep s).PRE]) (rw := [(ep s).SCR]) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
      reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).DIG h.D, (ep s).SIG, (ep s).PRE]) =>
      entered_ro (F := frameBytes) (A := 36) (argv := (ep s).argv) (rw := [(ep s).SCR]) hin.ok hsp' hR
    have hD : digB h (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) h.D :=
      ro (R := (ep s).DIG h.D) (by simp)
    have hG : sigB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1))
        (s.gpr .r1).toNat := by
      have e : Spec.Rsa.bytesAt (entered frameBytes s).mem (State.addr (stackArg s 1)) (ep s).gl =
          Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (ep s).gl := ro (R := (ep s).SIG) (by simp)
      rw [hin.glK] at e
      exact e
    unfold Res at res
    rw [hD, hG] at res
    rw [h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, reduceClassify,
    Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hp
  obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h1, h3])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [bytesAt_length, h1])
  have hw' := map_toNat_inj hw
  simp only [ep]
  rw [hsp, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8]
  rw [h0, h1] at hn
  rw [h2, h3] at he
  rw [a7, a8] at hw'
  rw [show State.addr (s₂.gpr .r0) = BitVec.setWidth 64 (s₂.gpr .r0) from rfl, hn,
    show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, he,
    show State.addr (stackArg s₂ 7) = BitVec.setWidth 64 (stackArg s₂ 7) from rfl, hw']

theorem code_ct (c : PdImpl) : ConstantTime isa (spec h.G).pre (spec h.G).pub (verifyCode h c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs,
      reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; have := spec_sp h h₁; simp only [stackBytes] at this; omega) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vq h (ep s₁) c).2.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h h₁, by rw [hep]; exact entered_state h h₂⟩

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling `c`, meets the shared contract
(satisfiable, `VfSat.lean`). -/
theorem verify_verified (hsat : ∃ s, (spec h.G).pre s) (c : PdImpl) :
    Verified target (verifyCode h c) (spec h.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h c, hsat⟩

end VG.Proof.RsaPss.Arm.Vf
