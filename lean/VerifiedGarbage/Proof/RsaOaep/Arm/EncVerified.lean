module

import VerifiedGarbage.Proof.RsaOaep.Arm.EncBody
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncChk
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`) and the result as the
shared contract states it: `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`,
calling a precomputed public operation `c`, is verified, given a state that
meets the contract (`EncSat.lean`): `encrypt_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes)

variable (h g : OHash)

/-- The code, calling `c`. -/
abbrev encryptCode (c : PdImpl) : Prog isa := encryptPrecomputed h.H g.H c.name c.code

theorem in_entered {s : State} (hs : (spec h.G g.G).pre s) : In h.H.D (ep s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  rw [h.glen] at hi
  exact hi

theorem entered_state {s : State} (hs : (spec h.G g.G).pre s) :
    S h (ep s) (entered frameBytes s) (entered frameBytes s) :=
  have hi := in_entered h g hs
  ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (hs : (spec h.G g.G).pre s) : stackBytes ≤ s.sp.toNat := by
  sig_pre [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val] at hs
  exact hs.1

theorem code_ok (c : PdImpl) {s : State} (hs : (spec h.G g.G).pre s) :
    WP isa (encryptCode h g c) s fun t => abiPreserved s t ∧ (spec h.G g.G).post s t := by
  have hsp := spec_sp h g hs
  have hin := in_entered h g hs
  have st := entered_state h g hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hsp; omega
  refine WP.mono (wrap_ok (by decide) (by omega) (W := ((ep s).lay h.H.D).W)
    (Q := fun r m => Res h g (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono ((body_vp h g (ep s) c).wp _ _ st) fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 44) (argv := (ep s).argv)
      (ro := [(ep s).N, (ep s).E, (ep s).LAB, (ep s).MSG, (ep s).SEED h.H.D, (ep s).PRE])
      (rw := [(ep s).OUT, (ep s).SCR]) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      reduceClassify, Loc.val]
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region}
        (hR : R ∈ [(ep s).N, (ep s).E, (ep s).LAB, (ep s).MSG, (ep s).SEED h.H.D, (ep s).PRE]) =>
      entered_ro (F := frameBytes) (A := 44) (argv := (ep s).argv) (rw := [(ep s).OUT, (ep s).SCR]) hin.ok hsp' hR
    have hL : labB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2))
        (stackArg s 3).toNat := ro (R := (ep s).LAB) (by simp)
    have hM : msgB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4))
        (stackArg s 5).toNat := ro (R := (ep s).MSG) (by simp)
    have hS : seedB h (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6))
        h.H.D := ro (R := (ep s).SEED h.H.D) (by simp)
    unfold Res at res
    rw [hL, hM, hS] at res
    rw [h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G g.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hp
  obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h3, a1])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [bytesAt_length, h3])
  have hw' := map_toNat_inj hw
  simp only [ep]
  rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
  rw [h2, h3] at hn
  rw [a0, a1] at he
  rw [a9, a10] at hw'
  rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
    show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
    show State.addr (stackArg s₂ 9) = BitVec.setWidth 64 (stackArg s₂ 9) from rfl, hw']

theorem code_ct (c : PdImpl) : ConstantTime isa (spec h.G g.G).pre (spec h.G g.G).pub (encryptCode h g c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h g hp
  have hsp : s₁.sp = s₂.sp := by
    sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      reduceClassify, Loc.val] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; have := spec_sp h g h₁; simp only [stackBytes] at this; omega) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h g (ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h g h₁, by rw [hep]; exact entered_state h g h₂⟩

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, calling `c`, meets the
shared contract (satisfiable, `EncSat.lean`). -/
theorem encrypt_verified (hsat : ∃ s, (spec h.G g.G).pre s) (c : PdImpl) :
    Verified target (encryptCode h g c) (spec h.G g.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h g c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h g c, hsat⟩

end VG.Proof.RsaOaep.Arm.Enc
