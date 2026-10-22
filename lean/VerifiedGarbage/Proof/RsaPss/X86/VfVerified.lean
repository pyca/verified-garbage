module

public import VerifiedGarbage.Proof.RsaPss.X86.VfMain
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# RSASSA-PSS verification with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/VfVerified.lean`): the body, which writes
`esp` only through the frames of its calls (`body_noSp`), the frames around
it (`wrap_ok`, `wrap_ct`) and the result as the shared contract states it:
`vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling a precomputed public
operation `c`, is verified for any hash function `h` it is given a
satisfiable contract for (`verify_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes

variable (h : PssHash)

theorem body_noSp (c : Ver.PublicImpl) : NoSp (verifyBody h.H c.name c.code) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig4
  have p3 := sp.lenArgs7
  have p4 := sp.fxSalt
  have p5 := sp.cpDb
  have p6 := sp.passSet
  have p7 := sp.anyLen
  have p8 := sp.cmpArgs
  have hct := ctHash_noSp h
  have hm := mgfXor_noSp h
  have hc := c.noSp
  simp only [verifyBody, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [verifyMain, fixedPath, anyPath, yDig, shift, passOne, cmpH, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

/-- The code, calling `c`. -/
abbrev verifyCode (c : Ver.PublicImpl) : Prog isa := verifyPrecomputed h.H c.name c.code

theorem spec_sp {s : State} (hs : (spec h.G).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argSlots, argVal, argBytes,
    stackBelow] at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem entered_state {s : State} (hs : (spec h.G).pre s) :
    S h (ep s) (entered frameBytes s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  rw [h.glen] at hi
  exact ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_ok (c : Ver.PublicImpl) {s : State} (hs : (spec h.G).pre s) :
    WP isa (verifyCode h c) s fun t => abiPreserved s t ∧ (spec h.G).post s t := by
  have hin := in_of_pre hs
  rw [h.glen] at hin
  obtain ⟨hsp0, hfit⟩ := spec_sp h hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hb := (body_vq h (ep s) c).1 _ _ (entered_state h hs)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp h c) hsp hfit (W := ((ep s).lay h.D).W)
    (Q := fun r _ => Res h (ep s) (entered frameBytes s) r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro h.D) (rw := (ep s).rw) (C := 48) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro h.D) (rw := (ep s).rw) (C := 48) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro h.D) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argSlots, argVal,
      argBytes]
    unfold Res at res
    have hG : sigB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 1).toNat := by
      have e : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 5).setWidth 64) (ep s).gl =
          Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (ep s).gl := ro (R := (ep s).SIG) (by simp)
      rw [hin.glK] at e
      exact e
    rw [show digB h (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DIG h.D) (by simp), hG] at res
    rw [BitVec.setWidth_append_eq_right, h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argSlots, argVal,
    argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hp
  obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a1, a3])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a1])
  have hw' := map_toNat_inj hw
  simp only [ep]
  rw [hsp, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]
  rw [a0, a1] at hn
  rw [a2, a3] at he
  rw [a11, a12] at hw'
  rw [hn, he, hw']

theorem code_ct (c : Ver.PublicImpl) : ConstantTime isa (spec h.G).pre (spec h.G).pub (verifyCode h c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argSlots, argVal,
      argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp h c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vq h (ep s₁) c).2.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h h₁, by rw [hep]; exact entered_state h h₂⟩

theorem code_noSp (c : Ver.PublicImpl) : NoSp (verifyCode h c) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp h c)) restore_noSp)

theorem code_sp (c : Ver.PublicImpl) : (verifyCode h c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp h c)

/-- `vg_rsa_pss_<H>_mgf1_<H>_verify_precomputed`, calling `c`, meets the shared
contract (satisfiable, `VfSat.lean`). -/
theorem verify_verified (hsat : ∃ s, (spec h.G).pre s) (c : Ver.PublicImpl) :
    Verified target (verifyCode h c) (spec h.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h c, hsat⟩

end VG.Proof.RsaPss.X86.Vf
