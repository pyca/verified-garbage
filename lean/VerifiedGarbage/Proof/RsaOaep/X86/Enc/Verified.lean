module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Call
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaOaep/Arm/EncBody.lean`, `EncVerified.lean`): the
checks, then zeros to `out` if the message does not fit (`fail_vp`), or
`EM` (`em_vp`), its masks (`mask_vp`) and the call (`pa_vp`, `call_vp`):
`body_vp`. The body writes `esp` only through the frames of its calls
(`body_noSp`); the frames around it (`wrap_ok`, `wrap_ct`) and the result
as the shared contract states it: `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`,
calling a precomputed public operation `c`, is verified, given a state that
meets the contract (`EncSat.lean`): `encrypt_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes seqs countLoop zeroLoop)

variable (h g : OHash)

/-- After the checks, when the message fits. -/
theorem main_vp (P : EP) (c : Ver.PublicImpl) : VP (E0 h P) (encMain h.H g.H c.name c.code) (Fin h g P) := by
  show VP _ (.seq (encEm h.H) (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor g.H) (.seq (.block (seedArgs h.H 3))
    (.seq (mgfXor g.H) (.seq (.block pubArgs) (.call c.name c.code))))))) _
  exact (em_vp h P).seq (mask_vp h g P ((pa_vp h g P).seq (call_vp h g P c)))

/-- The body. -/
theorem body_vp (P : EP) (c : Ver.PublicImpl) : VP (S h P) (encBody h.H g.H c.name c.code) (Fin h g P) := by
  show VP _ (.seq (.block (encChk h.H)) (.ite .ne encFail (encMain h.H g.H c.name c.code))) _
  refine (chk_vp h P).seq (VP.ite (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.2.2, h₂.2.2]) (fail_vp h g P) ?_)
  refine (main_vp h g P c).mono (fun σ s ⟨⟨hc, hi, z⟩, e⟩ => ⟨hc, hi, ?_⟩) fun _ _ hh => hh
  simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
  exact e

/-! ## The stack -/

theorem body_noSp (c : Ver.PublicImpl) : NoSp (encBody h.H g.H c.name c.code) := by
  obtain ⟨-, -, p3, -, p5, -, p7, p8, p9, -⟩ := h.certs.parts
  have hm := mgfX_noSp g
  have hl := hashLabel_noSp h (j := 6) (o := Impl.RsaPss.X86.oDig) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  have hc := c.noSp
  simp only [encBody, encMain, encEm, encFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | exact hm | exact hl | exact hc | exact p3 | exact p5 | exact p7 | exact p8 | exact p9
    | exact NoSp.of_all (by decide +kernel))

/-! ## The entry -/

/-- The code, calling `c`. -/
abbrev encryptCode (c : Ver.PublicImpl) : Prog isa := encryptPrecomputed h.H g.H c.name c.code

theorem in_entered {s : State} (hs : (spec h.G g.G).pre s) : In h.H.D (ep s) (entered frameBytes s) := by
  have hi := in_of_pre hs
  rw [h.glen] at hi
  exact hi

theorem entered_state {s : State} (hs : (spec h.G g.G).pre s) :
    S h (ep s) (entered frameBytes s) (entered frameBytes s) :=
  have hi := in_entered h g hs
  ⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem spec_sp {s : State} (hs : (spec h.G g.G).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argSlots, argVal,
    argBytes, stackBelow] at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem code_ok (c : Ver.PublicImpl) {s : State} (hs : (spec h.G g.G).pre s) :
    WP isa (encryptCode h g c) s fun t => abiPreserved s t ∧ (spec h.G g.G).post s t := by
  have hin := in_entered h g hs
  obtain ⟨hsp0, hfit⟩ := spec_sp h g hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hb := (body_vp h g (ep s) c).wp _ _ (entered_state h g hs)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp h g c) hsp hfit (W := ((ep s).lay h.H.D).W)
    (Q := fun r m => Res h g (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro h.H.D) (rw := (ep s).rw) (C := 100) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro h.H.D) (rw := (ep s).rw) (C := 100) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).ro h.H.D) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argSlots, argVal,
      argBytes]
    unfold Res at res
    have hL : labB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat :=
      ro (R := (ep s).LAB) (by simp)
    have hM : msgB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat :=
      ro (R := (ep s).MSG) (by simp)
    have hS : seedB h (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 10).setWidth 64) h.H.D :=
      ro (R := (ep s).SEED h.H.D) (by simp)
    rw [hL, hM, hS] at res
    rw [BitVec.setWidth_append_eq_right, h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : (spec h.G g.G).pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argSlots, argVal,
    argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := hp
  obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a3, a5])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [RsaPkcs1Sig.bytesAt_len, a3])
  have hw' := map_toNat_inj hw
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]
  rw [a2, a3] at hn
  rw [a4, a5] at he
  rw [a13, a14] at hw'
  rw [hn, he, hw']

theorem code_ct (c : Ver.PublicImpl) : ConstantTime isa (spec h.G g.G).pre (spec h.G g.G).pub (encryptCode h g c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  have hep := ep_eq h g hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argSlots, argVal,
      argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp h g c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h g (ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h g h₁, by rw [hep]; exact entered_state h g h₂⟩

theorem code_noSp (c : Ver.PublicImpl) : NoSp (encryptCode h g c) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp h g c)) restore_noSp)

theorem code_sp (c : Ver.PublicImpl) : (encryptCode h g c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp h g c)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, calling `c`, meets the
shared contract (satisfiable, `EncSat.lean`). -/
theorem encrypt_verified (hsat : ∃ s, (spec h.G g.G).pre s) (c : Ver.PublicImpl) :
    Verified target (encryptCode h g c) (spec h.G g.G) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok h g c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct h g c, hsat⟩

end VG.Proof.RsaOaep.X86.Enc
