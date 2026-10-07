import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on AArch64: verified

The pieces' relations put together (`dec_ct`): the one branch is on `k`,
which is public. With correctness (`dec_ok`), `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`,
for any implementation of the hash functions and `pv` of
`vg_rsa_private_checked`, is verified against the shared contract with the
stack it and its callee use (`dec_verified`), given that the contract is
satisfiable for it (which the registration file checks).
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl)
open VG.Proof.Mgf1 (ifp ifn)

theorem pub_sp {Hs Gs : Spec.Mgf1.Hash} {P : Nat} {s₁ s₂ : State} (h : (decSpec Hs Gs P).pub s₁ s₂) :
    s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem dec_ct {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x)
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D) (hGv : Proof.Mgf1.Valid Gs) (pv : PrivImpl) :
    ConstantTime isa (decSpec Hs Gs (pv.S + 1)).pre (decSpec Hs Gs (pv.S + 1)).pub
      (decrypt Hl Gm pv.name pv.code) := by
  have hS := pv.S15
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBody_eq]
  refine ((head_ct Hs Gs hS).seq ((priv_ct pv).seq ((resK_ct hD64 hS).seq (Q := fun _ _ => True) ?_))).mono ?_
    fun _ _ _ => trivial
  · refine RelCT.ite (fun a b ⟨e, _, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, _⟩, ⟨c₂, V₂, W₂, R₂, S₂, _⟩⟩, _⟩ e₁ e₂
      exact decFail_tr hS e _ _ _ _ _ _ ⟨hL, hP, ⟨c₁, V₁, W₁, R₁, S₁, trivial⟩, ⟨c₂, V₂, W₂, R₂, S₂, trivial⟩⟩ e₁ e₂
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, _⟩⟩, hb⟩ e₁ e₂
      have hP16 : 16 ≤ e.L.P := by omega
      have hkD : 2 * Hl.D + 2 ≤ e.L.k.toNat := by
        by_contra hc
        rw [eval_nonzero, x₁, ifn (by omega)] at hb
        exact absurd hb (by decide)
      have dx : ∀ {g vv m₀} {t : State} {W : Nat → BitVec 64}, Ctx e.L g vv m₀ t → Slots e.L W →
          DecX e.L.Q e.L.scr e.L.k.toNat e.L.lab e.L.labl.toNat e.L.out e.L.ml W t := fun hc hs =>
        ⟨hc.labAt hL hP16 hs, hc.outAt hL hP16 hs, by rw [hs.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
      exact decMain_tr hH hG hHh hGh hGl hGv hkD hL.k1024 e.L.labl.isLt _ _ _ _ _ _
        ⟨⟨V₁, W₁, c₁.lay hL hP16 R₁ S₁.scr, R₁, dx c₁ S₁⟩, ⟨V₂, W₂, c₂.lay hL hP16 R₂ S₂.scr, R₂, dx c₂ S₂⟩⟩ e₁ e₂
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack the function uses: the callee's and the frames'. -/
def decStack (pv : PrivImpl) : Nat := pv.stack + 288

theorem decStack_eq (pv : PrivImpl) : decStack pv = pv.S + 1 + 288 := by rw [decStack, pv.stack_eq]

include hH hG in
/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`, with `pv`. -/
theorem dec_verified {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) (pv : PrivImpl)
    (hsat : ∃ s, (Spec.RsaOaep.decryptContract Hs Gs AArch64.abi (decStack pv)).pre s) :
    Verified AArch64.target (decrypt Hl Gm pv.name pv.code)
      (Spec.RsaOaep.decryptContract Hs Gs AArch64.abi (decStack pv)) := by
  rw [decStack_eq] at hsat ⊢
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := dec_ok hH hG hHh hHl hHv hGh hGl hGv pv h
    exact ⟨t, s', he, hp⟩) (dec_ct hH hG hHh hGh hGl hGv pv) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Dec
