module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs

/-!
# RSAES-OAEP decryption on AArch64: verified

The pieces' relations put together (`dec_ct`): the branches are on `k` and
the hash functions' numbers, which are public. With correctness (`dec_ok`),
`vg_rsa_oaep_decrypt`, for any tier `t` of the hash functions and `pv` of
`vg_rsa_private_checked`, is verified against the shared contract with the
stack it and its callee use (`dec_verified`), given that the contract is
satisfiable for it (which the registration file checks).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Enc.AArch64 (PrivImpl)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.Pbkdf2.Md.AArch64 (Tier)

theorem pub_sp {P : Nat} {s₁ s₂ : State} (h : (decSpec P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

theorem dec_ct (t : Tier) (pv : PrivImpl) :
    ConstantTime isa (decSpec (pv.S + 1)).pre (decSpec (pv.S + 1)).pub (decrypt (tierHs t) pv.name pv.code) := by
  have hS := pv.S15
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBody_eq]
  refine ((head_ct hS).seq ((priv_ct pv).seq ((res_ct hS).seq ((setup_ct t hS).seq
    ((chk_ct t hS).seq (Q := fun _ _ => True) ?_))))).mono ?_ fun _ _ _ => trivial
  · refine RelCT.ite (fun a b ⟨e, _, _, _, ⟨_, _, _, _, _, _, xa⟩, ⟨_, _, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, _⟩, ⟨c₂, V₂, W₂, R₂, S₂, _⟩⟩, _⟩ e₁ e₂
      exact decFail_tr hS e _ _ _ _ _ _ ⟨hL, hP, ⟨c₁, V₁, W₁, R₁, S₁, trivial⟩, ⟨c₂, V₂, W₂, R₂, S₂, trivial⟩⟩ e₁ e₂
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, K₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, K₂, _⟩⟩, hb⟩ e₁ e₂
      have hP16 : 16 ≤ e.L.P := by omega
      obtain ⟨vH, hnH, -⟩ := tier_num t hL.hhk
      obtain ⟨vG, hnG, -⟩ := tier_num t hL.ghk
      rw [hnH.lenAt, hnG.lenAt] at K₁ K₂
      rw [hnH.lenAt] at x₁
      have hkD : 2 * vH.H.D + 2 ≤ e.L.k.toNat := by
        by_contra hc
        rw [eval_nonzero, x₁, ifn (by omega)] at hb
        exact absurd hb (by decide)
      have dx : ∀ {g vv m₀} {u : State} {W : Nat → BitVec 64}, Ctx e.L g vv m₀ u → Slots e.L W →
          HSlots W e.L.hh.toNat vH.H.D e.L.gh.toNat vG.H.D →
          DecX e.L.Q e.L.scr e.L.k.toNat e.L.lab e.L.labl.toNat e.L.out e.L.ml e.L.hh.toNat vH.H.D e.L.gh.toNat
            vG.H.D W u := fun hc hs hk =>
        ⟨hc.labAt hL hP16 hs, hc.outAt hL hP16 hs, by rw [hs.k, BitVec.ofNat_toNat, BitVec.setWidth_eq], hk⟩
      exact decMain_tr hnH hnG vH.ok.stream vG.ok.stream vH.mgf.hash vG.mgf.hash vG.mgf.len (mgf_valid vG.mgf) hkD
        hL.k1024 e.L.labl.isLt _ _ _ _ _ _
        ⟨⟨V₁, W₁, c₁.lay hL hP16 R₁ S₁.scr, R₁, dx c₁ S₁ K₁⟩, ⟨V₂, W₂, c₂.lay hL hP16 R₂ S₂.scr, R₂, dx c₂ S₂ K₂⟩⟩ e₁ e₂
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack the function uses: the callee's and the frames'. -/
def decStack (pv : PrivImpl) : Nat := pv.stack + 288

theorem decStack_eq (pv : PrivImpl) : decStack pv = pv.S + 1 + 288 := by rw [decStack, pv.stack_eq]

/-- `vg_rsa_oaep_decrypt`, with the tier `t` of hash functions and `pv`. -/
theorem dec_verified (t : Tier) (pv : PrivImpl)
    (hsat : ∃ s, (Spec.RsaOaep.decryptAnyContract AArch64.abi (decStack pv)).pre s) :
    Verified AArch64.target (decrypt (tierHs t) pv.name pv.code)
      (Spec.RsaOaep.decryptAnyContract AArch64.abi (decStack pv)) := by
  rw [decStack_eq] at hsat ⊢
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t', s', he, hp⟩ := dec_ok t pv h
    exact ⟨t', s', he, hp⟩) (dec_ct t pv) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Dec
