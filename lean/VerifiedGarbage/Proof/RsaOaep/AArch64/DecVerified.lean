module

import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.AArch64

/-!
# RSAES-OAEP decryption on AArch64: verified

The pieces' relations put together (`dec_ct`): the one branch is on `k`,
which is public. With correctness (`dec_ok`), `vg_rsa_oaep_<H>_mgf1_decrypt`,
for any implementation of the hash functions (MGF1's, the tables of `vs`) and `pv` of
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
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh tabOK_of held_tableOf mem_names)

theorem pub_sp {Hs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s₁ s₂ : State}
    (h : (decSpec Hs ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

variable {Hl : Hash} (hH : StreamOK Hl.stream)

include hH in
theorem dec_ct {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) {vs : List MdHash} (hc : Coh vs)
    (pv : PrivImpl) :
    ConstantTime isa (decSpec Hs (tables vs) (pv.S + 1)).pre (decSpec Hs (tables vs) (pv.S + 1)).pub
      (decrypt Hl (fnsOf vs) pv.name pv.code) := by
  have hS := pv.S15
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBody_eq]
  refine ((head_ct Hs (tables vs) hS).seq ((priv_ct pv (tables vs)).seq ((resK_ct hD64 hS (tables vs)).seq
    (Q := fun _ _ => True) ?_))).mono ?_
    fun _ _ _ => trivial
  · refine RelCT.ite (fun a b ⟨e, _, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, _, ⟨c₁, V₁, W₁, R₁, S₁, _⟩, ⟨c₂, V₂, W₂, R₂, S₂, _⟩⟩, _⟩ e₁ e₂
      exact decFail_tr hS e _ _ _ _ _ _ ⟨hL, hP, ⟨c₁, V₁, W₁, R₁, S₁, trivial⟩, ⟨c₂, V₂, W₂, R₂, S₂, trivial⟩⟩ e₁ e₂
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, ⟨_, ta⟩, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, _⟩⟩, hb⟩ e₁ e₂
      have hP16 : 16 ≤ e.L.P := by omega
      have hkD : 2 * Hl.D + 2 ≤ e.L.k.toNat := by
        by_contra hc
        rw [eval_nonzero, x₁, ifn (by omega)] at hb
        exact absurd hb (by decide)
      have dx : ∀ {g vv m₀} {t : State} {W : Nat → BitVec 64}, Ctx e.L g vv m₀ t → Slots e.L W →
          DecX e.L.Q e.L.scr e.L.k.toNat e.L.lab e.L.labl.toNat e.L.out e.L.ml W t := fun hc hs =>
        ⟨hc.labAt hL hP16 hs, hc.outAt hL hP16 hs, by rw [hs.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
      obtain ⟨⟨⟨T, hT, hh₁⟩, hd₁⟩, ⟨-, hd₂⟩, hsy, hiff⟩ := ta
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
      obtain ⟨hm₁, -, hD₁⟩ := held_tableOf hh₁
      obtain ⟨hm₂, -, hD₂⟩ := held_tableOf ((hiff _ hT).mp hh₁)
      have hn := mem_names hw
      have tx₁ : TabX w.H.stream (fnsOf vs) e.L.Q e.L.scr e.L.tab (s₁.syms w.H.initN) (s₁.syms w.H.updN)
          (s₁.syms w.H.finN) s₁ := ⟨c₁.tab hL hP16 (tabOK_of hc hd₁ hw) hm₁ hD₁, rfl, rfl, rfl⟩
      have tx₂ : TabX w.H.stream (fnsOf vs) e.L.Q e.L.scr e.L.tab (s₁.syms w.H.initN) (s₁.syms w.H.updN)
          (s₁.syms w.H.finN) s₂ := ⟨c₂.tab hL hP16 (tabOK_of hc hd₂ hw) hm₂ hD₂, (hsy _ hn.1).symm,
            (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm⟩
      exact decMain_tr hH w.ok.stream hHh w.mgf.hash w.mgf.len (mgf_valid w.mgf) hkD hL.k1024 e.L.labl.isLt
        _ _ _ _ _ _ ⟨⟨V₁, W₁, c₁.lay hL hP16 R₁ S₁.scr, R₁, dx c₁ S₁, tx₁⟩,
          ⟨V₂, W₂, c₂.lay hL hP16 R₂ S₂.scr, R₂, dx c₂ S₂, tx₂⟩⟩ e₁ e₂
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack the function uses: the callee's and the frames'. -/
def decStack (pv : PrivImpl) : Nat := pv.stack + 288

theorem decStack_eq (pv : PrivImpl) : decStack pv = pv.S + 1 + 288 := by rw [decStack, pv.stack_eq]

include hH in
/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, with `pv`, for the tables of `vs`. -/
theorem dec_verified {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) {vs : List MdHash} (hc : Coh vs) (pv : PrivImpl)
    (hsat : ∃ s, (decSpec Hs (tables vs) (pv.S + 1)).pre s) :
    Verified AArch64.target (decrypt Hl (fnsOf vs) pv.name pv.code) (decSpec Hs (tables vs) (pv.S + 1)) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := dec_ok hH hHh hHl hHv hc pv h
    exact ⟨t, s', he, hp⟩) (dec_ct hH hHh hc pv) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Dec
