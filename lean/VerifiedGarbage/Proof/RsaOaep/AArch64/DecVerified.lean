module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
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
which is public, and on the label's hash function's digest length, the same
for both, as they hold the same table (`two_split`). With correctness
(`dec_ok`), `vg_rsa_oaep_decrypt`, for the hash functions of the tables of
`vs` and `pv` of
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
open VG.Proof.HashTable.AArch64 (tables tableOf fnsOf Coh tabOK_of held_tableOf mem_names)

theorem pub_sp {ts : List FnTable} {P : Nat} {s₁ s₂ : State}
    (h : (decSpec ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

variable {vs : List MdHash} (hc : Coh vs)

include hc in
/-- After the digest length's branch, for the table of `w₁` as the label's
hash function's: the check of `k`, and the decoding or the failure. -/
theorem tail_ct {w₁ : MdHash} (hw₁ : w₁ ∈ vs) {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S (tables vs) (WithL (tables vs) (tableOf w₁) (LenI w₁.H.D)))
      (decTail (ofLen w₁.H.D) (fnsOf vs)) fun _ _ => True := by
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes w₁.ok.stream
  have hD64 : w₁.H.D ≤ 64 := Nat.le_trans hzDF hzF
  rw [decTail_D (G := ofLen w₁.H.D) (G' := w₁.H) rfl]
  unfold decTail Impl.RsaOaep.AArch64.Mgf1.seqs
  refine (resK_ct hD64 hS (tables vs) (tableOf w₁) w₁.H.D).seq ?_
  refine RelCT.ite (fun a b ⟨e, _, _, _, ⟨⟨_, _, _, _, _, xa⟩, _⟩, ⟨⟨_, _, _, _, _, xb⟩, _⟩⟩ => by
    rw [eval_nonzero, eval_nonzero, xa.2, xb.2]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, _, ⟨⟨c₁, V₁, W₁, R₁, S₁, _⟩, _⟩, ⟨⟨c₂, V₂, W₂, R₂, S₂, _⟩, _⟩⟩, _⟩ e₁ e₂
    exact decFail_tr hS e _ _ _ _ _ _ ⟨hL, hP, ⟨c₁, V₁, W₁, R₁, S₁, trivial⟩, ⟨c₂, V₂, W₂, R₂, S₂, trivial⟩⟩ e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP, ⟨_, taL, ta⟩, ⟨⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, hh₁, hdL₁⟩,
      ⟨⟨c₂, V₂, W₂, R₂, S₂, x₂⟩, hh₂, hdL₂⟩⟩, hb⟩ e₁ e₂
    have hP16 : 16 ≤ e.L.P := by omega
    have hkD : 2 * w₁.H.D + 2 ≤ e.L.k.toNat := by
      by_contra hk
      rw [eval_nonzero, x₁.2, ifn (by omega)] at hb
      exact absurd hb (by decide)
    have dx : ∀ {g vv m₀} {t : State} {W : Nat → BitVec 64}, Ctx e.L g vv m₀ t → Slots e.L W →
        DecX e.L.Q e.L.scr e.L.k.toNat e.L.lab e.L.labl.toNat e.L.out e.L.ml W t := fun hx hs =>
      ⟨hx.labAt hL hP16 hs, hx.outAt hL hP16 hs, by rw [hs.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
    -- MGF1's table.
    obtain ⟨⟨⟨T, hT, hh₁'⟩, hd₁⟩, ⟨-, hd₂⟩, hsy, hiff⟩ := ta
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
    obtain ⟨hm₁, -, hD₁⟩ := held_tableOf hh₁'
    obtain ⟨hm₂, -, hD₂⟩ := held_tableOf ((hiff _ hT).mp hh₁')
    have hn := mem_names hw
    have tx₁ : Table.TabX w.H.stream (fnsOf vs) (arg 16) e.L.Q e.L.scr e.L.tab (s₁.syms w.H.initN) (s₁.syms w.H.updN)
        (s₁.syms w.H.finN) s₁ := ⟨c₁.tab hL hP16 (tabOK_of hc hd₁ hw) hm₁ hD₁, rfl, rfl, rfl⟩
    have tx₂ : Table.TabX w.H.stream (fnsOf vs) (arg 16) e.L.Q e.L.scr e.L.tab (s₁.syms w.H.initN) (s₁.syms w.H.updN)
        (s₁.syms w.H.finN) s₂ := ⟨c₂.tab hL hP16 (tabOK_of hc hd₂ hw) hm₂ hD₂, (hsy _ hn.1).symm,
          (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm⟩
    -- The label's hash function's.
    obtain ⟨hmL₁, -, hDL₁⟩ := held_tableOf hh₁
    obtain ⟨hmL₂, -, hDL₂⟩ := held_tableOf hh₂
    have hnL := mem_names hw₁
    have l₁ : LabT w₁.H.stream (fnsOf vs) e.L.Q e.L.scr e.L.lab e.L.labl.toNat e.L.tabL (s₁.syms w₁.H.initN)
        (s₁.syms w₁.H.updN) (s₁.syms w₁.H.finN) W₁ s₁ :=
      ⟨(dx c₁ S₁).1, x₁.1, ⟨⟨s₁, arg 15, c₁.tabL hL hP16 (tabOK_of hc hdL₁ hw₁) hmL₁ hDL₁, Step.refl _ _ _ _, rfl⟩,
        rfl, rfl, rfl⟩⟩
    have l₂ : LabT w₁.H.stream (fnsOf vs) e.L.Q e.L.scr e.L.lab e.L.labl.toNat e.L.tabL (s₁.syms w₁.H.initN)
        (s₁.syms w₁.H.updN) (s₁.syms w₁.H.finN) W₂ s₂ :=
      ⟨(dx c₂ S₂).1, x₂.1, ⟨⟨s₂, arg 15, c₂.tabL hL hP16 (tabOK_of hc hdL₂ hw₁) hmL₂ hDL₂, Step.refl _ _ _ _, rfl⟩,
        (hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2).symm⟩⟩
    exact decMain_tr w₁.ok.stream w.ok.stream w₁.mgf.hash w.mgf.hash w.mgf.len (mgf_valid w.mgf) hkD hL.k1024
      e.L.labl.isLt _ _ _ _ _ _ ⟨⟨V₁, W₁, c₁.lay hL hP16 R₁ S₁.scr, R₁, ⟨dx c₁ S₁, tx₁⟩, l₁⟩,
        ⟨V₂, W₂, c₂.lay hL hP16 R₂ S₂.scr, R₂, ⟨dx c₂ S₂, tx₂⟩, l₂⟩⟩ e₁ e₂

include hc in
theorem dec_ct (pv : PrivImpl) :
    ConstantTime isa (decSpec (tables vs) (pv.S + 1)).pre (decSpec (tables vs) (pv.S + 1)).pub
      (decrypt (fnsOf vs) pv.name pv.code) := by
  have hS := pv.S15
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBody_eq]
  refine ((head_ct (tables vs) hS).seq ((priv_ct pv (tables vs)).seq (two_split (Q := fun _ _ => True) fun T hT => ?_))).mono ?_
    fun _ _ _ => trivial
  · obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT
    have hDl : w₁.H.D ∈ lens := by rw [← w₁.mgf.len]; exact mem_lens w₁.mgf.mem
    refine (tabSlot_ct hc hw₁ hS).seq ((lenLoad_ct hc hw₁ hS).seq (byLen_ct (D := w₁.H.D)
      (fun _ _ _ _ _ h => h.1.1) (mem_lens_lt hDl) (fun _ _ _ _ _ ⟨⟨_, _, _, _, _, _, h⟩, _⟩ => h)
      (fun L g vv m₀ t u hL hP h st hm sy hg => ?_) (tail_ct hc hw₁ hS) hDl fun x hx => mem_lens_lt hx))
    obtain ⟨⟨hcx, V, W, R, hSl, h32, h16⟩, _⟩ := id h
    exact WithL.of (Φ := LenI w₁.H.D) h sy ⟨hcx.step hL (by omega_arith) st nil_ws, V, W, hm ▸ R, hSl, h32,
      (hg _ (by decide)).trans h16⟩
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack the function uses: the callee's and the frames'. -/
def decStack (pv : PrivImpl) : Nat := pv.stack + 288

theorem decStack_eq (pv : PrivImpl) : decStack pv = pv.S + 1 + 288 := by rw [decStack, pv.stack_eq]

include hc in
/-- `vg_rsa_oaep_decrypt`, with `pv`, for the tables of `vs`. -/
theorem dec_verified (pv : PrivImpl) (hsat : ∃ s, (decSpec (tables vs) (pv.S + 1)).pre s) :
    Verified AArch64.target (decrypt (fnsOf vs) pv.name pv.code) (decSpec (tables vs) (pv.S + 1)) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := dec_ok hc pv h
    exact ⟨t, s', he, hp⟩) (dec_ct hc pv) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Dec
