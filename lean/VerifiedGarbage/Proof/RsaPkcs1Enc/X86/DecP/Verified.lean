module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecP.Body
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety

/-!
# RSAES-PKCS1-v1_5 decryption on x86, given `pre`: verified

`vg_rsa_pkcs1_decrypt_precomputed`, calling `vg_rsa_private_checked_precomputed`:
its entry (`in_of_preP`), the frames around the body (`wrap_ok`, `wrap_ct`),
and a state that meets its contract, with a real key (`satisfiablePre`):
verified (`decryptPrecomputed_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP crtPBaseline)
open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The contract, with the stack of `vg_rsa_pkcs1_decrypt`. -/
abbrev specP : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes

/-- `vg_rsa_pkcs1_decrypt`'s layout, of the state narrowed to its permissions. -/
theorem ok_narrow {P : EP} {pre : BitVec 32} {L : Nat} {σ : State} (h : (P.layP pre L).Ok σ) :
    P.lay.Ok (narrowS P σ) := by
  have fit := h.fit
  simp only [Lay.A, EP.argvP, List.length_cons, List.length_nil] at fit
  have args100 : Region.Sub P.lay.ARGS (P.layP pre L).ARGS := by
    simp only [Lay.ARGS, Lay.A, EP.argv, EP.argvP, List.length_cons, List.length_nil]
    exact Region.sub_prefix (by omega_using [])
  have subro : ∀ r ∈ P.ro, r ∈ (P.layP pre L).ro := by
    intro r hr
    simp only [EP.ro, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have sub : ∀ r ∈ P.ro ++ P.rw, r ∈ (P.layP pre L).ro ++ (P.layP pre L).rw := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (subro r hr)
    · exact List.mem_append_right _ hr
  refine ⟨h.sp, fun _ hr => hr,
    fun _ hr => (List.cons_subset_cons _ (List.cons_subset_cons _ (List.subset_append_left _ _))) hr,
    ⟨_, Nat.le_refl _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_singleton_self _)))⟩, h.BC, ?_, fun r hr => h.stk r (sub r hr), h.ret, ?_, h.wrw,
    fun r hr => h.fits r (sub r hr), ?_⟩
  · simp only [Lay.A, EP.argv, List.length_cons, List.length_nil]; omega_using [fit]
  · intro w hw r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.wro w hw r (List.mem_append_left _ (subro r hr))
    · obtain rfl := List.mem_singleton.mp hr
      exact (h.wro w hw _ (List.mem_append_right _ (List.mem_singleton_self _))).sub_right args100
  · intro j hj
    have hj' : j < 23 := by simpa only [EP.argv, List.length_cons, List.length_nil] using hj
    rw [show P.lay.argv.getD j 0 = (P.layP pre L).argv.getD j 0 by
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 by omega_using [hj']) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl]
    exact h.args j (by simp only [EP.argvP, List.length_cons, List.length_nil]; omega_using [hj'])

theorem ep_layP (s : State) (pre : BitVec 32) (L : Nat) :
    (ep s).layP pre L = layOf frameBytes ((ep s).argvP pre L) ((ep s).roP pre L) (ep s).rw s 3448 := rfl

theorem in_of_preP {s : State} (h : specP.pre s) :
    InP (ep s) (arg s 23) (arg s 24).toNat (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  rename_i hsp hsa hrd hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPre oA mN mE mD mI mP mQ mDP mDQ mQI mS mPre mA
    nS nA eS eA dS dA iS iA pS pA qS qA dpS dpA dqS dqA qiS qiA sPre sA preA
    rO rM rN rE rD rI rP rQ rDP rDQ rQI rS rPre rA kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPre kA
    fO fM fN fE fD fI fP fQ fDP fDQ fQI fS fPre kv olk ilk el1 elK dl1 dlK
    pl1 plK ql1 qlK dpl qil dql slK plen
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kM kN kE kD kI kP kQ kDP kDQ kQI kS kPre kA
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  have a10 : arg s 10 = arg s 4 := BitVec.eq_of_toNat_eq ilk
  have a16 : arg s 16 = arg s 12 := BitVec.eq_of_toNat_eq dpl
  have a20 : arg s 20 = arg s 12 := BitVec.eq_of_toNat_eq qil
  have a18 : arg s 18 = arg s 14 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oD oI oP oQ oDP oDQ oQI oS oPre oA rO kO fO
  rw [ilk] at hrd oI mI iS iA rI kI fI
  rw [dpl] at hrd oDP mDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI mQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ mDQ dqS dqA rDQ kDQ fDQ
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3568, 3568⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have sl32 : (arg s 22).toNat < 2 ^ 32 := (arg s 22).isLt
  have bytesE := fun {x : BitVec 32} {k : Nat}
      (hk : (⟨(s.gpr .esp).setWidth 64 - 3568#64, 3568⟩ : Region).Disjoint ⟨x.setWidth 64, k⟩) (hl : k ≤ 2 ^ 64) =>
    Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hk.sub_left below16).symm) hl
  have ok : ((ep s).layP (arg s 23) (arg s 24).toNat).Ok (entered frameBytes s) := by
    rw [ep_layP]
    refine ok_entered (S := 3568) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
      (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [EP.roP, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [kN, kE, kD, kI, kP, kQ, kDP, kDQ, kQI, kPre, kO, kM, kS]
    · intro r hr
      simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [rO, rM, rS]
    · intro w hw r hr
      simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [EP.roP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [oN, oE, oD, oI, oP, oQ, oDP, oDQ, oQI, oPre, oA, mN, mE, mD, mI, mP, mQ, mDP, mDQ, mQI, mPre, mA,
        nS.symm, eS.symm, dS.symm, iS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, sPre, sA]
    · refine List.Pairwise.cons ?_ (List.pairwise_pair.mpr mS)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [oM, oS]
    · intro r hr
      simp only [EP.roP, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [ep, BitVec.toNat_setWidth]
      all_goals first
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 23).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
        | (rw [Nat.mod_eq_of_lt (by have := (arg s 21).isLt; omega_arith)]; omega_arith)
    · intro j hj
      have : j < 25 := hj
      rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a10, a16, a18, a20]
  have hn := bytesE kN (by have := (arg s 4).isLt; omega_using [])
  have hp := bytesE kP (by have := (arg s 12).isLt; omega_using [])
  have hq := bytesE kQ (by have := (arg s 14).isLt; omega_using [])
  have he := bytesE kE (by have := (arg s 6).isLt; omega_using [])
  refine ⟨ok, ⟨ok_narrow ok, kv, el1, elK, dl1, dlK, pl1, plK, ql1, qlK, slK, sl32, hn, he⟩,
    plen, ?_⟩
  have hw : Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 23).setWidth 64) (arg s 24).toNat =
      Spec.Rsa.wordsAt s.mem ((arg s 23).setWidth 64) (arg s 24).toNat :=
    Proof.Rsa.wordsAt_frame hpush (by omega_arith) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [show 8 * (arg s 24).toNat = (arg s 24).toNat * 8 from Nat.mul_comm _ _]
      exact (kPre.sub_left below16).symm)
  change Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 11).setWidth 64) (arg s 12).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 13).setWidth 64) (arg s 14).toNat) =
    some (Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 23).setWidth 64) (arg s 24).toNat)
  rw [hp, hq, hw]
  exact h

theorem entered_stateP {s : State} (h : specP.pre s) :
    SP (ep s) (arg s 23) (arg s 24).toNat (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_preP h, ⟨(in_of_preP h).ok, (in_of_preP h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

/-- The code, with the backend `v` and calling `vg_rsa_private_checked_precomputed` over `c` and `w`. -/
abbrev decryptCodeP (v : Backend) (c : CrtImpl) (w : CrtPImpl) : Prog isa :=
  code v.F (privNameP c) (privCodeP c w) privArgsP

theorem specP_sp {s : State} (h : specP.pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, -⟩ := h
  exact ⟨hsp, by omega_using [hsa]⟩

theorem code_okP (v : Backend) (c : CrtImpl) (w : CrtPImpl) {s : State} (h : specP.pre s) :
    WP isa (decryptCodeP v c w) s fun t => abiPreserved s t ∧ specP.post s t := by
  have hin := in_of_preP h
  obtain ⟨hs, hfit⟩ := specP_sp h
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hs ⊢; omega_using [hs]
  have hb := (bodyP_vp (P := ep s) (pre := arg s 23) (L := (arg s 24).toNat) v c w).wp _ _ (entered_stateP h)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (bodyP_noSp v c w) hsp hfit (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_layP] at ok
    rw [save_eq (argv := (ep s).argvP (arg s 23) (arg s 24).toNat) (ro := (ep s).roP (arg s 23) (arg s 24).toNat)
      (rw := (ep s).rw) (C := 3448) hsp,
      ret_eq (argv := (ep s).argvP (arg s 23) (arg s 24).toNat) (ro := (ep s).roP (arg s 23) (arg s 24).toNat)
      (rw := (ep s).rw) (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_layP] at ok
    have ro := fun {R : Region} (hR : R ∈ (ep s).roP (arg s 23) (arg s 24).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes]
    unfold Res at res
    rw [show dB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).D) (by simp),
      show cB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).INP) (by simp),
      show pB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).PP) (by simp),
      show qB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).QQ) (by simp),
      show dpB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DP) (by simp),
      show dqB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).DQ) (by simp),
      show qiB (ep s) (entered frameBytes s) = _ from ro (R := (ep s).QI) (by simp)] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

/-- Two entry states with the same public data have the same public parameters, and the same `pre`. -/
theorem ep_eqP {s₁ s₂ : State} (hp : specP.pub s₁ s₂) :
    ep s₁ = ep s₂ ∧ arg s₁ 23 = arg s₂ 23 ∧ arg s₁ 24 = arg s₂ 24 := by
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22, a23, a24⟩ := hp
  obtain ⟨hne, -⟩ := List.append_inj hl (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a4, a6])
  obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hne) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a4])
  refine ⟨?_, a23, a24⟩
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a11, a12, a13, a14, a15, a17, a19, a21, a22]
  rw [a3, a4] at hn
  rw [a5, a6] at he
  rw [hn, he]

theorem code_ctP (v : Backend) (c : CrtImpl) (w : CrtPImpl) :
    ConstantTime isa specP.pre specP.pub (decryptCodeP v c w) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨hep, h23, h24⟩ := ep_eqP hp
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
      Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (bodyP_noSp v c w) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (bodyP_vp (P := ep s₁) (pre := arg s₁ 23) (L := (arg s₁ 24).toNat) v c w).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_stateP h₁, by rw [hep, h23, h24]; exact entered_stateP h₂⟩

/-! ## A state that meets the contract -/

/-- The arguments of `preState`; the key (`keyMem`) has `n` at `0x2000`,
`p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat := [0x1000, 64, 0x6800, 0x2000, 64, 0x2100, 1, 0x2200, 1, 0x3000, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the arguments on the stack from `0x20004`,
and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x20004 i && Nat.blt i 0x20068 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x20004) / 4) 0 / 256 ^ ((i - 0x20004) % 4))
  else bif keyIn i then keyMem a else 0

def preState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x3000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩,
    ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x6800, 8⟩, ⟨0xA000, 8448⟩, ⟨0x20004, 100⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x20004 a.toNat && Nat.blt a.toNat 0x20068) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s := by
  have a3 : arg preState 3 = 0x2000 := by decide
  have p3 : BitVec.setWidth 64 (arg preState 3) = 0x2000 := by rw [a3]; decide
  have a11 : arg preState 11 = 0x4200 := by decide
  have p11 : BitVec.setWidth 64 (arg preState 11) = 0x4200 := by rw [a11]; decide
  have a13 : arg preState 13 = 0x4300 := by decide
  have p13 : BitVec.setWidth 64 (arg preState 13) = 0x4300 := by rw [a13]; decide
  have a23 : arg preState 23 = 0x4800 := by decide
  have p23 : BitVec.setWidth 64 (arg preState 23) = 0x4800 := by rw [a23]; decide
  have a4 : arg preState 4 = 64 := by decide
  have l4 : (arg preState 4).toNat = 64 := by rw [a4]; decide
  have a12 : arg preState 12 = 32 := by decide
  have l12 : (arg preState 12).toNat = 32 := by rw [a12]; decide
  have a14 : arg preState 14 = 32 := by decide
  have l14 : (arg preState 14).toNat = 32 := by rw [a14]; decide
  have a24 : arg preState 24 = 24 := by decide
  have l24 : (arg preState 24).toNat = 24 := by rw [a24]; decide
  have e : argAddr preState 0 = 0x20004 := by decide
  have esp : preState.gpr .esp = 0x20000 := rfl
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argSlots, argVal, argBytes, stackBelow, e, esp,
    stackBytes, frameBytes, Spec.Rsa.lenValid, Spec.Rsa.scratchWords, Spec.Rsa.privatePrecomputedWords]
  sig_and_intros
  rotate_right
  · rw [p3, p11, p13, p23, l4, l12, l14, l24]; exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, preState] at h₁ h₂
       bv_omega)
theorem codeP_noSp (v : Backend) (c : CrtImpl) (w : CrtPImpl) : NoSp (decryptCodeP v c w) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (bodyP_noSp v c w)) restore_noSp)

theorem codeP_sp (v : Backend) (c : CrtImpl) (w : CrtPImpl) :
    (decryptCodeP v c w).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (codeP_noSp v c w)

/-- `vg_rsa_pkcs1_decrypt_precomputed` with the backend `v`, calling
`vg_rsa_private_checked_precomputed` over `c` and `vg_rsa_private_crt_precomputed`. -/
theorem decryptPrecomputed_verified (v : Backend) (c : CrtImpl) :
    Verified target (decryptCodeP v c crtPBaseline) specP :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_okP v c crtPBaseline h; ⟨t, s', he, hq.1, hq.2⟩,
    code_ctP v c crtPBaseline, satisfiablePre⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
