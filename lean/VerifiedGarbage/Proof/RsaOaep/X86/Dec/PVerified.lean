module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.PCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# RSAES-OAEP decryption on x86, given `pre`: verified

`decryptPrecomputedMdTablesContract`'s precondition gives
`vg_rsa_oaep_decrypt`'s state where the body starts, and `XP`: the wider
layout and `pre` the key's values (`in_of_preP`, `entered_stateP`). The body
(`body_vpP`) in the frames around it gives the result (`code_okP`), in time
that depends on what the two runs share (`code_ctP`):
`vg_rsa_oaep_decrypt_precomputed`, calling
`vg_rsa_private_checked_precomputed` over `c` and `w`, is verified
(`decP_verified`), given a state that meets the contract (`Dec/PSat.lean`).
-/

-- separate module: builds in parallel with the satisfying state (`Dec/PSat`), which needs only the contract.

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP)
open VG.Proof.HashTable.X86 (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered
  fnsOf_noSp)

variable {ai au af : BitVec 32} {T : State → Prop} {aiL auL afL : BitVec 32} {TL : State → Prop}

theorem ep_layP (s : State) (pre : BitVec 32) (L : Nat) :
    (ep s ai au af T aiL auL afL TL).layP pre L =
      layOf frameBytes ((ep s ai au af T aiL auL afL TL).argv ++ [pre, BitVec.ofNat 32 L])
        ((ep s ai au af T aiL auL afL TL).ro ++ [preR pre L]) (ep s ai au af T aiL auL afL TL).rw s 3448 := rfl

/-- The tables, as the contract gives them. -/
theorem spec_tabP {ts : List FnTable} {s : State} (h : (specP ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem ((arg s 24).setWidth 64) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (arg s 23).toNat + 44 ≤ 2 ^ 32 ∧ (arg s 24).toNat + 44 ≤ 2 ^ 32 := by
  decP_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPre oTL oT oA
    mN mE mP mQ mDP mDQ mQI mL mC mS mPre mTL mT mA nS nA eS eA pS pA qS qA dpS dpA dqS dqA qiS qiA lS lA cS cA
    sPre sTL sT sA preA tlA tA rO rM rN rE rP rQ rDP rDQ rQI rL rC rS rPre rTL rT rA kO kM kN kE kP kQ kDP kDQ
    kQI kL kC kS kPre kTL kT kA fO fM fN fE fP fQ fDP fDQ fQI fL fC fS fPre fTL fT kv olk clk el1 elK pl1 plK
    ql1 qlK dpl qil dql slK preLen
  exact ⟨hheld, hheld2, hpw, fTL, fT⟩

theorem spec_spP {ts : List FnTable} {s : State} (hs : (specP ts).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 108 ≤ 2 ^ 32 := by
  decP_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, hsa⟩

/-- The entry's layout. -/
theorem okP_of_pre {ts : List FnTable} {s : State} (h : (specP ts).pre s) :
    ((ep s ai au af T aiL auL afL TL).layP (arg s 25) (arg s 26).toNat).Ok (entered frameBytes s) := by
  decP_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPre oTL oT oA
    mN mE mP mQ mDP mDQ mQI mL mC mS mPre mTL mT mA nS nA eS eA pS pA qS qA dpS dpA dqS dqA qiS qiA lS lA cS cA
    sPre sTL sT sA preA tlA tA rO rM rN rE rP rQ rDP rDQ rQI rL rC rS rPre rTL rT rA kO kM kN kE kP kQ kDP kDQ
    kQI kL kC kS kPre kTL kT kA fO fM fN fE fP fQ fDP fDQ fQI fL fC fS fPre fTL fT kv olk clk el1 elK pl1 plK
    ql1 qlK dpl qil dql slK preLen
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kM kN kE kP kQ kDP kDQ kQI kL kC kS kPre kTL kT kA
  have a1 : arg s 1 = arg s 4 := BitVec.eq_of_toNat_eq olk
  have a20 : arg s 20 = arg s 4 := BitVec.eq_of_toNat_eq clk
  have a12 : arg s 12 = arg s 8 := BitVec.eq_of_toNat_eq dpl
  have a16 : arg s 16 = arg s 8 := BitVec.eq_of_toNat_eq qil
  have a14 : arg s 14 = arg s 10 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPre oTL oT oA rO kO fO
  rw [clk] at hrd oC mC cS cA rC kC fC
  rw [dpl] at hrd oDP mDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI mQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ mDQ dqS dqA rDQ kDQ fDQ
  rw [ep_layP]
  refine ok_entered_of (S := 3608) rfl (by decide) hsp (by simp) (by simp; omega_arith) ?_ ?_
    ⟨108, by simp, by rw [hwr]; simp⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [hrd]
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]
  · intro r hr
    rw [hwr]
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [ep]
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kL, kC, kTL, kT, kPre, kO, kM, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [rO, rM, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC, oTL, oT, oPre, oA, mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC, mTL,
      mT, mPre, mA, nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm, sTL, sT,
      sPre, sA]
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨oM, oS⟩, mS, fun _ h => h.elim⟩
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth, Sig.tableRegion]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 3).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 5).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 7).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 9).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 11).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 13).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 15).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 17).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 19).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 21).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 23).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 24).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 25).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 27 := by simpa using hj
    rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a12, a14, a16, a20]

/-- The state the body starts from, and what the precomputed entry adds, from the facts of the
precondition it needs. -/
theorem in_of_facts {s : State}
    (okP : ((ep s ai au af T aiL auL afL TL).layP (arg s 25) (arg s 26).toNat).Ok (entered frameBytes s))
    (hsp : 3608 ≤ (s.gpr .esp).toNat)
    (kv : Spec.Rsa.lenValid (arg s 4).toNat) (el1 : 1 ≤ (arg s 6).toNat) (elK : (arg s 6).toNat ≤ (arg s 4).toNat)
    (pl1 : 1 ≤ (arg s 8).toNat) (plK : (arg s 8).toNat < (arg s 4).toNat) (ql1 : 1 ≤ (arg s 10).toNat)
    (qlK : (arg s 10).toNat < (arg s 4).toNat) (slK : Spec.RsaPss.scratchWords (arg s 4).toNat ≤ (arg s 22).toNat)
    (kN : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩)
    (kE : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩)
    (kP : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 7).setWidth 64, (arg s 8).toNat⟩)
    (kQ : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩)
    (kPre : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 25).setWidth 64, (arg s 26).toNat * 8⟩)
    (preLen : (arg s 26).toNat =
      Spec.Rsa.privatePrecomputedWords (arg s 4).toNat (arg s 8).toNat (arg s 10).toNat)
    (key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat)
      (Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat) =
        some (Spec.Rsa.wordsAt s.mem ((arg s 25).setWidth 64) (arg s 26).toNat))
    (hT : T (entered frameBytes s)) (hTL : TL (entered frameBytes s)) :
    In (ep s ai au af T aiL auL afL TL) (entered frameBytes s) ∧
      XP (ep s ai au af T aiL auL afL TL) (arg s 25) (arg s 26).toNat (entered frameBytes s) := by
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3608, 3608⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.sub_below _ (by omega) (by omega)
  have fr : ∀ {R : Region}, (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 3608, 3608⟩ : Region).Disjoint R →
      R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt (entered frameBytes s).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
    fun hk hl => Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hk.sub_left below16).symm) hl
  have wf : Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 25).setWidth 64) (arg s 26).toNat =
      Spec.Rsa.wordsAt s.mem ((arg s 25).setWidth 64) (arg s 26).toNat := by
    refine Proof.Rsa.wordsAt_frame hpush (by omega) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [show 8 * (arg s 26).toNat = (arg s 26).toNat * 8 from Nat.mul_comm _ _]
    exact (kPre.sub_left below16).symm
  have nB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat :=
    fr (R := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩) kN (by show (arg s 4).toNat ≤ 2 ^ 64; omega)
  have eB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 5).setWidth 64) (arg s 6).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat :=
    fr (R := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩) kE (by show (arg s 6).toNat ≤ 2 ^ 64; omega)
  have pB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 7).setWidth 64) (arg s 8).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat :=
    fr (R := ⟨(arg s 7).setWidth 64, (arg s 8).toNat⟩) kP (by show (arg s 8).toNat ≤ 2 ^ 64; omega)
  have qB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 9).setWidth 64) (arg s 10).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat :=
    fr (R := ⟨(arg s 9).setWidth 64, (arg s 10).toNat⟩) kQ (by show (arg s 10).toNat ≤ 2 ^ 64; omega)
  refine ⟨⟨okBase okP, kv, el1, elK, pl1, plK, ql1, qlK, slK, (arg s 18).isLt, (arg s 22).isLt, nB, eB, hT, hTL⟩,
    okP, preLen, ?_⟩
  show Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 7).setWidth 64) (arg s 8).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 9).setWidth 64) (arg s 10).toNat) =
      some (Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 25).setWidth 64) (arg s 26).toNat)
  rw [pB, qB, wf]
  exact key

/-- The state the body starts from, and what the precomputed entry adds. -/
theorem in_of_preP {ts : List FnTable} {s : State} (h : (specP ts).pre s)
    (hT : T (entered frameBytes s)) (hTL : TL (entered frameBytes s)) :
    In (ep s ai au af T aiL auL afL TL) (entered frameBytes s) ∧
      XP (ep s ai au af T aiL auL afL TL) (arg s 25) (arg s 26).toNat (entered frameBytes s) := by
  have okP := okP_of_pre (ai := ai) (au := au) (af := af) (T := T) (aiL := aiL) (auL := auL) (afL := afL)
    (TL := TL) h
  decP_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPre oTL oT oA
    mN mE mP mQ mDP mDQ mQI mL mC mS mPre mTL mT mA nS nA eS eA pS pA qS qA dpS dpA dqS dqA qiS qiA lS lA cS cA
    sPre sTL sT sA preA tlA tA rO rM rN rE rP rQ rDP rDQ rQI rL rC rS rPre rTL rT rA kO kM kN kE kP kQ kDP kDQ
    kQI kL kC kS kPre kTL kT kA fO fM fN fE fP fQ fDP fDQ fQI fL fC fS fPre fTL fT kv olk clk el1 elK pl1 plK
    ql1 qlK dpl qil dql slK preLen
  exact in_of_facts okP (by simp only [stackBytes, frameBytes] at hsp; omega) kv el1 elK pl1 plK ql1 qlK slK
    kN kE kP kQ kPre preLen h hT hTL

variable {vs : List TVar}

theorem entered_stateP (hc : Coh vs) {s s' : State} (hs : (specP (tables vs)).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem ((arg s 24).setWidth 64) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (fun σ t => S (ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s 24) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
      (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s 23) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
        (s'.syms w₁.g.H.finN))) σ t ∧
      XP (ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s 24) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
      (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s 23) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
        (s'.syms w₁.g.H.finN))) (arg s 25) (arg s 26).toNat σ)
      (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tabP hs
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_spP hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have ok := (in_of_preP (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs trivial trivial).1.ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.X86.mem_names hw
  have hnL := Proof.HashTable.X86.mem_names hw₁
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  have tf := tabFacts_entered (argv := e0.argv) (ro := e0.ro) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 24)
    (by simp [e0, ep]) hfit hc hpw' hw hh
  have tfL := tabFacts_entered (argv := e0.argv) (ro := e0.ro) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 23)
    (by simp [e0, ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  have hi := in_of_preP (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs tf tfL
  exact ⟨⟨⟨hi.1, ⟨hi.1.ok, hi.1.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, hi.2⟩, rfl⟩

variable (vs)

/-- The code, calling `vg_rsa_private_checked_precomputed` over `c` and `w`,
with both hash functions any of the tables of `vs`. -/
abbrev decCodeP (c : CrtImpl) (w : CrtPImpl) : Prog isa :=
  decrypt (fnsOf vs) (privNameP c) (privCodeP c w) privArgsP

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev dspecP : Contract isa := specP (tables vs)

variable {vs}

theorem code_noSpP (c : CrtImpl) (w : CrtPImpl) : NoSp (decCodeP vs c w) :=
  have n := fnsOf_noSp vs
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSpP n.1 n.2.1 n.2.2 c w)) restore_noSp)

theorem code_spP (c : CrtImpl) (w : CrtPImpl) : (decCodeP vs c w).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSpP c w)

theorem code_okP (hc : Coh vs) (c : CrtImpl) (cw : CrtPImpl) {s : State} (hs : (dspecP vs).pre s) :
    WP isa (decCodeP vs c cw) s fun t => abiPreserved s t ∧ (dspecP vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tabP hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have hidxL := (held_tableOf hfitL hhL).2.1
  have he := entered_stateP hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := he.1.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_spP hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  have hb := (body_vpP w₁.g (epw (vs := vs) s w w₁) (arg s 25) (arg s 26).toNat w.g (fun _ x => x) (fun _ x => x)
    (fne_of hw) c cw).wp _ _ he
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSpP ni nu nf c cw) hsp (by omega)
    (W := (epw (vs := vs) s w w₁).lay.W)
    (Q := fun r m => Res w₁.g.G w.g.G (epw (vs := vs) s w w₁) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (epw (vs := vs) s w w₁).argv) (ro := (epw (vs := vs) s w w₁).ro)
        (rw := (epw (vs := vs) s w w₁).rw) (C := 3448) hsp,
      ret_eq (argv := (epw (vs := vs) s w w₁).argv) (ro := (epw (vs := vs) s w w₁).ro)
        (rw := (epw (vs := vs) s w w₁).rw) (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s w w₁).ro) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes]
    intro H G hH hG
    rw [hashAt_tableOf hfitL hidxL, Option.some.injEq] at hH
    rw [hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    have hP : pB (epw (vs := vs) s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat :=
      ro (R := (epw (vs := vs) s w w₁).PP) (by simp)
    have hQ : qB (epw (vs := vs) s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat :=
      ro (R := (epw (vs := vs) s w w₁).QQ) (by simp)
    have hDP : dpB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 11).setWidth 64)
        (arg s 8).toNat := ro (R := (epw (vs := vs) s w w₁).DP) (by simp)
    have hDQ : dqB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 13).setWidth 64)
        (arg s 10).toNat := ro (R := (epw (vs := vs) s w w₁).DQ) (by simp)
    have hQI : qiB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 15).setWidth 64)
        (arg s 8).toNat := ro (R := (epw (vs := vs) s w w₁).QI) (by simp)
    have hL : labB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 17).setWidth 64)
        (arg s 18).toNat := ro (R := (epw (vs := vs) s w w₁).LAB) (by simp)
    have hC : ctB (epw (vs := vs) s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 19).setWidth 64)
        (arg s 4).toNat := ro (R := (epw (vs := vs) s w w₁).CT) (by simp)
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem code_ctP (hc : Coh vs) (c : CrtImpl) (cw : CrtPImpl) :
    ConstantTime isa (dspecP vs).pre (dspecP vs).pub (decCodeP vs c cw) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tabP h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23, a24, a25, a26⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  have hep : epw (vs := vs) s₁ w w₁ = ep s₂ (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s₂ 24) (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN))
      (s₁.syms w₁.g.H.initN) (s₁.syms w₁.g.H.updN) (s₁.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s₂ 23) (s₁.syms w₁.g.H.initN) (s₁.syms w₁.g.H.updN)
        (s₁.syms w₁.g.H.finN)) := by
    obtain ⟨hl', -⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a4, a6])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl') (by simp [RsaPkcs1Sig.bytesAt_len, a4])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a17, a18, a19, a21, a22, a23, a24]
    rw [a3, a4] at hn
    rw [a5, a6] at he
    rw [hn, he]
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  refine (wrap_ct (F := frameBytes) (body_noSpP ni nu nf c cw) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vpP w₁.g (epw (vs := vs) s₁ w w₁) (arg s₁ 25) (arg s₁ 26).toNat w.g (fun _ x => x) (fun _ x => x)
    (fne_of hw) c cw).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  refine ⟨entered frameBytes s₁, entered frameBytes s₂,
    entered_stateP hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl), ?_⟩
  rw [hep, a25, a26]
  exact entered_stateP hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'

/-- `vg_rsa_oaep_decrypt_precomputed`, calling `vg_rsa_private_checked_precomputed`
over `c` and `w`, with both hash functions any of the tables of `vs`, meets the
precomputed contract (satisfiable, `Dec/PSat.lean`). -/
theorem decP_verified (hc : Coh vs) (hsat : ∃ s, (dspecP vs).pre s) (c : CrtImpl) (w : CrtPImpl) :
    Verified target (decCodeP vs c w) (dspecP vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_okP hc c w hs; ⟨t, s', he, hq.1, hq.2⟩, code_ctP hc c w, hsat⟩

end VG.Proof.RsaOaep.X86.Dec
