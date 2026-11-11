module

public import VerifiedGarbage.Proof.RsaPss.X86.SgPCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety

/-!
# RSASSA-PSS signing on x86, given `pre`: verified

`signPrecomputedMdTableContract`'s precondition gives `vg_rsa_pss_sign`'s
state where the body starts, and `XP`: the wider layout and `pre` the key's
values (`in_of_preP`, `entered_stateP`). The body (`body_vpP`) in the frames
around it gives the result (`code_okP`), in time that depends on what the
two runs share (`code_ctP`): `vg_rsa_pss_sign_precomputed`, calling
`vg_rsa_private_checked_precomputed` over `c` and `w`, is verified
(`signP_verified`), given a state that meets the contract (`SgPSat.lean`).
-/

-- separate module: builds in parallel with the satisfying state (`SgPSat`), which needs only the contract.

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP)
open VG.Proof.RsaOaep.X86 (OHash TabFacts)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable {hai hac had : BitVec 32} {TH : State → Prop} {ai au af : BitVec 32} {T : State → Prop}

theorem ep_layP (D : Nat) (s : State) (pre : BitVec 32) (L : Nat) :
    (ep s hai hac had TH ai au af T).layP D pre L =
      layOf frameBytes ((ep s hai hac had TH ai au af T).argv D ++ [pre, BitVec.ofNat 32 L])
        ((ep s hai hac had TH ai au af T).ro D ++ [preR pre L]) (ep s hai hac had TH ai au af T).rw s 3448 := rfl

/-- The tables, as the contract gives them. -/
theorem spec_tabP {tsH ts : List FnTable} {s : State} (h : (specP tsH ts).pre s) :
    (∃ T ∈ tsH, Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s T)) ∧
      ((tsH.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (arg s 22).toNat + 44 ≤ 2 ^ 32 ∧ (arg s 23).toNat + 44 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem ((arg s 22).setWidth 64) (arg s 17) := by
  signP_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPre oTH oT oA nS nA eS eA pS pA
    qS qA dpS dpA dqS dqA qiS qiA dS dA slS slA sPre sTH sT sA preA thA tA rO rN rE rP rQ rDP rDQ rQI rD rSl rS
    rPre rTH rT rA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPre kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPre
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK preLen key
  exact ⟨hheldH, hheld, hpw, fTH, fT, h⟩

theorem spec_spP {tsH ts : List FnTable} {s : State} (hs : (specP tsH ts).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 104 ≤ 2 ^ 32 := by
  signP_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, hsa⟩

/-- The entry's layout. -/
theorem okP_of_pre {tsH ts : List FnTable} {s : State} (h : (specP tsH ts).pre s) :
    ((ep s hai hac had TH ai au af T).layP (arg s 17).toNat (arg s 24) (arg s 25).toNat).Ok
      (entered frameBytes s) := by
  signP_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPre oTH oT oA nS nA eS eA pS pA
    qS qA dpS dpA dqS dqA qiS qiA dS dA slS slA sPre sTH sT sA preA thA tA rO rN rE rP rQ rDP rDQ rQI rD rSl rS
    rPre rTH rT rA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPre kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPre
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK preLen key
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPre kTH kT kA
  have a1 : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq olk
  have a11 : arg s 11 = arg s 7 := BitVec.eq_of_toNat_eq dpl
  have a15 : arg s 15 = arg s 7 := BitVec.eq_of_toNat_eq qil
  have a13 : arg s 13 = arg s 9 := BitVec.eq_of_toNat_eq dql
  rw [olk] at hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPre oTH oT oA rO kO fO
  rw [dpl] at hrd oDP dpS dpA rDP kDP fDP
  rw [qil] at hrd oQI qiS qiA rQI kQI fQI
  rw [dql] at hrd oDQ dqS dqA rDQ kDQ fDQ
  rw [ep_layP]
  refine ok_entered_of (S := 3608) rfl (by decide) hsp (by simp) (by simp; omega_arith) ?_ ?_
    ⟨104, by simp, by rw [hwr]; simp⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [hrd]
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]
  · intro r hr
    rw [hwr]
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [ep]
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kP, kQ, kDP, kDQ, kQI, kD, kSl, kTH, kT, kPre, kO, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rO, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oP, oQ, oDP, oDQ, oQI, oD, oSl, oTH, oT, oPre, oA, nS.symm, eS.symm, pS.symm, qS.symm,
      dpS.symm, dqS.symm, qiS.symm, dS.symm, slS.symm, sTH, sT, sPre, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth, Sig.tableRegion]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 12).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 14).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 16).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 18).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 22).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 23).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 24).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 20).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 26 := by simpa using hj
    rcases (by omega_using [this] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
        j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
        j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1, a11, a13, a15]

/-- The state the body starts from, and what the precomputed entry adds, from the facts of the
precondition it needs. -/
theorem in_of_facts {s : State} {D : Nat}
    (okP : ((ep s hai hac had TH ai au af T).layP D (arg s 24) (arg s 25).toNat).Ok (entered frameBytes s))
    (hsp : 3608 ≤ (s.gpr .esp).toNat)
    (kv : Spec.Rsa.lenValid (arg s 3).toNat) (el1 : 1 ≤ (arg s 5).toNat) (elK : (arg s 5).toNat ≤ (arg s 3).toNat)
    (pl1 : 1 ≤ (arg s 7).toNat) (plK : (arg s 7).toNat < (arg s 3).toNat) (ql1 : 1 ≤ (arg s 9).toNat)
    (qlK : (arg s 9).toNat < (arg s 3).toNat) (slK : Spec.RsaPss.scratchWords (arg s 3).toNat ≤ (arg s 21).toNat)
    (kN : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩)
    (kE : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩)
    (kP : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩)
    (kQ : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩)
    (kPre : (⟨(s.gpr .esp).setWidth 64 - 3608#64, 3608⟩ : Region).Disjoint
      ⟨(arg s 24).setWidth 64, (arg s 25).toNat * 8⟩)
    (preLen : (arg s 25).toNat =
      Spec.Rsa.privatePrecomputedWords (arg s 3).toNat (arg s 7).toNat (arg s 9).toNat)
    (key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
      (Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat) =
        some (Spec.Rsa.wordsAt s.mem ((arg s 24).setWidth 64) (arg s 25).toNat))
    (hTH : TH (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In D (ep s hai hac had TH ai au af T) (entered frameBytes s) ∧
      XP D (ep s hai hac had TH ai au af T) (arg s 24) (arg s 25).toNat (entered frameBytes s) := by
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
  have wf : Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 24).setWidth 64) (arg s 25).toNat =
      Spec.Rsa.wordsAt s.mem ((arg s 24).setWidth 64) (arg s 25).toNat := by
    refine Proof.Rsa.wordsAt_frame hpush (by omega) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [show 8 * (arg s 25).toNat = (arg s 25).toNat * 8 from Nat.mul_comm _ _]
    exact (kPre.sub_left below16).symm
  have nB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat :=
    fr (R := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩) kN (by show (arg s 3).toNat ≤ 2 ^ 64; omega)
  have eB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 4).setWidth 64) (arg s 5).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat :=
    fr (R := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩) kE (by show (arg s 5).toNat ≤ 2 ^ 64; omega)
  have pB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 6).setWidth 64) (arg s 7).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat :=
    fr (R := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩) kP (by show (arg s 7).toNat ≤ 2 ^ 64; omega)
  have qB : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 8).setWidth 64) (arg s 9).toNat =
      Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat :=
    fr (R := ⟨(arg s 8).setWidth 64, (arg s 9).toNat⟩) kQ (by show (arg s 9).toNat ≤ 2 ^ 64; omega)
  refine ⟨⟨okBase okP, kv, el1, elK, pl1, plK, ql1, qlK, slK, (arg s 19).isLt, (arg s 21).isLt, nB, eB, hTH, hT⟩,
    okP, preLen, ?_⟩
  show Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 6).setWidth 64) (arg s 7).toNat)
    (Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 8).setWidth 64) (arg s 9).toNat) =
      some (Spec.Rsa.wordsAt (entered frameBytes s).mem ((arg s 24).setWidth 64) (arg s 25).toNat)
  rw [pB, qB, wf]
  exact key

/-- The state the body starts from, and what the precomputed entry adds. -/
theorem in_of_preP {tsH ts : List FnTable} {s : State} (h : (specP tsH ts).pre s)
    (hTH : TH (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In (arg s 17).toNat (ep s hai hac had TH ai au af T) (entered frameBytes s) ∧
      XP (arg s 17).toNat (ep s hai hac had TH ai au af T) (arg s 24) (arg s 25).toNat (entered frameBytes s) := by
  have okP := okP_of_pre (hai := hai) (hac := hac) (had := had) (TH := TH) (ai := ai) (au := au) (af := af)
    (T := T) h
  signP_pre at h
  sig_split h
  rename_i hsp hsa hheldH hheld hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oPre oTH oT oA nS nA eS eA pS pA
    qS qA dpS dpA dqS dqA qiS qiA dS dA slS slA sPre sTH sT sA preA thA tA rO rN rE rP rQ rDP rDQ rQI rD rSl rS
    rPre rTH rT rA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kPre kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fPre
    fTH fT kv olk el1 elK pl1 plK ql1 qlK dpl qil dql slK preLen key
  exact in_of_facts okP (by simp only [stackBytes, frameBytes] at hsp; omega) kv el1 elK pl1 plK ql1 qlK slK
    kN kE kP kQ kPre preLen key hTH hT


variable {vs : List MVar} {gs : List TVar}
theorem code_noSpP (hok : OK vs gs) (c : CrtImpl) (w : CrtPImpl) : NoSp (signCodeP vs gs c w) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSpP (fnsSp vs gs) (hall_of hok) c w)) restore_noSp)

theorem code_spP (hok : OK vs gs) (c : CrtImpl) (w : CrtPImpl) :
    (signCodeP vs gs c w).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSpP hok c w)

/-- The digest's length, from the hash function the table names. -/
theorem dlen_ofP {s : State} (hs : (sspecP vs gs).pre s) {w : MVar}
    (hh : Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w))) :
    (arg s 17).toNat = w.h.D := by
  obtain ⟨-, -, -, hfitH, -, hdl⟩ := spec_tabP hs
  have := hdl _ (Proof.MdHashTable.X86.hashAt_tableOf hfitH (Proof.MdHashTable.X86.held_tableOf hfitH hh).2.2.2)
  rw [this, w.h.glen]

/-- The entry state, for the tables of `w` at the argument 22 and `wg` at
23, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_stateP (hok : OK vs gs) {s s' : State} (hs : (sspecP vs gs).pre s) {w : MVar} {wg : TVar}
    (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hhH : Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w)))
    (hh : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (Proof.HashTable.X86.tableOf wg)))
    (hsy : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s.syms n = s'.syms n) :
    Sy (S w.h (epw vs gs s s' w wg)) (entered frameBytes s) (entered frameBytes s) ∧
      XP w.h.D (epw vs gs s s' w wg) (arg s 24) (arg s 25).toNat (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitH, hfit, -⟩ := spec_tabP hs
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_spP hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hD := dlen_ofP hs hhH
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  have ok := (in_of_preP (hai := 0) (hac := 0) (had := 0) (TH := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs trivial trivial).1.ok
  rw [ep_lay] at ok
  have hn := Proof.MdHashTable.X86.mem_names hw
  have hng := Proof.HashTable.X86.mem_names hwg
  have hsyH : ∀ n ∈ Proof.MdHashTable.X86.names vs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_left _ h)
  have hsyG : ∀ n ∈ Proof.HashTable.X86.names gs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_right _ h)
  have tf := Proof.HashTable.X86.tabFacts_entered (argv := e0.argv (arg s 17).toNat) (ro := e0.ro (arg s 17).toNat)
    (rw := e0.rw) (C := 3448) hsp ok (p := arg s 23) (by simp [e0, ep]) hfit hok.2.2.1 hpwG hwg hh
  rw [hsyG _ hng.1, hsyG _ hng.2.1, hsyG _ hng.2.2] at tf
  have sy : (entered frameBytes s).syms = s.syms := pushRegs_syms s _
  obtain ⟨m0, m3, m4, m5⟩ := Proof.MdHashTable.X86.held_entered (argv := e0.argv (arg s 17).toNat)
    (ro := e0.ro (arg s 17).toNat) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 22) (by simp [e0, ep]) hfitH hhH
  have hf := Proof.MdHashTable.X86.hfacts_of hok.1 (σ := entered frameBytes s) (by rw [sy]; exact hpwH) hw m0 m3 m4
  rw [sy, hsyH _ hn.1, hsyH _ hn.2.2.2.1, hsyH _ hn.2.2.2.2] at hf
  have hi := in_of_preP (hai := s'.syms w.h.H.st.initN) (hac := s'.syms w.h.H.compN)
    (had := s'.syms (Proof.MdHashTable.X86.digName w)) (TH := THw vs w (arg s 22) s')
    (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN) (af := s'.syms wg.g.H.finN) hs ⟨hf, m5⟩ tf
  rw [hD] at hi
  exact ⟨⟨⟨hi.1, ⟨hi.1.ok, hi.1.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩, hi.2⟩

theorem code_okP (hok : OK vs gs) (c : CrtImpl) (cw : CrtPImpl) {s : State} (hs : (sspecP vs gs).pre s) :
    WP isa (signCodeP vs gs c cw) s fun t => abiPreserved s t ∧ (sspecP vs gs).post s t := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨T, hT, hh⟩, -, hfitH, hfit, -⟩ := spec_tabP hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  have hidxH := (Proof.MdHashTable.X86.held_tableOf hfitH hhH).2.2.2
  have hidx := (Proof.HashTable.X86.held_tableOf hfit hh).2.1
  have he := entered_stateP hok hs hw hwg hhH hh (s' := s) fun _ _ => rfl
  have hin := he.1.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_spP hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  obtain ⟨fneH, fne⟩ := fne_of hw hwg
  have hb := (body_vpP w.h (epw vs gs s s w wg) (arg s 24) (arg s 25).toNat (hok.2.1 w hw).1 (hok.2.1 w hw).2
    (fun _ x => x) fneH wg.g (fun _ x => x) fne c cw).wp _ _ he
  have hD := dlen_ofP hs hhH
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSpP (fnsSp vs gs) (hall_of hok) c cw) hsp
    (by omega) (W := ((epw vs gs s s w wg).lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G (epw vs gs s s w wg) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok hr
    rw [save_eq (argv := (epw vs gs s s w wg).argv (arg s 17).toNat) (ro := (epw vs gs s s w wg).ro (arg s 17).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 3448) hsp,
      ret_eq (argv := (epw vs gs s s w wg).argv (arg s 17).toNat) (ro := (epw vs gs s s w wg).ro (arg s 17).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw vs gs s s w wg).ro (arg s 17).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argSlots, argVal, argBytes]
    intro H G hH hG
    rw [Proof.MdHashTable.X86.hashAt_tableOf hfitH hidxH, Option.some.injEq] at hH
    rw [Proof.HashTable.X86.hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    rw [show pB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).PP) (by simp),
      show qB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).QQ) (by simp),
      show dpB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).DP) (by simp),
      show dqB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).DQ) (by simp),
      show qiB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).QI) (by simp),
      show saltB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).SALT) (by simp)]
      at res
    have hdg : digB w.h (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 16).setWidth 64) (arg s 17).toNat := by
      unfold digB; rw [← hD]; exact ro (R := (epw vs gs s s w wg).DIG (arg s 17).toNat) (by simp)
    rw [hdg, hD] at res
    rw [BitVec.setWidth_append_eq_right, w.h.glen]
    exact res

theorem code_ctP (hok : OK vs gs) (c : CrtImpl) (cw : CrtPImpl) :
    ConstantTime isa (sspecP vs gs).pre (sspecP vs gs).pub (signCodeP vs gs c cw) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨T, hT, hh₁⟩, -, -, -, -⟩ := spec_tabP h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabH, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23, a24, a25⟩ := hp
  have hhH₂ := (htabH _ _ rfl rfl _ hTH).mp hhH₁
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s₂.syms n = s₁.syms n :=
    fun n hn => (hsy n (by simpa [Proof.MdHashTable.X86.names, Proof.HashTable.X86.names] using hn)).symm
  have hep : epw vs gs s₁ s₁ w wg = epw vs gs s₂ s₁ w wg := by
    obtain ⟨hl', -⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a3, a5])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl') (by simp [RsaPkcs1Sig.bytesAt_len, a3])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a12, a14, a16, a18, a19, a20, a21, a22, a23]
    rw [a2, a3] at hn
    rw [a4, a5] at he
    rw [hn, he]
  obtain ⟨fneH, fne⟩ := fne_of hw hwg
  refine (wrap_ct (F := frameBytes) (body_noSpP (fnsSp vs gs) (hall_of hok) c cw) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vpP w.h (epw vs gs s₁ s₁ w wg) (arg s₁ 24) (arg s₁ 25).toNat (hok.2.1 w hw).1 (hok.2.1 w hw).2
    (fun _ x => x) fneH wg.g (fun _ x => x) fne c cw).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  refine ⟨entered frameBytes s₁, entered frameBytes s₂,
    entered_stateP hok h₁ hw hwg hhH₁ hh₁ (s' := s₁) (fun _ _ => rfl), ?_⟩
  rw [hep, a24, a25]
  exact entered_stateP hok h₂ hw hwg hhH₂ hh₂ (s' := s₁) hsy'

/-- `vg_rsa_pss_sign_precomputed`, calling `vg_rsa_private_checked_precomputed`
over `c` and `w`, with the hash function any of the tables of `vs` and MGF1's
any of `gs`, meets the precomputed contract (satisfiable, `SgPSat.lean`). -/
theorem signP_verified (hok : OK vs gs) (hsat : ∃ s, (sspecP vs gs).pre s) (c : CrtImpl) (w : CrtPImpl) :
    Verified target (signCodeP vs gs c w) (sspecP vs gs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_okP hok c w hs; ⟨t, s', he, hq.1, hq.2⟩, code_ctP hok c w, hsat⟩

end VG.Proof.RsaPss.X86.Sg
