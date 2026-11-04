module

import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.RsaPss.Arm.SgChk
public import VerifiedGarbage.Proof.MdHashTable.Arm.Tables
public import VerifiedGarbage.Proof.HashTable.Arm
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.RsaPss.Arm.Table

/-!
# RSASSA-PSS signing on ARMv7: verified

The body for the hash function `h` of the table `hash` and MGF1's `g` of
the table `mgf1` (`body_vp`): the checks, then zeros and 0 if something does
not fit, or the encoding and the call. Before it, the table's index chooses
the body for `h`'s shape (`tab_vp`, by RSAES-OAEP's `byLen_vp`). The frames
around it (`wrap_ok`, `wrap_ct`), the result as the shared contract states
it, with `hash` any of the tables of `MdHash` of `mvs` and `mgf1` any of the
tables of `Hash` of `vs`: `vg_rsa_pss_sign`, calling `vg_rsa_private_checked`
over any implementation `v` of `vg_rsa_private_crt`, is verified
(`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (OHash tA wp_ldrT St_roR St_roW byLen_vp)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

variable (h : PssHash)

theorem body_vp (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signBody f fg h.sh (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Sy (Fin h g.G P)) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk h.sh)) (.seq (.block (params ++ saltFits)) (.ite .ne signFail
    (.seq (signEnc f fg h.sh) (.seq (.block privArgs)
      (.call (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v))))))) _
  exact (VP.syms (chk_vp h P)).seq ((VP.syms (par_vp h P)).seq (VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g.G P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (((enc_vp h P Q hP).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩) fun _ _ h => h).seq
      ((VP.syms (pa_vp h g.G P)).seq (VP.syms (call_vp h g P v))))))

/-- The load of the table's word 5. -/
theorem idxWord_cert :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1]) (.block [.ldr .r1 .r1 20]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The comparisons of the index in `r1` with each of `idxs`. -/
theorem idxs_certs : ∀ x ∈ idxs, x < 2 ^ 32 ∧ encodable (BitVec.ofNat 32 x) = true ∧
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.cmp .r1 (.imm (BitVec.ofNat 32 x))]) hc).isSome =
      true := by
  intro x hx
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, _, by taint_decide⟩

/-- The index of the hash function of the table `hash` to `r1`. -/
theorem idx_vp {g : OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P) :
    VP (Sy (S h P)) (.block (idxLoad 22))
      (fun σ s => Sy (S h P) σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (Spec.HashTable.index h.G)) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.htbl
  have keep : ∀ σ s v, Sy (S h P) σ s → Sy (S h P) σ (s.setReg .r1 v) := fun σ s v ⟨⟨hi, st⟩, sy⟩ =>
    ⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩
  show VP _ (.block ([Impl.RsaPss.Arm.ld .r1 (arg 22)] ++ [.ldr .r1 .r1 20])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .r1 = P.hd)
    (VP.ldrSp (c := [(.r1, arg 22)]) (fun _ _ _ _ h₁ h₂ => h₁.1.2.sp.trans h₂.1.2.sp.symm)
      fun σ s hs => ?_)
    (VP.taint [.r1] idxWord_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · obtain ⟨⟨hi, st⟩, -⟩ := id hs
    obtain ⟨a22, r22, v22⟩ := argAt hi st (j := 22) (by decide)
    replace v22 : s.mem.readW ((P.lay h.D).fr (arg 22)) 32 = P.hd := v22
    have hw : WP isa (.block [.ldrSp .r1 (arg 22)]) s fun t => t = s.setReg .r1 P.hd := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec, arg_lt (show 22 < 24 by decide), ↓reduceIte, State.load32, st.sp, a22,
        r22, v22, Option.map_some, runStep_some, runBlock_nil]
      simp
    refine WP.mono hw fun t e => ?_
    subst e
    exact ⟨keep σ s _ hs, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · obtain ⟨hs2, h1⟩ := hs
    have T := Q.ht σ hs2.1.1.htabT
    refine WP.mono (wp_ldrT (by decide) h1 (St_roR hs2.1.2 tRo (tC 20 (by decide)))
      ((St_roW hs2.1.2 tRo (tC 20 (by decide))).trans T.ix)) fun t e => ?_
    subst e
    exact ⟨keep σ s _ hs2, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩

/-- The body for the hash function of the table `hash`, whose shape its
index gives. -/
theorem tab_vp (g : OHash) {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP) (Q : TF h g f fg dn P)
    (hsh : h.sh = ofIdx (Spec.HashTable.index h.G)) (hidx : Spec.HashTable.index h.G ∈ idxs)
    (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S h P)) (signTab f fg (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Sy (Fin h g.G P)) := by
  refine (idx_vp h P Q).seq (byLen_vp (D := Spec.HashTable.index h.G) (by
    simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hidx
    rcases hidx with e | e | e | e | e | e | e | e <;> rw [e] <;> decide)
    (fun _ _ hs => hs.2) (fun σ s v ⟨⟨⟨hi, st⟩, sy⟩, r1⟩ => ⟨⟨⟨hi, st.regs rfl rfl rfl rfl⟩, sy⟩, r1⟩) ?_
    hidx idxs_certs)
  rw [← hsh]
  exact (body_vp h g P Q v).mono (fun _ _ hs => hs.1) fun _ _ x => x

variable (mvs : List MVar) (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `MdHash` of `mvs` and MGF1's any of the tables
of `Hash` of `vs`. -/
abbrev signCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  sign (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

/-- The contract, with those tables. -/
abbrev sspec : Contract isa := spec (MdHashTable.Arm.tables mvs) (HashTable.Arm.tables vs)

variable {mvs vs}

/-- The tables, as the contract gives them: one of `hs` at the stack argument
18 and one of `ts` at 19, with the functions of distinct names at distinct
addresses, and the digest's length that of the former's hash function. -/
theorem spec_tab {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) :
    (∃ T ∈ hs, Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s T)) ∧
      ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
        (fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) ∧
      (stackArg s 18).toNat + 44 ≤ 2 ^ 32 ∧ (stackArg s 19).toNat + 20 ≤ 2 ^ 32 ∧
      Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 18)) (stackArg s 13) := by
  sign_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr oN oE oP oQ oDP oDQ oQI oD oSl oS oTH oT oA nS eS pS qS dpS dqS qiS dS
    slS sTH sT sA kO kN kE kP kQ kDP kDQ kQI kD kSl kS kTH kT kA fO fN fE fP fQ fDP fDQ fQI fD fSl fS fTH fT kv olk
    el1 elK pl1 plK ql1 qlK dpl qil dql slK
  exact ⟨hheld, hheld2, hpw, fTH, fT, h⟩

theorem spec_sp {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) : stackBytes ≤ s.sp.toNat := by
  sign_pre at h
  exact h.1

/-- The public parameters for the hash function's table of `w` and MGF1's of
`wg`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep s (s'.syms w.h.H.md.st.initN) (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w))
    (HTab w.h (MdHashTable.Arm.digName w) (MdHashTable.Arm.fnsOf mvs) (stackArg s 18) (s'.syms w.h.H.md.st.initN)
      (s'.syms w.h.H.md.compN) (s'.syms (MdHashTable.Arm.digName w)))
    (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (RsaOaep.Arm.TabFacts wg.g.H (HashTable.Arm.fnsOf vs) (stackArg s 19) (s'.syms wg.g.H.initN)
      (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN))

theorem gne_of {w : TVar} (hw : w ∈ vs) : (HashTable.Arm.fnsOf vs).init ≠ [] ∧ (HashTable.Arm.fnsOf vs).upd ≠ [] ∧
    (HashTable.Arm.fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [HashTable.Arm.fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

theorem fne_of {w : MVar} (hw : w ∈ mvs) : (MdHashTable.Arm.fnsOf mvs).init ≠ [] ∧
    (MdHashTable.Arm.fnsOf mvs).comp ≠ [] ∧ (MdHashTable.Arm.fnsOf mvs).dig ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [MdHashTable.Arm.fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The digest's length is that of `w`'s hash function. -/
theorem dl_of {s : State} {w : MVar} (hfit : (stackArg s 18).toNat + 44 ≤ 2 ^ 32)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hdl : Spec.RsaPss.digestLenOk 32 s.mem (State.addr (stackArg s 18)) (stackArg s 13)) :
    (stackArg s 13).toNat = w.h.D := by
  rw [hdl _ (MdHashTable.Arm.hashAt_tableOf hfit (MdHashTable.Arm.held_tableOf hfit hh).2.2.2), w.h.glen]

/-- The entry state, for the tables of `w` at the stack argument 18 and `wg`
at 19, with the functions where `s'` has them (`s'` has them where `s`
does). -/
theorem entered_state (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) {s s' : State}
    (hs : (sspec mvs vs).pre s) {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 18)) (FnTable.words isa s (MdHashTable.Arm.tableOf w)))
    (hhg : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (HashTable.Arm.tableOf wg)))
    (hsy : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s.syms n = s'.syms n) :
    Sy (S w.h (epw (mvs := mvs) (vs := vs) s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfit, hfitg, hdl⟩ := spec_tab hs
  have hD := dl_of hfit hh hdl
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_sp hs)
  have ok := (in_of_pre (hi := 0) (hc := 0) (hdg := 0) (HT := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs hD trivial trivial).ok
  rw [ep_lay] at ok
  have hn := MdHashTable.Arm.mem_names hw
  have hng := Proof.HashTable.Arm.mem_names hwg
  have ht := MdHashTable.Arm.htab_entered ok hsp' (p := stackArg s 18) (by simp [ep]) hfit hc hpwH hw hh
  have tf := Proof.HashTable.Arm.tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [ep]) hfitg hcg hpwG hwg hhg
  rw [hsy _ (List.mem_append_left _ hn.1), hsy _ (List.mem_append_left _ hn.2.1),
    hsy _ (List.mem_append_left _ hn.2.2)] at ht
  rw [hsy _ (List.mem_append_right _ hng.1), hsy _ (List.mem_append_right _ hng.2.1),
    hsy _ (List.mem_append_right _ hng.2.2)] at tf
  have hi := in_of_pre (hi := s'.syms w.h.H.md.st.initN) (hc := s'.syms w.h.H.md.compN)
    (hdg := s'.syms (MdHashTable.Arm.digName w)) (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN)
    (af := s'.syms wg.g.H.finN) hs hD ht tf
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

/-- What the body needs of the tables of `w` and `wg`. -/
theorem tf_of {s s' : State} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs) :
    TF w.h wg.g (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (MdHashTable.Arm.digName w)
      (epw (mvs := mvs) (vs := vs) s s' w wg) :=
  ⟨fun _ x => x, fun _ x => x, fne_of hw, gne_of hwg⟩

/-- Unfolds the contract's postcondition. -/
macro "sign_post" : tactic => `(tactic| (
  sig_post [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]))

theorem code_ok (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl) {s : State}
    (hs : (sspec mvs vs).pre s) :
    WP isa (signCode mvs vs v) s fun t => abiPreserved s t ∧ (sspec mvs vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, ⟨Tg, hTg, hhg⟩, -, hfit, hfitg, hdl⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  have hD := dl_of hfit hh hdl
  have hidx := (MdHashTable.Arm.held_tableOf hfit hh).2.2.2
  have hidxg := (Proof.HashTable.Arm.held_tableOf hfitg hhg).2.1
  have st := entered_state hc hcg hs hw hwg hh hhg (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_sp hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  let P := epw (mvs := mvs) (vs := vs) s s w wg
  have hb := (tab_vp w.h wg.g P (tf_of hw hwg) w.shape w.mem v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (P.lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G P (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 80) (C := 3440) (argv := P.argv w.h.D) (ro := (P.lay w.h.D).ro)
      (rw := (P.lay w.h.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sign_post
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 18) = State.addr (stackArg s 18) from rfl,
      MdHashTable.Arm.hashAt_tableOf hfit hidx, Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl,
      Proof.HashTable.Arm.hashAt_tableOf hfitg hidxg, Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (P.lay w.h.D).ro) =>
      entered_ro (F := frameBytes) (A := 80) (C := 3440) (argv := P.argv w.h.D) (rw := (P.lay w.h.D).rw) hin.ok
        hsp' hR
    have hP : pB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
      ro (R := P.PP) (by simp)
    have hQ : qB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
      ro (R := P.QQ) (by simp)
    have hDP : dpB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 6))
        (stackArg s 3).toNat := ro (R := P.DP) (by simp)
    have hDQ : dqB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 8))
        (stackArg s 5).toNat := ro (R := P.DQ) (by simp)
    have hQI : qiB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10))
        (stackArg s 3).toNat := ro (R := P.QI) (by simp)
    have hDg : digB w.h P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 12)) w.h.D :=
      ro (R := P.DIG w.h.D) (by simp)
    have hS : saltB P (entered frameBytes s) = Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 14))
        (stackArg s 15).toNat := ro (R := P.SALT) (by simp)
    unfold Res at res
    rw [hP, hQ, hDP, hDQ, hQI, hDg, hS] at res
    rw [w.h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (sspec mvs vs).pre (sspec mvs vs).pub (signCode mvs vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, ⟨Tg, hTg, hhg₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hTg
  sig_pub [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, htabg, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhg₂ := (htabg _ _ rfl rfl _ hTg).mp hhg₁
  have hsy' : ∀ n ∈ MdHashTable.Arm.names mvs ++ HashTable.Arm.names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by
      rcases List.mem_append.mp hn with e | e
      · exact List.mem_append_left _ e
      · exact List.mem_append_right _ (List.mem_append_left _ e))).symm
  have hep : epw (mvs := mvs) (vs := vs) s₁ s₁ w wg = epw (mvs := mvs) (vs := vs) s₂ s₁ w wg := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, h3])
    simp only [ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a8, a10, a12, a14, a15, a16, a17, a18, a19]
    rw [h2, h3] at hn
    rw [a0, a1] at he
    rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
      show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (tab_vp w.h wg.g (epw (mvs := mvs) (vs := vs) s₁ s₁ w wg) (tf_of hw hwg) w.shape w.mem v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc hcg h₁ hw hwg hh₁ hhg₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc hcg h₂ hw hwg hh₂ hhg₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the
hash function any of the tables of `MdHash` of `mvs` and MGF1's any of the
tables of `Hash` of `vs`, meets the shared contract (satisfiable,
`SgSat.lean`). -/
theorem sign_verified (hc : MdHashTable.Arm.Coh mvs) (hcg : HashTable.Arm.Coh vs) (hsat : ∃ s, (sspec mvs vs).pre s)
    (v : Proof.Rsa.Arm.CrtImpl) : Verified target (signCode mvs vs v) (sspec mvs vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc hcg v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc hcg v, hsat⟩

end VG.Proof.RsaPss.Arm.Sg
