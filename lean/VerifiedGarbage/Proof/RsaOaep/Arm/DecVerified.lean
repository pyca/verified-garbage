module

import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaOaep.Arm.DecEnd
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecChk
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaOaep.Arm.DecFail
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.HashTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.RsaOaep.Arm

/-!
# RSAES-OAEP decryption on ARMv7: verified

The body (`body_vp`): the private-key operation into `EM`'s place, the
digest length of the label's hash function's table (`len_vp`), and, for
that length (`byLen_vp`), zeros and `(r = 2) ? 2 : 0` if `k < 2 hLen + 2`,
or the decoding. The frames around it (`wrap_ok`, `wrap_ct`), the result as
the shared contract states it, for the label's hash function the one whose
table the stack argument 19 is and MGF1's the one whose table the stack
argument 20 is (`tabFacts_entered`): `vg_rsa_oaep_decrypt`, calling
`vg_rsa_private_checked` over any implementation `v` of
`vg_rsa_private_crt`, with both hash functions any of the tables of `vs`, is
verified (`dec_verified`). Every stage keeps the addresses of the statics
(`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.HashTable.Arm (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered)

section
variable {F G H : State → State → Prop} {a b c d e r : Prog isa}

theorem relCT_assoc' {Q R : State → State → Prop} (h : RelCT isa Q (.seq a (.seq b c)) R) :
    RelCT isa Q (.seq (.seq a b) c) R := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem VP.assoc' (h : VP F (.seq a (.seq b c)) G) : VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

/-- A piece of `n` steps, then the rest. -/
theorem VP.cont2 (h : VP F (.seq a b) G) (h₂ : VP G r H) : VP F (.seq a (.seq b r)) H := VP.assoc (h.seq h₂)

theorem VP.cont3 (h : VP F (.seq a (.seq b c)) G) (h₂ : VP G r H) : VP F (.seq a (.seq b (.seq c r))) H :=
  VP.assoc (VP.cont2 (VP.assoc' h) h₂)

theorem VP.cont4 (h : VP F (.seq a (.seq b (.seq c d))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d r)))) H :=
  VP.assoc (VP.cont3 (VP.assoc' h) h₂)

theorem VP.cont5 (h : VP F (.seq a (.seq b (.seq c (.seq d e)))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d (.seq e r))))) H :=
  VP.assoc (VP.cont4 (VP.assoc' h) h₂)

end

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The decoding, when `k ≥ 2 hLen + 2`, with the label's hash function `h`
and MGF1's `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => Sy (C2 h.H.D P) σ s ∧ isa.eval .ne s = some false) (decMain h.H f) (Sy (Fin h.G g.G P)) :=
  VP.cont2 ((labT_vp h P hTL fne).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (VP.cont4 (unmask_vp h g P hT fne) (VP.syms (VP.cont5 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
      (VP.cont4 (buf_vp h g P) ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (outCopy_vp h g P)
        (VP.cont2 (outMask_vp h g P) (end_vp h g P))))))))))

/-- The digest length of the label's hash function's table to `r1`. -/
theorem len_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ) :
    VP (R2 P) (.block (lenLoad 23)) (fun σ s => R2 P σ s ∧ s.gpr .r1 = BitVec.ofNat 32 h.H.D) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := tblL_of hi₀
  have keep : ∀ σ s v, R2 P σ s → R2 P σ (s.setReg .r1 v) := fun σ s v ⟨hc, hi, he, r0, hk⟩ =>
    ⟨Ctx.setReg_iff.mpr hc, hi, he, by simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r0, hk⟩
  show VP _ (.block ([Impl.RsaPss.Arm.ld .r1 (Impl.RsaPss.Arm.arg 23)] ++ [.ldr .r1 .r1 16])) _
  refine VP.block_append (G := fun σ s => R2 P σ s ∧ s.gpr .r1 = P.tabL)
    (VP.ldrSp (c := [(.r1, Impl.RsaPss.Arm.arg 23)]) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
      fun σ s hs => ?_)
    (VP.taint [.r1] lenWord_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · obtain ⟨hc, hi, -⟩ := id hs
    obtain ⟨a23, r23, v23⟩ := argAt hi hc.st (j := 23) (by decide)
    replace v23 : s.mem.readW (P.lay.fr (Impl.RsaPss.Arm.arg 23)) 32 = P.tabL := v23
    have hw : WP isa (.block [.ldrSp .r1 (Impl.RsaPss.Arm.arg 23)]) s fun t => t = s.setReg .r1 P.tabL := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec, arg_lt (show 23 < 25 by decide), ↓reduceIte, State.load32, hc.st.sp, a23,
        r23, v23, Option.map_some, runStep_some, runBlock_nil]
      simp
    refine WP.mono hw fun t e => ?_
    subst e
    exact ⟨keep σ s _ hs, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · obtain ⟨hr2, h1⟩ := hs
    have T := hTL σ hr2.2.1.tabTL
    refine WP.mono (wp_ldrT (by decide) h1 (St_roR hr2.1.st tRo (tC 16 (by decide)))
      ((St_roW hr2.1.st tRo (tC 16 (by decide))).trans T.d)) fun t e => ?_
    subst e
    exact ⟨keep σ s _ hr2, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Impl.Pbkdf2.Stream.Arm.Hash} (hD : G.D = G'.D) (f : Fns) :
    decTail G f = decTail G' f := by
  simp only [decTail, decMain, decChk, seedArgs, dbArgs, cmpSet, scanSet, tSet, mlSet, hD]

theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (v : Proof.Rsa.Arm.CrtImpl) :
    VP (Sy (S P)) (decBody f (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)) (Sy (Fin h.G g.G P)) := by
  refine VP.cont4 (VP.syms ((start_vp P).seq ((pa_vp P).seq ((call_vp P v).seq (len_vp h P hTL)))))
    (byLen_vp (D := h.H.D) (by have := h.D_le; omega) (fun _ _ hs => hs.1.2)
      (fun σ s v ⟨⟨⟨hc, hi, he, r0, hk⟩, r1⟩, sy⟩ => ⟨⟨⟨hc.regs rfl rfl rfl rfl, hi, he, r0, hk⟩, r1⟩, sy⟩) ?_
      h.lens lens_certs)
  show VP _ (decTail (ofLen h.H.D) f) _
  rw [decTail_D (G := ofLen h.H.D) (G' := h.H) rfl f]
  show VP _ (.seq (.block (decChk h.H)) (.ite .ne decFail (decMain h.H f))) _
  exact VP.seq ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨r2, _⟩, sy⟩ => ⟨r2, sy⟩) fun _ _ x => x) (VP.ite
    (fun _ _ _ _ h₁ h₂ => by
      rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT hTL fne))

variable (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with both hash
functions any of the tables of `vs`. -/
abbrev decCode (v : Proof.Rsa.Arm.CrtImpl) : Prog isa :=
  decrypt (fnsOf vs) (Proof.Rsa.Arm.privName v) (Proof.Rsa.Arm.privCode v)

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev dspec : Contract isa := spec (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w w₁ : TVar) : EP :=
  ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (stackArg s 20) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
    (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (stackArg s 19) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
      (s'.syms w₁.g.H.finN))

theorem spec_sp {s : State} (hs : (dspec vs).pre s) : stackBytes ≤ s.sp.toNat := by
  dec_pre at hs
  exact hs.1

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the tables of `w` at the stack argument 20 and `w₁`
at 19, with the functions where `s'` has them (`s'` has them where `s`
does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (dspec vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 20)) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem (State.addr (stackArg s 19)) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S (epw (vs := vs) s s' w w₁)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tab hs
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) (spec_sp hs)
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs trivial trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.Arm.mem_names hw
  have hnL := Proof.HashTable.Arm.mem_names hw₁
  have tf := tabFacts_entered ok hsp' (p := stackArg s 20) (by simp [ep]) hfit hc hpw' hw hh
  have tfL := tabFacts_entered ok hsp' (p := stackArg s 19) (by simp [ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs tf tfL
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (v : Proof.Rsa.Arm.CrtImpl) {s : State} (hs : (dspec vs).pre s) :
    WP isa (decCode vs v) s fun t => abiPreserved s t ∧ (dspec vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tab hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have hidxL := (held_tableOf hfitL hhL).2.1
  have st := entered_state hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := st.1.1
  have hsp := spec_sp hs
  have hsp' : 56 + frameBytes ≤ s.sp.toNat := Nat.le_trans (Nat.le_add_right _ _) hsp
  have hF : FrameOk frameBytes := by decide
  have hb := (body_vp w₁.g (epw (vs := vs) s s w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) v).wp _ _ st
  refine WP.mono (wrap_ok hF (by rw [Nat.add_comm]; exact hsp') (W := (epw (vs := vs) s s w w₁).lay.W)
    (Q := fun r m => Res w₁.g.G w.g.G (epw (vs := vs) s s w w₁) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 84) (C := 3440) (argv := (epw (vs := vs) s s w w₁).argv)
      (ro := (epw (vs := vs) s s w w₁).lay.ro) (rw := (epw (vs := vs) s s w w₁).lay.rw) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 19) = State.addr (stackArg s 19) from rfl, hashAt_tableOf hfitL hidxL,
      Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 20) = State.addr (stackArg s 20) from rfl, hashAt_tableOf hfit hidx,
      Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    have ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s s w w₁).lay.ro) =>
      entered_ro (F := frameBytes) (A := 84) (C := 3440) (argv := (epw (vs := vs) s s w w₁).argv)
        (rw := (epw (vs := vs) s s w w₁).lay.rw) hin.ok hsp' hR
    have hP : pB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).PP) (by simp)
    have hQ : qB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5)) (stackArg s 6).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).QQ) (by simp)
    have hDP : dpB (epw (vs := vs) s s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 7)) (stackArg s 4).toNat := ro (R := (epw (vs := vs) s s w w₁).DP) (by simp)
    have hDQ : dqB (epw (vs := vs) s s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 9)) (stackArg s 6).toNat := ro (R := (epw (vs := vs) s s w w₁).DQ) (by simp)
    have hQI : qiB (epw (vs := vs) s s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 11)) (stackArg s 4).toNat := ro (R := (epw (vs := vs) s s w w₁).QI) (by simp)
    have hL : labB (epw (vs := vs) s s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 13)) (stackArg s 14).toNat := ro (R := (epw (vs := vs) s s w w₁).LAB) (by simp)
    have hC : ctB (epw (vs := vs) s s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 15)) (stackArg s 0).toNat := ro (R := (epw (vs := vs) s s w w₁).CT) (by simp)
    unfold Res at res
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (v : Proof.Rsa.Arm.CrtImpl) :
    ConstantTime isa (dspec vs).pre (dspec vs).pub (decCode vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14, a15, a16, a17, a18, a19, a20⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  have hep : epw (vs := vs) s₁ s₁ w w₁ = epw (vs := vs) s₂ s₁ w w₁ := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.Arm.bytesAt_length, a0])
    simp only [ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a9, a11, a13, a14, a15, a17, a18, a19, a20]
    rw [h3, a0] at hn
    rw [a1, a2] at he
    rw [show State.addr (s₂.gpr .r3) = BitVec.setWidth 64 (s₂.gpr .r3) from rfl, hn,
      show State.addr (stackArg s₂ 1) = BitVec.setWidth 64 (stackArg s₂ 1) from rfl, he]
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; exact Nat.le_trans (Nat.le_add_right _ _) (spec_sp h₁)) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w₁.g (epw (vs := vs) s₁ s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_oaep_decrypt`, calling `vg_rsa_private_checked` over `v`, with
both hash functions any of the tables of `vs`, meets the shared contract
(satisfiable, `DecSat.lean`). -/
theorem dec_verified (hc : Coh vs) (hsat : ∃ s, (dspec vs).pre s) (v : Proof.Rsa.Arm.CrtImpl) :
    Verified target (decCode vs v) (dspec vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc v, hsat⟩

end VG.Proof.RsaOaep.Arm.Dec
