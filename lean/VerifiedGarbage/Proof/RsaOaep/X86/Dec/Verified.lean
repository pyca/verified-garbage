module

public import VerifiedGarbage.Proof.RsaOaep.X86.Dec.End
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# RSAES-OAEP decryption on x86: verified

As on ARMv7 (`Proof/RsaOaep/Arm/DecVerified.lean`): the private-key
operation and the check of `k` (`pa_vp`, `call_vp`, `chk_vp`), then zeros if
`k` is too short (`fail_vp`) or the decoding (`main_vp`): `body_vp`. The body
writes `esp` only through the frames of its calls (`body_noSp`); the frames
around it (`wrap_ok`, `wrap_ct`) and the result as the shared contract states
it, for MGF1's hash function the variant `w` whose table the argument 23 is
(`tabFacts_entered`): `vg_rsa_oaep_<H>_mgf1_decrypt`, calling
`vg_rsa_private_checked` over `v`, with MGF1's hash function any of the
tables of `vs`, is verified, given a state that meets the contract
(`Dec/Sat.lean`): `dec_verified`. Every stage keeps the addresses of the
statics (`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Dec

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes seqs countLoop zeroLoop clrArgs)
open VG.Proof.HashTable.X86 (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered
  fnsOf_noSp)

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

theorem vpAssoc (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs => WP.assoc (h.wp σ s hs), RelCT.assoc h.ct⟩

theorem vpAssoc' (h : VP F (.seq a (.seq b c)) G) : VP F (.seq (.seq a b) c) G :=
  ⟨fun σ s hs => WP.assoc' (h.wp σ s hs), relCT_assoc' h.ct⟩

/-- A piece of `n` steps, then the rest. -/
theorem VP.cont2 (h : VP F (.seq a b) G) (h₂ : VP G r H) : VP F (.seq a (.seq b r)) H := vpAssoc (h.seq h₂)

theorem VP.cont3 (h : VP F (.seq a (.seq b c)) G) (h₂ : VP G r H) : VP F (.seq a (.seq b (.seq c r))) H :=
  vpAssoc (VP.cont2 (vpAssoc' h) h₂)

theorem VP.cont4 (h : VP F (.seq a (.seq b (.seq c d))) G) (h₂ : VP G r H) :
    VP F (.seq a (.seq b (.seq c (.seq d r)))) H :=
  vpAssoc (VP.cont3 (vpAssoc' h) h₂)

end

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The decoding, when `k ≥ 2 hLen + 2`, with MGF1's hash function `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => Sy (C2 h.H.D P) σ s ∧ isa.eval .b s = some false) (decMain h.H f) (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (hashLabel h.H 17 oLh) (.seq (.block (seedArgs h.H 4)) (.seq (mgfXor f 23)
    (.seq (.block (dbArgs h.H 4)) (.seq (mgfXor f 23) (.seq (.block (cmpSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.cmpBody) (.seq (.block accPut) (.seq (.block (scanSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.scanBody) (.seq (.block scanEnd) (.seq (.block (clrArgs oBuf 2048))
    (.seq zeroLoop (.seq (.block (tSet h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq shift (.seq (.block okMask)
    (.seq (.block outSet) (.seq (countLoop outBody) (.seq (.block (mlSet h.H)) (.block decRet)))))))))))))))))))))
    _
  exact ((VP.syms (lab_vp h P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x).seq
    (VP.cont4 (unmask_vp h g P hT fne) (VP.syms (VP.cont3 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
      (buf_vp h g P ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (out_vp h g P) (end_vp h g P)))))))))

theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (Sy (S P)) (decBody h.H f (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (.block (decStart ++ privArgs)) (.seq (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v))
    (.seq (.block (decChk h.H)) (.ite .b decFail (decMain h.H f))))) _
  exact VP.cont3 (VP.syms ((pa_vp P).seq ((call_vp P v).seq (chk_vp h P)))) (VP.ite
    (fun σ s hs => ⟨decide (P.K < 2 * h.H.D + 2), by simp only [eval, hs.1.2.2.2.2.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT fne))

/-! ## The stack -/

theorem body_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2)
    (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    NoSp (decBody h.H f (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) := by
  obtain ⟨-, p2, -, p4, -, -, -, p8, p9, p10, p11, p12⟩ := h.certs.parts
  have hm := mgfX_noSp hi hu hf (j := 23) (NoSp.of_all (by decide +kernel))
  have hl := hashLabel_noSp h (j := 17) (o := oLh) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  have hc := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  simp only [decBody, decMain, decFail, shift, passOne, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | exact hm | exact hl | exact hc | exact p2 | exact p4 | exact p8 | exact p9 | exact p10 | exact p11
    | exact p12
    | exact NoSp.of_all (by decide +kernel))

/-! ## The entry -/

variable (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with MGF1's hash
function any of the tables of `vs`. -/
abbrev decCode (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : Prog isa :=
  decrypt h.H (fnsOf vs) (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)

/-- The contract, with MGF1's hash function one of the tables of `vs`. -/
abbrev dspec : Contract isa := spec h.G (tables vs)

variable {h vs}

/-- The public parameters for the table of `w`, with its functions where `s` has them. -/
abbrev epw (s : State) (w : TVar) : EP :=
  ep s (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (arg s 23) (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN))

theorem spec_sp {s : State} (hs : (dspec h vs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  dec_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the table of `w` at the argument 23, with the
functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (dspec h vs).pre s) {w : TVar} (hw : w ∈ vs)
    (hh : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (tableOf w)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S (ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s 23) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))))
      (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, hpw, hfit⟩ := spec_tab hs
  rw [List.append_nil] at hpw
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) hs trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.X86.mem_names hw
  have tf := tabFacts_entered (argv := (ep s 0 0 0 fun _ => True).argv) (ro := (ep s 0 0 0 fun _ => True).ro)
    (rw := (ep s 0 0 0 fun _ => True).rw) (C := 3448) hsp ok (p := arg s 23) (by simp [ep]) hfit hc hpw hw hh
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN) hs tf
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) {s : State} (hs : (dspec h vs).pre s) :
    WP isa (decCode h vs v) s fun t => abiPreserved s t ∧ (dspec h vs).post s t := by
  obtain ⟨⟨T, hT, hh⟩, -, hfit⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have he := entered_state hc hs hw hh (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  have hb := (body_vp h (epw (vs := vs) s w) w.g (fun _ x => x) (fne_of hw) v).wp _ _ he
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp h ni nu nf v) hsp hfit4
    (W := (epw (vs := vs) s w).lay.W)
    (Q := fun r m => Res h.G w.g.G (epw (vs := vs) s w) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (epw (vs := vs) s w).argv) (ro := (epw (vs := vs) s w).ro)
        (rw := (epw (vs := vs) s w).rw) (C := 3448) hsp,
      ret_eq (argv := (epw (vs := vs) s w).argv) (ro := (epw (vs := vs) s w).ro) (rw := (epw (vs := vs) s w).rw)
        (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s w).ro) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes]
    intro G hG
    rw [hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hG
    unfold Res at res
    have hP : pB (epw (vs := vs) s w) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat := ro (R := (epw (vs := vs) s w).PP) (by simp)
    have hQ : qB (epw (vs := vs) s w) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 9).setWidth 64) (arg s 10).toNat := ro (R := (epw (vs := vs) s w).QQ) (by simp)
    have hDP : dpB (epw (vs := vs) s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 11).setWidth 64)
        (arg s 8).toNat := ro (R := (epw (vs := vs) s w).DP) (by simp)
    have hDQ : dqB (epw (vs := vs) s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 13).setWidth 64)
        (arg s 10).toNat := ro (R := (epw (vs := vs) s w).DQ) (by simp)
    have hQI : qiB (epw (vs := vs) s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 15).setWidth 64)
        (arg s 8).toNat := ro (R := (epw (vs := vs) s w).QI) (by simp)
    have hL : labB (epw (vs := vs) s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 17).setWidth 64)
        (arg s 18).toNat := ro (R := (epw (vs := vs) s w).LAB) (by simp)
    have hC : ctB (epw (vs := vs) s w) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 19).setWidth 64)
        (arg s 4).toNat := ro (R := (epw (vs := vs) s w).CT) (by simp)
    rw [hP, hQ, hDP, hDQ, hQI, hL, hC] at res
    rw [BitVec.setWidth_append_eq_right]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    ConstantTime isa (dspec h vs).pre (dspec h vs).pub (decCode h vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T, hT, hh₁⟩, -, hfit⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (by rw [List.append_eq, List.append_nil]; exact hn)).symm
  have hep : epw (vs := vs) s₁ w = ep s₂ (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s₂ 23) (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN)) := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.bytesAt_len, a4])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a17, a18, a19, a21, a22, a23]
    rw [a3, a4] at hn
    rw [a5, a6] at he
    rw [hn, he]
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  refine (wrap_ct (F := frameBytes) (body_noSp h ni nu nf v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp h (epw (vs := vs) s₁ w) w.g (fun _ x => x) (fne_of hw) v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hh₂ (s' := s₁) hsy'⟩

theorem code_noSp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : NoSp (decCode h vs v) :=
  have n := fnsOf_noSp vs
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp h n.1 n.2.1 n.2.2 v)) restore_noSp)

theorem code_sp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : (decCode h vs v).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp v)

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, calling `vg_rsa_private_checked` over
`v`, with MGF1's hash function any of the tables of `vs`, meets the shared
contract (satisfiable, `Dec/Sat.lean`). -/
theorem dec_verified (hc : Coh vs) (hsat : ∃ s, (dspec h vs).pre s) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (decCode h vs v) (dspec h vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc v, hsat⟩

end VG.Proof.RsaOaep.X86.Dec
