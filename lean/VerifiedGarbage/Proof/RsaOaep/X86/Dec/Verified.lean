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
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.Taint

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

/-- The decoding, when `k ≥ 2 hLen + 2`, with the label's hash function `h`
and MGF1's `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => Sy (C2 h.H.D P) σ s ∧ isa.eval .b s = some false) (decMain h.H f) (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (.block (tabSlot 23)) (.seq (hashLabelT f 17 oLh) (.seq (.block (seedArgs h.H 4))
    (.seq (mgfXor f 24) (.seq (.block (dbArgs h.H 4)) (.seq (mgfXor f 24) (.seq (.block (cmpSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.cmpBody) (.seq (.block accPut) (.seq (.block (scanSet h.H))
    (.seq (countLoop Impl.RsaPss.X86.scanBody) (.seq (.block scanEnd) (.seq (.block (clrArgs oBuf 2048))
    (.seq zeroLoop (.seq (.block (tSet h.H)) (.seq Impl.Bignum.X86.copyBytes (.seq shift (.seq (.block okMask)
    (.seq (.block outSet) (.seq (countLoop outBody) (.seq (.block (mlSet h.H)) (.block decRet))))))))))))))))))))))
    _
  exact VP.cont2 ((labT_vp h P hTL fne).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (VP.cont4 (unmask_vp h g P hT fne) (VP.syms (VP.cont3 (acc_vp h g P) (VP.cont3 (tscan_vp h g P)
      (buf_vp h g P ((shift_vp h g P).seq ((okMask_vp h g P).seq (VP.cont2 (out_vp h g P) (end_vp h g P)))))))))

/-- The digest length of the label's hash function's table to `edx`. -/
theorem len_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ) :
    VP (R2 P) (.block (lenLoad 23)) (fun σ s => R2 P σ s ∧ s.gpr .edx = BitVec.ofNat 32 h.H.D) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨tR, tRo, tC⟩ := tblL_of hi₀
  show VP _ (.block ([Impl.RsaPss.X86.ld .edx (Impl.RsaPss.X86.arg 23)] ++
    [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 16))])) _
  refine VP.block_append (G := fun σ s => R2 P σ s ∧ s.gpr .edx = P.tabL)
    (VP.taint [.esp] lenArg23_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] lenWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.st.sp, h₂.1.st.sp]
  · obtain ⟨hc, hi, he, hr0, hk⟩ := hs
    simp only [Impl.RsaPss.X86.ld]
    refine hc.wp_arg hg (j := 23) (by simp) (by decide) (by decide) fun t1 c1 u1 => WP.block_nil
      ⟨⟨c1, hi, by rw [u1.mem]; exact he, by rw [u1.other _ (by decide)]; exact hr0, hk⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.st.sp, h₂.1.1.st.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨hc, hi, he, hr0, hk⟩, hdx⟩ := hs
    have T := hTL σ hi.tabTL
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabL 16) 4 := ⟨tR, hc.st.inRo tRo, tC 16 (by decide)⟩
    refine wp_ldm (B := P.tabL) hdx hin fun t2 u2 => WP.block_nil
      ⟨⟨hc.upd u2 (by decide) (by decide), hi, by rw [u2.mem]; exact he, by rw [u2.other _ (by decide)]; exact hr0,
        hk⟩, ?_⟩
    rw [u2.gpr, St_roW hc.st tRo (tC 16 (by decide)), T.d]

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Impl.Pbkdf2.Stream.X86.Hash} (hD : G.D = G'.D) (f : Fns) :
    decTail G f = decTail G' f := by
  simp only [decTail, decMain, decChk, seedArgs, dbArgs, cmpSet, scanSet, tSet, mlSet, hD]

theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    VP (Sy (S P)) (decBody f (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) (Sy (Fin h.G g.G P)) := by
  show VP _ (.seq (.block (decStart ++ privArgs)) (.seq (.call (privName v) (Proof.Rsa.X86.PrivChecked.privCode v))
    (.seq (.block (lenLoad 23)) (byLen (fun d => decTail (ofLen d) f) lens)))) _
  refine VP.cont3 (VP.syms ((pa_vp P).seq ((call_vp P v).seq (len_vp h P hTL)))) (byLen_vp (D := h.H.D)
    (by have := h.D_le; omega) (fun _ _ hs => hs.1.2)
    (fun σ s t ⟨⟨⟨hc, hi, he, hr0, hk⟩, dx⟩, sy⟩ fu sy' =>
      ⟨⟨⟨hc.fupd fu, hi, by rw [fu.mem]; exact he, by rw [fu.gpr]; exact hr0, hk⟩, by rw [fu.gpr]; exact dx⟩,
        sy'.trans sy⟩) ?_ h.lens cmpLens_taint)
  show VP _ (decTail (ofLen h.H.D) f) _
  rw [decTail_D (G := ofLen h.H.D) (G' := h.H) rfl f]
  show VP _ (.seq (.block (decChk h.H)) (.ite .b decFail (decMain h.H f))) _
  exact VP.seq ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨r2, _⟩, sy⟩ => ⟨r2, sy⟩) fun _ _ x => x) (VP.ite
    (fun σ s hs => ⟨decide (P.K < 2 * h.H.D + 2), by simp only [eval, hs.1.2.2.2.2.2]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x)
    (main_vp h P g hT hTL fne))

/-! ## The stack -/

theorem tail_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (c : OCerts G) {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2)
    (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2) : NoSp (decTail G f) := by
  obtain ⟨-, p2, -, p4, -, -, -, p8, p9, p10, p11, p12⟩ := c.parts
  have hm := mgfX_noSp hi hu hf (j := 24) (NoSp.of_all (by decide +kernel))
  have hl := hashLabelT_noSp hi hu hf (j := 17) (o := oLh) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  simp only [decTail, decMain, decFail, shift, passOne, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | exact hm | exact hl | exact p2 | exact p4 | exact p8 | exact p9 | exact p10 | exact p11 | exact p12
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2)
    (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    NoSp (decBody f (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)) := by
  have hc := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  have hb := byLen_noSp (b := fun d => decTail (ofLen d) f) (ds := lens) fun d hd => tail_noSp _ (lens_certs hd) hi hu hf
  simp only [decBody, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_call
    | exact hc | exact hb
    | exact NoSp.of_all (by decide +kernel))

/-! ## The entry -/

variable (vs : List TVar)

/-- The code, calling `vg_rsa_private_checked` over `v`, with both hash
functions any of the tables of `vs`. -/
abbrev decCode (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : Prog isa :=
  decrypt (fnsOf vs) (privName v) (Proof.Rsa.X86.PrivChecked.privCode v)

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev dspec : Contract isa := spec (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s` has them. -/
abbrev epw (s : State) (w w₁ : TVar) : EP :=
  ep s (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (arg s 24) (s.syms w.g.H.initN) (s.syms w.g.H.updN) (s.syms w.g.H.finN))
    (s.syms w₁.g.H.initN) (s.syms w₁.g.H.updN) (s.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (arg s 23) (s.syms w₁.g.H.initN) (s.syms w₁.g.H.updN) (s.syms w₁.g.H.finN))

theorem spec_sp {s : State} (hs : (dspec vs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  dec_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the tables of `w` at the argument 24 and `w₁` at
23, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (dspec vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem ((arg s 24).setWidth 64) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S (ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s 24) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
      (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s 23) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
        (s'.syms w₁.g.H.finN))))
      (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tab hs
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs trivial trivial).ok
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
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs tf tfL
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) {s : State} (hs : (dspec vs).pre s) :
    WP isa (decCode vs v) s fun t => abiPreserved s t ∧ (dspec vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tab hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hidx := (held_tableOf hfit hh).2.1
  have hidxL := (held_tableOf hfitL hhL).2.1
  have he := entered_state hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  have hb := (body_vp w₁.g (epw (vs := vs) s w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) v).wp _ _ he
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp ni nu nf v) hsp hfit4
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
    sig_post [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes]
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

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    ConstantTime isa (dspec vs).pre (dspec vs).pub (decCode vs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23, a24⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  have hep : epw (vs := vs) s₁ w w₁ = ep s₂ (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN)
      (TabFacts w.g.H (fnsOf vs) (arg s₂ 24) (s₁.syms w.g.H.initN) (s₁.syms w.g.H.updN) (s₁.syms w.g.H.finN))
      (s₁.syms w₁.g.H.initN) (s₁.syms w₁.g.H.updN) (s₁.syms w₁.g.H.finN)
      (TabFacts w₁.g.H (fnsOf vs) (arg s₂ 23) (s₁.syms w₁.g.H.initN) (s₁.syms w₁.g.H.updN)
        (s₁.syms w₁.g.H.finN)) := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.bytesAt_len, a4])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a17, a18, a19, a21, a22, a23, a24]
    rw [a3, a4] at hn
    rw [a5, a6] at he
    rw [hn, he]
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  refine (wrap_ct (F := frameBytes) (body_noSp ni nu nf v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w₁.g (epw (vs := vs) s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) v).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'⟩

theorem code_noSp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : NoSp (decCode vs v) :=
  have n := fnsOf_noSp vs
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp n.1 n.2.1 n.2.2 v)) restore_noSp)

theorem code_sp (v : Proof.Rsa.X86.PrivChecked.CrtImpl) : (decCode vs v).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp v)

/-- `vg_rsa_oaep_decrypt`, calling `vg_rsa_private_checked` over `v`, with
both hash functions any of the tables of `vs`, meets the shared contract
(satisfiable, `Dec/Sat.lean`). -/
theorem dec_verified (hc : Coh vs) (hsat : ∃ s, (dspec vs).pre s) (v : Proof.Rsa.X86.PrivChecked.CrtImpl) :
    Verified target (decCode vs v) (dspec vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc v, hsat⟩

end VG.Proof.RsaOaep.X86.Dec
