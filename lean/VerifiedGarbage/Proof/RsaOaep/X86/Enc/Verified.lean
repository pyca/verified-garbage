module

public import VerifiedGarbage.Proof.RsaOaep.X86.Enc.Call
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.X86.Certs
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.Taint

/-!
# RSAES-OAEP encryption with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaOaep/Arm/EncBody.lean`, `EncVerified.lean`): the
checks, then zeros to `out` if the message does not fit (`fail_vp`), or
`EM` (`em_vp`), its masks (`mask_vp`) and the call (`pa_vp`, `call_vp`):
`body_vp`. The body writes `esp` only through the frames of its calls
(`body_noSp`); the frames around it (`wrap_ok`, `wrap_ct`) and the result
as the shared contract states it, for MGF1's hash function the variant `w`
whose table the argument 15 is (`tabFacts_entered`):
`vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, calling a precomputed public
operation `c`, with MGF1's hash function any of the tables of `vs`, is
verified, given a state that meets the contract (`Enc/Sat.lean`):
`encrypt_verified`. Every stage keeps the addresses of the statics
(`VP.syms`), which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86.Enc

open VG VG.X86.Wp VG.Impl.RsaOaep.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86 VG.Proof.RsaOaep.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaPss.X86 (frameBytes seqs countLoop zeroLoop)
open VG.Proof.HashTable.X86 (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered
  fnsOf_noSp)

variable (h : OHash)

/-- A stage, with what follows it, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- After the checks, when the message fits, with the label's hash function
`h` and MGF1's `g`. -/
theorem main_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : Ver.PublicImpl) :
    VP (Sy (E0 h P)) (encMain h.H f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (encEm h.H f) (.seq (.block (dbArgs h.H 3)) (.seq (mgfXor f 17) (.seq (.block (seedArgs h.H 3))
    (.seq (mgfXor f 17) (.seq (.block pubArgs) (.call c.name c.code))))))) _
  exact (em_vp h P hTL fne).seq (mask_vp h g P hT fne (VP.syms ((pa_vp h g P).seq (call_vp h g P c))))

/-- The digest length of the label's hash function's table to `edx`. -/
theorem len_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ) :
    VP (S h P) (.block (lenLoad 16)) (fun σ s => S h P σ s ∧ s.gpr .edx = BitVec.ofNat 32 h.H.D) := by
  by_cases hP : ∃ σ, In h.H.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := tblL_of hi₀
  show VP _ (.block ([Impl.RsaPss.X86.ld .edx (Impl.RsaPss.X86.arg 16)] ++
    [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 16))])) _
  refine VP.block_append (G := fun σ s => S h P σ s ∧ s.gpr .edx = P.tabL)
    (VP.taint [.esp] lenArg16_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] lenWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.sp, h₂.2.sp]
  · obtain ⟨hi, hs⟩ := hs
    simp only [Impl.RsaPss.X86.ld, Impl.RsaPkcs1Sig.X86.stk]
    exact hs.wp_arg (enc_arg (j := 16) (by decide)) (by decide) fun t1 s1 u1 =>
      WP.block_nil ⟨⟨hi, s1⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.2.sp, h₂.1.2.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨hi, hs⟩, hdx⟩ := hs
    have T := hTL σ hi.tabTL
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabL 16) 4 := ⟨tR, hs.inRo tRo, tC 16 (by decide)⟩
    refine wp_ldm (B := P.tabL) hdx hin fun t2 u2 => WP.block_nil ⟨⟨hi, hs.upd u2 (by decide)⟩, ?_⟩
    rw [u2.gpr, St_roW hs tRo (tC 16 (by decide)), T.d]

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem encTail_D {G G' : Impl.Pbkdf2.Stream.X86.Hash} (hD : G.D = G'.D) (f : Fns) (n : String) (c : Prog isa) :
    encTail G f n c = encTail G' f n c := by
  simp only [encTail, encMain, encEm, encChk, seedSet, lhSet, dbArgs, seedArgs, hD]

/-- The body. -/
theorem body_vp (P : EP) (g : OHash) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) (c : Ver.PublicImpl) :
    VP (Sy (S h P)) (encBody f c.name c.code) (Sy (Fin h g P)) := by
  show VP _ (.seq (.block (lenLoad 16)) (byLen (fun d => encTail (ofLen d) f c.name c.code) lens)) _
  refine (VP.syms (len_vp h P hTL)).seq (byLen_vp (D := h.H.D) (by have := h.D_le; omega) (fun _ _ hs => hs.1.2)
    (fun σ s t ⟨⟨⟨hi, st⟩, dx⟩, sy⟩ fu sy' => ⟨⟨⟨hi, st.fupd fu⟩, by rw [fu.gpr]; exact dx⟩, sy'.trans sy⟩) ?_
    h.lens cmpLens_taint)
  show VP _ (encTail (ofLen h.H.D) f c.name c.code) _
  rw [encTail_D (G := ofLen h.H.D) (G' := h.H) rfl]
  show VP _ (.seq (.block (encChk h.H)) (.ite .ne encFail (encMain h.H f c.name c.code))) _
  refine ((VP.syms (chk_vp h P)).mono (fun _ _ ⟨⟨s', _⟩, sy⟩ => ⟨s', sy⟩) fun _ _ x => x).seq (VP.ite
    (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.1.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2, h₂.1.2.2])
    ((VP.syms (fail_vp h g P)).mono (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) fun _ _ x => x) ?_)
  refine (main_vp h P g hT hTL fne c).mono (fun σ s ⟨⟨⟨hc, hi, z⟩, sy⟩, e⟩ => ⟨⟨hc, hi, ?_⟩, sy⟩) fun _ _ hh => hh
  simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
  exact e

/-! ## The stack -/

theorem tail_noSp (G : Impl.Pbkdf2.Stream.X86.Hash) (cs : OCerts G) {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2)
    (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2) (c : Ver.PublicImpl) :
    NoSp (encTail G f c.name c.code) := by
  obtain ⟨p1, -, p3, -, p5, p6, p7, -⟩ := cs.parts
  have hm := mgfX_noSp hi hu hf (j := 17) (NoSp.of_all (by decide +kernel))
  have hl := hashLabelT_noSp hi hu hf (j := 6) (o := Impl.RsaPss.X86.oDig) (NoSp.of_all (by decide +kernel))
    (NoSp.of_all (by decide +kernel))
  have hc := c.noSp
  simp only [encTail, encMain, encEm, encFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply RsaPss.X86.noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | exact hm | exact hl | exact hc | exact p1 | exact p3 | exact p5 | exact p6 | exact p7
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSp {f : Fns} (hi : ∀ q ∈ f.init, NoSp q.2) (hu : ∀ q ∈ f.upd, NoSp q.2) (hf : ∀ q ∈ f.fin, NoSp q.2)
    (c : Ver.PublicImpl) : NoSp (encBody f c.name c.code) :=
  noSp_seq (NoSp.of_all (by decide +kernel))
    (byLen_noSp fun d hd => tail_noSp (ofLen d) (lens_certs hd) hi hu hf c)

/-! ## The entry -/

variable (vs : List TVar)

/-- The code, calling `c`, with both hash functions any of the tables of `vs`. -/
abbrev encryptCode (c : Ver.PublicImpl) : Prog isa := encryptPrecomputed (fnsOf vs) c.name c.code

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev espec : Contract isa := spec (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w w₁ : TVar) : EP :=
  ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (arg s 17) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
    (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (arg s 16) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN))

theorem spec_sp {s : State} (hs : (espec vs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  enc_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the tables of `w` at the argument 17 and `w₁` at
16, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (espec vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem ((arg s 17).setWidth 64) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem ((arg s 16).setWidth 64) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S w₁.g (epw (vs := vs) s s' w w₁)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tab hs
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hHa := hashAt_tableOf hfitL (held_tableOf hfitL hhL).2.1
  have ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs hHa trivial trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.HashTable.X86.mem_names hw
  have hnL := Proof.HashTable.X86.mem_names hw₁
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  have tf := tabFacts_entered (argv := e0.argv) (ro := e0.ro w₁.g.G.len) (rw := e0.rw) (C := 100) hsp ok
    (p := arg s 17) (by simp [e0, ep]) hfit hc hpw' hw hh
  have tfL := tabFacts_entered (argv := e0.argv) (ro := e0.ro w₁.g.G.len) (rw := e0.rw) (C := 100) hsp ok
    (p := arg s 16) (by simp [e0, ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  have hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs hHa tf tfL
  rw [w₁.g.glen] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (c : Ver.PublicImpl) {s : State} (hs : (espec vs).pre s) :
    WP isa (encryptCode vs c) s fun t => abiPreserved s t ∧ (espec vs).post s t := by
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
  have hb := (body_vp w₁.g (epw (vs := vs) s s w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) c).wp _ _ he
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp ni nu nf c) hsp hfit4
    (W := ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).W)
    (Q := fun r m => Res w₁.g w.g (epw (vs := vs) s s w w₁) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (epw (vs := vs) s s w w₁).argv) (ro := (epw (vs := vs) s s w w₁).ro w₁.g.H.D)
        (rw := (epw (vs := vs) s s w w₁).rw) (C := 100) hsp,
      ret_eq (argv := (epw (vs := vs) s s w w₁).argv) (ro := (epw (vs := vs) s s w w₁).ro w₁.g.H.D)
        (rw := (epw (vs := vs) s s w w₁).rw) (C := 100) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw (vs := vs) s s w w₁).ro w₁.g.H.D) => entered_ro hsp ok hR
    sig_post [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argSlots, argVal, argBytes]
    intro H G hH hG
    rw [hashAt_tableOf hfitL hidxL, Option.some.injEq] at hH
    rw [hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    have hL : labB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).LAB) (by simp)
    have hM : msgB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).MSG) (by simp)
    have hS : seedB w₁.g (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 10).setWidth 64) w₁.g.H.D :=
      ro (R := (epw (vs := vs) s s w w₁).SEED w₁.g.H.D) (by simp)
    rw [hL, hM, hS] at res
    rw [BitVec.setWidth_append_eq_right, w₁.g.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (c : Ver.PublicImpl) :
    ConstantTime isa (espec vs).pre (espec vs).pub (encryptCode vs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    a17⟩ := hp
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  have hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  have hep : epw (vs := vs) s₁ s₁ w w₁ = epw (vs := vs) s₂ s₁ w w₁ := by
    obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a3, a5])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [RsaPkcs1Sig.bytesAt_len, a3])
    have hw' := map_toNat_inj hw
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17]
    rw [a2, a3] at hn
    rw [a4, a5] at he
    rw [a14, a15] at hw'
    rw [hn, he, hw']
  obtain ⟨ni, nu, nf⟩ := fnsOf_noSp vs
  refine (wrap_ct (F := frameBytes) (body_noSp ni nu nf c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w₁.g (epw (vs := vs) s₁ s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) c).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'⟩

theorem code_noSp (c : Ver.PublicImpl) : NoSp (encryptCode vs c) :=
  have n := fnsOf_noSp vs
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp n.1 n.2.1 n.2.2 c)) restore_noSp)

theorem code_sp (c : Ver.PublicImpl) : (encryptCode vs c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp c)

/-- `vg_rsa_oaep_encrypt_precomputed`, calling `c`, with both hash functions
any of the tables of `vs`, meets the shared contract (satisfiable,
`Enc/Sat.lean`). -/
theorem encrypt_verified (hc : Coh vs) (hsat : ∃ s, (espec vs).pre s) (c : Ver.PublicImpl) :
    Verified target (encryptCode vs c) (espec vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc c, hsat⟩

end VG.Proof.RsaOaep.X86.Enc
