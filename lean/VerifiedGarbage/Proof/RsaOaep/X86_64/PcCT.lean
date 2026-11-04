module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcContract
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfTCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcTab
public import VerifiedGarbage.Proof.HashTable.X86_64
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Spec.RsaPkcs1Sig
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.PcContract
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Spec.RsaPkcs1Sig

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: constant time

The pieces of `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` (`EncCT`), for entry states
related to the anchor by `contract` too (`PP`: the precondition, `pre` and
its words), and the call of the precomputed public operation, constant time
for its contract, which makes `pre`'s words public. Nothing follows the
call.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.HashTable.X86_64 (tableOf tables fnsOf names Coh tabOK_of held_tableOf hashAt_tableOf fnsGood_of
  mem_names)

/-- What `contract` adds to `encK`'s precondition and public data, with the
table `T` at the stack argument 9. -/
def PP (H : Spec.Mgf1.Hash) (ts : List FnTable) (T : FnTable) (a s : State) : Prop :=
  PPreT H s ∧ stackArg a 7 = stackArg s 7 ∧ stackArg a 8 = stackArg s 8 ∧
    (Spec.Rsa.wordsAt a.mem (stackArg a 7) (stackArg a 8).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 7) (stackArg s 8).toNat ∧ stackArg a 9 = stackArg s 9 ∧
      (∀ f ∈ tabFnsE ts, a.syms f = s.syms f) ∧
      Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s T) ∧
      (tabFnsE ts).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g))

/-- Before the call, with its arguments. -/
structure EWPP (s t : State) : Prop where
  he : EnvE s t
  L : Lay t (fb s) (stackArg s 5)
  w : ∀ i < 4, t.mem.readW (off (fb s) (8 * i)) 64 = pw s i
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rcx
  rdx : t.gpr .rdx = stackArg s 7
  rcx : t.gpr .rcx = stackArg s 8
  r8 : t.gpr .r8 = s.gpr .r8
  r9 : t.gpr .r9 = s.gpr .r9

variable {H G : Spec.Mgf1.Hash} {ts : List FnTable} {T : FnTable}

theorem ew_pubArgs' {s t : State} (hp : PPre H s) (h : EW s t) :
    WP isa (.block Impl.RsaOaep.X86_64.Precomputed.pubArgs) t (EWPP s) := by
  rw [Impl.RsaOaep.X86_64.Precomputed.pubArgs, WP.block_append_iff]
  refine WP.mono (ew_pubArgs h) fun t₁ e => ?_
  refine WP.mono (wp_good (block_good _ rfl) (load_pre hp e.he.rsp e.he.rd e.he.fr))
    fun u ⟨⟨k, hm, hdx, hcx⟩, sp', mx', f'⟩ => ?_
  exact ⟨e.he.step k.2.1 k.2.2 sp' (keep_cs3 k (by decide)) mx' f', e.L.congr (k.gpr (by decide)) k.2.2
    (by rw [hm]), fun i hi => by rw [hm]; exact e.w i hi, (k.gpr (by decide)).trans e.rdi,
    (k.gpr (by decide)).trans e.rsi, hdx, hcx, (k.gpr (by decide)).trans e.r8, (k.gpr (by decide)).trans e.r9⟩

/-- What the precomputed public operation's contract makes public, from the anchor. -/
theorem pub_view {a s t : State} (S : ESib H G (PP H ts T) a s) (h : EWPP s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (pubWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 7, stackArg a 8, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    (∀ i < 4, stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = pw a i) ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 7) (stackArg a 8).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  have hp := S.2.2.1.toPPre
  have hF := fb_toNat hp.toEPre
  have hfe : Frame [below (fb s) 16] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, h.he.rsp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide) (by decide))
  have hfE : FrE s t.callEntry.mem :=
    h.he.fr.trans (hfe.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., ret_sub s⟩)
  refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
  · rw [e_entry_regs, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.he.rsp, S.fb, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rcx) (by decide), S.2.2.2.1, S.2.2.2.2.1, S.gpr (r := .r8) (by decide),
      S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry h.he.rsp (by have := hp.sp1; unfold encStack frameBytes at *; omega) _ _
      (by have := hp.sp2; unfold frameBytes at *; omega), h.w i hi, pw_sib S]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), h.rdx, h.rcx]
    rw [State.withRegions_mem, pre_words hp hfE, S.2.2.2.2.2.1]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.r8, h.r9]
    rw [entryBytes h.he _ _ hp.d_stk_e hp.d_out_e hp.d_e_scr.symm (by have := hp.wE; omega)]
    exact S.2.1.2.2.2.symm

theorem call_ct (v : PublicImpl) : RelCT isa (Two (EAt H G (PP H ts T) EWPP)) (.call v.name v.code)
    fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  have hp₁ := S₁.2.2.1.toPPre
  have hp₂ := S₂.2.2.1.toPPre
  obtain ⟨r₁, g₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers hp₁ j₁.he.rd j₁.he.wr
  obtain ⟨c₂, w₂⟩ := call_covers hp₂ j₂.he.rd j₂.he.wr
  have p₁ := call_pre hp₁ j₁.he.rsp (j₁.w 0 (by decide)) (j₁.w 1 (by decide)) (j₁.w 2 (by decide))
    (j₁.w 3 (by decide)) j₁.rdi j₁.rsi j₁.rdx j₁.rcx j₁.r8 j₁.r9
  have p₂ := call_pre hp₂ j₂.he.rsp (j₂.w 0 (by decide)) (j₂.w 1 (by decide)) (j₂.w 2 (by decide))
    (j₂.w 3 (by decide)) j₂.rdi j₂.rsi j₂.rdx j₂.rcx j₂.r8 j₂.r9
  refine ⟨callRd s₁, pubWr s₁, callRd s₂, pubWr s₂, p₁, p₂, ⟨List.map_inj_left.mp (r₁.trans r₂.symm),
    (g₁ 0 (by decide)).trans (g₂ 0 (by decide)).symm, (g₁ 1 (by decide)).trans (g₂ 1 (by decide)).symm,
    (g₁ 2 (by decide)).trans (g₂ 2 (by decide)).symm, (g₁ 3 (by decide)).trans (g₂ 3 (by decide)).symm,
    n₁.trans n₂.symm, e₁.trans e₂.symm⟩, c₁, w₁, c₂, w₂, by rw [j₁.he.rsp, j₂.he.rsp, S₁.fb, S₂.fb]⟩

section
variable {Hl : Hash} (hH : HashOK Hl) (KH : Callees Hl) (mH : MgfLink Hl hH) {vs : List MdHash} (hc : Coh vs)

/-- MGF1's public data from the anchor's: its `MQ`, the table, and the
addresses of `w`'s functions. -/
def mqtE (w : MdHash) (q : MQ) (a : State) : Table.MQT :=
  ⟨q, stackArg a 9, a.syms w.H.initN, a.syms w.H.updN, a.syms w.H.finN⟩

include hc in
/-- Where MGF1 starts, with its table, for the anchor's public data. -/
theorem met_of {w : MdHash} (hw : w ∈ vs) {src srcLen dst dstLen : Nat → Nat} {a s t : State}
    (S : ESib H G (PP H (tables vs) (tableOf w)) a s) (hsy : t.syms = s.syms)
    (h : EWM s t (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat))
    (hf : MFit (src (s.gpr .rcx).toNat) (srcLen (s.gpr .rcx).toNat) (dst (s.gpr .rcx).toNat)
      (dstLen (s.gpr .rcx).toNat)) :
    Table.MET w.H.stream (fnsOf vs) 2 (frameBytes + 8 + 8 * 9)
      (mqtE w ⟨fb a, stackArg a 5, [outR a, scrR a], src (a.gpr .rcx).toNat, srcLen (a.gpr .rcx).toNat,
        dst (a.gpr .rcx).toNat, dstLen (a.gpr .rcx).toNat⟩ a) t := by
  obtain ⟨hp, -, -, -, h9, hsy', hheld, hd⟩ := S.2.2
  obtain ⟨hm, -, hDm⟩ := held_tableOf hheld
  have T := etab hp h.he hsy (tabOK_of hc hd hw) hm hDm
  have hn := mem_names hw
  refine ⟨me_of S h hf, ?_, ?_, ?_, ?_⟩
  · simp only [mqtE]; rw [← S.fb, h9]; exact T
  · simp only [mqtE]; rw [hsy]; exact (hsy' _ hn.1).symm
  · simp only [mqtE]; rw [hsy]; exact (hsy' _ hn.2.1).symm
  · simp only [mqtE]; rw [hsy]; exact (hsy' _ hn.2.2).symm

/-- What correctness says after a piece, from what the entry state's
relation to the anchor says too. -/
theorem e_postS {P : State → State → Prop} {J J' : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two (EAt H G P J)) c fun _ _ => True)
    (hw : ∀ a s t, ESib H G P a s → J s t → WP isa c t (J' s)) :
    RelCT isa (Two (EAt H G P J)) c (Two (EAt H G P J')) :=
  two_post hct fun a t ⟨s, S, j⟩ => WP.mono (hw a s t S j) fun _ j' => ⟨s, S, j'⟩

theorem etabArg_taint : ∃ hc, (taint.check (frT [] [] 2)
    (.block (Impl.Mgf1.X86_64.Table.tabArg (frameBytes + 8 + 8 * 9) sTab)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

include hH KH mH hc in
/-- `EM` built and masked with the table's hash function, then `rest`,
constant time if `rest` is. -/
theorem encMask_ct {w : MdHash} (hw : w ∈ vs) {rest : Prog isa}
    (hrest : RelCT isa (Two (EAt mH.G mH.G (PP mH.G (tables vs) (tableOf w)) (EK Hl.D))) rest fun _ _ => True) :
    RelCT isa (Two (EAt mH.G mH.G (PP mH.G (tables vs) (tableOf w)) (EK Hl.D)))
      (.seq (encEm Hl.stream) (.seq (.block (dbArgs Hl.stream)) (.seq (mgfT (fnsOf vs) 9)
        (.seq (.block (seedArgs Hl.stream)) (.seq (mgfT (fnsOf vs) 9) rest))))) fun _ _ => True := by
  have hz := sizes hH.stream
  have hsD : Hl.stream.D = Hl.D := rfl
  have hD65 : Hl.D < 65 := by omega
  have hD0 := hH.hD0
  obtain ⟨hgi, hgu, hgf⟩ := fnsGood_of vs
  refine RelCT.seq (encEm_ct (hH := hH) (KH := KH) (mH := mH) (mG := mH)) ?_
  -- `DB` masked.
  refine RelCT.seq (e_post (J' := fun s t => EWM s t (oEm + 1) Hl.D (oEm + 1 + Hl.D)
      ((s.gpr .rcx).toNat - (Hl.D + 1)) ∧ 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat ∧
      t.syms = s.syms)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, dbArgs_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono_syms (ew_dbArgs (Hm := Hl.stream) (by omega) (by have := h.2.1; omega) h.1)
      fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  refine RelCT.seq (e_postS (J' := EK Hl.D) (two_map (fun a => mqtE w ⟨fb a, stackArg a 5, [outR a, scrR a],
      oEm + 1, Hl.D, oEm + 1 + Hl.D, (a.gpr .rcx).toNat - (Hl.D + 1)⟩ a)
      (fun a t ⟨s, S, e, hk, sy⟩ => met_of hc hw (src := fun _ => oEm + 1) (srcLen := fun _ => Hl.D)
        (dst := fun _ => oEm + 1 + Hl.D) (dstLen := fun k => k - (Hl.D + 1)) S sy e (fit_db S.1 hk))
      (Table.mgfT_ct w.ok.stream hgi hgu hgf w.mgf.hash w.mgf.len (valid_of_link w.ok w.mgf) (.inl rfl)
        etabArg_taint))
    fun a s t S h => by
      obtain ⟨hp, -, -, -, -, -, hheld, hd⟩ := S.2.2
      obtain ⟨hm, -, hDm⟩ := held_tableOf hheld
      exact WP.mono_syms (ew_mgfT w.ok w.mgf hgi hgu hgf (fit_db S.1 h.2.1) h.1
        (etab hp h.1.he h.2.2 (tabOK_of hc hd hw) hm hDm)) fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  -- The seed masked.
  refine RelCT.seq (e_post (J' := fun s t => EWM s t (oEm + 1 + Hl.D) ((s.gpr .rcx).toNat - (Hl.D + 1)) (oEm + 1)
      Hl.D ∧ 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat ∧ t.syms = s.syms)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, seedArgs_taint Hl.D hD65⟩)
    fun s t hs h => WP.mono_syms (ew_seedArgs (Hm := Hl.stream) (by omega) (by have := h.2.1; omega) h.1)
      fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  refine RelCT.seq (e_postS (J' := EK Hl.D) (two_map (fun a => mqtE w ⟨fb a, stackArg a 5, [outR a, scrR a],
      oEm + 1 + Hl.D, (a.gpr .rcx).toNat - (Hl.D + 1), oEm + 1, Hl.D⟩ a)
      (fun a t ⟨s, S, e, hk, sy⟩ => met_of hc hw (src := fun _ => oEm + 1 + Hl.D) (srcLen := fun k => k - (Hl.D + 1))
        (dst := fun _ => oEm + 1) (dstLen := fun _ => Hl.D) S sy e (fit_seed S.1 hk hD0))
      (Table.mgfT_ct w.ok.stream hgi hgu hgf w.mgf.hash w.mgf.len (valid_of_link w.ok w.mgf) (.inl rfl)
        etabArg_taint))
    fun a s t S h => by
      obtain ⟨hp, -, -, -, -, -, hheld, hd⟩ := S.2.2
      obtain ⟨hm, -, hDm⟩ := held_tableOf hheld
      exact WP.mono_syms (ew_mgfT w.ok w.mgf hgi hgu hgf (fit_seed S.1 h.2.1 hD0) h.1
        (etab hp h.1.he h.2.2 (tabOK_of hc hd hw) hm hDm)) fun _ e sy => ⟨e, h.2.1, sy.trans h.2.2⟩) ?_
  exact hrest

include hH KH mH hc in
theorem encMain_ct (v : PublicImpl) {w : MdHash} (hw : w ∈ vs) :
    RelCT isa (Two (EAt mH.G mH.G (PP mH.G (tables vs) (tableOf w)) (EK Hl.D)))
      (Impl.RsaOaep.X86_64.Precomputed.encMain Hl.stream (fnsOf vs) v.name v.code) fun _ _ => True := by
  unfold Impl.RsaOaep.X86_64.Precomputed.encMain seqs seqs seqs seqs seqs seqs
  refine encMask_ct hH KH mH hc hw ?_
  refine RelCT.seq (two_post (Ψ := EAt mH.G mH.G (PP mH.G (tables vs) (tableOf w)) EWPP)
    (e_taintF (fun _ _ _ h => h.1) [] [] (by decide) nopin ⟨_, by taint_decide⟩)
    fun _ t ⟨s, S, h⟩ => WP.mono (ew_pubArgs' S.2.2.1.toPPre h.1) fun _ e => ⟨s, S, e⟩) ?_
  exact call_ct v

include hH KH mH hc in
theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa (contract mH.G (tables vs)).pre (contract mH.G (tables vs)).pub
      (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream (fnsOf vs) v.name v.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨-, ⟨T, hT, hheld⟩, -⟩ := preT_of h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have key := relCT_alloc (P := fun x y => (contract mH.G (tables vs)).pre x ∧ (contract mH.G (tables vs)).pre y ∧
      (contract mH.G (tables vs)).pub x y ∧ Abi.tableHeld 64 x.mem (stackArg x 9) (FnTable.words isa x (tableOf w)))
    ((encBodyWith_ct (P := PP mH.G (tables vs) (tableOf w)) (hH := hH) (hG := hH) (mH := mH) (mG := mH)
      (hmain := encMain_ct hH KH mH hc v hw)).mono (fun _ _ ⟨x, y, ⟨hx, hy, hxy, hh⟩, ex, ey⟩ => by
        obtain ⟨px, -, dx⟩ := preT_of hx
        obtain ⟨py, -, dy⟩ := preT_of hy
        exact ⟨x, ⟨x, ⟨px.toEPre, encPub_refl _ _ x, px, rfl, rfl, rfl, rfl, fun _ _ => rfl, hh, dx⟩, ex⟩,
          ⟨y, ⟨py.toEPre, hxy.1, py, hxy.2.1, hxy.2.2.1, hxy.2.2.2.1, hxy.2.2.2.2.1, hxy.2.2.2.2.2.1,
            (hxy.2.2.2.2.2.2 _ hT).mp hh, dy⟩, ey⟩⟩) fun _ _ h => h)
  exact (key _ _ _ _ _ _ ⟨h₁, h₂, hpub, hheld⟩ e₁ e₂).1

include hH KH mH hc in
/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract, with the
tables of `vs`. -/
theorem code_verified (v : PublicImpl) (hsat : ∃ s, (encC mH.G (tables vs)).pre s) :
    Verified target (Impl.RsaOaep.X86_64.Precomputed.encrypt Hl.stream (fnsOf vs) v.name v.code)
      (encC mH.G (tables vs)) :=
  Verified.of_correct (k := contract mH.G (tables vs)) (code_correct hH KH mH hc v)
    (code_constantTime hH KH mH hc v) (implies mH.G (tables vs) hsat)

end

end VG.Proof.RsaOaep.X86_64.Pc
