module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.Proof.Rsa.PreKey
import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
public import VerifiedGarbage.Proof.HashTable.AArch64
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.DecEntry
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCallee
meta import VerifiedGarbage.Proof.HashTable.AArch64
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
meta import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `RsaOaep.AArch64.EncVerified`, which only this module used -/

section

/-!
# RSAES-OAEP encryption on AArch64: verified

The prologue (`head_ct`), from two entry states whose public data agree and
which hold the same table `hash`; the table's address and digest length, and
the branch on it (`byLen_ct`), the same in both; the failure (`encFail_tr`);
the checks of `k` and the message's length; and `encMain_tr`, put together
(`rest_ct`, `enc_ct`): the other branches are on `k` and the message's
length, which are public. With correctness (`enc_ok`),
`vg_rsa_oaep_encrypt_precomputed`, for the hash functions of the tables of
`vs` and `c` of a precomputed public operation, is verified against the shared contract with the stack it and its
callee use (`enc_verified`), given that the contract is satisfiable for it
(which the registration file checks).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (leak_split bytesAt_length)
open VG.Proof.RsaOaep.AArch64.Dec (entered)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables tableOf fnsOf Coh tabOK_of held_tableOf hashAt_tableOf mem_names TabAgree tabFns
  words_congr)

/-- `x11` all ones iff `k < 2 hLen + 2`. -/
def KX (D k : Nat) (_ : Nat → BitVec 64) (t : State) : Prop :=
  t.gpr .x11 = if 2 * D + 2 ≤ k then 0 else BitVec.allOnes 64

/-- `x11` all ones iff `mLen > k - 2 hLen - 2`. -/
def MX (D k mLen : Nat) (_ : Nat → BitVec 64) (t : State) : Prop :=
  t.gpr .x11 = if mLen ≤ k - (2 * D + 2) then 0 else BitVec.allOnes 64

/-- Zeros to `out` and 0, in both runs the same. -/
theorem encFail_tr {P : Nat} {e : Env} (hL : e.L.Ok) (hP16 : 16 ≤ e.L.P) {X : (Nat → BitVec 64) → State → Prop} :
    RelCT isa (PW P e X) encFail fun _ _ => True := by
  have hk64 := hL.k64
  refine RelCT.seq (R := PW P e fun _ _ => True) (pw_wp (pw_seq_tr [.x11, .x12, .x13]
    (fun r => if r = .x11 then e.L.out else if r = .x12 then e.L.k else 0)
    (by taint_decide) (by taint_decide)
    fun _ _ _ _ _ _ _ _ hc R hS _ => zeroE_pin hL hP16 hc R hS)
    fun _ _ _ _ _ _ _ _ hc R hS _ => ?_) (pw_taint [] (by taint_decide) nopin)
  refine WP.mono (zeroOut_ok (hc.lay hL hP16 R hS.scr) R hS.out (by rw [hS.k, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (by omega_arith) hL.k1024
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨e.L.OUT, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩)
    hL.bO (out_apart hL hP16)) fun _ ⟨_, Su, Ru, _⟩ =>
      In.of_step hL hP16 hc Su (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) Ru hS trivial

/-! ## The prologue -/

theorem head_ok {ts : List FnTable} {H : Spec.Mgf1.Hash} {P : Nat} {s : State} (h : (encSpec ts P).pre s)
    (hHa : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some H) :
    WP isa (.block encPrologue) (entered s) (In (lay H.len P s) s.gpr s.v s.mem fun _ _ => True) :=
  WP.mono (prologue_ok h hHa) fun t ⟨hc, _, hS⟩ =>
    ⟨hc, fun o => t.mem (off (lay H.len P s).scr o), fun j => word t.mem (lay H.len P s).Q (8 * j),
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩, hS, trivial⟩

/-- Two calls whose public data agree, in the inner frame, the first with the
table of `w₁` as the label's hash function's. -/
def Entered (vs : List MdHash) (w₁ : MdHash) (P : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (encSpec (tables vs) P).pre s₁ ∧ (encSpec (tables vs) P).pre s₂ ∧ (encSpec (tables vs) P).pub s₁ s₂ ∧
    Abi.tableHeld 64 s₁.mem (stackArg s₁ 8) ((tableOf w₁).words isa s₁) ∧ a = entered s₁ ∧ b = entered s₂

/-- The words of a table held in two memories with its functions at the
same addresses: the same. -/
theorem held_words {m₁ m₂ : Mem} {p : Addr} {a b : State} {T : FnTable} (h11 : T.fns.length + T.data.length = 11)
    (h₁ : Abi.tableHeld 64 m₁ p (T.words isa a)) (h₂ : Abi.tableHeld 64 m₂ p (T.words isa b))
    (hw : T.words isa a = T.words isa b) : Spec.Rsa.wordsAt m₁ p 11 = Spec.Rsa.wordsAt m₂ p 11 := by
  have hl : (T.words isa b).length = 11 := by simp [FnTable.words, h11]
  rw [hw] at h₁
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 11 := List.mem_range.mp hi
  have e₁ := h₁ i (by omega_using [hl, hi])
  have e₂ := h₂ i (by omega_using [hl, hi])
  simp only [Nat.reduceDiv] at e₁ e₂
  rw [e₁, e₂]

/-- The tables of `vs` have eleven words. -/
theorem tables_eleven (vs : List MdHash) : ∀ T ∈ tables vs, T.fns.length + T.data.length = 11 := by
  intro T hT
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hT
  rfl

/-- A table both runs hold, with its functions at the same addresses: the
same words. -/
theorem held_words_of {ts : List FnTable} (h11 : ∀ T ∈ ts, T.fns.length + T.data.length = 11) {m₁ m₂ : Mem}
    {p : Addr} {a b : State} (hsy : ∀ f ∈ tabFns ts, a.syms f = b.syms f) {T : FnTable} (hT : T ∈ ts)
    (h₁ : Abi.tableHeld 64 m₁ p (T.words isa a)) (h₂ : Abi.tableHeld 64 m₂ p (T.words isa b)) :
    Spec.Rsa.wordsAt m₁ p 11 = Spec.Rsa.wordsAt m₂ p 11 :=
  held_words (h11 T hT) h₁ h₂ (by
    simp only [FnTable.words]
    congr 1
    exact List.map_congr_left fun n hn => hsy n (List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hT, hn⟩))

theorem head_ct (vs : List MdHash) {w₁ : MdHash} (hw₁ : w₁ ∈ vs) {P : Nat} :
    RelCT isa (Entered vs w₁ P) (.block encPrologue)
      fun a b => ∃ e : Env, e.L.D = w₁.H.D ∧ PreOk e.L e.m₁ ∧ PreOk e.L e.m₂ ∧
        TabAgree (tables vs) (tabW e.L e.m₁) e.m₁ e.m₂ a b ∧
        Abi.tableHeld 64 e.m₁ (tabLW e.L e.m₁) ((tableOf w₁).words isa a) ∧
        Abi.tableHeld 64 e.m₂ (tabLW e.L e.m₂) ((tableOf w₁).words isa b) ∧ PW P e (fun _ _ => True) a b := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, hh₁, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨hL₁, hT₁, hd₁⟩ := spec_tab h₁
  obtain ⟨-, hT₂, hd₂⟩ := spec_tab h₂
  sig_pub [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, h4, h5', h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hp
  have hsy' : ∀ f ∈ tabFns (tables vs), s₁.syms f = s₂.syms f := fun f hf => hsy f (List.mem_append_left _ hf)
  have hTw : tableOf w₁ ∈ tables vs := List.mem_map_of_mem hw₁
  have hh₂ := (htabL _ _ rfl rfl _ hTw).mp hh₁
  have hHa₁ := hashAt_tableOf (held_tableOf hh₁).2.1
  have hHa₂ := hashAt_tableOf (held_tableOf hh₂).2.1
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (c := .block encPrologue) (by taint_decide)
    _ _ _ _ _ _ (by
      show (entered s₁).sp = (entered s₂).sp
      rw [entered_sp w₁.mgf.G.len P, entered_sp w₁.mgf.G.len P]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := head_ok h₁ hHa₁
  obtain ⟨_, u₂, x₂, y₂⟩ := head_ok h₂ hHa₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay w₁.mgf.G.len P s₂ = lay w₁.mgf.G.len P s₁ := by
    simp only [lay, preX, h0, h1, h2, h3, h4, h5', h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hsp]
  obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, h3, h5'])
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
  obtain ⟨hn, he⟩ := leak_split hb (by rw [bytesAt_length, bytesAt_length, h3])
  have tw : tabW (lay w₁.mgf.G.len P s₁) s₁.mem = stackArg s₁ 9 := tabW_lay _ _ _
  have tlw₁ : tabLW (lay w₁.mgf.G.len P s₁) s₁.mem = stackArg s₁ 8 := tabLW_lay _ _ _
  have tlw₂ : tabLW (lay w₁.mgf.G.len P s₁) s₂.mem = stackArg s₂ 8 := by rw [← e]; exact tabLW_lay _ _ _
  have hta : TabAgree (tables vs) (stackArg s₁ 9) s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨hT₁, hd₁⟩, ⟨by rw [a9]; exact hT₂, hd₂⟩, hsy', fun T hT => htab _ _ rfl a9.symm T hT⟩
  have sy₁ := Exec.syms e₁
  have sy₂ := Exec.syms e₂
  refine ⟨ht, ⟨lay w₁.mgf.G.len P s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, w₁.mgf.len, preOk_lay h₁ hHa₁,
    e ▸ preOk_lay h₂ hHa₂, by rw [tw]; exact hta.congr sy₁ sy₂, by rw [tlw₁, words_congr sy₁]; exact hh₁,
    by rw [tlw₂, words_congr sy₂]; exact hh₂, lay_ok h₁ hHa₁, rfl, ⟨?_, ?_, ?_⟩, y₁, e ▸ y₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    rw [hn, h2, h3]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    rw [he, h4, h5']
  · intro R hR
    simp only [lay, preX, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 6) ((stackArg s₁ 7).toNat * 8 / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 6) ((stackArg s₁ 7).toNat * 8 / 8)
      rw [Nat.mul_div_cancel _ (by decide : 0 < 8), hw, a6, a7]
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 8) (11 * (64 / 8) / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 8) (11 * (64 / 8) / 8)
      exact held_words_of (tables_eleven vs) hsy' hTw hh₁ (by rw [a8]; exact hh₂)
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 9) (11 * (64 / 8) / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 9) (11 * (64 / 8) / 8)
      obtain ⟨T, hT, hh⟩ := hT₁
      exact held_words_of (tables_eleven vs) hsy' hT hh ((htab _ _ rfl a9.symm T hT).mp hh)

theorem pub_sp {ts : List FnTable} {P : Nat} {s₁ s₂ : State}
    (h : (encSpec ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

theorem pw_mono {P : Nat} {e : Env} {X Y : (Nat → BitVec 64) → State → Prop} (h : ∀ W t, X W t → Y W t)
    {a b : State} (hp : PW P e X a b) : PW P e Y a b :=
  let ⟨hL, hP, hk, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ := hp
  ⟨hL, hP, hk, ⟨c₁, V₁, W₁, R₁, S₁, h _ _ x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, h _ _ x₂⟩⟩

/-! ## The digest length's branch -/

/-- `byLen` in two runs in the layout of `e` with the same digest length `D`
in `x16`: both take the branch of `D`. -/
theorem byLen_ct {P : Nat} {e : Env} (hL : e.L.Ok) (hP16 : 16 ≤ e.L.P) {b : Nat → Prog isa}
    {Q : State → State → Prop} {X : (Nat → BitVec 64) → State → Prop} {D : Nat} (hD : D < 4096)
    (h16 : ∀ W (t : State), X W t → t.gpr .x16 = BitVec.ofNat 64 D)
    (hst : ∀ W (t u : State), X W t → Step e.L.Q e.L.scr [] t u → u.syms = t.syms →
      (∀ r, r ≠ .x17 → u.gpr r = t.gpr r) → X W u)
    (hb : RelCT isa (PW P e X) (b D) Q) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 4096) → RelCT isa (PW P e X) (byLen b ds) Q
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    have hx0 := hx x (List.mem_cons_self ..)
    have hev : ∀ u : State, (u.gpr .x17 == 0) = decide (D = x) →
        isa.eval (.zero .x .x17) u = some (decide (D = x)) := fun u hz => by
      show eval (.zero .x .x17) u = _
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]
    have hback : ∀ s₁ s₂ (c : Option Bool), (PW P e (fun W t => X W t ∧ (t.gpr .x17 == 0) = decide (D = x)) s₁ s₂ ∧
        isa.eval (.zero .x .x17) s₁ = c) → PW P e X s₁ s₂ := fun _ _ _ ⟨hp, _⟩ => pw_mono (fun _ _ h => h.1) hp
    refine RelCT.seq (pw_blk (X' := fun W t => X W t ∧ (t.gpr .x17 == 0) = decide (D = x)) []
      (check_of_zImm (τ := Taint.ofRegs []) (c := .block [.subImm .x .x17 .x16 x])
        (c' := .block [.subImm .x .x17 .x16 0]) rfl (by taint_decide)) nopin
      fun _ _ _ _ _ _ _ _ hc R hS hφ => WP.mono (Table.wp_sy (cmpLen_ok (F := e.L.Q) (S := e.L.scr)
        (h16 _ _ hφ) hD hx0)) fun u ⟨⟨hz, st, hm, hg⟩, sy⟩ =>
          In.of_step hL hP16 hc st nil_ws (hm ▸ R) hS ⟨hst _ _ _ hφ st sy hg, hz⟩) ?_
    refine RelCT.ite (fun a b ⟨_, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [hev a xa.2, hev b xb.2]) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun a b h => hback a b _ h) fun _ _ h => h
      · exact RelCT.of_false fun a _ ⟨⟨_, _, _, ⟨_, _, _, _, _, xa⟩, _⟩, ht⟩ => by
          rw [hev a xa.2] at ht; simp [hDx] at ht
    · by_cases hDx : D = x
      · exact RelCT.of_false fun a _ ⟨⟨_, _, _, ⟨_, _, _, _, _, xa⟩, _⟩, ht⟩ => by
          rw [hev a xa.2] at ht; simp [hDx] at ht
      · exact (byLen_ct hL hP16 hD h16 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono (fun a b h => hback a b _ h) fun _ _ h => h

/-! ## The whole function -/

/-- After the prologue, in the layout of `e`, with the label's hash function
`w₁`'s and MGF1's `w`'s, at the addresses of the first run's functions:
the table's address to its slot and its digest length to `x16`, the branch
on it, the checks of `k` and the message's length, and `encMain`. -/
theorem rest_ct {vs : List MdHash} (c : PdChecked) {w₁ w : MdHash} {P : Nat} (hP : c.stack ≤ P) {e : Env}
    (hL : e.L.Ok) (hP' : e.L.P = P) (hP16 : 16 ≤ e.L.P) (hDe : e.L.D = w₁.H.D) (q₁ : PreOk e.L e.m₁)
    (q₂ : PreOk e.L e.m₂) {ai au af aiL auL afL : Addr} :
    RelCT isa (PW P e fun _ t => Table.TabX w.H.stream (fnsOf vs) (arg 9) e.L.Q e.L.scr (tabW e.L e.m₁) ai au af t ∧
        Table.TabX w₁.H.stream (fnsOf vs) (arg 8) e.L.Q e.L.scr (tabLW e.L e.m₁) aiL auL afL t)
      (.seq (.block (tabSlot 8)) (.seq (.block lenLoad)
        (byLen (fun d => encChecks (ofLen d) (Impl.RsaOaep.AArch64.Precomputed.encMain (ofLen d) (fnsOf vs)
          c.name c.code)) lens))) fun _ _ => True := by
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes w₁.ok.stream
  have hD64 : w₁.H.D ≤ 64 := Nat.le_trans hzDF hzF
  have hDl : w₁.H.D ∈ lens := by rw [← w₁.mgf.len]; exact mem_lens w₁.mgf.mem
  let X0 : (Nat → BitVec 64) → State → Prop := fun _ t =>
    Table.TabX w.H.stream (fnsOf vs) (arg 9) e.L.Q e.L.scr (tabW e.L e.m₁) ai au af t ∧
      Table.TabX w₁.H.stream (fnsOf vs) (arg 8) e.L.Q e.L.scr (tabLW e.L e.m₁) aiL auL afL t
  have ly : ∀ {g vv m₀} {t : State} {V W}, Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W → Slots e.L W →
      Lay t e.L.Q e.L.scr := fun hc R hS => hc.lay hL hP16 R hS.scr
  -- The table's address to its slot.
  refine RelCT.seq (pw_blk (X' := fun W t => X0 W t ∧ W 32 = tabLW e.L e.m₁) [] (by taint_decide) nopin
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (tabSlot_ok (by decide) (ly hc R hS) R hx.2.1))
      fun _ ⟨⟨_, Su, Ru, _⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws Ru
        (hS.of fun j _ h2 _ => by simp only [upd]; rw [ifn (by omega_arith)])
        ⟨⟨hx.1.step Su sy, hx.2.step Su sy⟩, by simp [upd]⟩) ?_
  -- Its digest length to `x16`.
  refine RelCT.seq (pw_wp (X' := fun W t => X0 W t ∧ t.gpr .x16 = BitVec.ofNat 64 w₁.H.D) (by
      show RelCT isa _ (.block ([.ldrSp .x16 sTab] ++ [.ldr .x .x16 .x16 48])) _
      exact RelCT.block_append (pw_seq_tr [.x16] (fun _ => tabLW e.L e.m₁) (by taint_decide) (by taint_decide)
        fun g vv m₀ t V W _ _ hc R hS h32 => by
          have Ly := ly hc R hS
          have h256 : InRegions (t.rd ++ t.wr) (e.L.Q + BitVec.ofNat 64 256) 8 := Ly.ld (d := 256) (by decide)
          have r32 := R.rd8 (d := 256) (k := 32) rfl (by decide) h32.2
          oaep_run [sTab, h256, Ly.sp, r32]
          and_intros <;> first | trivial | rfl | (intro r hr; rw [List.mem_singleton.mp hr]; rfl)))
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (lenLoad_ok (ly hc R hS) R hx.2 hx.1.2.1.rdD
      (hx.1.2.1.mem _ (Frame.refl _ _)).2.1))
      fun _ ⟨⟨Su, hm, h16, _⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws (hm ▸ R) hS
        ⟨⟨hx.1.1.step Su sy, hx.1.2.step Su sy⟩, h16⟩) ?_
  -- The branch for that length.
  refine byLen_ct hL hP16 (mem_lens_lt hDl) (fun _ _ h => h.2)
    (fun _ _ _ ⟨x0, h16⟩ st sy hg => ⟨⟨x0.1.step st sy, x0.2.step st sy⟩, (hg _ (by decide)).trans h16⟩) ?_ hDl
    fun x hx => mem_lens_lt hx
  show RelCT isa _ (encChecks (ofLen w₁.H.D) (Impl.RsaOaep.AArch64.Precomputed.encMain (ofLen w₁.H.D) (fnsOf vs)
    c.name c.code)) _
  rw [encChecks_D (G := ofLen w₁.H.D) (G' := w₁.H) rfl, encMain_D (G := ofLen w₁.H.D) (G' := w₁.H) rfl]
  unfold encChecks seqs seqs
  have hk3 : ∀ {W : Nat → BitVec 64}, Slots e.L W → W 21 = BitVec.ofNat 64 e.L.k.toNat := fun hS => by
    rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The check of `k`.
  refine RelCT.seq (pw_blk (X' := fun W t => KX w₁.H.D e.L.k.toNat W t ∧ X0 W t) []
    (check_of_zImm (τ := Taint.ofRegs []) (c := .block (chkK w₁.H)) (c' := .block (chkK gH)) rfl (by taint_decide))
    nopin fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (chkK_ok (H := w₁.H) (ly hc R hS) R (hk3 hS)
      hL.k1024 (by omega_arith)))
      fun _ ⟨⟨_, Su, hm, x11⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws (by rw [hm]; exact R) hS
        ⟨x11, hx.1.1.step Su sy, hx.1.2.step Su sy⟩) ?_
  refine RelCT.ite (fun a b ⟨_, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
    rw [eval_nonzero, eval_nonzero, xa.1, xb.1]) ?_ ?_
  · exact (encFail_tr hL hP16).mono (fun _ _ h => h.1) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hb⟩ e₁ e₂
  have hkD : 2 * w₁.H.D + 2 ≤ e.L.k.toNat := by
    obtain ⟨_, _, _, ⟨_, _, _, _, _, x₁⟩, _⟩ := hp
    by_contra hc
    rw [eval_nonzero, x₁.1, ifn (by omega_arith)] at hb
    exact absurd hb (by decide)
  -- The check of the message's length.
  refine (RelCT.seq (Q := fun _ _ => True) (pw_blk (X' := fun W t => MX w₁.H.D e.L.k.toNat e.L.ml.toNat W t ∧ X0 W t)
    [] (check_of_zImm (τ := Taint.ofRegs []) (c := .block (chkMsg w₁.H)) (c' := .block (chkMsg gH)) rfl
      (by taint_decide)) nopin
    fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (chkMsg_ok (H := w₁.H) (ly hc R hS) R (hk3 hS)
      (by rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hL.k1024 e.L.ml.isLt hkD))
      fun _ ⟨⟨_, Su, hm, x11⟩, sy⟩ => In.of_step hL hP16 hc Su nil_ws (by rw [hm]; exact R) hS
        ⟨x11, hx.1.step Su sy, hx.2.step Su sy⟩) ?_) _ _ _ _ _ _ (pw_mono (fun _ _ h => h.2) hp) e₁ e₂
  refine RelCT.ite (fun a b ⟨_, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
    rw [eval_nonzero, eval_nonzero, xa.1, xb.1]) ?_ ?_
  · exact (encFail_tr hL hP16).mono (fun _ _ h => h.1) fun _ _ h => h
  intro a₁ a₂ u₁ u₂ a₁' a₂' ⟨hp', hb'⟩ e₁ e₂
  have hmk : e.L.ml.toNat ≤ e.L.k.toNat - (2 * w₁.H.D + 2) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, _, x₁⟩, _⟩ := hp'
    by_contra hc
    rw [eval_nonzero, x₁.1, ifn (by omega_arith)] at hb'
    exact absurd hb' (by decide)
  exact encMain_tr w₁.ok.stream w.ok.stream w₁.mgf.hash w.mgf.hash w.mgf.len (mgf_valid w.mgf) c hL (hP' ▸ hP)
    hP16 hDe q₁ q₂ (by omega_arith) _ _ _ _ _ _ (pw_mono (fun _ _ h => h.2) hp') e₁ e₂

theorem enc_ct {vs : List MdHash} (hc : Coh vs) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) :
    ConstantTime isa (encSpec (tables vs) P).pre (encSpec (tables vs) P).pub
      (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [encBody_eq]
  intro a b ta tb a' b' hpre e₁ e₂
  obtain ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, ea, eb⟩, ea', eb'⟩ := hpre
  obtain ⟨⟨T₁, hT₁, hh₁⟩, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  refine ((head_ct vs hw₁).seq (Q := fun _ _ => True) ?_) _ _ _ _ _ _
    ⟨s₁, s₂, h₁, h₂, hp, hh₁, by rw [ea', ea]; rfl, by rw [eb', eb]; rfl⟩ e₁ e₂
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨e, hDe, q₁, q₂, ta, hl₁, hl₂, hL, hP', hk, f₁, f₂⟩ e₁ e₂
  have hP16' : 16 ≤ e.L.P := hP' ▸ hP16
  -- MGF1's table, in each run.
  obtain ⟨⟨⟨T, hT, hh₁⟩, hd₁⟩, ⟨-, hd₂⟩, hsy, hiff⟩ := ta
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨-, -, tw, tlw⟩ := pre_eq q₁ q₂
  obtain ⟨hm₁, -, hD₁⟩ := held_tableOf hh₁
  obtain ⟨hm₂, -, hD₂⟩ := held_tableOf ((hiff _ hT).mp hh₁)
  have hn := mem_names hw
  -- The label's hash function's.
  obtain ⟨hmL₁, -, hDL₁⟩ := held_tableOf hl₁
  obtain ⟨hmL₂, -, hDL₂⟩ := held_tableOf hl₂
  have hnL := mem_names hw₁
  have x₁ : Table.TabX w.H.stream (fnsOf vs) (arg 9) e.L.Q e.L.scr (tabW e.L e.m₁) (s₁.syms w.H.initN)
      (s₁.syms w.H.updN) (s₁.syms w.H.finN) s₁ ∧
      Table.TabX w₁.H.stream (fnsOf vs) (arg 8) e.L.Q e.L.scr (tabLW e.L e.m₁) (s₁.syms w₁.H.initN)
      (s₁.syms w₁.H.updN) (s₁.syms w₁.H.finN) s₁ :=
    ⟨⟨tab_of hL hP16' f₁.1 q₁ (tabOK_of hc hd₁ hw) hm₁ hD₁, rfl, rfl, rfl⟩,
      ⟨tabL_of hL hP16' f₁.1 q₁ (tabOK_of hc hd₁ hw₁) hmL₁ hDL₁, rfl, rfl, rfl⟩⟩
  have x₂ : Table.TabX w.H.stream (fnsOf vs) (arg 9) e.L.Q e.L.scr (tabW e.L e.m₁) (s₁.syms w.H.initN)
      (s₁.syms w.H.updN) (s₁.syms w.H.finN) s₂ ∧
      Table.TabX w₁.H.stream (fnsOf vs) (arg 8) e.L.Q e.L.scr (tabLW e.L e.m₁) (s₁.syms w₁.H.initN)
      (s₁.syms w₁.H.updN) (s₁.syms w₁.H.finN) s₂ :=
    ⟨⟨by rw [tw]; exact tab_of hL hP16' f₂.1 q₂ (tabOK_of hc hd₂ hw) (tw ▸ hm₂) (tw ▸ hD₂),
        (hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm⟩,
      ⟨by rw [tlw]; exact tabL_of hL hP16' f₂.1 q₂ (tabOK_of hc hd₂ hw₁) hmL₂ hDL₂,
        (hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2).symm⟩⟩
  exact rest_ct c hP hL hP' hP16' hDe q₁ q₂ _ _ _ _ _ _ ⟨hL, hP', hk,
    ⟨f₁.1, f₁.2.choose, f₁.2.choose_spec.choose, f₁.2.choose_spec.choose_spec.1, f₁.2.choose_spec.choose_spec.2.1, x₁⟩,
    ⟨f₂.1, f₂.2.choose, f₂.2.choose_spec.choose, f₂.2.choose_spec.choose_spec.1, f₂.2.choose_spec.choose_spec.2.1, x₂⟩⟩
    e₁ e₂

/-- The stack below the frames: the callee's, and at least 16 bytes. -/
def encP (c : PdChecked) : Nat := max c.stack 16

/-- The stack the function uses: the callee's and the frames'. -/
def encStack (c : PdChecked) : Nat := encP c + 288

/-- `vg_rsa_oaep_encrypt_precomputed`, calling the precomputed public
operation `c`, for the tables of `vs`. -/
theorem enc_verified {vs : List MdHash} (hc : Coh vs) (c : PdChecked)
    (hsat : ∃ s, (encSpec (tables vs) (encP c)).pre s) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf vs) c.name c.code)
      (encSpec (tables vs) (encP c)) := by
  have hP : c.stack ≤ encP c := Nat.le_max_left _ _
  have hP16 : 16 ≤ encP c := Nat.le_max_right _ _
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := enc_ok hc c hP hP16 h
    exact ⟨t, s', he, hp⟩) (enc_ct hc c hP hP16) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Enc

end

end

/-! ### `RsaOaep.AArch64.DecPCT`, which only this module used -/

section

/-! ### `RsaOaep.AArch64.DecVerified`, which this module and modules that import it used -/

section

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
  sig_pub [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
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
    have hP16 : 16 ≤ e.L.P := by omega_using [hS, hP]
    have hkD : 2 * w₁.H.D + 2 ≤ e.L.k.toNat := by
      by_contra hk
      rw [eval_nonzero, x₁.2, ifn (by omega_using [hk])] at hb
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
/-- After the private-key operation: the table of the label's hash
function, its digest length, and the tail for it. -/
theorem after_ct {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (Two S (tables vs) CalledI) (.seq (.block (tabSlot 15)) (.seq (.block lenLoad)
      (byLen (fun d => decTail (ofLen d) (fnsOf vs)) lens))) fun _ _ => True :=
  two_split (Q := fun _ _ => True) fun T hT => by
    obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT
    have hDl : w₁.H.D ∈ lens := by rw [← w₁.mgf.len]; exact mem_lens w₁.mgf.mem
    refine (tabSlot_ct hc hw₁ hS).seq ((lenLoad_ct hc hw₁ hS).seq (byLen_ct (D := w₁.H.D)
      (fun _ _ _ _ _ h => h.1.1) (mem_lens_lt hDl) (fun _ _ _ _ _ ⟨⟨_, _, _, _, _, _, h⟩, _⟩ => h)
      (fun L g vv m₀ t u hL hP h st hm sy hg => ?_) (tail_ct hc hw₁ hS) hDl fun x hx => mem_lens_lt hx))
    obtain ⟨⟨hcx, V, W, R, hSl, h32, h16⟩, _⟩ := id h
    exact WithL.of (Φ := LenI w₁.H.D) h sy ⟨hcx.step hL (by omega_arith) st nil_ws, V, W, hm ▸ R, hSl, h32,
      (hg _ (by decide)).trans h16⟩

include hc in
theorem dec_ct (pv : PrivImpl) :
    ConstantTime isa (decSpec (tables vs) (pv.S + 1)).pre (decSpec (tables vs) (pv.S + 1)).pub
      (decrypt (fnsOf vs) pv.name pv.code) := by
  have hS := pv.S15
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBody_eq]
  refine ((head_ct (tables vs) hS).seq ((priv_ct pv (tables vs)).seq (after_ct hc hS))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
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

end

end

/-! ### `RsaOaep.AArch64.DecP`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on AArch64, given the key's precomputed values

`vg_rsa_oaep_decrypt_precomputed` (`decryptP`) is `vg_rsa_oaep_decrypt` with
`vg_rsa_private_checked_precomputed` as the private-key operation: our stack
arguments 17 and 18, `pre` and `pre_len`, are its stack arguments 12 and 13,
the frame's words 12 and 13 (`preArgs`), MGF1's slots of `scratch` and of its
source, which nothing reads before the call; after it, `scratch` goes back to
its slot (`fixScr`), and the decoding is `vg_rsa_oaep_decrypt`'s (`after_ok`).

The layout (`layP`) is `vg_rsa_oaep_decrypt`'s, with `pre` among the buffers
read (`DLay.X`), our 19 stack arguments (`DLay.al`), and `pre`'s modulus'
values among what the function may leak (`DLay.lk`). `specP` is what the
contract says of it, and `PreX` what the call needs of `pre`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash Stream)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked stackArgs_fourteen)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce bytesAt_eq read8 write8 q_add add_add toNat_sub_k
  popped_mem popped_sp popped_v popped_gpr_self popped_gpr_ne freed_mem freed_sp freed_v freed_gpr preserved_ne)

/-- The contract, with both hash functions each one of the tables `ts` and
`P + 288` bytes of stack. -/
abbrev decSpecP (ts : List FnTable) (P : Nat) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract (AArch64.abi.withTables
    Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) (P + 288)

/-- Unfolds the contract's precondition at `h`. -/
macro "dec_preP" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- What a call from `s` adds to the layout: `pre` (our stack arguments 17
and 18), our 19 stack arguments, and the modulus' values in `pre`, which the
function may leak. -/
def dxP (s : State) : DX where
  X := [⟨stackArg s 17, (stackArg s 18).toNat * 8⟩]
  al := 152
  pre := stackArg s 17
  prl := stackArg s 18
  lk := fun m => Spec.Rsa.privatePrecomputedLeak m (stackArg s 17) (s.gpr .x4).toNat

/-- The layout of a call from `s`, with `P` bytes of stack for the calls. -/
abbrev layP (P : Nat) (s : State) : DLay := lay P s (dxP s)

/-- What the call of `vg_rsa_private_checked_precomputed` needs of `pre`,
from the memory `m₀` on entry. -/
structure PreX (L : DLay) (m₀ : Mem) : Prop where
  x : L.X = [⟨L.pre, L.prl.toNat * 8⟩]
  al : L.al = 152
  a17 : m₀.readW (L.Q + BitVec.ofNat 64 424) 64 = L.pre
  a18 : m₀.readW (L.Q + BitVec.ofNat 64 432) 64 = L.prl
  prlv : L.prl.toNat = Spec.Rsa.privatePrecomputedWords L.k.toNat L.pl.toNat L.ql.toNat
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat)
      (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) =
    some (Spec.Rsa.wordsAt m₀ L.pre L.prl.toNat)
  lk : L.lk = fun m => Spec.Rsa.privatePrecomputedLeak m L.pre L.k.toNat

/-- What the contract says of a call. -/
structure SpecP (ts : List FnTable) (P : Nat) (s : State) : Prop where
  ok : (layP P s).Ok
  rd : s.rd = [(layP P s).N, (layP P s).E, (layP P s).PP, (layP P s).QQ, (layP P s).DP, (layP P s).DQ,
    (layP P s).QI, (layP P s).LAB, (layP P s).CT] ++ (layP P s).X ++
    [(layP P s).TABL, (layP P s).TAB, (layP P s).ARGS]
  wr : s.wr = [(layP P s).OUT, (layP P s).ML, (layP P s).SCR]
  pre : PreX (layP P s) s.mem
  sp : P + 288 ≤ s.sp.toNat
  tabL : ∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)
  tab : ∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)
  pw : ((ts.map (·.fns)).flatten).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)

theorem stackArg_q (P : Nat) (s : State) (x : DX) (j : Nat) :
    s.mem.readW ((lay P s x).Q + BitVec.ofNat 64 (288 + 8 * j)) 64 = stackArg s j := by
  rw [stackArg, stackArgAddr, ← lay_Q P s x, add_add]

theorem specP {ts : List FnTable} {P : Nat} {s : State} (h : (decSpecP ts P).pre s) : SpecP ts P s := by
  dec_preP at h
  sig_split h
  rename_i hsp hsp2 hheld hheld2 hpw hrd hwr oM oN oE oP oQ oDP oDQ oQI oL oC oS oPr oTL oT oA mN mE mP mQ mDP
    mDQ mQI mL mC mS mPr mTL mT mA nS eS pS qS dpS dqS qiS lS cS sPr sTL sT sA kO kM kN kE kP kQ kDP kDQ kQI kL kC
    kS kPr kTL kT kA bO bM bN bE bP bQ bDP bDQ bQI bL bC bS bPr bTL bT kv hk1 hk2 el1 elk pl1 plk ql1 qlk hdp hqi
    hdq slk prl
  have key := h
  clear h kA
  simp only [hk1, hk2, hdp, hqi, hdq] at oA oN oE oP oQ oDP oDQ oQI oL oC oS oM oT oTL oPr
  simp only [hk2, hdp, hqi, hdq] at mC mDP mDQ mQI cS dpS dqS qiS
  simp only [hk1, hk2, hdp, hqi, hdq] at kO kC kDP kDQ kQI bO bC bDP bDQ bQI
  obtain eA : (layP P s).ARGS = ⟨stackArgAddr s 0, 152⟩ := by
    show (⟨(layP P s).Q + BitVec.ofNat 64 288, 152⟩ : Region) = _
    rw [lay_args P s (dxP s)]
  obtain eK : (layP P s).STK = ⟨s.sp - BitVec.ofNat 64 (P + 288), P + 288⟩ := by
    show (⟨(layP P s).Q - BitVec.ofNat 64 P, P + 288⟩ : Region) = _
    rw [lay_stk P s (dxP s)]
  obtain hQ : (layP P s).Q.toNat = s.sp.toNat - 288 := toNat_sub_k (by omega_arith)
  obtain one : ∀ {F : Region → Prop}, F ⟨stackArg s 17, (stackArg s 18).toNat * 8⟩ →
      ∀ R ∈ (layP P s).X, F R := fun hF R hR => by
    rw [List.mem_singleton.mp hR]; exact hF
  refine ⟨⟨oM, oS, mS, forall_ro ⟨oN, oE, oP, oQ, oDP, oDQ, oQI, oL, oC⟩,
    forall_ro ⟨mN, mE, mP, mQ, mDP, mDQ, mQI, mL, mC⟩,
    forall_ro ⟨nS.symm, eS.symm, pS.symm, qS.symm, dpS.symm, dqS.symm, qiS.symm, lS.symm, cS.symm⟩, eA ▸ oA,
    eA ▸ mA, eA ▸ sA, oT, mT, sT, oTL, mTL, sTL, eK ▸ kO, eK ▸ kM, eK ▸ kS, forall_ro ⟨eK ▸ kN, eK ▸ kE, eK ▸ kP,
    eK ▸ kQ, eK ▸ kDP, eK ▸ kDQ, eK ▸ kQI, eK ▸ kL, eK ▸ kC⟩, eK ▸ kT, eK ▸ kTL, bO, bM, bS,
    forall_ro ⟨bN, bE, bP, bQ, bDP, bDQ, bQI, bL, bC⟩, bT, bTL,
    by simp only [lay] at hQ ⊢; omega_arith, by simp only [lay] at hQ ⊢; omega_arith, kv, hk1, hk2, el1, elk,
    pl1, plk, ql1, qlk, hdp, hqi, hdq, slk, (by decide : 136 ≤ 152), Nat.le_refl _,
    by show (layP P s).Q.toNat + 288 + 152 ≤ _; simp only [lay] at hQ ⊢; omega_arith, one oPr.symm, one mPr.symm, one sPr.symm, one (eK ▸ kPr), one bPr⟩,
    ?_, ?_, ⟨rfl, rfl, ?_, ?_, prl, key, rfl⟩, hsp, hheld, hheld2, hpw.sublist (List.sublist_append_left _ _)⟩
  · rw [hrd, hk2, hdp, hqi, hdq, ← lay_args P s (dxP s)]; rfl
  · rw [hwr, hk1]; rfl
  · exact stackArg_q P s (dxP s) 17
  · exact stackArg_q P s (dxP s) 18

/-! ## The moves of `pre` and `pre_len` -/

section
variable {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- A word of our stack arguments 17 and 18, as on entry. -/
theorem PreX.arg (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) {d : Nat}
    (hd : d = 424 ∨ d = 432) :
    t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = m₀.readW (L.Q + BitVec.ofNat 64 d) 64 := by
  have hpQ := hL.pQ
  have hn := hL.nQa
  have hal := hx.al
  obtain hs : Region.Sub ⟨L.Q + BitVec.ofNat 64 d, 8⟩ L.ARGS := Offset.sub _ (by omega_using [hd]) (by omega_using [hd, hal])
  refine hc.frame.readW (r := ⟨L.Q + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact (hL.oA.sub_right hs).symm
  · exact (hL.mA.sub_right hs).symm
  · exact (hL.sA.sub_right hs).symm
  · show Region.Disjoint _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P + 288⟩
    rw [q_add L.Q L.P d]
    exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hd, hpQ, hn, hal])

/-- Our stack arguments 17 and 18 to the frame's words 12 and 13. -/
theorem preArgs_ok (hL : L.Ok) (hP : 16 ≤ L.P) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hr : Ready L t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) :
    WP isa (.block preArgs) t fun u => Ctx L g vv m₀ u ∧ Ready L u ∧
      Rep u.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl) := by
  have hpQ := hL.pQ
  have hn := hL.nQa
  have hal := hx.al
  obtain G' := hL.geo hP
  unfold preArgs
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain h0 : WP isa (.block [.addSp .x9 0]) t fun t₀ => t₀ = t.write .x .x9 L.Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, hc.sp,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  obtain x9 : (t.write .x .x9 L.Q).gpr .x9 = L.Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  obtain inA : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ d, d = 424 ∨ d = 432 →
      InRegions (u.rd ++ u.wr) (L.Q + BitVec.ofNat 64 d) 8 := fun u hu hw d hd =>
    ⟨L.ARGS, by rw [hu, hw, hc.rd]; simp, Offset.contains _ (by omega_using [hd]) (by omega_using [hal, hd]) (by omega_using [hal])⟩
  obtain inF : ∀ (u : State), u.wr = t.wr → ∀ d, d + 8 ≤ frameBytes →
      InRegions u.wr (L.Q + BitVec.ofNat 64 d) 8 := fun u hw d hd =>
    ⟨L.FR, by rw [hw, hc.wr]; simp, Offset.contains_base _ hd (by unfold frameBytes at hd; omega_using [hd])⟩
  refine WP.mono (mv_step (j := 17) (d := 96) (by decide) (by decide)
    (by rw [RegUpd.sp_write, hc.sp]; exact inA _ (RegUpd.rd_write ..) (RegUpd.wr_write ..) 424 (.inl rfl))
    (by rw [x9]; exact inF _ (RegUpd.wr_write ..) 96 (by decide))) fun t₁ ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
  obtain sp₁ : t₁.sp = L.Q := by rw [s₁, RegUpd.sp_write, hc.sp]
  refine WP.mono (mv_step (j := 18) (d := 104) (by decide) (by decide)
    (by rw [sp₁]; exact inA _ (r₁.trans (RegUpd.rd_write ..)) (w₁.trans (RegUpd.wr_write ..)) 432 (.inr rfl))
    (by rw [g₁ .x9 (by decide), x9]; exact inF _ (w₁.trans (RegUpd.wr_write ..)) 104 (by decide)))
    fun u ⟨r₂, w₂, s₂, v₂, m₂, g₂⟩ => ?_
  -- The values moved.
  obtain e17 : (t.write .x .x9 L.Q).mem.readW ((t.write .x .x9 L.Q).sp + BitVec.ofNat 64 (arg 17)) 64 = L.pre := by
    rw [RegUpd.mem_write, RegUpd.sp_write, hc.sp, show arg 17 = 424 from rfl, hx.arg hL hc (.inl rfl), hx.a17]
  obtain sep : Mem.Sep (L.Q + BitVec.ofNat 64 432) 8 (L.Q + BitVec.ofNat 64 96) 8 :=
    Offset.sep _ (by omega_using []) (by omega_using []) (by omega_using [])
  obtain e18 : t₁.mem.readW (t₁.sp + BitVec.ofNat 64 (arg 18)) 64 = L.prl := by
    rw [m₁, x9, e17, sp₁, show arg 18 = 432 from rfl, RegUpd.mem_write,
      Mem.readW_writeW_sep sep (by decide), hx.arg hL hc (.inr rfl), hx.a18]
  obtain mu : u.mem = (t.mem.write (off L.Q (8 * 12)) 8 L.pre).write (off L.Q (8 * 13)) 8 L.prl := by
    rw [m₂, e18, g₁ .x9 (by decide), x9, m₁, x9, e17, RegUpd.mem_write, write8, write8]
  obtain gu : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r := fun r h9 h10 => by
    rw [g₂ r h10, g₁ r h10, RegUpd.gpr_write_of_ne _ _ _ h9]
  obtain S : Step L.Q L.scr [] t u := ⟨r₂.trans (r₁.trans (RegUpd.rd_write ..)),
    w₂.trans (w₁.trans (RegUpd.wr_write ..)), by rw [s₂, sp₁, hc.sp],
    fun r hr _ => gu r (preserved_ne hr (by decide)) (preserved_ne hr (by decide)),
    fun r _ => by rw [v₂, v₁, RegUpd.v_write], by
      rw [mu]
      exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF L.Q (by decide)))
        (List.mem_cons_self ..) _ (cF L.Q (by decide))⟩
  refine ⟨hc.step hL hP S fun r h => absurd h List.not_mem_nil, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [gu .x0 (by decide) (by decide)]; exact hr.x0
  · rw [gu .x1 (by decide) (by decide)]; exact hr.x1
  · rw [gu .x2 (by decide) (by decide)]; exact hr.x2
  · rw [gu .x3 (by decide) (by decide)]; exact hr.x3
  · rw [gu .x4 (by decide) (by decide)]; exact hr.x4
  · rw [gu .x5 (by decide) (by decide)]; exact hr.x5
  · rw [gu .x6 (by decide) (by decide)]; exact hr.x6
  · rw [gu .x7 (by decide) (by decide)]; exact hr.x7
  · rw [mu]; exact (R.wq G' (k := 12) (by decide) _).wq G' (k := 13) (by decide) _

/-! ## The call -/

/-- The regions the call of `vg_rsa_private_checked_precomputed` reads. -/
abbrev privRdP (L : DLay) : List Region :=
  [L.N, L.E, L.CT, L.PP, L.QQ, L.DP, L.DQ, L.QI, ⟨L.pre, L.prl.toNat * 8⟩, ⟨L.Q + BitVec.ofNat 64 0, 112⟩]

theorem upd2 {W : Nat → BitVec 64} {a b : BitVec 64} {i : Nat} (hi : i < 12) :
    upd (upd W 12 a) 13 b i = W i := by
  simp only [upd]; rw [ifn (by omega_using [hi]), ifn (by omega_using [hi])]

theorem pre_mem (hx : PreX L m₀) : (⟨L.pre, L.prl.toNat * 8⟩ : Region) ∈ L.X := by rw [hx.x]; simp

/-- The first `n` words of `pre`, as on entry. -/
theorem PreX.words (hx : PreX L m₀) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {n : Nat}
    (hn : n ≤ L.prl.toNat) : Spec.Rsa.wordsAt t.mem L.pre n = Spec.Rsa.wordsAt m₀ L.pre n := by
  obtain hPm := pre_mem hx
  have := hL.xw _ hPm
  dsimp only at this
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  refine hc.frame.readW (r := ⟨L.pre, L.prl.toNat * 8⟩) (Offset.contains_base _ (by omega_using [hn, hi]) (by omega_using [hn, this, hi])) ?_
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  exacts [hL.xO _ hPm, hL.xM _ hPm, hL.xS _ hPm, (hL.xK _ hPm).symm]

theorem privP_pre (hL : L.Ok) {S : Nat} (hP : L.P = S + 1) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t)
    (hr : Ready L t) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl))
    (hA : CallArgs L W) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)).pre
      (t.callEntry.withRegions (privRdP L) (privWr L)) := by
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hs8 := hL.s8192
  have hk := hL.k1024
  have hbS := hL.bS
  rw [hP] at hpQ
  obtain hPm := pre_mem hx
  obtain hlow : (⟨L.Q - BitVec.ofNat 64 (S + 1), S + 1⟩ : Region) = L.LOW := by
    show _ = (⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩ : Region); rw [hP]
  obtain sa : ∀ i < 14, stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) i = upd (upd W 12 L.pre) 13 L.prl i :=
    fun i hi => by rw [stackArg_ce, hc.sp]; exact R.fr i (by unfold nW frameBytes; omega_arith)
  obtain sw : ∀ i < 12, stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) i = W i :=
    fun i hi => (sa i (by omega_using [hi])).trans (upd2 hi)
  obtain a0 := (sw 0 (by decide)).trans hA.p
  obtain a1 := (sw 1 (by decide)).trans (hA.args 0 (by decide))
  obtain a2 := (sw 2 (by decide)).trans (hA.args 1 (by decide))
  obtain a3 := (sw 3 (by decide)).trans (hA.args 2 (by decide))
  obtain a4 := (sw 4 (by decide)).trans (hA.args 3 (by decide))
  obtain a5 := (sw 5 (by decide)).trans (hA.args 4 (by decide))
  obtain a6 := (sw 6 (by decide)).trans (hA.args 5 (by decide))
  obtain a7 := (sw 7 (by decide)).trans (hA.args 6 (by decide))
  obtain a8 := (sw 8 (by decide)).trans (hA.args 7 (by decide))
  obtain a9 := (sw 9 (by decide)).trans (hA.args 8 (by decide))
  obtain a10 := (sw 10 (by decide)).trans hA.s10
  obtain a11 := (sw 11 (by decide)).trans hA.s11
  obtain a12 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 12 = L.pre :=
    (sa 12 (by decide)).trans (by simp [upd])
  obtain a13 : stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) 13 = L.prl :=
    (sa 13 (by decide)).trans (by simp [upd])
  simp only [ourArg] at a1 a2 a3 a4 a5 a6 a7 a8 a9
  obtain aa : stackArgAddr (t.callEntry.withRegions (privRdP L) (privWr L)) 0 = L.Q + BitVec.ofNat 64 0 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp]
  obtain arS : Region.Sub ⟨L.Q + BitVec.ofNat 64 0, 112⟩ L.STK := DLay.Ok.sub_stk (by omega_arith)
  obtain lS := DLay.Ok.low_stk (L := L)
  obtain hsl := sl_sub hL
  obtain hOut : Region.Sub ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩ L.SCR := Offset.sub_base _ (by omega_arith)
  obtain hScr : Region.Sub ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ L.SCR :=
    Offset.sub_base _ (by rw [hsl]; omega_arith)
  obtain dOS : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 0, L.k.toNat⟩
      ⟨L.scr + BitVec.ofNat 64 8192, (L.sl - BitVec.ofNat 64 1024).toNat * 8⟩ :=
    Offset.disjoint L.scr (.inl (by omega_arith)) (by omega_arith) (by rw [hsl]; omega_arith)
  obtain hw := hx.words hL hc (Nat.le_refl _)
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  simp only [hc.sp, hr.x0, hr.x1, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, hr.x7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13, aa, hlow, hL.dpl, hL.qil, hL.dql, hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hw]
  refine ⟨by omega_arith, by omega_arith, trivial, trivial,
    (hL.sR _ (ro_N L)).sub_left hOut, (hL.sR _ (ro_E L)).sub_left hOut, (hL.sR _ (ro_CT L)).sub_left hOut,
    (hL.sR _ (ro_PP L)).sub_left hOut, (hL.sR _ (ro_QQ L)).sub_left hOut, (hL.sR _ (ro_DP L)).sub_left hOut,
    (hL.sR _ (ro_DQ L)).sub_left hOut, (hL.sR _ (ro_QI L)).sub_left hOut, dOS,
    (hL.xS _ hPm).symm.sub_left hOut, ((hL.kS.sub_left arS).symm.sub_left hOut),
    ((hL.sR _ (ro_N L)).sub_left hScr).symm, ((hL.sR _ (ro_E L)).sub_left hScr).symm,
    ((hL.sR _ (ro_CT L)).sub_left hScr).symm, ((hL.sR _ (ro_PP L)).sub_left hScr).symm,
    ((hL.sR _ (ro_QQ L)).sub_left hScr).symm, ((hL.sR _ (ro_DP L)).sub_left hScr).symm,
    ((hL.sR _ (ro_DQ L)).sub_left hScr).symm, ((hL.sR _ (ro_QI L)).sub_left hScr).symm,
    (hL.xS _ hPm).symm.sub_left hScr, ((hL.kS.sub_left arS).symm.sub_left hScr),
    (hL.kS.sub_left lS).sub_right hOut, (hL.kR _ (ro_N L)).sub_left lS, (hL.kR _ (ro_E L)).sub_left lS,
    (hL.kR _ (ro_CT L)).sub_left lS, (hL.kR _ (ro_PP L)).sub_left lS, (hL.kR _ (ro_QQ L)).sub_left lS,
    (hL.kR _ (ro_DP L)).sub_left lS, (hL.kR _ (ro_DQ L)).sub_left lS, (hL.kR _ (ro_QI L)).sub_left lS,
    (hL.kS.sub_left lS).sub_right hScr, (hL.xK _ hPm).sub_left lS, (hL.fr_low (by omega_arith)).symm,
    by rw [BitVec.add_zero]; omega_arith, hL.bR _ (ro_N L), hL.bR _ (ro_E L), hL.bR _ (ro_CT L), hL.bR _ (ro_PP L),
    hL.bR _ (ro_QQ L), hL.bR _ (ro_DP L), hL.bR _ (ro_DQ L), hL.bR _ (ro_QI L),
    by rw [scr8192 hL, hsl]; omega_arith, hL.xw _ hPm,
    hL.kv, trivial, trivial, hL.el1, hL.elk, hL.pl1, hL.plk, hL.ql1, hL.qlk, trivial, trivial, trivial,
    by rw [hsl]; have := hL.slk; unfold Spec.RsaPss.scratchWords at this; omega_arith, hx.prlv, hx.key⟩

theorem covers_privP (hL : L.Ok) (hx : PreX L m₀) {t : State} (hc : Ctx L g vv m₀ t) :
    Covers (privRdP L ++ privWr L) (t.rd ++ t.wr) ∧ Covers (privWr L) t.wr := by
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have hs8 := hL.s8192
  have hk := hL.k1024
  obtain hsl := sl_sub hL
  obtain c1 : ∃ off, L.scr + BitVec.ofNat 64 0 = L.SCR.base + BitVec.ofNat 64 off ∧ off + L.k.toNat ≤ L.SCR.len :=
    ⟨0, rfl, by show 0 + L.k.toNat ≤ L.sl.toNat * 8; omega_arith⟩
  obtain c2 : ∃ off, L.scr + BitVec.ofNat 64 8192 = L.SCR.base + BitVec.ofNat 64 off ∧
      off + (L.sl - BitVec.ofNat 64 1024).toNat * 8 ≤ L.SCR.len :=
    ⟨8192, rfl, by show 8192 + _ ≤ L.sl.toNat * 8; rw [hsl]; omega_arith⟩
  rw [hc.rd, hc.wr, hx.x]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [privRdP, privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.N, by simp, 0, z _, by simp⟩
    · exact ⟨L.E, by simp, 0, z _, by simp⟩
    · exact ⟨L.CT, by simp, 0, z _, by simp⟩
    · exact ⟨L.PP, by simp, 0, z _, by simp⟩
    · exact ⟨L.QQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.DP, by simp, 0, z _, by simp⟩
    · exact ⟨L.DQ, by simp, 0, z _, by simp⟩
    · exact ⟨L.QI, by simp, 0, z _, by simp⟩
    · exact ⟨⟨L.pre, L.prl.toNat * 8⟩, by simp, 0, z _, by simp⟩
    · exact ⟨L.FR, by simp, 0, rfl, by show 0 + 112 ≤ frameBytes; decide⟩
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.SCR, by simp, c2⟩
  · simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.SCR, by simp, c1⟩
    · exact ⟨L.SCR, by simp, c2⟩

/-- The call of `vg_rsa_private_checked_precomputed`: as `priv_call`, the
frame's words as they were. -/
theorem privP_call (c : PrivPChecked) (hL : L.Ok) (hP : L.P = c.stack) (hx : PreX L m₀) {t : State}
    (hc : Ctx L g vv m₀ t) (hr : Ready L t) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl)) (hA : CallArgs L W) :
    WP isa (.call c.name c.code) t (Called L g vv m₀ (upd (upd W 12 L.pre) 13 L.prl)) := by
  obtain ⟨S, hS⟩ : ∃ S, c.stack = S + 1 := ⟨c.stack - 1, by have := c.pos; omega_using [this]⟩
  obtain hP' : L.P = S + 1 := hP.trans hS
  have hnQ := hL.nQ
  obtain hdp : 16 * c.code.aarch64Depth ≤ S + 1 := hS ▸ c.depth
  have hpQ := hL.pQ
  rw [hP'] at hpQ
  obtain ⟨hcov, hcovw⟩ := covers_privP hL hx hc
  have hs8 := hL.s8192
  have hk := hL.k1024
  obtain hsl := sl_sub hL
  obtain hv : Verified AArch64.target c.code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)) :=
    hS ▸ c.verified
  refine WP.callFV hv.1 (privP_pre hL hP' hx hc hr R hA) hcov hcovw
    (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega_arith)
  obtain hlow : Region.Sub (below t.sp (16 * c.code.aarch64Depth)) L.LOW := by
    rw [hc.sp]
    show Region.Sub _ ⟨L.Q - BitVec.ofNat 64 L.P, L.P⟩
    rw [hP']; exact Offset.sub_below _ hdp (by omega_arith)
  obtain hws : ∀ r ∈ privWr L ++ [below t.sp (16 * c.code.aarch64Depth)],
      Region.Sub r L.SCR ∨ Region.Sub r L.LOW := fun r hr => by
    simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Offset.sub_base _ (by omega_arith))
    · exact .inl (Offset.sub_base _ (by rw [hsl]; omega_arith))
    · exact .inr hlow
  obtain hfr : ∀ d, d + 8 ≤ 424 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      ∀ X ∈ privWr L ++ [below t.sp (16 * c.code.aarch64Depth)], Region.Disjoint ⟨L.Q + BitVec.ofNat 64 d, 8⟩ X :=
    fun d h₁ h₂ X hX => by
      rcases hws X hX with hs | hs
      · rcases h₂ with h₂ | h₂
        · exact hL.stk_buf h₂ (.inr (.inr hs))
        · exact hL.args_buf h₂ h₁ (.inr (.inr hs))
      · exact (hL.fr_low h₁).sub_right hs
  obtain hk' : ∀ d, d + 8 ≤ 424 → (d + 8 ≤ 288 ∨ 288 ≤ d) →
      s'.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (hfr d h₁ h₂) (by decide)
  obtain hc' : Ctx L g vv m₀ s' :=
    ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr h30 => (hcs r hr h30).trans (hc.cs r hr h30),
      fun r hr => (hvs r hr).trans (hc.vs r hr), (hk' 272 (by decide) (by decide)).trans hc.lr,
      fun j hj => (hk' _ (by omega_arith) (by omega_arith)).trans (hc.args j hj), hc.frame.trans (hf.sub fun r hr => by
        rcases hws r hr with hs | hs
        · exact ⟨L.SCR, by simp, hs⟩
        · exact ⟨L.STK, by simp, fun x hx => (DLay.Ok.low_stk (L := L)) x (hs x hx)⟩)⟩
  refine ⟨hc', ⟨fun _ _ => rfl, fun j hj => ?_⟩, ?_⟩
  · have : 8 * j + 8 ≤ 272 := by unfold nW frameBytes at hj; omega_arith
    exact (hk' (8 * j) (by omega_arith) (.inl (by omega_arith))).trans (R.fr j hj)
  obtain sw : ∀ i < 12, stackArg (t.callEntry.withRegions (privRdP L) (privWr L)) i = W i := fun i hi => by
    rw [stackArg_ce, hc.sp]; exact (R.fr i (by unfold nW frameBytes; omega_arith)).trans (upd2 hi)
  obtain a0 := (sw 0 (by decide)).trans hA.p
  obtain a1 := (sw 1 (by decide)).trans (hA.args 0 (by decide))
  obtain a2 := (sw 2 (by decide)).trans (hA.args 1 (by decide))
  obtain a3 := (sw 3 (by decide)).trans (hA.args 2 (by decide))
  obtain a4 := (sw 4 (by decide)).trans (hA.args 3 (by decide))
  obtain a6 := (sw 6 (by decide)).trans (hA.args 5 (by decide))
  obtain a8 := (sw 8 (by decide)).trans (hA.args 7 (by decide))
  simp only [ourArg] at a1 a2 a3 a4 a6 a8
  have hp := hpost
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, stackArgs_fourteen,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at hp
  simp only [hr.x0, hr.x2, hr.x3, hr.x4, hr.x5, hr.x6, a0, a1, a2, a3, a4, a6, a8] at hp
  rw [hc.bytes_ro hL (ro_N L), hc.bytes_ro hL (ro_E L), hc.bytes_ro hL (ro_CT L), hc.bytes_ro hL (ro_PP L),
    hc.bytes_ro hL (ro_QQ L), hc.bytes_ro hL (ro_DP L), hc.bytes_ro hL (ro_DQ L), hc.bytes_ro hL (ro_QI L)] at hp
  exact hp

/-! ## `scratch` back to its slot -/

theorem writtenOutcome_congr {m m' : Mem} {a : Addr} {n : Nat} {r r' : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n) (hr : r' = r) (h : Spec.Rsa.writtenOutcome m a n r o) :
    Spec.Rsa.writtenOutcome m' a n r' o := by
  cases o <;> exact ⟨hr.trans h.1, hb.trans h.2⟩

theorem fixScr_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} {W : Nat → BitVec 64} (hcl : Called L g vv m₀ W t) :
    WP isa (.block fixScr) t (Called L g vv m₀ (upd W 12 L.scr)) := by
  have hc := hcl.ctx
  obtain G' := hL.geo hP
  have hn := hL.nQa
  have hal := hL.al136
  have hal' := hL.al152
  have hk := hL.k1024
  rw [show fixScr = [.addSp .x9 0] ++ mvArg 13 sScr from rfl, WP.block_append_iff]
  obtain h0 : WP isa (.block [.addSp .x9 0]) t fun t₀ => t₀ = t.write .x .x9 L.Q := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, hc.sp,
      BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine WP.mono h0 fun t₀ ht₀ => ?_
  subst ht₀
  obtain x9 : (t.write .x .x9 L.Q).gpr .x9 = L.Q := by
    simp only [RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq]
  refine WP.mono (mv_step (j := 13) (d := 96) (by decide) (by decide)
    (by rw [RegUpd.sp_write, hc.sp, RegUpd.rd_write, RegUpd.wr_write]
        exact ⟨L.ARGS, by rw [hc.rd]; simp, Offset.contains _ (by decide) (by unfold arg frameBytes; omega_using [hal])
          (by omega_using [hal'])⟩)
    (by rw [x9, RegUpd.wr_write]
        exact ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ (by decide) (by decide)⟩))
    fun u ⟨r₁, w₁, s₁, v₁, m₁, g₁⟩ => ?_
  obtain mu : u.mem = t.mem.write (off L.Q (8 * 12)) 8 L.scr := by
    rw [m₁, x9, RegUpd.mem_write, RegUpd.sp_write, hc.sp, show arg 13 = 288 + 8 * 13 from rfl, hc.args 13 (by decide),
      write8]
    rfl
  obtain gu : ∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r := fun r h9 h10 => by
    rw [g₁ r h10, RegUpd.gpr_write_of_ne _ _ _ h9]
  obtain S : Step L.Q L.scr [] t u := ⟨r₁.trans (RegUpd.rd_write ..), w₁.trans (RegUpd.wr_write ..),
    by rw [s₁, RegUpd.sp_write],
    fun r hr _ => gu r (preserved_ne hr (by decide)) (preserved_ne hr (by decide)),
    fun r _ => by rw [v₁, RegUpd.v_write], by
      rw [mu]; exact Frame.write (Frame.refl _ _) (List.mem_cons_self ..) _ (cF L.Q (by decide))⟩
  obtain R' : Rep u.mem L.Q L.scr (fun o => t.mem (off L.scr o)) (upd W 12 L.scr) := by
    rw [mu]; exact hcl.rep.wq G' (k := 12) (by decide) _
  refine ⟨hc.step hL hP S fun r h => absurd h List.not_mem_nil, ⟨fun _ _ => rfl, R'.fr⟩, ?_⟩
  refine writtenOutcome_congr (bytesAt_eq fun i hi => ?_) (by rw [gu .x0 (by decide) (by decide)]) hcl.out
  rw [BitVec.add_zero]
  exact R'.scr i (by unfold oRsa; omega_using [hk, hi])

end

/-- The slots, after `scratch` goes back to its slot over `pre`. -/
theorem slots_fix {L : DLay} {W : Nat → BitVec 64} {a b : BitVec 64} (hS : Slots L W) :
    Slots L (upd (upd (upd W 12 a) 13 b) 12 L.scr) :=
  hS.of fun j _ _ h3 => by
    simp only [upd]
    rcases h3 with rfl | h3
    · rw [ifp rfl]; exact hS.scr.symm
    · rw [ifn (by omega_using [h3]), ifn (by omega_using [h3]), ifn (by omega_using [h3])]

/-! ## The whole function -/

theorem decBodyP_eq (f : Fns) (privN : String) (privC : Prog isa) :
    decBodyP f privN privC = .seq (.block (decPrologue ++ privArgs ++ preArgs)) (.seq (.call privN privC)
      (.seq (.block fixScr) (.seq (.block (tabSlot 15)) (.seq (.block lenLoad)
        (byLen (fun d => decTail (ofLen d) f) lens))))) := rfl

/-- The postcondition, from what the body wrote with `Hs` and `Gs`, the hash
functions the tables name. -/
theorem resultP_ok {Hs Gs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s : State} {t : State}
    (hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some Hs)
    (hG : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some Gs)
    (hw : Spec.RsaOaep.writtenDecrypt t.mem (lay P s).out (lay P s).ml (lay P s).k.toNat ((t.gpr .x0).setWidth 32)
      (decOut Hs Gs (Spec.Rsa.bytesAt s.mem (lay P s).lab (lay P s).labl.toNat) (privOut (lay P s) s.mem))) :
    (decSpecP ts P).post s t := by
  sig_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
    List.append_eq]
  intro H' G' hH' hG'
  obtain rfl : Hs = H' := Option.some.inj (hH.symm.trans hH')
  obtain rfl : Gs = G' := Option.some.inj (hG.symm.trans hG')
  rw [decrypt_eq (by simp [Spec.Rsa.bytesAt])]
  exact hw

/-- `vg_rsa_oaep_decrypt_precomputed` meets its contract and the calling
convention, with both hash functions the tables of `vs`, calling `c`. -/
theorem decP_ok {vs : List MdHash} (hc : Coh vs) (c : PrivPChecked) (h16 : 16 ≤ c.stack) {s : State}
    (h : (decSpecP (tables vs) c.stack).pre s) :
    WP isa (decryptP (fnsOf vs) c.name c.code) s fun s' =>
      abiPreserved s s' ∧ (decSpecP (tables vs) c.stack).post s s' := by
  obtain hx := specP h
  have hL := hx.ok
  have hnQ := hL.nQ
  have hpQ := hL.pQ
  have hsp := hx.sp
  obtain ⟨T₁, hT₁, hheld₁⟩ := hx.tabL
  obtain ⟨T, hT, hheld⟩ := hx.tab
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨hmL, hixL, hDL⟩ := held_tableOf hheld₁
  obtain ⟨hm, hix, hD⟩ := held_tableOf hheld
  obtain okL := tabOK_of hc hx.pw hw₁
  obtain ok := tabOK_of hc hx.pw hw
  obtain hHa := hashAt_tableOf hixL
  obtain hGa := hashAt_tableOf hix
  have hP16 : 16 ≤ (layP c.stack s).P := h16
  refine WP.frameAlloc (by omega_arith) (by decide) ?_ ?_
  · show 272 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 272 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (decBodyP (fnsOf vs) c.name c.code) (entered s) _
    rw [decBodyP_eq]
    refine WP.seq ?_
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (Table.wp_sy (prologueX_ok hL hx.rd hx.wr)) fun t ⟨⟨hct, h9, hpw⟩, sy⟩ => ?_
    have sy' : t.syms = s.syms := sy
    rw [WP.block_append_iff, privArgs_eq, WP.block_append_iff]
    obtain R₀ : Rep t.mem (layP c.stack s).Q (layP c.stack s).scr (fun o => t.mem (off (layP c.stack s).scr o))
        (fun j => word t.mem (layP c.stack s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    refine WP.mono (Table.wp_sy (privW_ok hL hP16 hct h9 R₀ hpw.slots)) fun u1 ⟨⟨hc1, _, R1⟩, sy1⟩ => ?_
    obtain hS1 : Slots (layP c.stack s) (privW (layP c.stack s) fun j => word t.mem (layP c.stack s).Q (8 * j)) :=
      hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
    refine WP.mono (Table.wp_sy (privR_ok hL hP16 hc1 R1 hS1)) fun u2 ⟨⟨hc2, hm2, hr2⟩, sy2⟩ => ?_
    obtain R2 : Rep u2.mem (layP c.stack s).Q (layP c.stack s).scr (fun o => t.mem (off (layP c.stack s).scr o))
        (privW (layP c.stack s) fun j => word t.mem (layP c.stack s).Q (8 * j)) := hm2 ▸ R1
    obtain hA : CallArgs (layP c.stack s) (privW (layP c.stack s) fun j => word t.mem (layP c.stack s).Q (8 * j)) :=
      ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
        simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]; exact hpw.args j hj,
        by simp [privW, upd], by simp [privW, upd]⟩
    refine WP.mono (Table.wp_sy (preArgs_ok hL hP16 hx.pre hc2 hr2 R2)) fun u3 ⟨⟨hc3, hr3, R3⟩, sy3⟩ => ?_
    refine WP.seq (WP.mono (Table.wp_sy (privP_call c hL rfl hx.pre hc3 hr3 R3 hA)) fun u4 ⟨hcl, sy4⟩ => ?_)
    refine WP.seq (WP.mono (Table.wp_sy (fixScr_ok hL hP16 hcl)) fun u5 ⟨hcl5, sy5⟩ => ?_)
    obtain hS5 := slots_fix (a := (layP c.stack s).pre) (b := (layP c.stack s).prl) hS1
    obtain sy05 : u5.syms = s.syms := sy5.trans (sy4.trans (sy3.trans (sy2.trans (sy1.trans sy'))))
    refine WP.mono (after_ok w₁.ok.stream w.ok.stream w₁.mgf.hash w₁.mgf.len (mgf_valid w₁.mgf) w₁.mgf.mem
      w.mgf.hash w.mgf.len (mgf_valid w.mgf) hL hP16 hS5 hcl5 (sy05 ▸ okL) (sy05 ▸ hmL) hDL (sy05 ▸ ok)
      (sy05 ▸ hm) hD) fun u' ⟨hc', hw'⟩ mm uu fl => ?_
    obtain hsp' : (freed frameBytes u').sp = (layP c.stack s).Q + BitVec.ofNat 64 272 := by
      rw [freed_sp, hc'.sp]; rfl
    -- The output and its length lie apart from the stack, whose frames' bytes are lost.
    obtain hS : Region.Sub (below s.sp (272 + 16)) (layP c.stack s).STK := by
      obtain h288 := DLay.Ok.sub_stk (L := layP c.stack s) (d := 0) (n := 288) (by omega_arith)
      rw [show (layP c.stack s).Q + BitVec.ofNat 64 0 = (layP c.stack s).Q from BitVec.add_zero _] at h288
      exact h288
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩
    · show (popped .x30 (freed frameBytes u')).gpr r = s.gpr r
      by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc'.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc'.cs r hr h30
    · show (popped .x30 (freed frameBytes u')).sp = s.sp
      rw [popped_sp, hsp']
      show (layP c.stack s).Q + BitVec.ofNat 64 272 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ s _
    · exact hc'.vs r hr
    · refine resultP_ok hHa hGa (writtenDecrypt_congr (m := u'.mem)
        (List.map_congr_left fun i hi => lost_byte fl (hL.kO.symm.sub_right hS) (List.mem_range.mp hi))
        (fl.readW (r := (layP c.stack s).ML) (Region.contains_self _ _) (fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; exact hL.kM.symm.sub_right hS) (by decide)) ?_)
      show Spec.RsaOaep.writtenDecrypt u'.mem _ _ _ (((popped .x30 (freed frameBytes u')).gpr .x0).setWidth 32) _
      rw [popped_gpr_ne _ (by decide), freed_gpr]
      exact hw'

end VG.Proof.RsaOaep.AArch64.Dec

end

end

/-!
# RSAES-OAEP decryption on AArch64, given the key's precomputed values: verified

As for `vg_rsa_oaep_decrypt` (`Proof/RsaOaep/AArch64/Inst.lean`): two
calls whose public data agree, `pre`'s modulus' values among them, have the
same layout (`headP_ct`); the call of `vg_rsa_private_checked_precomputed`
leaks alike in both (`privP_ct`), `scratch` goes back to its slot
(`fixScr_ct`), and the rest is `vg_rsa_oaep_decrypt`'s (`after_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked stackArgs_fourteen)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (gpr_ce stackArg_ce leak_split bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)

/-- Ready for `vg_rsa_private_checked_precomputed`. -/
abbrev PrivReadyP : Inv := fun L g vv m₀ t =>
  Ctx L g vv m₀ t ∧ Ready L t ∧ PreX L m₀ ∧ ∃ V W, Rep t.mem L.Q L.scr V (upd (upd W 12 L.pre) 13 L.prl) ∧
    Slots L W ∧ CallArgs L W

theorem headP_ok {ts : List FnTable} {P : Nat} {s : State} (h : (decSpecP ts P).pre s) (hP : 16 ≤ P) :
    WP isa (.block (decPrologue ++ privArgs ++ preArgs)) (entered s) (PrivReadyP (layP P s) s.gpr s.v s.mem) := by
  have hx := specP h
  have hL := hx.ok
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (prologueX_ok hL hx.rd hx.wr) fun t ⟨hc, h9, hpw⟩ => ?_
  rw [WP.block_append_iff, privArgs_eq, WP.block_append_iff]
  have R₀ : Rep t.mem (layP P s).Q (layP P s).scr (fun o => t.mem (off (layP P s).scr o))
      (fun j => word t.mem (layP P s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  refine WP.mono (privW_ok hL hP hc h9 R₀ hpw.slots) fun u1 ⟨hc1, _, R1⟩ => ?_
  have hS1 : Slots (layP P s) (privW (layP P s) fun j => word t.mem (layP P s).Q (8 * j)) :=
    hpw.slots.of fun j _ _ h3 => by simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]
  refine WP.mono (privR_ok hL hP hc1 R1 hS1) fun u2 ⟨hc2, hm2, hr2⟩ => ?_
  refine WP.mono (preArgs_ok hL hP hx.pre hc2 hr2 (hm2 ▸ R1)) fun u3 ⟨hc3, hr3, R3⟩ => ?_
  exact ⟨hc3, hr3, hx.pre, _, _, R3, hS1, ⟨by simp only [privW, upd]; exact hpw.p, fun j hj => by
      simp only [privW, upd]; rw [ifn (by omega_arith), ifn (by omega_arith)]; exact hpw.args j hj,
      by simp [privW, upd], by simp [privW, upd]⟩⟩

/-- Two calls whose public data agree, in the inner frame. -/
def EnteredP (ts : List FnTable) (S : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (decSpecP ts (S + 1)).pre s₁ ∧ (decSpecP ts (S + 1)).pre s₂ ∧ (decSpecP ts (S + 1)).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

theorem headP_ct (ts : List FnTable) {S : Nat} (hS : 15 ≤ S) :
    RelCT isa (EnteredP ts S) (.block (decPrologue ++ privArgs ++ preArgs)) (Two S ts PrivReadyP) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  have x₁ := specP h₁
  have x₂ := specP h₂
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp (S + 1), entered_sp (S + 1)]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, y₁, z₁⟩ := headP_ok h₁ (by omega_arith)
  obtain ⟨_, u₂, y₂, z₂⟩ := headP_ok h₂ (by omega_arith)
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  have e : layP (S + 1) s₂ = layP (S + 1) s₁ := by
    simp only [lay, dxP, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16, a17, a18, hsp]
  obtain ⟨hl₁, hl₂⟩ := List.append_inj hl (by simp only [List.length_map, List.length_append, bytesAt_length, h4, h6])
  obtain ⟨hn, he⟩ := leak_split hl₁ (by rw [bytesAt_length, bytesAt_length, h4])
  have hsy' : ∀ f ∈ Proof.HashTable.AArch64.tabFns ts, s₁.syms f = s₂.syms f :=
    fun f hf => hsy f (List.mem_append_left _ hf)
  have htaL : Proof.HashTable.AArch64.TabAgree ts (layP (S + 1) s₁).tabL s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨x₁.tabL, x₁.pw⟩, ⟨by rw [show (layP (S + 1) s₁).tabL = stackArg s₂ 15 from a15]; exact x₂.tabL, x₂.pw⟩, hsy',
      fun T hT => htabL _ _ rfl a15.symm T hT⟩
  have hta : Proof.HashTable.AArch64.TabAgree ts (layP (S + 1) s₁).tab s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨x₁.tab, x₁.pw⟩, ⟨by rw [show (layP (S + 1) s₁).tab = stackArg s₂ 16 from a16]; exact x₂.tab, x₂.pw⟩, hsy',
      fun T hT => htab _ _ rfl a16.symm T hT⟩
  refine ⟨ht, ⟨layP (S + 1) s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, x₁.ok, rfl,
    ⟨⟨?_, ?_, ?_⟩, htaL.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl),
      hta.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl)⟩, z₁, e ▸ z₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat
    rw [hn, h3, h4]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x5) (s₁.gpr .x6).toNat
    rw [he, h5, h6]
  · show Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 17) (s₁.gpr .x4).toNat =
      Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₁ 17) (s₁.gpr .x4).toNat
    rw [hl₂, a17, h4]

/-! ## The call -/

theorem privP_args_eq {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {a : State}
    (ha : PrivReadyP L g vv m₀ a) (rd wr : List Region) :
    ∀ i < 14, stackArg (a.callEntry.withRegions rd wr) i =
      [L.p, L.pl, L.q, L.ql, L.dp, L.dpl, L.dq, L.dql, L.qi, L.qil, L.scr + BitVec.ofNat 64 8192,
        L.sl - BitVec.ofNat 64 1024, L.pre, L.prl].getD i 0 := by
  obtain ⟨hc, -, -, V, W, R, -, hA⟩ := ha
  intro i hi
  rw [stackArg_ce, hc.sp, show a.mem.readW (L.Q + BitVec.ofNat 64 (8 * i)) 64 = upd (upd W 12 L.pre) 13 L.prl i from
    R.fr i (by unfold nW frameBytes; omega_arith)]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  exacts [(upd2 (by decide)).trans hA.p, (upd2 (by decide)).trans (hA.args 0 (by decide)),
    (upd2 (by decide)).trans (hA.args 1 (by decide)), (upd2 (by decide)).trans (hA.args 2 (by decide)),
    (upd2 (by decide)).trans (hA.args 3 (by decide)), (upd2 (by decide)).trans (hA.args 4 (by decide)),
    (upd2 (by decide)).trans (hA.args 5 (by decide)), (upd2 (by decide)).trans (hA.args 6 (by decide)),
    (upd2 (by decide)).trans (hA.args 7 (by decide)), (upd2 (by decide)).trans (hA.args 8 (by decide)),
    (upd2 (by decide)).trans hA.s10, (upd2 (by decide)).trans hA.s11, by simp [upd], by simp [upd],
    absurd hi (by omega_arith)]

theorem privP_pub' {L : DLay} {S : Nat} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}
    (hL : L.Ok) (hk : LeakEq L m₁ m₂) {a b : State} (ha : PrivReadyP L g₁ v₁ m₁ a) (hb : PrivReadyP L g₂ v₂ m₂ b) :
    (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)).pub
      (a.callEntry.withRegions (privRdP L) (privWr L))
      ((b.callEntry.withRegions (privRdP L) (privWr L)).withDit (a.callEntry.withRegions (privRdP L) (privWr L)).dit) := by
  have aa := privP_args_eq ha (privRdP L) (privWr L)
  have ab := privP_args_eq hb (privRdP L) (privWr L)
  have hx := ha.2.2.1
  have hle : Spec.Rsa.precomputedWords L.k.toNat ≤ L.prl.toNat := by
    rw [hx.prlv]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs, stackArgs_fourteen, List.append_eq,
    _root_.List.range, _root_.List.range.loop]
  simp only [stackArg_withDit]
  have e : ∀ i < 14, stackArg (a.callEntry.withRegions (privRdP L) (privWr L)) i =
      stackArg (b.callEntry.withRegions (privRdP L) (privWr L)) i := fun i hi => (aa i hi).trans (ab i hi).symm
  refine ⟨by rw [ha.1.sp, hb.1.sp], ?_, by rw [ha.2.1.x0, hb.2.1.x0], by rw [ha.2.1.x1, hb.2.1.x1],
    by rw [ha.2.1.x2, hb.2.1.x2], by rw [ha.2.1.x3, hb.2.1.x3], by rw [ha.2.1.x4, hb.2.1.x4],
    by rw [ha.2.1.x5, hb.2.1.x5], by rw [ha.2.1.x6, hb.2.1.x6], by rw [ha.2.1.x7, hb.2.1.x7],
    e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide),
    e 12 (by decide), e 13 (by decide)⟩
  have hl := hk.2.2
  rw [hx.lk] at hl
  simp only [Spec.Rsa.privatePrecomputedLeak] at hl ⊢
  rw [ha.2.1.x2, ha.2.1.x3, ha.2.1.x4, ha.2.1.x5, hb.2.1.x2, hb.2.1.x3, hb.2.1.x4, hb.2.1.x5,
    aa 12 (by decide), ab 12 (by decide)]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [ha.1.bytes_ro hL (ro_N L), hb.1.bytes_ro hL (ro_N L), ha.1.bytes_ro hL (ro_E L), hb.1.bytes_ro hL (ro_E L),
    hk.1, hk.2.1, hx.words hL ha.1 hle, hb.2.2.1.words hL hb.1 hle, hl]

/-- After the call: the frame's words with `pre` and `pre_len` in words 12
and 13. -/
abbrev CalledP : Inv := fun L g vv m₀ t => ∃ W, Called L g vv m₀ (upd (upd W 12 L.pre) 13 L.prl) t ∧ Slots L W

theorem privP_ct (c : PrivPChecked) {S : Nat} (hS : c.stack = S + 1) (ts : List FnTable) :
    RelCT isa (Two S ts PrivReadyP) (.call c.name c.code) (Two S ts CalledP) := by
  have hv : Verified AArch64.target c.code (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi (S + 1)) :=
    hS ▸ c.verified
  exact two_wp (fun e => RelCT.callDit (n := c.name) hv.1 hv.2.1 c.noDit (fun _ _ h => h) (privRdP e.L) (privWr e.L)
    fun _ _ ⟨hL, hP, hk, f₁, f₂⟩ => by
      obtain ⟨c₁, r₁, x₁, V₁, W₁, R₁, s₁, A₁⟩ := f₁
      obtain ⟨c₂, r₂, x₂, V₂, W₂, R₂, s₂, A₂⟩ := f₂
      exact ⟨privP_pre hL hP x₁ c₁ r₁ R₁ A₁, privP_pre hL hP x₂ c₂ r₂ R₂ A₂,
        privP_pub' hL hk.1 ⟨c₁, r₁, x₁, V₁, W₁, R₁, s₁, A₁⟩ ⟨c₂, r₂, x₂, V₂, W₂, R₂, s₂, A₂⟩,
        (covers_privP hL x₁ c₁).1, (covers_privP hL x₁ c₁).2, (covers_privP hL x₂ c₂).1,
        (covers_privP hL x₂ c₂).2⟩)
    fun _ _ _ _ _ hL hP ⟨hc, hr, hx, V, W, R, hSl, hA⟩ =>
      WP.mono (privP_call c hL (hP.trans hS.symm) hx hc hr R hA) fun _ h => ⟨W, h, hSl⟩

/-! ## `scratch` back to its slot -/

theorem fixScr_ct {S : Nat} (hS : 15 ≤ S) (ts : List FnTable) :
    RelCT isa (Two S ts CalledP) (.block fixScr) (Two S ts CalledI) :=
  two [] (by taint_decide)
    (fun _ _ _ _ _ _ _ _ _ _ ⟨_, f₁, _⟩ ⟨_, f₂, _⟩ =>
      ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ _ hL hP ⟨_, hcl, hSl⟩ => WP.mono (fixScr_ok hL (by omega_using [hS, hP]) hcl) fun _ h => ⟨_, h, slots_fix hSl⟩

/-! ## The whole function -/

theorem pubP_sp {ts : List FnTable} {P : Nat} {s₁ s₂ : State} (h : (decSpecP ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
      Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
      Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
      List.append_eq] at h
  exact h.1

variable {vs : List MdHash} (hc : Coh vs)

include hc in
theorem decP_ct (c : PrivPChecked) {S : Nat} (hS : c.stack = S + 1) (h15 : 15 ≤ S) :
    ConstantTime isa (decSpecP (tables vs) (S + 1)).pre (decSpecP (tables vs) (S + 1)).pub
      (decryptP (fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pubP_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [decBodyP_eq]
  refine ((headP_ct (tables vs) h15).seq ((privP_ct c hS (tables vs)).seq ((fixScr_ct h15 (tables vs)).seq
    (after_ct hc h15)))).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

include hc in
/-- `vg_rsa_oaep_decrypt_precomputed`, calling `c`, for the tables of `vs`. -/
theorem decP_verified (c : PrivPChecked) (h16 : 16 ≤ c.stack)
    (hsat : ∃ s, (decSpecP (tables vs) c.stack).pre s) :
    Verified AArch64.target (decryptP (fnsOf vs) c.name c.code) (decSpecP (tables vs) c.stack) := by
  obtain ⟨S, hS⟩ : ∃ S, c.stack = S + 1 := ⟨c.stack - 1, by omega_using [h16]⟩
  have hct := decP_ct hc c hS (by omega)
  rw [← hS] at hct
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := decP_ok hc c h16 h
    exact ⟨t, s', he, hp⟩) hct (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Dec

end

end

/-!
# RSAES-OAEP on AArch64: the instances emitted

States meeting both contracts, with both tables at `0x300000`
(`withTable`), and the instances' proofs against the contracts the
registrations state (`dec_ok`, `enc_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK MgfLink MdHash mdHashes)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.HashTable.AArch64 (tables fnsOf names Coh tableOf)
open VG.Proof.HashTable (symsOf_distinct2)
open VG.Proof.MdHashTable.AArch64 (withTable withTable_below withTable_held held_twL)
open VG.Proof.HashTable.AArch64 (held_tableOf hashAt_tableOf)

theorem withTable_addr (s : State) (vs : List MdHash) (w : MdHash) (j : Nat) :
    stackArgAddr (withTable s vs w) j = stackArgAddr s j := rfl

theorem withTable_arg (s : State) (vs : List MdHash) (w : MdHash) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTable s vs w) j = stackArg s j :=
  withTable_below s vs w hj

/-! ## Decryption -/

/-- A state meeting decryption's contract but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `0x10000`, and both
tables' address `0x300000`. -/
def decSatBase : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10070 then 0x20
    else bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x43
    else bif Nat.beq a.toNat 0x10010 then 1 else bif Nat.beq a.toNat 0x10019 then 0x44
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x45
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x46
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x47
    else bif Nat.beq a.toNat 0x10059 then 0x41 else bif Nat.beq a.toNat 0x10060 then 64
    else bif Nat.beq a.toNat 0x1006A then 0x02 else bif Nat.beq a.toNat 0x10071 then 0x08
    else bif Nat.beq a.toNat 0x1007A then 0x30 else bif Nat.beq a.toNat 0x10082 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Dec.decSpec (tables vs) ((RsaPkcs1Enc.AArch64.privOf c).S + 1)).pre s := by
  refine ⟨withTable decSatBase vs w, ?_⟩
  have hA : ∀ j < 17, (stackArgAddr decSatBase j).toNat + 8 ≤ 0x300000 := by decide
  have hS : (RsaPkcs1Enc.AArch64.privOf c).S + 1 = 3248 := by
    rw [← Nat.add_right_cancel_iff (n := 288), ← Dec.decStack_eq]; rfl
  rw [hS]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [withTable_arg _ vs w (hA 0 (by decide)), withTable_arg _ vs w (hA 1 (by decide)),
    withTable_arg _ vs w (hA 2 (by decide)), withTable_arg _ vs w (hA 3 (by decide)),
    withTable_arg _ vs w (hA 4 (by decide)), withTable_arg _ vs w (hA 5 (by decide)),
    withTable_arg _ vs w (hA 6 (by decide)), withTable_arg _ vs w (hA 7 (by decide)),
    withTable_arg _ vs w (hA 8 (by decide)), withTable_arg _ vs w (hA 9 (by decide)),
    withTable_arg _ vs w (hA 10 (by decide)), withTable_arg _ vs w (hA 11 (by decide)),
    withTable_arg _ vs w (hA 12 (by decide)), withTable_arg _ vs w (hA 13 (by decide)),
    withTable_arg _ vs w (hA 14 (by decide)), withTable_arg _ vs w (hA 15 (by decide)),
    withTable_arg _ vs w (hA 16 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  sig_and_intros
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 15 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
    | exact ⟨tableOf w, List.mem_map_of_mem hw, by
        rw [show stackArg decSatBase 16 = 0x300000 by decide]; exact held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact symsOf_distinct2 hl
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (intro a h₁ h₂
       set_option linter.unusedSimpArgs false in
       sig_simp_only [Region.Contains, decSatBase, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

/-! ## Decryption with the key's precomputed values -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.HashTable (putWs add8_toNat)

/-- The stack arguments of `decPSatBase`: the key (`keyMem`'s), an empty
label, a 64-byte ciphertext, a working space of 2080 words, both tables at
`0x300000`, and `pre` at `0x4800`. -/
def decPArgs : List Nat :=
  [32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64, 0x20000, 2080, 0x300000, 0x300000,
    0x4800, 24]

/-- The memory of `decPSatBase`: the stack arguments from `0x10000`, and the
key. -/
def decPMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10098 then
    BitVec.ofNat 8 (decPArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the precomputed decryption's precondition but for the
tables: the key `keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit
primes at `0x4200` and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def decPSatBase : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem := decPMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem decPSat_args : ∀ j < 19, stackArg decPSatBase j = BitVec.ofNat 64 (decPArgs.getD j 0) := by decide

/-- Below the words `putWs` writes, a byte as before. -/
theorem putWs_byte {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)}, a.toNat < p.toNat →
    p.toNat + 8 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    simp only [putWs]
    rw [putWs_byte (by rw [h8]; omega_using [h]) (by rw [h8]; omega_using [hp])]
    have hne : ¬ (a - p).toNat < 64 / 8 := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [hp]
    simp only [Mem.writeW, Mem.write, hne, ↓reduceIte]

theorem decPSat_key (vs : List MdHash) (w : MdHash) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable decPSatBase vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable decPSatBase vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable decPSatBase vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTable decPSatBase vs w).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    have h2 : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10098) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    show putWs decPMem 0x300000 (MdHashTable.AArch64.twL vs w) a = keyMem a
    rw [putWs_byte (by show a.toNat < 0x300000; omega_using [hk]) (MdHashTable.AArch64.twL_room vs w)]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

theorem decP_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Dec.decSpecP (tables vs) (RsaPkcs1Sig.AArch64.privPOf c).stack).pre s := by
  refine ⟨withTable decPSatBase vs w, ?_⟩
  have hA : ∀ j < 19, (stackArgAddr decPSatBase j).toNat + 8 ≤ 0x300000 := by decide
  have hb : ∀ j < 19, stackArg (withTable decPSatBase vs w) j = BitVec.ofNat 64 (decPArgs.getD j 0) :=
    fun j hj => (withTable_arg _ vs w (hA j hj)).trans (decPSat_args j hj)
  rw [show (RsaPkcs1Sig.AArch64.privPOf c).stack = 3248 from rfl]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
    List.append_eq]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide), hb 9 (by decide), hb 10 (by decide),
    hb 11 (by decide), hb 12 (by decide), hb 13 (by decide), hb 14 (by decide), hb 15 (by decide),
    hb 16 (by decide), hb 17 (by decide), hb 18 (by decide), decPArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop,
    List.append_eq]
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact decPSat_key vs w)
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact symsOf_distinct2 hl
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## Encryption with a precomputed key -/

/-- A state meeting encryption's contract for `H` but for the tables: a
512-bit modulus, a one-byte `e`, an empty label and message, `H`'s seed, a
working space of 2080 words, 16 words of `pre` at `0x5000`, the stack
arguments at `0x10000`, and both tables' address `0x300000`. -/
def encSatBase (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10028 then 0x20
    else bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10011 then 0x42
    else bif Nat.beq a.toNat 0x10018 then BitVec.ofNat 8 H.len
    else bif Nat.beq a.toNat 0x10022 then 0x02 else bif Nat.beq a.toNat 0x10029 then 0x08
    else bif Nat.beq a.toNat 0x10031 then 0x50 else bif Nat.beq a.toNat 0x10038 then 16
    else bif Nat.beq a.toNat 0x10042 then 0x30 else bif Nat.beq a.toNat 0x1004A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, H.len⟩, ⟨0x5000, 128⟩,
    ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

theorem enc_sat {vs : List MdHash} {w : MdHash} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 32)
    (v : Proof.Rsa.AArch64.PublicImpl) :
    ∃ s, (Enc.encSpec (tables vs) (Enc.encP (RsaPkcs1Sig.AArch64.pdOf v))).pre s := by
  have hha : ∀ s : State, Spec.MdHashTable.hashAt 64 (withTable s vs w).mem 0x300000 = some w.mgf.G := fun s =>
    hashAt_tableOf (held_tableOf (withTable_held s vs w)).2.1
  have hH := w.mgf.mem
  generalize w.mgf.G = H at hha hH
  refine ⟨withTable (encSatBase H) vs w, ?_⟩
  have hB : ∀ j < 10, ((0x10000 : Addr) + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ 0x300000 := by decide
  have hA : ∀ (G : Spec.Mgf1.Hash), ∀ j < 10, (stackArgAddr (encSatBase G) j).toNat + 8 ≤ 0x300000 :=
    fun _ j hj => hB j hj
  have hha' := hha (encSatBase H)
  have hP : Enc.encP (RsaPkcs1Sig.AArch64.pdOf v) = 16 := rfl
  rw [hP]
  have args := (show ∀ H ∈ mdHashes,
      stackArg (encSatBase H) 0 = 0x4100 ∧ stackArg (encSatBase H) 1 = 0 ∧ stackArg (encSatBase H) 2 = 0x4200 ∧
      stackArg (encSatBase H) 3 = BitVec.ofNat 64 H.len ∧ stackArg (encSatBase H) 4 = 0x20000 ∧
      stackArg (encSatBase H) 5 = 2080 ∧ stackArg (encSatBase H) 6 = 0x5000 ∧ stackArg (encSatBase H) 7 = 16 ∧
      stackArg (encSatBase H) 8 = 0x300000 ∧ stackArg (encSatBase H) 9 = 0x300000 by decide) H hH
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [withTable_arg _ vs w (hA _ 0 (by decide)), withTable_arg _ vs w (hA _ 1 (by decide)),
    withTable_arg _ vs w (hA _ 2 (by decide)), withTable_arg _ vs w (hA _ 3 (by decide)),
    withTable_arg _ vs w (hA _ 4 (by decide)), withTable_arg _ vs w (hA _ 5 (by decide)),
    withTable_arg _ vs w (hA _ 6 (by decide)), withTable_arg _ vs w (hA _ 7 (by decide)),
    withTable_arg _ vs w (hA _ 8 (by decide)), withTable_arg _ vs w (hA _ 9 (by decide))]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', withTable_addr, args]
  sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq]
  sig_and_intros
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | exact rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact symsOf_distinct2 hl
    | (simp only [Spec.Rsa.lenValid]; decide)
    -- What mentions the seed's length, for each hash.
    | (simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
       rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
         | exact rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)
         | (intro H' hH'
            obtain rfl := Option.some.inj (hha'.symm.trans hH')
            decide))

/-! ## The instances -/

/-- What the registrations check of the variants whose tables a function
takes. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ []

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List MdHash} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs` and the private-key
operation of `c`. -/
theorem dec_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.decrypt (fnsOf vs) (RsaPkcs1Enc.AArch64.privOf c).name
        (RsaPkcs1Enc.AArch64.privOf c).code)
      (Spec.RsaOaep.decryptMdTablesContract
        (AArch64.abi.withTables Spec.RsaOaep.decryptMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        (Dec.decStack (RsaPkcs1Enc.AArch64.privOf c))) := by
  rw [Dec.decStack_eq]
  exact Dec.dec_verified h.1 _ (let ⟨_, hw⟩ := h.mem; dec_sat hw h.2.1 c)

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs`, calling
`vg_rsa_private_checked_precomputed` of the implementation `c`. -/
theorem decP_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.decryptP (fnsOf vs) (RsaPkcs1Sig.AArch64.privPOf c).name
        (RsaPkcs1Sig.AArch64.privPOf c).code)
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (AArch64.abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        ((RsaPkcs1Sig.AArch64.privPOf c).stack + 288)) :=
  Dec.decP_verified h.1 _ (by show 16 ≤ Proof.Rsa.AArch64.stackBytes; decide)
    (let ⟨_, hw⟩ := h.mem; decP_sat hw h.2.1 c)

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs` and the
precomputed public operation of `c`. -/
theorem enc_ok (vs : List MdHash) (h : OK vs) (c : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf vs)
        (RsaPkcs1Sig.AArch64.pdOf c).name (RsaPkcs1Sig.AArch64.pdOf c).code)
      (Spec.RsaOaep.encryptMdTablesContract
        (AArch64.abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        (Enc.encStack (RsaPkcs1Sig.AArch64.pdOf c))) :=
  Enc.enc_verified h.1 _ (let ⟨_, hw⟩ := h.mem; enc_sat hw h.2.1 c)

end VG.Proof.RsaOaep.AArch64
