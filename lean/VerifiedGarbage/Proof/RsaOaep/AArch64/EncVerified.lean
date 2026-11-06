module

import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfTCT
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.HashTable.AArch64

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
    (hHa : Spec.HashTable.hashAt 64 s.mem (stackArg s 8) = some H) :
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
theorem held_words {m₁ m₂ : Mem} {p : Addr} {a b : State} {T : FnTable} (h5 : T.fns.length + T.data.length = 5)
    (h₁ : Abi.tableHeld 64 m₁ p (T.words isa a)) (h₂ : Abi.tableHeld 64 m₂ p (T.words isa b))
    (hw : T.words isa a = T.words isa b) : Spec.Rsa.wordsAt m₁ p 5 = Spec.Rsa.wordsAt m₂ p 5 := by
  have hl : (T.words isa b).length = 5 := by simp [FnTable.words, h5]
  rw [hw] at h₁
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 5 := List.mem_range.mp hi
  have e₁ := h₁ i (by omega)
  have e₂ := h₂ i (by omega)
  simp only [Nat.reduceDiv] at e₁ e₂
  rw [e₁, e₂]

/-- The tables of `vs` have five words. -/
theorem tables_five (vs : List MdHash) : ∀ T ∈ tables vs, T.fns.length + T.data.length = 5 := by
  intro T hT
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hT
  rfl

/-- A table both runs hold, with its functions at the same addresses: the
same words. -/
theorem held_words_of {ts : List FnTable} (h5 : ∀ T ∈ ts, T.fns.length + T.data.length = 5) {m₁ m₂ : Mem}
    {p : Addr} {a b : State} (hsy : ∀ f ∈ tabFns ts, a.syms f = b.syms f) {T : FnTable} (hT : T ∈ ts)
    (h₁ : Abi.tableHeld 64 m₁ p (T.words isa a)) (h₂ : Abi.tableHeld 64 m₂ p (T.words isa b)) :
    Spec.Rsa.wordsAt m₁ p 5 = Spec.Rsa.wordsAt m₂ p 5 :=
  held_words (h5 T hT) h₁ h₂ (by
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
  sig_pub [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
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
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 8) (5 * (64 / 8) / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 8) (5 * (64 / 8) / 8)
      exact held_words_of (tables_five vs) hsy' hTw hh₁ (by rw [a8]; exact hh₂)
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 9) (5 * (64 / 8) / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 9) (5 * (64 / 8) / 8)
      obtain ⟨T, hT, hh⟩ := hT₁
      exact held_words_of (tables_five vs) hsy' hT hh ((htab _ _ rfl a9.symm T hT).mp hh)

theorem pub_sp {ts : List FnTable} {P : Nat} {s₁ s₂ : State}
    (h : (encSpec ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
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
      show RelCT isa _ (.block ([.ldrSp .x16 sTab] ++ [.ldr .x .x16 .x16 32])) _
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
