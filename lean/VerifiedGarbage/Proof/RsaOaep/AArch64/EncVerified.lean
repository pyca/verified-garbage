module

import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Impl.RsaOaep.AArch64.Precomputed
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCTBase
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCall
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEntry
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.HashTable.AArch64

/-!
# RSAES-OAEP encryption on AArch64: verified

The prologue and the check of `k` (`head_ct`), from two entry states whose
public data agree; the failure (`encFail_tr`); the check of the message's
length; and `encMain_tr`, put together (`enc_ct`): the two branches are on
`k` and the message's length, which are public. With correctness
(`enc_ok`), `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, for any
implementation of the hash functions and `c` of a precomputed public
operation, is verified against the shared contract with the stack it and its
callee use (`enc_verified`), given that the contract is satisfiable for it
(which the registration file checks).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.RsaPkcs1Enc.AArch64.Enc (leak_split bytesAt_length)
open VG.Proof.RsaOaep.AArch64.Dec (entered)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf Coh tabOK_of held_tableOf mem_names TabAgree tabFns words_congr)

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

/-! ## The prologue and the check of `k` -/

theorem head_ok {Hs : Spec.Mgf1.Hash} {ts : List FnTable} {H : Hash} (hD : H.D ≤ 64) {P : Nat} {s : State}
    (h : (encSpec Hs ts P).pre s) (hP : 16 ≤ P) :
    WP isa (.block (encPrologue ++ chkK H)) (entered s)
      (In (lay Hs.len P s) s.gpr s.v s.mem (KX H.D (lay Hs.len P s).k.toNat)) := by
  have hL := lay_ok h
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok h) fun t ⟨hc, _, hS⟩ => ?_
  have R : Rep t.mem (lay Hs.len P s).Q (lay Hs.len P s).scr (fun o => t.mem (off (lay Hs.len P s).scr o))
      (fun j => word t.mem (lay Hs.len P s).Q (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hk3 : (fun j => word t.mem (lay Hs.len P s).Q (8 * j)) 21 = BitVec.ofNat 64 (lay Hs.len P s).k.toNat :=
    hS.k.trans (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  exact WP.mono (chkK_ok (H := H) (hc.lay hL hP R hS.scr) R hk3 hL.k1024 (by omega_arith))
    fun _ ⟨_, S1, hm1, x11⟩ => In.of_step hL hP hc S1 nil_ws (by rw [hm1]; exact R) hS x11

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (Hs : Spec.Mgf1.Hash) (ts : List FnTable) (P : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (encSpec Hs ts P).pre s₁ ∧ (encSpec Hs ts P).pre s₂ ∧ (encSpec Hs ts P).pub s₁ s₂ ∧
    a = entered s₁ ∧ b = entered s₂

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

theorem head_ct (Hs : Spec.Mgf1.Hash) {ts : List FnTable} (h5 : ∀ T ∈ ts, T.fns.length + T.data.length = 5) {H : Hash}
    (hD : H.D ≤ 64) {P : Nat} (hP : 16 ≤ P) :
    RelCT isa (Entered Hs ts P) (.block (encPrologue ++ chkK H))
      fun a b => ∃ e : Env, e.L.D = Hs.len ∧ PreOk e.L e.m₁ ∧ PreOk e.L e.m₂ ∧
        TabAgree ts (tabW e.L e.m₁) e.m₁ e.m₂ a b ∧ PW P e (KX H.D e.L.k.toNat) a b := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨hT₁, hd₁⟩ := spec_tab h₁
  obtain ⟨hT₂, hd₂⟩ := spec_tab h₂
  sig_pub [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htab, hl, h0, h1, h2, h3, h4, h5', h6, h7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩)
    (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (encPrologue ++ chkK gH)) (by rfl) (by taint_decide))
    _ _ _ _ _ _ (by
      show (entered s₁).sp = (entered s₂).sp
      rw [entered_sp Hs.len P, entered_sp Hs.len P]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := head_ok hD h₁ hP
  obtain ⟨_, u₂, x₂, y₂⟩ := head_ok hD h₂ hP
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay Hs.len P s₂ = lay Hs.len P s₁ := by
    simp only [lay, preX, h0, h1, h2, h3, h4, h5', h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, hsp]
  obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, h3, h5'])
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
  obtain ⟨hn, he⟩ := leak_split hb (by rw [bytesAt_length, bytesAt_length, h3])
  have tw : tabW (lay Hs.len P s₁) s₁.mem = stackArg s₁ 7 := tabW_lay _ _ _
  have hta : TabAgree ts (stackArg s₁ 7) s₁.mem s₂.mem s₁ s₂ :=
    ⟨⟨hT₁, hd₁⟩, ⟨by rw [a7]; exact hT₂, hd₂⟩, hsy, fun T hT => htab _ _ rfl a7.symm T hT⟩
  refine ⟨ht, ⟨lay Hs.len P s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, rfl, preOk_lay h₁,
    e ▸ preOk_lay h₂, by rw [tw]; exact hta.congr (by rw [Exec.syms e₁]; rfl) (by rw [Exec.syms e₂]; rfl),
    lay_ok h₁, rfl, ⟨?_, ?_, ?_⟩, y₁, e ▸ y₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    rw [hn, h2, h3]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    rw [he, h4, h5']
  · intro R hR
    simp only [lay, preX, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 5) ((stackArg s₁ 6).toNat * 8 / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 5) ((stackArg s₁ 6).toNat * 8 / 8)
      rw [Nat.mul_div_cancel _ (by decide : 0 < 8), hw, a5, a6]
    · show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 7) (5 * (64 / 8) / 8) =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 7) (5 * (64 / 8) / 8)
      obtain ⟨T, hT, hh⟩ := hT₁
      have hh₂ := (htab _ _ rfl a7.symm T hT).mp hh
      exact held_words (h5 T hT) hh hh₂ (by
        simp only [FnTable.words]
        congr 1
        exact List.map_congr_left fun n hn =>
          hsy n (List.mem_flatten.mpr ⟨_, List.mem_map_of_mem hT, hn⟩))

theorem pub_sp {Hs : Spec.Mgf1.Hash} {ts : List FnTable} {P : Nat} {s₁ s₂ : State}
    (h : (encSpec Hs ts P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

/-- `In` with `X`, as `In` with nothing more. -/
theorem In.forget {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {X : (Nat → BitVec 64) → State → Prop} {t : State} (h : In L g vv m₀ X t) : In L g vv m₀ (fun _ _ => True) t :=
  ⟨h.1, h.2.choose, h.2.choose_spec.choose, h.2.choose_spec.choose_spec.1, h.2.choose_spec.choose_spec.2.1, trivial⟩

variable {Hl : Hash} (hH : StreamOK Hl.stream)

/-- The tables of `vs` have five words. -/
theorem tables_five (vs : List MdHash) : ∀ T ∈ tables vs, T.fns.length + T.data.length = 5 := by
  intro T hT
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hT
  rfl

include hH in
theorem enc_ct {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    {vs : List MdHash} (hc : Coh vs) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) :
    ConstantTime isa (encSpec Hs (tables vs) P).pre (encSpec Hs (tables vs) P).pub
      (Impl.RsaOaep.AArch64.Precomputed.encrypt Hl (fnsOf vs) c.name c.code) := by
  obtain ⟨-, hzF, -, hzDF, -⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [encBody_eq]
  refine ((head_ct Hs (tables_five vs) hD64 hP16).seq (Q := fun _ _ => True) ?_).mono ?_ fun _ _ _ => trivial
  · refine RelCT.ite (fun a b ⟨e, _, _, _, _, _, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, _, _, _, _, hL, hP', hp⟩, _⟩ e₁ e₂
      exact encFail_tr hL (hP' ▸ hP16) _ _ _ _ _ _ ⟨hL, hP', hp⟩ e₁ e₂
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hDe, q₁, q₂, ta, hL, hP', hk, f₁, f₂⟩, hb⟩ e₁ e₂
    have hP16' : 16 ≤ e.L.P := hP' ▸ hP16
    have hkD : 2 * Hl.D + 2 ≤ e.L.k.toNat := by
      by_contra hc
      rw [eval_nonzero, f₁.2.choose_spec.choose_spec.2.2, ifn (by omega_arith)] at hb
      exact absurd hb (by decide)
    -- MGF1's table, in each run.
    obtain ⟨⟨⟨T, hT, hh₁⟩, hd₁⟩, ⟨-, hd₂⟩, hsy, hiff⟩ := ta
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
    have tw : tabW e.L e.m₁ = tabW e.L e.m₂ := (pre_eq q₁ q₂).2.2
    obtain ⟨hm₁, -, hD₁⟩ := held_tableOf hh₁
    obtain ⟨hm₂, -, hD₂⟩ := held_tableOf ((hiff _ hT).mp hh₁)
    have hn := mem_names hw
    let TX : (Nat → BitVec 64) → State → Prop := fun _ t => Table.TabX w.H.stream (fnsOf vs) (arg 7) e.L.Q e.L.scr
      (tabW e.L e.m₁) (s₁.syms w.H.initN) (s₁.syms w.H.updN) (s₁.syms w.H.finN) t
    have tx₁ : TX (fun _ => 0) s₁ := ⟨tab_of hL hP16' f₁.1 q₁ (tabOK_of hc hd₁ hw) hm₁ hD₁, rfl, rfl, rfl⟩
    have tx₂ : TX (fun _ => 0) s₂ := ⟨by rw [tw]; exact tab_of hL hP16' f₂.1 q₂ (tabOK_of hc hd₂ hw) (tw ▸ hm₂) (tw ▸ hD₂),
      (hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm⟩
    have In.tx : ∀ {g vv m₀} {t : State} {X : (Nat → BitVec 64) → State → Prop}, In e.L g vv m₀ X t → TX (fun _ => 0) t →
        In e.L g vv m₀ TX t := fun h x =>
      ⟨h.1, h.2.choose, h.2.choose_spec.choose, h.2.choose_spec.choose_spec.1, h.2.choose_spec.choose_spec.2.1, x⟩
    refine (RelCT.seq (Q := fun _ _ => True) (pw_blk (X' := fun W t => MX Hl.D e.L.k.toNat e.L.ml.toNat W t ∧ TX W t) []
      (check_of_zImm (τ := Taint.ofRegs []) (c' := .block (chkMsg gH)) (by rfl) (by taint_decide)) nopin
      fun _ _ _ _ _ _ _ _ hc R hS hx => WP.mono (Table.wp_sy (chkMsg_ok (H := Hl) (hc.lay hL hP16' R hS.scr) R
        (by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq])
        hL.k1024 e.L.ml.isLt hkD))
        fun _ ⟨⟨_, Su, hm, x11⟩, sy⟩ => In.of_step hL hP16' hc Su nil_ws (by rw [hm]; exact R) hS
          ⟨x11, Table.TabX.step hx Su sy⟩) ?_) _ _ _ _ _ _
      ⟨hL, hP', hk, In.tx f₁ tx₁, In.tx f₂ tx₂⟩ e₁ e₂
    refine RelCT.ite (fun a b ⟨_, _, _, ⟨_, _, _, _, _, xa, _⟩, ⟨_, _, _, _, _, xb, _⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · exact (encFail_tr hL hP16').mono (fun _ _ h => h.1) fun _ _ h => h
    · intro a₁ a₂ u₁ u₂ a₁' a₂' ⟨⟨_, _, _, g₁, g₂⟩, hb'⟩ e₁ e₂
      have hmk : e.L.ml.toNat ≤ e.L.k.toNat - (2 * Hl.D + 2) := by
        by_contra hc
        rw [eval_nonzero, g₁.2.choose_spec.choose_spec.2.2.1, ifn (by omega_arith)] at hb'
        exact absurd hb' (by decide)
      exact encMain_tr hH w.ok.stream hHh w.mgf.hash w.mgf.len (mgf_valid w.mgf) c hL (hP' ▸ hP) hP16'
        (hDe.trans hHl) q₁ q₂ (by omega_arith) _ _ _ _ _ _
        ⟨hL, hP', hk, In.tx g₁ g₁.2.choose_spec.choose_spec.2.2.2, In.tx g₂ g₂.2.choose_spec.choose_spec.2.2.2⟩ e₁ e₂
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack below the frames: the callee's, and at least 16 bytes. -/
def encP (c : PdChecked) : Nat := max c.stack 16

/-- The stack the function uses: the callee's and the frames'. -/
def encStack (c : PdChecked) : Nat := encP c + 288

include hH in
/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed`, calling the precomputed
public operation `c`, for the tables of `vs`. -/
theorem enc_verified {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) {vs : List MdHash} (hc : Coh vs) (c : PdChecked)
    (hsat : ∃ s, (encSpec Hs (tables vs) (encP c)).pre s) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.Precomputed.encrypt Hl (fnsOf vs) c.name c.code)
      (encSpec Hs (tables vs) (encP c)) := by
  have hP : c.stack ≤ encP c := Nat.le_max_left _ _
  have hP16 : 16 ≤ encP c := Nat.le_max_right _ _
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := enc_ok hH hHh hHl hHv hc c hP hP16 h
    exact ⟨t, s', he, hp⟩) (enc_ct hH hHh hHl hc c hP hP16) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Enc
