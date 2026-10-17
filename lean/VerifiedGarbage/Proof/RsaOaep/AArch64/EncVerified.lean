module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# RSAES-OAEP encryption on AArch64: verified

The prologue (`pro_ct`), from two entry states whose public data agree, the
hash functions' slots (`setup_ct`) and the check of `k` (`chk_ct`); the
failure (`encFail_tr`); the check of the message's length; and
`encMain_tr`, put together (`enc_ct`): the branches are on `k`, the
message's length and the hash functions' numbers, which are public. With
correctness (`enc_ok`), `vg_rsa_oaep_encrypt_precomputed`, for any tier `t`
of the hash functions and `c` of a precomputed public operation, is
verified against the shared contract with the stack it and its
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
open VG.Proof.Pbkdf2.Md.AArch64 (Tier)

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
      BitVec.setWidth_eq]) (by omega) hL.k1024
    (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨e.L.OUT, by rw [hc.wr]; simp, 0, (BitVec.add_zero _).symm, by simp⟩)
    hL.bO (out_apart hL hP16)) fun _ ⟨_, Su, Ru, _⟩ =>
      In.of_step hL hP16 hc Su (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) Ru hS trivial

/-! ## The prologue, the hash functions' slots and the check of `k` -/

/-- What correctness says of a point of the code. -/
abbrev EInv := ELay → (Reg → BitVec 64) → (VReg → BitVec 128) → Mem → State → Prop

/-- Two runs in the layout of `e`, each satisfying `Φ`, with MGF1's `hLen`
that of `hs`'s hash function its number names. -/
def TwoE (hs : List Hash) (P : Nat) (Φ : EInv) (e : Env) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = P ∧ e.L.DG = lenAt hs e.L.gh.toNat ∧ LeakEq e.L e.m₁ e.m₂ ∧ PreOk e.L e.m₁ ∧
    PreOk e.L e.m₂ ∧ Φ e.L e.g₁ e.v₁ e.m₁ a ∧ Φ e.L e.g₂ e.v₂ e.m₂ b

/-- Two runs with the same layout, each satisfying `Φ`. -/
def Two (hs : List Hash) (P : Nat) (Φ : EInv) (a b : State) : Prop := ∃ e : Env, TwoE hs P Φ e a b

theorem two_wp {hs : List Hash} {P : Nat} {c : Prog isa} {Φ Ψ : EInv}
    (hct : ∀ e, RelCT isa (TwoE hs P Φ e) c fun _ _ => True)
    (hw : ∀ (L : ELay) g vv m₀ (t : State), L.Ok → L.P = P → L.DG = lenAt hs L.gh.toNat → PreOk L m₀ →
      Φ L g vv m₀ t → WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two hs P Φ) c (Two hs P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨e, hp⟩ e₁ e₂
  obtain ⟨ht, -⟩ := hct e _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, hG, hk, q₁, q₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL hP hG q₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL hP hG q₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hP, hG, hk, q₁, q₂, y₁, y₂⟩

/-- After the prologue. -/
abbrev ProI : EInv := fun L g vv m₀ t => Ctx L g vv m₀ t ∧ ∃ V W, Rep t.mem L.Q L.scr V W ∧ Prologued L W

/-- After the first number's slot. -/
abbrev Set1I : EInv := fun L g vv m₀ t => Ctx L g vv m₀ t ∧ ∃ V W, Rep t.mem L.Q L.scr V W ∧ Prologued L W ∧
  W 2 = BitVec.ofNat 64 L.hh.toNat ∧ W 4 = BitVec.ofNat 64 L.D

/-- In the frames, with `X`. -/
abbrev InI (X : ELay → (Nat → BitVec 64) → State → Prop) : EInv := fun L g vv m₀ t => In L g vv m₀ (X L) t

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (P : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (encSpec P).pre s₁ ∧ (encSpec P).pre s₂ ∧ (encSpec P).pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem pub_sp {P : Nat} {s₁ s₂ : State} (h : (encSpec P).pub s₁ s₂) : s₁.sp = s₂.sp := by
  sig_pub [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, AArch64.abi,
    AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h.1

theorem pro_ct (hs : List Hash) {P : Nat} :
    RelCT isa (Entered P) (.block encPrologue) (Two hs P ProI) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, hp, ea, eb⟩ e₁ e₂
  subst ea eb
  sig_pub [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, AArch64.abi,
    AArch64.argRegs, _root_.List.range, _root_.List.range.loop, List.append_eq] at hp
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (c := .block encPrologue) (by taint_decide)
    _ _ _ _ _ _ (by
      show (entered s₁).sp = (entered s₂).sp
      rw [entered_sp 0 P, entered_sp 0 P]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨_, u₁, x₁, y₁⟩ := prologue_ok (DG := lenAt hs (stackArg s₁ 9).toNat) h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := prologue_ok (DG := lenAt hs (stackArg s₁ 9).toNat) h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : lay (lenAt hs (stackArg s₁ 9).toNat) P s₂ = lay (lenAt hs (stackArg s₁ 9).toNat) P s₁ := by
    simp only [lay, preX, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hsp]
  obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, h3, h5])
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
  obtain ⟨hn, he⟩ := leak_split hb (by rw [bytesAt_length, bytesAt_length, h3])
  refine ⟨ht, ⟨lay (lenAt hs (stackArg s₁ 9).toNat) P s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩,
    lay_ok h₁, rfl, rfl, ⟨?_, ?_, ?_⟩, preOk_lay h₁, e ▸ preOk_lay h₂, ⟨y₁.1, _, _, ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
      y₁.2.2⟩, ?_⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    rw [hn, h2, h3]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    rw [he, h4, h5]
  · intro R hR
    simp only [lay, preX, List.mem_singleton] at hR
    subst hR
    show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 6) ((stackArg s₁ 7).toNat * 8 / 8) =
      Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 6) ((stackArg s₁ 7).toNat * 8 / 8)
    rw [Nat.mul_div_cancel _ (by decide : 0 < 8), hw, a6, a7]
  · rw [← e]; exact ⟨y₂.1, _, _, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, y₂.2.2⟩

/-- The number of a hash function, our stack argument `j`, to its slot,
and in `x16`, from `Ctx`. -/
theorem selHead_e {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hL : L.Ok) (hP : 16 ≤ L.P) (hp : PreOk L m₀) (hc : Ctx L g vv m₀ t) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep t.mem L.Q L.scr V W) (hS : W 12 = L.scr) {j a : Nat} (hj : j = 8 ∨ j = 9)
    (ha : 8 * a + 8 ≤ frameBytes) :
    WP isa (.block [.ldrSp .x16 (arg j), .addSp .x9 0, .str .x .x16 .x9 (8 * a)]) t fun u' =>
      u'.sp = t.sp ∧ u'.gpr .x16 = BitVec.ofNat 64 (if j = 8 then L.hh else L.gh).toNat := by
  obtain ⟨ld, v⟩ := selAt hL hc hp hj
  exact selHead_ok (hc.lay hL hP R hS) (by rcases hj with rfl | rfl <;> decide) ⟨by omega, ha⟩ ld v

theorem setup_ct (t : Tier) {P : Nat} (hP16 : 16 ≤ P) :
    RelCT isa (Two (tierHs t) P ProI) (hashSetup (tierHs t) 8 9) (Two (tierHs t) P (InI fun _ _ _ => True)) := by
  refine RelCT.seq (R := Two (tierHs t) P Set1I) (two_wp (fun e => ?_) fun L g vv m₀ u hL hP hG hp hin => ?_)
    (two_wp (fun e => ?_) fun L g vv m₀ u hL hP hG hp hin => ?_)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨v, hn, -⟩ := tier_num t hp.1.hhk
    have hP' : 16 ≤ e.L.P := by rw [hp.2.1]; exact hP16
    exact selArg_tr hn (j := 8) (by taint_decide) (by taint_decide)
      (fun a b ⟨_, _, _, _, _, _, ⟨fa, _⟩, ⟨fb, _⟩⟩ => fa.sp.trans fb.sp.symm)
      (fun a b ⟨hL, _, _, _, qa, qb, ⟨ca, Va, Wa, Ra, Sa⟩, ⟨cb, Vb, Wb, Rb, Sb⟩⟩ s hs => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact selHead_e (a := 2) hL hP' qa ca Ra Sa.scr (.inl rfl) (by decide)
        · exact selHead_e (a := 2) hL hP' qb cb Rb Sb.scr (.inl rfl) (by decide)) _ _ _ _ _ _ hp e₁ e₂
  · obtain ⟨v, hn, hm⟩ := tier_num t hL.hhk
    obtain ⟨-, hzF, -, hzDF, -⟩ := sizes v.ok.stream
    have hD64 : v.H.D ≤ 64 := Nat.le_trans hzDF hzF
    have hLD : L.D = v.H.D := (hL.hsd _ hm).trans v.mgf.len
    have hP' : 16 ≤ L.P := by rw [hP]; exact hP16
    obtain ⟨hc, V, W, R, hS⟩ := hin
    obtain ⟨ld, hv⟩ := selAt hL hc hp (j := 8) (.inl rfl)
    exact WP.mono (selArg_ok hn (by omega) (hc.lay hL hP' R hS.scr) R (j := 8) (a := 2) (b := 4) (by decide)
      (by decide) (by decide) (by decide) (by decide) ld hv []) fun u' ⟨_, S1, R1⟩ =>
        ⟨hc.step hL hP' S1 nil_ws, _, _, R1, hS.of fun j h1 _ _ => by
          simp only [upd]; rw [ifn (by omega), ifn (by omega)], by simp [upd], by rw [hLD]; simp [upd]⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨v, hn, -⟩ := tier_num t hp.1.ghk
    have hP' : 16 ≤ e.L.P := by rw [hp.2.1]; exact hP16
    exact selArg_tr hn (j := 9) (by taint_decide) (by taint_decide)
      (fun a b ⟨_, _, _, _, _, _, ⟨fa, _⟩, ⟨fb, _⟩⟩ => fa.sp.trans fb.sp.symm)
      (fun a b ⟨hL, _, _, _, qa, qb, ⟨ca, Va, Wa, Ra, Sa, _⟩, ⟨cb, Vb, Wb, Rb, Sb, _⟩⟩ s hs => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact selHead_e (a := 3) hL hP' qa ca Ra Sa.scr (.inr rfl) (by decide)
        · exact selHead_e (a := 3) hL hP' qb cb Rb Sb.scr (.inr rfl) (by decide)) _ _ _ _ _ _ hp e₁ e₂
  · obtain ⟨v, hn, -⟩ := tier_num t hL.ghk
    obtain ⟨-, hzF, -, hzDF, -⟩ := sizes v.ok.stream
    have hD64 : v.H.D ≤ 64 := Nat.le_trans hzDF hzF
    have hP' : 16 ≤ L.P := by rw [hP]; exact hP16
    obtain ⟨hc, V, W, R, hS, h2, h4⟩ := hin
    obtain ⟨ld, hv⟩ := selAt hL hc hp (j := 9) (.inr rfl)
    exact WP.mono (selArg_ok hn (by omega) (hc.lay hL hP' R hS.scr) R (j := 9) (a := 3) (b := 5) (by decide)
      (by decide) (by decide) (by decide) (by decide) ld hv []) fun u' ⟨_, S1, R1⟩ =>
        ⟨hc.step hL hP' S1 nil_ws, _, _, R1, hS.slots (fun j h1 _ _ => by
          simp only [upd]; rw [ifn (by omega), ifn (by omega)])
          ⟨by simp only [upd]; rw [ifn (by decide), ifn (by decide)]; exact h2, by simp [upd],
            by simp only [upd]; rw [ifn (by decide), ifn (by decide)]; exact h4,
            by rw [hG, hn.lenAt]; simp [upd]⟩, trivial⟩

/-- `x11` all ones iff `k < 2 hLen + 2`. -/
def KX (L : ELay) (_ : Nat → BitVec 64) (t : State) : Prop :=
  t.gpr .x11 = if 2 * L.D + 2 ≤ L.k.toNat then 0 else BitVec.allOnes 64

theorem chkK_taint : RelCT isa (fun a b => a.sp = b.sp) (.block chkK) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ h => ⟨h, fun _ h => absurd (Taint.mem_ofRegs.mp h)
    List.not_mem_nil⟩) (by taint_decide)

theorem chk_ct (t : Tier) {P : Nat} (hP16 : 16 ≤ P) :
    RelCT isa (Two (tierHs t) P (InI fun _ _ _ => True)) (.block chkK) (Two (tierHs t) P (InI KX)) :=
  two_wp (fun _ => chkK_taint.mono (fun a b ⟨_, _, _, _, _, _, ⟨fa, _⟩, ⟨fb, _⟩⟩ => fa.sp.trans fb.sp.symm)
      fun _ _ h => h)
    fun L g vv m₀ u hL hP _ _ ⟨hc, V, W, R, hS, _⟩ => by
      have hP' : 16 ≤ L.P := by rw [hP]; exact hP16
      have hk : W 21 = BitVec.ofNat 64 L.k.toNat := by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      obtain ⟨v, -, hm⟩ := tier_num t hL.hhk
      obtain ⟨-, hzF, -, hzDF, -⟩ := sizes v.ok.stream
      have hD64 : v.H.D ≤ 64 := Nat.le_trans hzDF hzF
      have hLD : L.D = v.H.D := (hL.hsd _ hm).trans v.mgf.len
      exact WP.mono (chkK_ok (hc.lay hL hP' R hS.scr) R hk hS.hsl.hlen hL.k1024 (by omega))
        fun u' ⟨_, S1, hm, x11⟩ => In.of_step hL hP' hc S1 nil_ws (hm ▸ R) hS x11

/-- `In` with `X`, as `In` with nothing more. -/
theorem In.forget {L : ELay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}
    {X : (Nat → BitVec 64) → State → Prop} {t : State} (h : In L g vv m₀ X t) : In L g vv m₀ (fun _ _ => True) t :=
  ⟨h.1, h.2.choose, h.2.choose_spec.choose, h.2.choose_spec.choose_spec.1, h.2.choose_spec.choose_spec.2.1, trivial⟩

theorem enc_ct (t : Tier) (c : PdChecked) {P : Nat} (hP : c.stack ≤ P) (hP16 : 16 ≤ P) :
    ConstantTime isa (encSpec P).pre (encSpec P).pub
      (Impl.RsaOaep.AArch64.Precomputed.encrypt (tierHs t) c.name c.code) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => pub_sp h.2.2) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [encBody_eq]
  refine ((pro_ct (tierHs t)).seq ((setup_ct t hP16).seq ((chk_ct t hP16).seq (Q := fun _ _ => True) ?_))).mono
    ?_ fun _ _ _ => trivial
  · refine RelCT.ite (fun a b ⟨e, _, _, _, _, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP', _, hk, _, _, f₁, f₂⟩, _⟩ e₁ e₂
      exact encFail_tr hL (hP' ▸ hP16) _ _ _ _ _ _ ⟨hL, hP', hk, f₁, f₂⟩ e₁ e₂
    intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨⟨e, hL, hP', hG, hk, q₁, q₂, f₁, f₂⟩, hb⟩ e₁ e₂
    have hP16' : 16 ≤ e.L.P := hP' ▸ hP16
    obtain ⟨vH, hnH, hmH⟩ := tier_num t hL.hhk
    obtain ⟨vG, hnG, -⟩ := tier_num t hL.ghk
    have hLD : e.L.D = vH.H.D := (hL.hsd _ hmH).trans vH.mgf.len
    have hLDG : e.L.DG = vG.H.D := hG.trans hnG.lenAt
    have hkD : 2 * e.L.D + 2 ≤ e.L.k.toNat := by
      by_contra hc
      rw [eval_nonzero, f₁.2.choose_spec.choose_spec.2.2, ifn (by omega)] at hb
      exact absurd hb (by decide)
    refine (RelCT.seq (Q := fun _ _ => True) (pw_blk (X' := MX e.L.D e.L.k.toNat e.L.ml.toNat) []
      (by taint_decide) nopin
      fun _ _ _ _ _ _ _ _ hc R hS _ => WP.mono (chkMsg_ok (hc.lay hL hP16' R hS.scr) R
        (by rw [hS.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [hS.ml, BitVec.ofNat_toNat, BitVec.setWidth_eq])
        hS.hsl.hlen hL.k1024 e.L.ml.isLt hkD)
        fun _ ⟨_, Su, hm, x11⟩ => In.of_step hL hP16' hc Su nil_ws (by rw [hm]; exact R) hS x11) ?_) _ _ _ _ _ _
      ⟨hL, hP', hk, f₁.forget, f₂.forget⟩ e₁ e₂
    refine RelCT.ite (fun a b ⟨_, _, _, ⟨_, _, _, _, _, xa⟩, ⟨_, _, _, _, _, xb⟩⟩ => by
      rw [eval_nonzero, eval_nonzero, xa, xb]) ?_ ?_
    · exact (encFail_tr hL hP16').mono (fun _ _ h => h.1) fun _ _ h => h
    · intro a₁ a₂ u₁ u₂ a₁' a₂' ⟨⟨_, _, _, g₁, g₂⟩, hb'⟩ e₁ e₂
      have hmk : e.L.ml.toNat ≤ e.L.k.toNat - (2 * e.L.D + 2) := by
        by_contra hc
        rw [eval_nonzero, g₁.2.choose_spec.choose_spec.2.2, ifn (by omega)] at hb'
        exact absurd hb' (by decide)
      exact encMain_tr vH.ok.stream vG.ok.stream vH.mgf.hash vG.mgf.hash vG.mgf.len (mgf_valid vG.mgf) c hL
        (hP' ▸ hP) hP16' hnH hnG hLD hLDG q₁ q₂ (by omega) _ _ _ _ _ _ ⟨hL, hP', hk, g₁.forget, g₂.forget⟩ e₁ e₂
  · rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

/-- The stack below the frames: the callee's, and at least 16 bytes. -/
def encP (c : PdChecked) : Nat := max c.stack 16

/-- The stack the function uses: the callee's and the frames'. -/
def encStack (c : PdChecked) : Nat := encP c + 288

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tier `t` of hash functions,
calling the precomputed public operation `c`. -/
theorem enc_verified (t : Tier) (c : PdChecked)
    (hsat : ∃ s, (Spec.RsaOaep.encryptAnyContract AArch64.abi (encStack c)).pre s) :
    Verified AArch64.target (Impl.RsaOaep.AArch64.Precomputed.encrypt (tierHs t) c.name c.code)
      (Spec.RsaOaep.encryptAnyContract AArch64.abi (encStack c)) := by
  have hP : c.stack ≤ encP c := Nat.le_max_left _ _
  have hP16 : 16 ≤ encP c := Nat.le_max_right _ _
  exact Verified.of_correct (fun _ h => by
    obtain ⟨t', s', he, hp⟩ := enc_ok t c hP hP16 h
    exact ⟨t', s', he, hp⟩) (enc_ct t c hP hP16) (Contract.Implies.refl hsat)

end VG.Proof.RsaOaep.AArch64.Enc
