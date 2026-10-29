module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Select
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Check
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Peer
/-! # Coordinate recovery and final checks preserve the parsed encoding -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Start.lean`, which only this module imported.
section

/-! # Decode the compressed x coordinate with the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

structure DecompressPre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .x1, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .x2, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .x1, c.C.len + 1⟩ ⟨s.gpr .x2, size⟩
  fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64

structure DecompressStart (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  fixed : Fixed c (s₀.gpr .x2) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  pk : s.gpr .x6 = s₀.gpr .x1
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = BitVec.allOnes 64
  outside : Outside (s₀.gpr .x2) 0 size s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressStart_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressStart c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none)) rest)) s₀ Q := by
  have hsz : size = 8192 := rfl
  have := hc.len8
  have := hc.len_hi
  have := hc.n10
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.rd, k₁.wr]
  have hsp : SetupPre c s₁ := by
    have hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
    have hd : Region.Disjoint ⟨s₀.gpr .x1 + 1, c.C.len⟩ ⟨s₀.gpr .x2, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega))
    exact ⟨by rw [k₁.wr, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  apply h s₁.gpr s₂
  refine ⟨S.scr, setup_fixed S,
    fun r hr => k₁.gpr r (by revert r; decide), S.x20.trans (k₁.gpr _ (by decide)),
    (S.keep.gpr _ (by decide)).trans r9, ?_, S.flag, ?_, ?_, ?_⟩
  · rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.mem]
  · rw [← k₁.mem]
    exact S.unch.outside (by simp)
  · rw [S.keep.rd, k₁.rd]
  · rw [S.keep.wr, k₁.wr]

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/Rhs.lean`, which only this module imported.
section

/-! # The curve polynomial used by coordinate recovery -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.AArch64 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.AArch64 (rhsOps)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsOps_eq (c : Cfg) : rhsOps c =
    .mul (c.sl QXM) (c.sl E) (c.sl R2P) :: rhsTail.map (FOp.rename c.sl) := rfl

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkA c.MP' size c.C.p s'.mem base
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.AArch64.fprogB c.MP' (rhsOps c)) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.AArch64.opProg c.MP'
    (.mul (c.sl QXM) (c.sl E) (c.sl R2P)))
    (VG.Impl.Weierstrass.AArch64.fprogB c.MP' (rhsTail.map (FOp.rename c.sl)))) s _
  have hneq : c.sl E ≠ c.sl R2P := by
    intro he
    have := sl_inj c hc.n0 he
    contradiction
  have first : VG.Impl.Weierstrass.AArch64.opProg c.MP' (.mul (c.sl QXM) (c.sl E) (c.sl R2P)) =
      c.mulPP (c.sl QXM) (c.sl E) (c.sl R2P) := by
    unfold VG.Impl.Weierstrass.AArch64.opProg Cfg.mulPP
    cases hh : VG.Impl.Weierstrass.AArch64.Mont.callOf c.MP' with
    | none => simp [VG.Impl.Weierstrass.AArch64.opCode, hneq]
    | some fm => obtain ⟨f, m⟩ := fm; simp [hneq, MP'_n]
  rw [first]
  refine WP.seq (WP.mono (slMulP_ok hc hs hM (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  have a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  have b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  have hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ rhsSlots.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i, MP'_A c, fun f m h => (hc.call_p f m h).2⟩
  have I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega)
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  refine WP.mono (fprogB_ok hL hAl hpR _ I (fun op hop x hx => ?_)
    (by
      intro op hop
      apply Low.of_call
      intro f m h x hx
      obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
      have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
        cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      have hi' := rhsTail_slots op₀ hop₀ i hi
      have H : ∀ i ∈ rhsSlots, i < 45 ∧ i ≠ TMP := by decide
      exact sl_own_fn c h7 (H i hi').1 (H i hi').2)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  have hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  have v₂ := I₂.val _ hw
  have H : ∀ op ∈ rhsTail, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
  rw [congrFun (runOps_rename c.sl rhsTail _ fun op hop y h =>
    sl_inj c hc.n0 h (.inr (H op hop).2) (.inl (H op hop).1)) W2, rhsTail_run] at v₂
  have U₁ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have U₂ : Unch base (slW c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  refine ⟨PK.scr hs₁, I₂.mod, fun r hr => (PK.gpr r hr).trans (k₁.gpr r hr),
    PK.rd.trans k₁.rd, PK.wr.trans k₁.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DecompressFront.lean`, which only this module imported.
section

/-! # Prepare the polynomial and retain the compressed input's checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (R2P BP QXM W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (s.gpr .x1) = 2 ∨ s.mem (s.gpr .x1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  fixed : Fixed c (s₀.gpr .x2) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  tag : word s.mem (s₀.gpr .x2) (c.sl D) = (s₀.mem (s₀.gpr .x1)).setWidth 64
  r2 : sv c (s₀.gpr .x2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (s₀.gpr .x2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (CompressedPrefix c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Keep the input checks while a field-arithmetic phase writes other slots. -/
theorem DecompressFront.frame {c : Cfg} (hc : BaseCfgOk c) {s₀ s t : State}
    {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s)
    (K : KeepRegs (powClob c.n) s t) {W : List (Nat × Nat)}
    (U : Unch (s₀.gpr .x2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ g t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (s₀.gpr .x2) t i = sv c (s₀.gpr .x2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      word t.mem (s₀.gpr .x2) (c.sl i) = word s.mem (s₀.gpr .x2) (c.sl i) :=
    U.word (fun w hw => by have := ha i hm w hw; omega)
      (by have := sl_le c h7 hi; omega)
  refine ⟨F.scr.of_keepRegs K (x0_not_powClob _), F.fixed.unch h7 hn hW U, F.original,
    (K.gpr _ (x20_not_powClob _)).trans F.out,
    (e (by decide) (by simp)).trans F.x, (ew (by decide) (by simp)).trans F.tag,
    (e (by decide) (by simp)).trans F.r2, ?_, ?_, (ew (by decide) (by simp)).trans F.flag,
    K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs

theorem decompressFront_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressFront c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.EcKey.Compressed.AArch64.decompressPeer c))
      (.seq (Impl.Weierstrass.AArch64.fprogB c.MP'
        (Impl.EcKey.Compressed.AArch64.rhsOps c)) rest)))) s₀ Q := by
  apply decompressStart_ok hc hp
  intro g s S
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := S.scr.nowrap
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr S.pk
    (by rw [S.rd, S.wr]; exact hp.pk) hp.disjoint S.fixed.mp S.flag)
    fun s₁ ⟨hs₁, k₁, U₁, r2₁, bp₁, tag₁, flag₁⟩ => ?_)
  have F₁ := S.fixed.unch h7 hn (fixedOk_slW (l := [R2P, BP, D, FLAG]) (by decide)) U₁
  have x₁ : sv c (s₀.gpr .x2) s₁ E = keyX c s₀ :=
    (sv_unch U₁ h7 hn (by decide) (apart_slW (by decide))).trans S.x
  have lead : s.mem (s₀.gpr .x1) = s₀.mem (s₀.gpr .x1) := by
    have e := keep_of_disjoint' S.outside hp.disjoint (by omega) (i := 0) (by omega)
      (by have := hc.len_hi; omega)
    simpa only [BitVec.add_zero] using e
  rw [lead, S.x] at flag₁
  rw [lead] at tag₁
  refine WP.seq (WP.mono (rhs_ok hc hs₁ (modP_of hc F₁.mp) r2₁ F₁.ap bp₁) fun s₂ R => ?_)
  have F₂ := F₁.unch h7 hn (fixedOk_slW (l := [QXM, W1, W2, W3, TMP]) (by decide)) R.unch
  have eq₂ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, W1, W2, W3, TMP]) :
      sv c (s₀.gpr .x2) s₂ i = sv c (s₀.gpr .x2) s₁ i :=
    sv_unch R.unch h7 hn hi (apart_slW hw)
  apply h g s₂
  refine ⟨R.scr, F₂, S.original, ?_, (eq₂ (by decide) (by decide)).trans x₁,
    ?_, (eq₂ (by decide) (by decide)).trans r2₁, R.lt, ?_, ?_, ?_, ?_⟩
  · rw [R.gpr _ (by intro h; exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h)), k₁.gpr _ (by decide), S.out]
  · exact (R.unch.word (fun w hw => by
      have := (apart_slW (c := c) (by decide : D ∉ [QXM, W1, W2, W3, TMP])) w hw
      have := hc.n0
      omega) (by have := sl_le c h7 (i := D) (by decide); omega)).trans tag₁
  · simpa only [x₁] using R.val
  · rw [flag_unch R.unch h7 hc.n0 hn (by decide), flag₁]
  · rw [R.rd, k₁.rd, S.rd]
  · rw [R.wr, k₁.wr, S.wr]

end VG.Proof.EcKey.Compressed.AArch64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (s.gpr .x1)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (s.gpr .x1)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  saved : Spill.Saved (s₀.gpr .x2) g Cfg.saved s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  y : sv c (s₀.gpr .x2) s QY = (keyRoot c root s₀).val
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (CompressedAccept c root s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : BaseCfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s) :
    WP isa (.seq (Impl.EcKey.Compressed.AArch64.rootCandidate c)
      (.seq (Impl.EcKey.Compressed.AArch64.selectRoot c)
        (Impl.EcKey.Compressed.AArch64.checkRoot c))) s (DecompressChecked c root s₀ g) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  have F₁ := F.frame hc C.keep C.unch (candidate_fixed hc) (by
    intro i hi
    have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ ACC :: candidateSlots := by decide
    exact candidate_apart hc (h i hi).1 (h i hi).2)
  have root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .x2) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  have F₂ := F₁.frame hc (S.keep.mono (fun _ hr => List.mem_cons_of_mem _ hr)) S.unch
    (fixedOk_slW (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slW (h i hi) (by
        have H : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 := by decide
        have := H i hi
        omega) (by decide))
  have y₂ : Fin.ofNat c.C.p (sv c (s₀.gpr .x2) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (s₀.gpr .x1)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  have yval₂ : sv c (s₀.gpr .x2) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  have F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slW (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (s₀.gpr .x2) s₃ i = sv c (s₀.gpr .x2) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slW hw)
  refine ⟨K.scr, F₃.saved, F.original, (K.keep.gpr _ (by intro h; exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h))).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (s₀.gpr .x1)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.AArch64
