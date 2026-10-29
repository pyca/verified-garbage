module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Spec.EcKey.Compressed

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressFinish
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Setup
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Front
import VerifiedGarbage.Proof.Ecdsa.X86_64.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86_64.Middle
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Ecdh.X86_64.Validate
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Peer
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Parity
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Check
/-! # Decompression meets the merged API contract -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Start.lean`, which only this module imported.
section

/-! # Decode the compressed x coordinate with the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

structure DecompressPre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .rsi, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .rdx, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .rsi, c.C.len + 1⟩ ⟨s.gpr .rdx, size⟩
  fit : (s.gpr .rdx).toNat + size ≤ 2 ^ 64

structure DecompressStart (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  fixed : Fixed c (s₀.gpr .rdx) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  pk : s.gpr .r9 = s₀.gpr .rsi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = BitVec.allOnes 64
  outside : Outside (s₀.gpr .rdx) 0 size s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressStart_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressStart c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.X86_64.args)
      (.seq (.block (c.setupWith none)) rest)) s₀ Q := by
  have hsz : size = 8192 := rfl
  have := hc.len8
  have := hc.len_hi
  have := hc.n10
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  have hsp : SetupPre c s₁ := by
    have hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
    have hd : Region.Disjoint ⟨s₀.gpr .rsi + 1, c.C.len⟩ ⟨s₀.gpr .rdx, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega))
    exact ⟨by rw [k₁.2.2.2, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  apply h s₁.gpr s₂
  refine ⟨S.scr, VG.Proof.EcKey.Validate.X86_64.setup_fixed S,
    fun r hr => k₁.1 r (by revert r; decide), S.rsi.trans (k₁.1 _ (by decide)),
    (S.keep.gpr _ (by decide)).trans r9, ?_, S.flag, ?_, ?_, ?_⟩
  · rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.2.1]
  · rw [← k₁.2.1]
    exact S.unch.outside (by simp)
  · rw [S.keep.rd, k₁.2.2.1]
  · rw [S.keep.wr, k₁.2.2.2]

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Rhs.lean`, which only this module imported.
section

/-! # The curve polynomial used by coordinate recovery -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86_64 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.X86_64 (rhsOps)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64

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
  mod : ModOkW c.MP' size c.C.p s'.mem base
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.X86_64.fprogB c.MP' (rhsOps c)).inline s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [rhsOps_eq, fprogB_cons_iff]
  refine WP.mono (slMulP_ok h7 hs hM (o := QXM) (a := E) (b := R2P) (by decide) (by decide)
    (by decide) (by decide) (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  have a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  have b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  have hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
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
  refine WP.mono (fprogB_ok hL hpR _ I (fun op hop x hx => ?_)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  have hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  have v₂ := I₂.val _ hw
  rw [congrFun (runOps_rename c.sl rhsTail _ fun _ _ y h => sl_inj c hc.n0 h) W2, rhsTail_run] at v₂
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

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DecompressFront.lean`, which only this module imported.
section

/-! # Prepare the polynomial and retain the compressed input's checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (R2P BP QXM W1 W2 W3)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (s.gpr .rsi) = 2 ∨ s.mem (s.gpr .rsi) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  fixed : Fixed c (s₀.gpr .rdx) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  tag : word s.mem (s₀.gpr .rdx) (c.sl D) = (s₀.mem (s₀.gpr .rsi)).setWidth 64
  r2 : sv c (s₀.gpr .rdx) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (s₀.gpr .rdx) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = mask (CompressedPrefix c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Keep the input checks while a field-arithmetic phase writes other slots. -/
theorem DecompressFront.frame {c : Cfg} (hc : BaseCfgOk c) {s₀ s t : State}
    {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s)
    (K : KeepRegs (powClob c.n) s t) {W : List (Nat × Nat)}
    (U : Unch (s₀.gpr .rdx) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ g t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (s₀.gpr .rdx) t i = sv c (s₀.gpr .rdx) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      word t.mem (s₀.gpr .rdx) (c.sl i) = word s.mem (s₀.gpr .rdx) (c.sl i) :=
    U.word (fun w hw => by have := ha i hm w hw; omega)
      (by have := sl_le c h7 hi; omega)
  refine ⟨F.scr.of_keepRegs K (rdi_not_powClob _), F.fixed.unch h7 hn hW U, F.original,
    (K.gpr _ (rsi_not_powClob _)).trans F.out,
    (e (by decide) (by simp)).trans F.x, (ew (by decide) (by simp)).trans F.tag,
    (e (by decide) (by simp)).trans F.r2, ?_, ?_, (ew (by decide) (by simp)).trans F.flag,
    K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs

theorem decompressFront_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressFront c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.X86_64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.EcKey.Compressed.X86_64.decompressPeer c))
      (.seq (Impl.Weierstrass.X86_64.fprogB c.MP'
        (Impl.EcKey.Compressed.X86_64.rhsOps c)).inline rest)))) s₀ Q := by
  apply decompressStart_ok hc hp
  intro g s S
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := S.scr.nowrap
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr S.pk
    (by rw [S.rd, S.wr]; exact hp.pk) hp.disjoint S.fixed.mp S.flag)
    fun s₁ ⟨hs₁, k₁, U₁, r2₁, bp₁, tag₁, flag₁⟩ => ?_)
  have F₁ := S.fixed.unch h7 hn (fixedOk_slW (l := [R2P, BP, D, FLAG]) (by decide)) U₁
  have x₁ : sv c (s₀.gpr .rdx) s₁ E = keyX c s₀ :=
    (sv_unch U₁ h7 hn (by decide) (apart_slW (by decide))).trans S.x
  have lead : s.mem (s₀.gpr .rsi) = s₀.mem (s₀.gpr .rsi) := by
    have e := keep_of_disjoint' S.outside hp.disjoint (by omega) (i := 0) (by omega)
      (by have := hc.len_hi; omega)
    simpa only [BitVec.add_zero] using e
  rw [lead, S.x] at flag₁
  rw [lead] at tag₁
  refine WP.seq (WP.mono (rhs_ok hc hs₁ (modP_of hc F₁.mp) r2₁ F₁.ap bp₁) fun s₂ R => ?_)
  have F₂ := F₁.unch h7 hn (fixedOk_slW (l := [QXM, W1, W2, W3, TMP]) (by decide)) R.unch
  have eq₂ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, W1, W2, W3, TMP]) :
      sv c (s₀.gpr .rdx) s₂ i = sv c (s₀.gpr .rdx) s₁ i :=
    sv_unch R.unch h7 hn hi (apart_slW hw)
  apply h g s₂
  refine ⟨R.scr, F₂, S.original, ?_, (eq₂ (by decide) (by decide)).trans x₁,
    ?_, (eq₂ (by decide) (by decide)).trans r2₁, R.lt, ?_, ?_, ?_, ?_⟩
  · rw [R.gpr _ (rsi_not_clob _), k₁.gpr _ (by decide), S.out]
  · exact (R.unch.word (fun w hw => by
      have := apart_slW (c := c) (by decide : D ∉ [QXM, W1, W2, W3, TMP]) w hw
      have := hc.n0
      omega) (by have := sl_le c h7 (i := D) (by decide); omega)).trans tag₁
  · simpa only [x₁] using R.val
  · rw [flag_unch R.unch h7 hc.n0 hn (by decide), flag₁]
  · rw [R.rd, k₁.rd, S.rd]
  · rw [R.wr, k₁.wr, S.wr]

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/Select.lean`, which only this module imported.
section

/-! # Leave Montgomery form and choose between the two canonical roots -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (QY W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

structure SelectPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QY, W0, TMP]) s.mem s'.mem
  lt : sv c base s' QY < c.C.p
  val : Fin.ofNat c.C.p (sv c base s' QY) =
    let y := toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
    if y.val % 2 = (word s.mem base (c.sl D)).toNat % 2 then y else -y

theorem selectRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONE = 1) (hZero : sv c base s ZERO = 0) :
    WP isa (Impl.EcKey.Compressed.X86_64.selectRoot c).inline s (SelectPost c base s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hY := sl_le c h7 (i := QY) (by decide)
  have hZ := sl_le c h7 (i := ZERO) (by decide)
  have hW := sl_le c h7 (i := W0) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hMP := sl_le c h7 (i := MP) (by decide)
  change WP isa (.seq (opProg c.MP' (.mul (c.sl QY) (c.sl ACC) (c.sl ONE))).inline
    (.block (opCode c.MP' (.sub (c.sl W0) (c.sl ZERO) (c.sl QY)) ++
      Impl.EcKey.Compressed.X86_64.parityMask c ++ sel c.n (c.sl QY) (c.sl QY) (c.sl W0)))) s _
  refine WP.seq (WP.mono (slMulP_ok h7 hs hM (o := QY) (a := ACC) (b := ONE)
    (by decide) (by decide) (by decide) (by decide) (by rw [hOne]; omega))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hM₁ := hM.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have normal : Fin.ofNat c.C.p (sv c base s₁ QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) :=
    toM_one_mul (unitMod_pow_two hc.p_odd (64 * c.n)) (by simpa only [hOne] using e₁)
  have normalVal : sv c base s₁ QY =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt lt₁] using congrArg Fin.val normal
  have zero₁ : sv c base s₁ ZERO = 0 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hZero
  have ha := slots_apart (MP'_n c) (MP'_tmp c) (MP'_mo c)
    (o := W0) (a := ZERO) (b := QY) (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₁ hM₁ hW hZ hY ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    (by change sv c base s₁ ZERO < c.C.p; rw [zero₁]; omega)
    lt₁) fun s₂ ⟨k₂, e₂⟩ => ?_
  change sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p at e₂
  have hs₂ := k₂.scr hs₁
  have hM₂ := hM₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have y₂ : sv c base s₂ QY = sv c base s₁ QY :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  have negLt : sv c base s₂ W0 < c.C.p := by
    rw [e₂]
    exact Nat.mod_lt _ (by omega)
  have negVal : Fin.ofNat c.C.p (sv c base s₂ W0) = -(Fin.ofNat c.C.p (sv c base s₁ QY)) := by
    apply Fin.ext
    simp only [Fin.val_ofNat, Fin.neg_def]
    rw [show sv c base s₂ W0 = (sv c base s₁ ZERO + c.C.p - sv c base s₁ QY) % c.C.p from e₂,
      zero₁, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt lt₁]
  have U₁₂ : Unch base (slW c [QY, W0, TMP]) s.mem s₂.mem :=
    unch_same (unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp))
      (unch_slots (MP'_n c) rfl k₂.unch (by simp) (by simp))
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) :=
    U₁₂.word (fun w hw => by
      have := apart_slW (c := c) (by decide : D ∉ [QY, W0, TMP]) w hw
      omega) (by have := hs.nowrap; omega)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (sel_ok (decide (sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2)) c.n hs₃
    (by simpa only [mask, decide_eq_true_eq] using mask₃)
    hY hY hW (Or.inl (Nat.le_refl _))
    (by have := sl_apart c (i := QY) (j := W0) (by decide); omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have hM₄ : ModOkW c.MP' size c.C.p s₄.mem base := modP_of hc (by
    rw [O₄.wordsVal (d := c.sl MP) (k := c.n)
      (sl_apart c (i := MP) (j := QY) (by decide)) (by omega), k₃.2.1]
    exact hM₂.val)
  have e₄' : sv c base s₄ QY =
      if sv c base s₂ QY % 2 ≠ (word s₂.mem base (c.sl D)).toNat % 2 then
        sv c base s₂ W0 else sv c base s₂ QY := by
    simpa only [sv, k₃.2.1, decide_eq_true_eq] using e₄
  refine ⟨hs₄, hM₄, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · have hra : r ≠ .rax := fun h => hr (h ▸ by simp [clob])
      have hrd : r ≠ .rdx := fun h => hr (h ▸ by simp [clob])
      have hrc : r ≠ .rcx := fun h => hr (h ▸ by simp [clob])
      rw [k₄.gpr _ (by simp [hra, hrd]), k₃.1 _ (by simp [hrd, hrc]), k₂.gpr _ hr, k₁.gpr _ hr]
    · rw [k₄.rd, k₃.2.2.1, k₂.rd, k₁.rd]
    · rw [k₄.wr, k₃.2.2.2, k₂.wr, k₁.wr]
  · apply unch_same U₁₂
    rw [← k₃.2.1]
    exact slot_frame (by simp) (Nat.le_refl _) O₄
  · rw [e₄']
    split
    · exact negLt
    · rw [y₂]
      exact lt₁
  · change Fin.ofNat c.C.p (sv c base s₄ QY) =
      if (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2 then _ else _
    rw [y₂, tag₂, normalVal] at e₄'
    by_cases hm : (toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)).val % 2 =
        (word s.mem base (c.sl D)).toNat % 2
    · rw [ite_eq_left hm]
      rw [ite_eq_right (not_not_intro hm)] at e₄'
      rw [e₄']
      exact Fin.ext (Nat.mod_eq_of_lt (toM _ _ _).isLt)
    · rw [ite_eq_right hm]
      rw [ite_eq_left hm] at e₄'
      rw [e₄', negVal, normal]

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DecompressMiddle.lean`, which only this module imported.
section

/-! # Coordinate recovery and final checks preserve the parsed encoding -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (QY QYM R2P W0 W1 W2 W3)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (chooseRoot)

def keyRhs (c : Cfg) (s : State) : Spec.Weierstrass.Fe c.C :=
  let x := Fin.ofNat c.C.p (keyX c s)
  x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

def keyRoot (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :=
  chooseRoot (root (keyRhs c s)) ((s.mem (s.gpr .rsi)).toNat % 2)

def CompressedAccept (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s : State) : Prop := CompressedPrefix c s ∧
  (keyRoot c root s * keyRoot c root s = keyRhs c s ∧
    (keyRoot c root s).val % 2 = (s.mem (s.gpr .rsi)).toNat % 2)

instance (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) (s : State) :
    Decidable (CompressedAccept c root s) := inferInstanceAs (Decidable (_ ∧ (_ ∧ _)))

structure DecompressChecked (c : Cfg)
    (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  saved : Spill.Saved s.mem (s₀.gpr .rdx) g Cfg.saved
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  y : sv c (s₀.gpr .rdx) s QY = (keyRoot c root s₀).val
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = mask (CompressedAccept c root s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressMiddle_ok {c : Cfg} (hc : BaseCfgOk c)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C} (hroot : CandidateCorrect c root)
    {s₀ s : State} {g : Reg → BitVec 64} (F : DecompressFront c s₀ g s) :
    WP isa (.seq (Impl.EcKey.Compressed.X86_64.rootCandidate c).inline
      (.seq (Impl.EcKey.Compressed.X86_64.selectRoot c).inline
        (Impl.EcKey.Compressed.X86_64.checkRoot c).inline)) s (DecompressChecked c root s₀ g) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := F.scr.nowrap
  refine WP.seq (WP.mono (hroot _ s F.scr (modP_of hc F.fixed.mp) F.rhs_lt F.fixed.onep)
    fun s₁ C => ?_)
  have F₁ := F.frame hc C.keep C.unch (candidate_fixed c) (by
    intro i hi
    have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i < 45 ∧ i ∉ candidateSlots := by decide
    exact candidate_apart (h i hi).1 (h i hi).2)
  have root₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₁ ACC) = root (keyRhs c s₀) := by
    rw [C.val, F.rhs]; rfl
  refine WP.seq (WP.mono (selectRoot_ok hc F₁.scr (modP_of hc F₁.fixed.mp)
    F₁.fixed.one F₁.fixed.zero) fun s₂ S => ?_)
  have F₂ := F₁.frame hc (S.keep.mono (fun _ hr => List.mem_cons_of_mem _ hr)) S.unch
    (fixedOk_slW (l := [QY, W0, TMP]) (by decide)) (by
      intro i hi
      have h : ∀ i ∈ [E, D, R2P, W2, FLAG], i ∉ [QY, W0, TMP] := by decide
      exact apart_slW (h i hi))
  have y₂ : Fin.ofNat c.C.p (sv c (s₀.gpr .rdx) s₂ QY) = keyRoot c root s₀ := by
    rw [S.val, root₁, F₁.tag]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
      (s₀.mem (s₀.gpr .rsi)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
    rfl
  have yval₂ : sv c (s₀.gpr .rdx) s₂ QY = (keyRoot c root s₀).val := by
    simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt S.lt] using congrArg Fin.val y₂
  refine WP.mono (checkRoot_ok hc F₂.scr (modP_of hc F₂.fixed.mp) S.lt
    F₂.rhs_lt F₂.r2 F₂.flag) fun s₃ K => ?_
  have F₃ := F₂.fixed.unch h7 hn
    (fixedOk_slW (l := [QYM, W1, W3, TMP, FLAG]) (by decide)) K.unch
  have e₃ {i : Nat} (hi : i < 45) (hw : i ∉ [QYM, W1, W3, TMP, FLAG]) :
      sv c (s₀.gpr .rdx) s₃ i = sv c (s₀.gpr .rdx) s₂ i :=
    sv_unch K.unch h7 hn hi (apart_slW hw)
  refine ⟨K.scr, F₃.saved, F.original, (K.keep.gpr _ (rsi_not_clob _)).trans F₂.out,
    (e₃ (by decide) (by decide)).trans F₂.x,
    (e₃ (by decide) (by decide)).trans yval₂, ?_, K.keep.rd.trans F₂.rd, K.keep.wr.trans F₂.wr⟩
  rw [K.flag, y₂, yval₂, F₂.rhs, F₂.tag]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show
    (s₀.mem (s₀.gpr .rsi)).toNat < 2 ^ 64 from Nat.lt_trans (BitVec.isLt _) (by decide))]
  simp only [mask, CompressedAccept, keyRhs, and_assoc]

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (s.gpr .rsi) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi) (c.C.len + 1) =
      s.mem (s.gpr .rsi) :: Spec.Ecdsa.bytesAt s.mem (s.gpr .rsi + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : BaseCfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (hi : (Impl.EcKey.Compressed.X86_64.decompress c).InlineOk = true)
    (hmx : (Impl.EcKey.Compressed.X86_64.decompress c).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.X86_64.decompress c).inline s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hro, hrw, hfit, hwfit⟩ := hs
  have hp : DecompressPre c s :=
    ⟨by rw [hrd]; simp, by rw [hwr]; simp, hpw, hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.X86_64.decompress c).inline s fun s' =>
      (decompressContract c.C root).post s s' ∧ ∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r := by
    apply decompressFront_ok hc hp
    intro g t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega]; simp)
      (by simpa only [Nat.add_comm] using how)
      (by omega) U.saved
      (decide (CompressedAccept c root s)) (by simp only [U.flag, mask, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, _⟩ => ?_
    refine ⟨?_, fun r hr => (hsave r hr).trans (U.original r hr)⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave⟩ := hrun
  have F := (Exec.regions he (Code.noCalls_inline hi)).2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; exact hmx) he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact Exec.gpr (Code.clobbers_rsp_of_inlineOk hi) he
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
    · exact hsave _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrw) (by decide)

end VG.Proof.EcKey.Compressed.X86_64
