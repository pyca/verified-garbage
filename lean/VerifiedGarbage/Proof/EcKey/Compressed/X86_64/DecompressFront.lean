module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Start
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Rhs
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed

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
