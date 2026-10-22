module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Rhs
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Framework.Offset

/-! # Prepare the curve polynomial and retain the input checks on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP W2)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (ptr s 1) = 2 ∨ s.mem (ptr s 1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ 2) size
  fixed : Fixed c (ptr s₀ 2) s₀.gpr s.mem
  x : sv c (ptr s₀ 2) s E = keyX c s₀
  tag : s.mem.readW (off (ptr s₀ 2) (c.sl D)) 32 = (s₀.mem (ptr s₀ 1)).setWidth 32
  r2 : sv c (ptr s₀ 2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (ptr s₀ 2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : flagW c (ptr s₀ 2) s = mask32 (CompressedPrefix c s₀)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem DecompressFront.frame {c : Cfg} (hc : CfgOk c) {s₀ s t : State}
    (F : DecompressFront c s₀ s) (K : Keeps powClob s t)
    {W : List (Nat × Nat)} (U : Unch (ptr s₀ 2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (ptr s₀ 2) t i = sv c (ptr s₀ 2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      t.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 = s.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 :=
    Unch.readW32 U (fun w hw => by have := ha i hm w hw; omega)
      (by have := sl_le c h7 hi; omega)
  refine ⟨F.scr.of_keeps K (by decide), F.fixed.unch h7 hn hW U,
     (e (by decide) (by simp)).trans F.x,
    (ew (by decide) (by simp)).trans F.tag, (e (by decide) (by simp)).trans F.r2,
    ?_, ?_, ?_, (K.1 _ (by decide)).trans F.esp, K.2.1.trans F.rd, K.2.2.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs
  · rw [flagW, ew (by decide) (by simp), ← flagW]; exact F.flag

theorem decompressFront_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, DecompressFront c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
      (.seq (.block (Impl.EcKey.Compressed.X86.decompressPeer c))
      (.seq (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)) rest))) s₀ Q := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hd : Region.Disjoint ⟨ptr s₀ 1, 1 + c.C.len⟩ ⟨ptr s₀ 2, size⟩ :=
    hp.disjoint
  refine WP.seq (WP.mono (setup_ok hc (input_setup hp (by omega))) fun s₁ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.X86.args s₀ (ptr s₀ 2) s₁ at S
  have F₁ := setup_fixed S
  have hn := S.scr.nowrap
  have W₁ : Outside (ptr s₀ 2) 0 size s₀.mem s₁.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr (q32 := arg s₀ 1)
    (by
      intro t hesp hrw W
      apply argLoad_ok (s₀ := s₀) (i := 1)
      · exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega) (by decide)⟩
      · exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega) (by decide))
      · exact hesp.trans (S.keep.1 _ (by decide))
      · rw [hrw, S.keep.2.1, S.keep.2.2]
      · exact W₁.trans W)
    hp.pk_fit (by rw [S.keep.2.1, S.keep.2.2]; exact hp.pk) hd F₁.mp S.flag)
    fun s₂ ⟨hs₂, K₂, U₂, r2₂, bp₂, x₂, tag₂, flag₂⟩ => ?_)
  have F₂ := F₁.unch h7 hn (fixedOk_slW (l := [R2P, BP, E, D, FLAG]) (by decide)) U₂
  have lead : s₁.mem (ptr s₀ 1) = s₀.mem (ptr s₀ 1) := by
    have e := keep_of_disjoint' W₁ hd (by decide) (i := 0) (by omega) (by have := hc.len_hi; omega)
    simpa only [BitVec.add_zero] using e
  have x₂' : sv c (ptr s₀ 2) s₂ E = keyX c s₀ := by
    rw [x₂]
    congr 1
    exact bytesAt_keep W₁ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega))) (by decide)
      (by have := hc.len_hi; omega)
  rw [lead] at tag₂ flag₂
  refine WP.seq (WP.mono (rhs_ok hc hs₂ (modP_of hc F₂.mp) r2₂ F₂.ap bp₂)
    fun s₃ R => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slWk (l := [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1,
    W2, Impl.Ecdh.X86.W3, TMP]) (by decide)) R.unch
  have e {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1, W2, Impl.Ecdh.X86.W3, TMP]) :
      sv c (ptr s₀ 2) s₃ i = sv c (ptr s₀ 2) s₂ i :=
    sv_unch R.unch h7 hn hi (apart_slWk hi hw)
  have ew {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1, W2, Impl.Ecdh.X86.W3, TMP]) :
      s₃.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 = s₂.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 :=
    Unch.readW32 R.unch (fun w hw' => by have := (apart_slWk hi hw h7) w hw'; omega)
      (by have := sl_le c h7 hi; omega)
  apply h s₃
  refine ⟨R.scr, F₃,
    (e (by decide) (by decide)).trans x₂', (ew (by decide) (by decide)).trans tag₂,
    (e (by decide) (by decide)).trans r2₂, R.lt, ?_, ?_,
    (R.rest.1 _ (by decide)).trans ((K₂.1 _ (by decide)).trans (S.keep.1 _ (by decide))),
    R.rd.trans (K₂.2.1.trans S.keep.2.1), R.wr.trans (K₂.2.2.trans S.keep.2.2)⟩
  · simpa only [x₂'] using R.val
  · rw [flagW, ew (by decide) (by decide), ← flagW, flag₂, x₂']

end VG.Proof.EcKey.Compressed.X86
