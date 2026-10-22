module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Setup
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdh.X86.Validate
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.X86.Exec

/-! # Reuse 32-bit x86's existing EC setup and point validation -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Ecdh.X86
open VG.Impl.Ecdh.X86 (QY R2P BP QXM QYM W0 W1 W2 W3 PY)


 abbrev keyX (c : Cfg) (s : State) :=
  Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (ptr s 1 + 1) c.C.len)
 abbrev keyY (c : Cfg) (s : State) :=
  Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (ptr s 1 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
 abbrev KeyOk (c : Cfg) (s : State) : Prop :=
  ((s.mem (ptr s 1) = 4 ∧ keyX c s < c.C.p) ∧ keyY c s < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s)) (Fin.ofNat c.C.p (keyY c s))

 structure Front (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ 2) size
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off (ptr s₀ 2) rd.2) 32 = s₀.gpr rd.1
  x : sv c (ptr s₀ 2) s E = keyX c s₀
  y : sv c (ptr s₀ 2) s QY = keyY c s₀
  flag : flagW c (ptr s₀ 2) s = mask32 (KeyOk c s₀)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

 theorem front_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + 2 * c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, Front c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
      (.seq (.block (Impl.Ecdh.X86.Cfg.peerAt c 1))
      (.seq (Impl.Ecdh.X86.Cfg.validate c) rest))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hd : Region.Disjoint ⟨ptr s₀ 1, 1 + 2 * c.C.len⟩ ⟨ptr s₀ 2, size⟩ :=
    hp.disjoint
  refine WP.seq (WP.mono (VG.Proof.Ecdsa.X86.setup_ok hc (input_setup hp (by omega))) fun s₂ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.X86.args s₀ (ptr s₀ 2) s₂ at S
  have F₂ := setup_fixed S
  have hn := S.scr.nowrap
  have W₂ : Outside (ptr s₀ 2) 0 size s₀.mem s₂.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (peer_ok hc S.scr (i := 1) (q32 := arg s₀ 1)
    (by
      intro t hesp hrw W
      apply argLoad_ok (s₀ := s₀) (i := 1)
      · exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega) (by decide)⟩
      · exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega) (by decide))
      · exact hesp.trans (S.keep.1 _ (by decide))
      · rw [hrw, S.keep.2.1, S.keep.2.2]
      · exact W₂.trans W)
    hp.pk_fit (by rw [S.keep.2.1, S.keep.2.2]; exact hp.pk) hd F₂.mp)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₃
  have x₃' : sv c (ptr s₀ 2) s₃ E = keyX c s₀ := by
    rw [x₃]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega))) (by decide) (by have := hc.len_hi; omega)
  have y₃' : sv c (ptr s₀ 2) s₃ QY = keyY c s₀ := by
    rw [y₃]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base _ (d := 1 + c.C.len) (by omega)))
      (by decide) (by have := hc.len_hi; omega)
  have lead₂ : s₂.mem (ptr s₀ 1) = s₀.mem (ptr s₀ 1) := by
    have e := keep_of_disjoint' W₂ hd (by decide) (i := 0) (by have := hc.len8; omega) (by have := hc.len_hi; omega)
    simpa only [BitVec.add_zero] using e
  have flag₃ : flagW c (ptr s₀ 2) s₃ =
      mask32 ((s₀.mem (ptr s₀ 1) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) := by
    rw [f₃, S.flag, x₃', y₃']
    change BitVec.allOnes 32 &&& mask32 (s₂.mem (ptr s₀ 1) = 4) &&& _ &&& _ = _
    rw [lead₂, BitVec.allOnes_and, mask32_and, mask32_and]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ flag₃)
    fun s₄ ⟨hs₄, k₄, rd₄, wr₄, U₄, f₄, _, _, _, _⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slWk (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY])
    (by decide)).append fixedOk_flag) U₄
  have e₄ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY])
      (hf : i ≠ FLAG) : sv c (ptr s₀ 2) s₄ i = sv c (ptr s₀ 2) s₃ i :=
    sv_unch U₄ h7 hn hi (apart_append (apart_slWk hi hw) (apart_flag h0 hf))
  exact h s₄ ⟨hs₄, F₄.saved,
    (e₄ (by decide) (by decide) (by decide)).trans x₃',
    (e₄ (by decide) (by decide) (by decide)).trans y₃',
    by simpa only [PeerOk, KeyOk, x₃', y₃'] using f₄,
    (k₄ _ (by decide)).trans ((k₃.1 _ (by decide)).trans (S.keep.1 _ (by decide))),
    rd₄.trans (k₃.2.1.trans S.keep.2.1), wr₄.trans (k₃.2.2.trans S.keep.2.2)⟩

end VG.Proof.EcKey.Compressed.X86
