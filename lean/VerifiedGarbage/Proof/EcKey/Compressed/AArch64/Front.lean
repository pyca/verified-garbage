module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout

/-! # Reuse signature setup and ECDH's peer and point checks -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64

open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

/-- The encoded public point and the writable working space. -/
structure Pre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .x1, 1 + 2 * c.C.len⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .x2, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .x1, 1 + 2 * c.C.len⟩ ⟨s.gpr .x2, size⟩
  fit : (s.gpr .x2).toNat + size ≤ 2 ^ 64

abbrev keyX (c : Cfg) (s : State) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1 + 1) c.C.len)
abbrev keyY (c : Cfg) (s : State) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
abbrev KeyOk (c : Cfg) (s : State) : Prop :=
  ((s.mem (s.gpr .x1) = 4 ∧ keyX c s < c.C.p) ∧ keyY c s < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s)) (Fin.ofNat c.C.p (keyY c s))

/-- A point-check result and the original callee-saved registers. -/
structure Front (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .x2) size
  saved : Spill.Saved (s₀.gpr .x2) g Cfg.saved s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .x20 = s₀.gpr .x0
  x : sv c (s₀.gpr .x2) s E = keyX c s₀
  y : sv c (s₀.gpr .x2) s QY = keyY c s₀
  flag : word s.mem (s₀.gpr .x2) (c.sl FLAG) = mask (KeyOk c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The wrapper's setup and check, followed by any continuation. -/
theorem front_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : Pre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, Front c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.AArch64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
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
  have F₂ := setup_fixed S
  have hn := S.scr.nowrap
  have out₂ : s₂.gpr .x20 = s₀.gpr .x0 := S.x20.trans (k₁.gpr _ (by decide))
  have hq₂ : s₂.gpr .x6 = s₀.gpr .x1 := (S.keep.gpr _ (by decide)).trans r9
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S.keep.rd, S.keep.wr, rw₁]
  have W₂ : Outside (s₀.gpr .x2) 0 size s₀.mem s₂.mem := by
    rw [← k₁.mem]; exact S.unch.outside (by simp)
  have x₂ : sv c (s₀.gpr .x2) s₂ E = keyX c s₀ := by
    rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.mem]
  refine WP.seq (WP.mono (peer_ok hc S.scr hq₂ (by rw [rw₂]; exact hp.pk) hp.disjoint)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .x2) s₃ i = sv c (s₀.gpr .x2) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have x₃ := (e₃ (i := E) (by decide) (by decide) (by decide)).trans x₂
  have y₃' : sv c (s₀.gpr .x2) s₃ QY = keyY c s₀ := by
    rw [y₃, bytesAt_keep W₂ (hp.disjoint.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have lead₂ : s₂.mem (s₀.gpr .x1) = s₀.mem (s₀.gpr .x1) := by
    have e := keep_of_disjoint' W₂ hp.disjoint (by omega) (i := 0) (by omega) (by omega)
    simpa only [BitVec.add_zero] using e
  have flag₃ : word s₃.mem (s₀.gpr .x2) (c.sl FLAG) = mask (s₀.mem (s₀.gpr .x1) = 4) := by
    rw [f₃, S.flag, BitVec.allOnes_and, lead₂]
  refine WP.seq (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ flag₃) fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, _, _, _, _⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY])
    (by decide)).append fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (s₀.gpr .x2) s₄ i = sv c (s₀.gpr .x2) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have out₄ : s₄.gpr .x20 = s₀.gpr .x0 := by
    rw [g₄ _ (by intro h; exact (by decide : Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h)), k₃.gpr _ (by decide), out₂]
  exact h s₁.gpr s₄ ⟨hs₄, F₄.saved, fun r hr => k₁.gpr r (by revert r; decide),
    out₄, (e₄ (by decide) (by decide) (by decide)).trans x₃,
    (e₄ (by decide) (by decide) (by decide)).trans y₃',
    by simpa only [PeerOk, x₃, y₃', KeyOk] using f₄,
    by rw [rd₄, k₃.rd, S.keep.rd, k₁.rd], by rw [wr₄, k₃.wr, S.keep.wr, k₁.wr]⟩

end VG.Proof.EcKey.Compressed.AArch64
