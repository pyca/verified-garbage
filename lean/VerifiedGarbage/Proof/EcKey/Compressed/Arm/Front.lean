module

public import VerifiedGarbage.Proof.Ecdh.Arm.Validate
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed

import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Arm.Exec
/-! # Reuse ARMv7's existing EC setup and point validation -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/Arm/Setup.lean`, which only this module imported.
section

/-! # Shared input and workspace setup for ARMv7 point conversion -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

 structure InputPre (c : Cfg) (len : Nat) (s : State) : Prop where
  pk : (⟨ptr s .r1, len⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨ptr s .r2, 8192⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨ptr s .r1, len⟩ ⟨ptr s .r2, 8192⟩
  pk_fit : (s.gpr .r1).toNat + len ≤ 2 ^ 32
  ws_fit : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

 theorem input_setup {c : Cfg} {len : Nat} {s : State}
    (hp : InputPre c len s) (hlen : c.C.len ≤ len) :
    SetupPre c Impl.EcKey.Compressed.Arm.args s := by
  change SetupPre c ⟨.r1, .r1, .r1, some .r2, none⟩ s
  have hf := hp.pk_fit
  have hi : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s .r1 + BitVec.ofNat 64 e) 4 := by
    intro e he
    exact ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : Region.Disjoint ⟨ptr s .r1, c.C.len⟩ ⟨ptr s .r2, size⟩ :=
    (hp.disjoint.sub_left (by simpa using Offset.sub_base (ptr s .r1) (d := 0) (by omega : 0 + c.C.len ≤ len))).sub_right
      (by simpa using Offset.sub_base (ptr s .r2) (d := 0) (by decide : size ≤ 8192))
  refine ⟨.inl rfl, by simp [argsOk], ?_, hp.ws, hi, hi, hi, hd, hd, hd,
    by change (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32; omega, by change (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32; omega,
    by change (s.gpr .r1).toNat + c.C.len ≤ 2 ^ 32; omega, hp.ws_fit⟩
  intro h
  cases h

 theorem setup_fixed {c : Cfg} {s₀ s : State} {base : Addr}
    (P : SetupPost c Impl.EcKey.Compressed.Arm.args s₀ base s) : Fixed c base s₀.gpr s.mem :=
  ⟨P.consts (MP, c.C.p) (by simp [Cfg.consts]), P.consts (MN, c.C.n) (by simp [Cfg.consts]),
    P.consts (ZERO, 0) (by simp [Cfg.consts]), P.consts (ONE, 1) (by simp [Cfg.consts]),
    (P.consts (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
    P.consts (AP, c.mont c.C.a) (by simp [Cfg.consts]),
    P.consts (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
    P.consts (GX, c.mont c.C.gx) (by simp [Cfg.consts]),
    P.consts (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
    P.consts (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]),
    P.consts (ONEN, c.R % c.C.n) (by simp [Cfg.consts]), P.saved⟩

end VG.Proof.EcKey.Compressed.Arm
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Ecdh.Arm
open VG.Impl.Ecdh.Arm (QY R2P BP QXM QYM W0 W1 W2 W3 PY)
open VG.Proof.X25519.Arm (Rest)

 abbrev keyX (c : Cfg) (s : State) :=
  Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (ptr s .r1 + 1) c.C.len)
 abbrev keyY (c : Cfg) (s : State) :=
  Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (ptr s .r1 + BitVec.ofNat 64 (1 + c.C.len)) c.C.len)
 abbrev KeyOk (c : Cfg) (s : State) : Prop :=
  ((s.mem (ptr s .r1) = 4 ∧ keyX c s < c.C.p) ∧ keyY c s < c.C.p) ∧
    OnCurve c (Fin.ofNat c.C.p (keyX c s)) (Fin.ofNat c.C.p (keyY c s))

 structure Front (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ .r2) size
  saved : ∀ rd ∈ Cfg.saved, s.mem.readW (off (ptr s₀ .r2) rd.2) 32 = s₀.gpr rd.1
  out : s.gpr .lr = s₀.gpr .r0
  x : sv c (ptr s₀ .r2) s E = keyX c s₀
  y : sv c (ptr s₀ .r2) s QY = keyY c s₀
  flag : flagW c (ptr s₀ .r2) s = mask32 (KeyOk c s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

 theorem front_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + 2 * c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, Front c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.Arm.args))
      (.seq (.block (Impl.Ecdh.Arm.Cfg.peerAt c .r1))
      (.seq (Impl.Ecdh.Arm.Cfg.validate c) rest))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hd : Region.Disjoint ⟨ptr s₀ .r1, 1 + 2 * c.C.len⟩ ⟨ptr s₀ .r2, size⟩ :=
    hp.disjoint.sub_right (by simpa using Offset.sub_base (ptr s₀ .r2) (d := 0) (by decide : 0 + size ≤ 8192))
  refine WP.seq (WP.mono (VG.Proof.Ecdsa.Arm.setup_ok hc (input_setup hp (by omega))) fun s₂ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.Arm.args s₀ (ptr s₀ .r2) s₂ at S
  have F₂ := setup_fixed S
  have hn := S.scr.nowrap
  have r1₂ : s₂.gpr .r1 = s₀.gpr .r1 := S.keep.gpr _ (by decide)
  have W₂ : Outside (ptr s₀ .r2) 0 size s₀.mem s₂.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (peer_ok hc S.scr (q := .r1) (by decide) (by decide)
    (by rw [r1₂]; exact hp.pk_fit)
    (by rw [S.keep.rd, S.keep.wr]; change (⟨State.addr (s₂.gpr .r1), _⟩ : Region) ∈ _
        rw [r1₂]; exact hp.pk)
    (by change Region.Disjoint ⟨State.addr (s₂.gpr .r1), _⟩ _; rw [r1₂]; exact hd) F₂.mp)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₃
  have x₃' : sv c (ptr s₀ .r2) s₃ E = keyX c s₀ := by
    rw [x₃, r1₂]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega))) (by decide) (by have := hc.len_hi; omega)
  have y₃' : sv c (ptr s₀ .r2) s₃ QY = keyY c s₀ := by
    rw [y₃, r1₂]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base _ (d := 1 + c.C.len) (by omega)))
      (by decide) (by have := hc.len_hi; omega)
  have lead₂ : s₂.mem (ptr s₀ .r1) = s₀.mem (ptr s₀ .r1) := by
    have e := keep_of_disjoint' W₂ hd (by decide) (i := 0) (by have := hc.len8; omega) (by have := hc.len_hi; omega)
    simpa only [BitVec.add_zero] using e
  have flag₃ : flagW c (ptr s₀ .r2) s₃ =
      mask32 ((s₀.mem (ptr s₀ .r1) = 4 ∧ keyX c s₀ < c.C.p) ∧ keyY c s₀ < c.C.p) := by
    rw [f₃, S.flag, x₃', y₃']
    change BitVec.allOnes 32 &&& mask32 (s₂.mem (State.addr (s₂.gpr .r1)) = 4) &&& _ &&& _ = _
    rw [r1₂, lead₂, BitVec.allOnes_and, mask32_and, mask32_and]
  refine WP.seq (WP.mono (validate_ok hc hs₃ (S.far.of_rest k₃) F₃ r2₃ bp₃ flag₃)
    fun s₄ ⟨hs₄, k₄, U₄, f₄, _, _, _, _⟩ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slWk h7 (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY])
    (by decide)).append fixedOk_flag) U₄
  have e₄ {i : Nat} (hi : i < 45) (hw : i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY])
      (hf : i ≠ FLAG) : sv c (ptr s₀ .r2) s₄ i = sv c (ptr s₀ .r2) s₃ i :=
    sv_unch U₄ h7 hn hi (apart_append (apart_slWk h7 hi hw) (apart_flag h0 hf))
  exact h s₄ ⟨hs₄, F₄.saved, (k₄.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans S.lr),
    (e₄ (by decide) (by decide) (by decide)).trans x₃',
    (e₄ (by decide) (by decide) (by decide)).trans y₃',
    by simpa only [PeerOk, KeyOk, x₃', y₃'] using f₄,
    by rw [k₄.sp, k₃.sp, S.keep.sp],
    by rw [k₄.rd, k₃.rd, S.keep.rd], by rw [k₄.wr, k₃.wr, S.keep.wr]⟩

end VG.Proof.EcKey.Compressed.Arm
