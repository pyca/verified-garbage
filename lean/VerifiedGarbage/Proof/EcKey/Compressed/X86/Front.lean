module

public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdh.X86.Validate
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed

/-! ### `EcKey.Compressed.X86.Setup`, which only this module used -/

section

/-! # Shared stack arguments and scratch setup for x86 point conversion -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

structure InputPre (c : Cfg) (len : Nat) (s : State) : Prop where
  pk : (⟨ptr s 1, len⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨ptr s 2, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨ptr s 1, len⟩ ⟨ptr s 2, size⟩
  pk_fit : (arg s 1).toNat + len ≤ 2 ^ 32
  ws_fit : (arg s 2).toNat + size ≤ 2 ^ 32
  args : (⟨argAddr s 0, 12⟩ : Region) ∈ s.rd ++ s.wr
  args_sc : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨ptr s 2, size⟩
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_lo : c.stk ≤ (s.gpr .esp).toNat
  stk_sc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 c.stk, c.stk⟩ ⟨ptr s 2, size⟩

theorem args_idx {i : Nat} (hi : i ∈ Impl.EcKey.Compressed.X86.args.idx) : i < 3 := by
  simp only [Impl.EcKey.Compressed.X86.args, Args.idx, List.mem_cons, List.not_mem_nil, or_false] at hi
  omega_using [hi]

theorem input_setup {c : Cfg} {len : Nat} {s : State}
    (hp : InputPre c len s) (hlen : c.C.len ≤ len) :
    SetupPre c Impl.EcKey.Compressed.X86.args s := by
  have hfit := hp.pk_fit
  have hi : ∀ e, e + 4 ≤ c.C.len → InRegions (s.rd ++ s.wr) (ptr s 1 + BitVec.ofNat 64 e) 4 :=
    fun _ he => ⟨_, hp.pk, Offset.contains_base _ (by omega_using [hlen, he]) (by omega_using [hlen, hfit, he])⟩
  have hd : Region.Disjoint ⟨ptr s 1, c.C.len⟩ ⟨ptr s 2, size⟩ :=
    hp.disjoint.sub_left (by simpa using Region.sub_prefix hlen)
  refine ⟨.inl rfl, hp.ws, ?_, ?_, ?_, hi, hi, hi, hd, hd, hd,
    by change (arg s 1).toNat + c.C.len ≤ 2 ^ 32; have := hp.pk_fit; omega_using [hlen, hfit],
    by change (arg s 1).toNat + c.C.len ≤ 2 ^ 32; have := hp.pk_fit; omega_using [hlen, hfit],
    by change (arg s 1).toNat + c.C.len ≤ 2 ^ 32; have := hp.pk_fit; omega_using [hlen, hfit],
    hp.ws_fit, ?_, hp.sp_lo, hp.stk_sc⟩
  · intro i h
    exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega_using [this]) (args_idx h)⟩
  · intro i h
    exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega_using [this]) (args_idx h))
  · intro i h
    have := args_idx h
    have := hp.sp_fit
    omega_arith
  · exact stkOk_of (Cfg.stk_ge c) hp.sp_lo
      (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := hp.ws_fit; omega_using [])]; exact hp.ws_fit)
      (by decide) hp.stk_sc

theorem setup_fixed {c : Cfg} {s₀ s : State} {base : Addr}
    (P : SetupPost c Impl.EcKey.Compressed.X86.args s₀ base s) : Fixed c base s₀.gpr s.mem :=
  ⟨P.consts (MP, c.C.p) (by simp [Cfg.consts]), P.consts (MN, c.C.n) (by simp [Cfg.consts]),
    P.consts (ZERO, 0) (by simp [Cfg.consts]), P.consts (ONE, 1) (by simp [Cfg.consts]),
    (P.consts (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
    P.consts (AP, c.mont c.C.a) (by simp [Cfg.consts]),
    P.consts (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
    P.consts (GX, c.mont c.C.gx) (by simp [Cfg.consts]),
    P.consts (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
    P.consts (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]),
    P.consts (ONEN, c.R % c.C.n) (by simp [Cfg.consts]), P.saved, P.table⟩

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.Pre`, which the modules that import this one used -/

section

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86

theorem codec_input {c : Cfg} {inputLen outputLen : Nat} {s : State}
    (h : codecPre inputLen outputLen false s) : InputPre c inputLen s := by
  obtain ⟨hrd, hwr, _, _, hpk, _, hargs, _, _, _, hpf, hwf, hsp, hlo, _, hstk⟩ := h
  have lo : c.stk ≤ (s.gpr .esp).toNat := Nat.le_trans (Cfg.stk_le c) hlo
  have stk : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 c.stk, c.stk⟩
      ⟨ptr s 2, size⟩ := by
    have sub := below_le_sub (sp := s.gpr .esp) (Cfg.stk_le c) hlo
    change Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 c.stk).setWidth 64, c.stk⟩
      ⟨((s.gpr .esp) - BitVec.ofNat 32 28).setWidth 64, 28⟩ at sub
    rw [Taint.sub_setWidth lo, Taint.sub_setWidth hlo] at sub
    exact hstk.sub_left sub
  exact ⟨by rw [hrd, hwr]; simp, by rw [hwr]; simp, hpk, hpf, hwf,
    by rw [hrd, hwr]; simp, hargs, hsp, lo, stk⟩

end VG.Proof.EcKey.Compressed.X86

end

end

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
  refine WP.seq (WP.mono (VG.Proof.Ecdsa.X86.setup_ok hc (input_setup hp (by omega_using []))) fun s₂ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.X86.args s₀ (ptr s₀ 2) s₂ at S
  have F₂ := setup_fixed S
  have hn := S.scr.nowrap
  have W₂ : Outside (ptr s₀ 2) 0 size s₀.mem s₂.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (peer_ok hc S.scr (i := 1) (q32 := arg s₀ 1)
    (by
      intro t hesp hrw W
      apply argLoad_ok (s₀ := s₀) (i := 1)
      · exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega_using [this]) (by decide)⟩
      · exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega_using [this]) (by decide))
      · exact hesp.trans (S.keep.1 _ (by decide))
      · rw [hrw, S.keep.2.1, S.keep.2.2]
      · exact W₂.trans W)
    hp.pk_fit (by rw [S.keep.2.1, S.keep.2.2]; exact hp.pk) hd F₂.mp)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₃
  have x₃' : sv c (ptr s₀ 2) s₃ E = keyX c s₀ := by
    rw [x₃]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))) (by decide) (by have := hc.len_hi; omega_using [h7, this])
  have y₃' : sv c (ptr s₀ 2) s₃ QY = keyY c s₀ := by
    rw [y₃]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base _ (d := 1 + c.C.len) (by omega_using [])))
      (by decide) (by have := hc.len_hi; omega_using [h7, this])
  have lead₂ : s₂.mem (ptr s₀ 1) = s₀.mem (ptr s₀ 1) := by
    have e := keep_of_disjoint' W₂ hd (by decide) (i := 0) (by have := hc.len8; omega_using []) (by have := hc.len_hi; omega_using [h7, this])
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
