module

import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Setup
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
public import VerifiedGarbage.Proof.Ecdh.X86_64.Validate
import VerifiedGarbage.Proof.Ecdh.X86_64.Check
import VerifiedGarbage.Proof.Ecdsa.X86_64.Setup

/-! # Reuse signature setup and ECDH's peer and point checks -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64
open VG.Proof.Ecdsa.Verify.X86_64 (KeyOk keyX keyY)
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

/-- The encoded public point and the writable working space. -/
structure Pre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .rdi, 1 + 2 * c.C.len⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .rsi, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .rdi, 1 + 2 * c.C.len⟩ ⟨s.gpr .rsi, size⟩
  fit : (s.gpr .rsi).toNat + size ≤ 2 ^ 64

/-- What signature setup already proves about its constants and saves. -/
theorem setup_fixed {c : Cfg} {s₀ s : State} {base : Addr}
    (P : SetupPost c none s₀ base s) : Fixed c base s₀.gpr s.mem :=
  ⟨P.consts (MP, c.C.p) (by simp [Cfg.consts]), P.consts (MN, c.C.n) (by simp [Cfg.consts]),
    P.consts (ZERO, 0) (by simp [Cfg.consts]), P.consts (ONE, 1) (by simp [Cfg.consts]),
    (P.consts (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
    P.consts (AP, c.mont c.C.a) (by simp [Cfg.consts]),
    P.consts (B3P, c.mont (3 * c.C.b)) (by simp [Cfg.consts]),
    P.consts (GX, c.mont c.C.gx) (by simp [Cfg.consts]),
    P.consts (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
    P.consts (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]),
    P.consts (ONEN, c.R % c.C.n) (by simp [Cfg.consts]), P.saved⟩

/-- A point-check result and the original callee-saved registers. -/
structure Front (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rsi) size
  saved : Spill.Saved s.mem (s₀.gpr .rsi) g Cfg.saved
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  flag : word s.mem (s₀.gpr .rsi) (c.sl FLAG) = mask (KeyOk c s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The wrapper's setup and check, followed by any continuation. -/
theorem front_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : Pre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, Front c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Validate.X86_64.args)
      (.seq (.block (c.setupWith none))
      (.seq (.block (Impl.Ecdh.X86_64.Cfg.peer c))
      (.seq (Impl.Ecdh.X86_64.Cfg.check c).inline rest)))) s₀ Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  have hsp : SetupPre c s₁ := by
    have hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
    have hd : Region.Disjoint ⟨s₀.gpr .rdi + 1, c.C.len⟩ ⟨s₀.gpr .rsi, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega))
    exact ⟨by rw [k₁.2.2.2, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  have F₂ := setup_fixed S
  have hn := S.scr.nowrap
  have hq₂ : s₂.gpr .r9 = s₀.gpr .rdi := (S.keep.gpr _ (by decide)).trans r9
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [S.keep.rd, S.keep.wr, rw₁]
  have W₂ : Outside (s₀.gpr .rsi) 0 size s₀.mem s₂.mem := by
    rw [← k₁.2.1]; exact S.unch.outside (by simp)
  have x₂ : sv c (s₀.gpr .rsi) s₂ E = keyX c s₀ := by
    rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.2.1]
    rfl
  refine WP.seq (WP.mono (peer_ok hc S.scr hq₂ (by rw [rw₂]; exact hp.pk) hp.disjoint)
    fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, y₃, f₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn ((fixedOk_slW (l := [R2P, BP, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, QY] → i ≠ FLAG →
      sv c (s₀.gpr .rsi) s₃ i = sv c (s₀.gpr .rsi) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have x₃ := (e₃ (i := E) (by decide) (by decide) (by decide)).trans x₂
  have y₃' : sv c (s₀.gpr .rsi) s₃ QY = keyY c s₀ := by
    rw [y₃, bytesAt_keep W₂ (hp.disjoint.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have lead₂ : s₂.mem (s₀.gpr .rdi) = s₀.mem (s₀.gpr .rdi) := by
    have e := keep_of_disjoint' W₂ hp.disjoint (by omega) (i := 0) (by omega) (by omega)
    simpa only [BitVec.add_zero] using e
  have flag₃ : word s₃.mem (s₀.gpr .rsi) (c.sl FLAG) = mask (s₀.mem (s₀.gpr .rdi) = 4) := by
    rw [f₃, S.flag, BitVec.allOnes_and, lead₂]
  refine WP.seq (WP.mono (check_ok hc hs₃ F₃.mp F₃.ap r2₃ bp₃ flag₃) fun s₄ C₄ => ?_)
  have F₄ := F₃.unch h7 hn ((fixedOk_slW (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY])
    (by decide)).append fixedOk_flag) C₄.unch
  exact h s₁.gpr s₄ ⟨C₄.scr, F₄.saved, fun r hr => k₁.1 r (by revert r; decide),
    by simpa only [CheckOk, PeerOk, x₃, y₃', KeyOk] using C₄.flag,
    by rw [C₄.rd, k₃.rd, S.keep.rd, k₁.2.2.1], by rw [C₄.wr, k₃.wr, S.keep.wr, k₁.2.2.2]⟩

end VG.Proof.EcKey.Validate.X86_64
