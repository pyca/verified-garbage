module

public import VerifiedGarbage.Proof.Ecdh.X86_64.Validate
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer

/-!
# ECDH and verification on x86-64: the check of the public point

`checkBody` checks `x < p` and `y < p` (`checkLts_ok`) and runs `validate`
(`validate_ok`): `checkBody_ok`. `check` runs it inline or as
`vg_<curve>_check_point`, between copying the callee-saved registers into
`xmm0`–`xmm5` and back (`check_ok`, of the code with its calls inlined).
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Impl.Ecdh.X86_64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- `x < p` and `y < p`: the flag `&=` their masks. -/
theorem checkLts_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.checkLtP c (c.sl E) ++ Impl.Ecdh.X86_64.Cfg.checkLtP c (c.sl QY))) s
      fun s' => Scr s' base size ∧ KeepRegs [.rax, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem ∧
        word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&& mask (sv c base s E < c.C.p) &&&
          mask (sv c base s QY < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (checkLtP_ok c hs h0 (sl_le c h7 (i := E) (by decide)) (sl_le c h7 (i := MP) (by decide)) hF)
    fun s₁ ⟨f₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (checkLtP_ok c hs₁ h0 (sl_le c h7 (i := QY) (by decide)) (sl_le c h7 (i := MP) (by decide)) hF)
    fun s₂ ⟨f₂, k₂, O₂⟩ => ⟨hs₁.of_keepRegs k₂ (by decide), k₁.trans k₂, O₁.trans O₂, ?_⟩
  rw [f₂, f₁, sv_flag O₁ h0 h7 hn (i := QY) (by decide) (by decide),
    sv_flag O₁ h0 h7 hn (i := MP) (by decide) (by decide), show wordsVal s.mem base (c.sl MP) c.n = c.C.p from hmp]

/-- The public point passes, as `checkBody` checks it from the flag `P₀`:
`x < p`, `y < p` and the curve's equation. -/
abbrev CheckOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)

/-- What `checkBody` leaves, from `s` with the flag `mask P₀`, writing no
register but those of `K`. -/
structure CheckPost (c : Cfg) (K : List Reg) (base : Addr) (P₀ : Prop) [Decidable P₀] (s s' : State) :
    Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ K → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem
  flag : word s'.mem base (c.sl FLAG) = mask (CheckOk c base s P₀)
  qxm : sv c base s' QXM = sv c base s E * 2 ^ (64 * c.n) % c.C.p
  qym : sv c base s' QYM = sv c base s QY * 2 ^ (64 * c.n) % c.C.p
  px : sv c base s' PX = (if CheckOk c base s P₀ then sv c base s E * 2 ^ (64 * c.n) % c.C.p
    else sv c base s GX)
  py : sv c base s' PY = (if CheckOk c base s P₀ then sv c base s QY * 2 ^ (64 * c.n) % c.C.p
    else sv c base s GY)

/-- `checkBody`, from `p` and `a R mod p` in their slots, the constants
`peer` sets and the flag a mask: the flag `&=` the mask of the point's
validity, `x R mod p` and `y R mod p`, and the point the scalar
multiplication takes. -/
theorem checkBody_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.X86_64.Cfg.checkBody c) s (CheckPost c (clob c.n) base P₀ s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  refine WP.seq (WP.mono (checkLts_ok hc hs hmp) fun s₁ ⟨hs₁, k₁, O₁, f₁⟩ => ?_)
  have e₁ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₁ i = sv c base s i := fun hi hf =>
    sv_flag O₁ h0 h7 hn hi hf
  refine WP.mono (validate_ok hc hs₁ (by rw [e₁ (by decide) (by decide)]; exact hmp)
    (by rw [e₁ (by decide) (by decide)]; exact hap) (by rw [e₁ (by decide) (by decide)]; exact hr2)
    (by rw [e₁ (by decide) (by decide)]; exact hbp)
    (P₀ := (P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) (by rw [f₁, hf, mask_and, mask_and]))
    fun s' ⟨hs', g', rd', wr', U', f', qx, qy, px, py⟩ => ?_
  have eE : sv c base s₁ E = sv c base s E := e₁ (by decide) (by decide)
  have eY : sv c base s₁ QY = sv c base s QY := e₁ (by decide) (by decide)
  have eGX : sv c base s₁ GX = sv c base s GX := e₁ (by decide) (by decide)
  have eGY : sv c base s₁ GY = sv c base s GY := e₁ (by decide) (by decide)
  refine ⟨hs', fun r hr => ?_, by rw [rd', k₁.rd], by rw [wr', k₁.wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g' r hr, k₁.gpr r (fun h => hr (by simp at h; rcases h with rfl | rfl <;> simp [clob]))]
  · exact O₁.unch.trans U' |>.mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_right _ (by simpa using hw)
      · exact hw
  · rw [f']; simp only [PeerOk, eE, eY]
  · rw [qx, eE]
  · rw [qy, eY]
  · rw [px]; simp only [PeerOk, eE, eY, eGX]
  · rw [py]; simp only [PeerOk, eE, eY, eGY]

theorem checkBody_inline (c : Cfg) :
    (Impl.Ecdh.X86_64.Cfg.checkBody c).inline = Impl.Ecdh.X86_64.Cfg.checkBody c := by
  show Code.seq _ (Impl.Ecdh.X86_64.Cfg.validate c).inline = _
  rw [Impl.Ecdh.X86_64.Cfg.validate, blocks_inline]; rfl

/-- The registers `check` may write: `checkBody`'s, and the callee-saved
registers, which the function copies into `xmm` registers and back. -/
def checkClob (n : Nat) : List Reg := clob n ++ Cfg.invKeptX.map Prod.fst

/-- `vg_<curve>_check_point`: `checkBody` between copying the callee-saved
registers into `xmm0`–`xmm5` and back. -/
theorem checkFn_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody c)) s (CheckPost c (checkClob c.n) base P₀ s) := by
  have hK : ∀ r, r ∉ checkClob c.n → r ∉ clob c.n := fun r hr h => hr (List.mem_append_left _ h)
  refine WP.seq (WP.mono (savesX_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  have e₁ : ∀ i, sv c base s₁ i = sv c base s i := fun i => by simp only [sv, m₁]
  refine WP.seq (WP.mono (checkBody_ok hc hs₁ (by rw [e₁]; exact hmp) (by rw [e₁]; exact hap)
    (by rw [e₁]; exact hr2) (by rw [e₁]; exact hbp) (P₀ := P₀) (by rw [m₁]; exact hf)) fun s₂ h₂ => ?_)
  refine WP.mono (restoresX_ok s₂) fun s' ⟨g', m', rd', wr'⟩ => ?_
  have e' : ∀ i, sv c base s' i = sv c base s₂ i := fun i => by simp only [sv, m']
  have ok : CheckOk c base s₁ P₀ ↔ CheckOk c base s P₀ := by simp only [CheckOk, PeerOk, e₁]
  refine ⟨⟨by rw [g' .rdi (by decide)]; exact h₂.scr.rdi, by rw [wr']; exact h₂.scr.wr, hs.nowrap⟩,
    fun r hr => ?_, by rw [rd', h₂.rd, rd₁], by rw [wr', h₂.wr, wr₁], by rw [m', ← m₁]; exact h₂.unch,
    by rw [m', h₂.flag]; simp only [mask, ok], ?_, ?_, ?_, ?_⟩
  · rw [g' r (fun h => hr (List.mem_append_right _ h)), h₂.gpr r (hK r hr), g₁]
  · rw [e', h₂.qxm, e₁]
  · rw [e', h₂.qym, e₁]
  · rw [e', h₂.px]; simp only [CheckOk, PeerOk, e₁]
  · rw [e', h₂.py]; simp only [CheckOk, PeerOk, e₁]

/-- `check`, with its call inlined: `checkBody`, or `checkBody` between
copying the callee-saved registers into `xmm0`–`xmm5` and back. -/
theorem check_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.X86_64.Cfg.check c).inline s (CheckPost c (checkClob c.n) base P₀ s) := by
  have hK : ∀ r, r ∉ checkClob c.n → r ∉ clob c.n := fun r hr h => hr (List.mem_append_left _ h)
  unfold Impl.Ecdh.X86_64.Cfg.check
  cases c.checkPoint with
  | none =>
    rw [checkBody_inline]
    exact WP.mono (checkBody_ok hc hs hmp hap hr2 hbp hf) fun s' h =>
      { h with gpr := fun r hr => h.gpr r (hK r hr) }
  | some C =>
    show WP isa (Code.seq _ (Code.seq (Impl.Ecdh.X86_64.Cfg.checkBody c).inline _)) s _
    rw [checkBody_inline]
    exact checkFn_ok hc hs hmp hap hr2 hbp hf

theorem rsi_not_checkClob (n : Nat) : Reg.rsi ∉ checkClob n := fun h => by
  rcases List.mem_append.mp h with h | h
  · exact rsi_not_clob n h
  · revert h; decide

/-- `CheckPost` with `G` where the caller keeps it (`Fixed`): the point for
the scalar multiplication, below `p`, standing for the public point if it
passes, else for `G`. -/
theorem CheckPost.point (hc : BaseCfgOk c) {K : List Reg} {base : Addr} {P₀ : Prop} [Decidable P₀]
    {s s' : State} (h : CheckPost c K base P₀ s s') {g : Reg → BitVec 64} (F : Fixed c base g s.mem) :
    sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if CheckOk c base s P₀ then Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if CheckOk c base s P₀ then Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  have hp3 := hc.p_ge
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hlt : ∀ x, x * 2 ^ (64 * c.n) % c.C.p < c.C.p := fun x => Nat.mod_lt _ (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.px]; split
    · exact hlt _
    · exact lt_of_eq_of_lt F.gx (hmont _)
  · rw [h.py]; split
    · exact hlt _
    · exact lt_of_eq_of_lt F.gy (hmont _)
  · rw [h.px]; split
    · exact toM_mont hpR
    · show toM _ _ (wordsVal s.mem base (c.sl GX) c.n) = _
      rw [F.gx, toM_cmont hc]
  · rw [h.py]; split
    · exact toM_mont hpR
    · show toM _ _ (wordsVal s.mem base (c.sl GY) c.n) = _
      rw [F.gy, toM_cmont hc]

end VG.Proof.Ecdh.X86_64
