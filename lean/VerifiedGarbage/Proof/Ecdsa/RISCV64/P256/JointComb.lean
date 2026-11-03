module

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.Window
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Tail
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P256.MulVerified
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# ECDSA verification over P-256 on RISC-V: `[u]G` by the comb and `[v]Q` by windows

`VerifyComb.Cfg.joint p256` leaves in `R` a representative of `[u]G + [v]Q`
(`jointComb_ok`), as the joint ladder's `JointJ.jointJ_ok` does: `[v]Q` by the
call of `vg_p256_mul` (`Window.mul_rv`), `O` instead if `v = 0` (`zeroR_ok`),
moved to `P = (GX : CPX : CPY)`; `[u]G` by the call of `vg_p256_mul_g`
(`Comb.mulG_rv`), with the comb's table, which the first call leaves alone
(`wp_tab`: code without frames changes memory only in its writable regions),
and `O` instead if `u = 0`; then their sum by the complete addition
(`Joint.addPt_ok`). The calls' contracts give their results for scalars in
`[1, n - 1]` and keep the rest of the working space but `b`'s slot, which
`zeroR` sets again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256.JointComb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Ecdsa.RISCV64.VerifyComb
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (W unit)
open VG.Proof.Ecdsa.RISCV64.Joint (PtOk addPt_ok JPre jSl addW mul_zero')
open VG.Proof.Ecdh.RISCV64.P256 (TailConsts sv_unch sl_eq FL mulKW unch_of_mulKeeps coord_sv point_eq dq
  rep_of_represents wsCallR_ok)
open VG.Proof.Ecdsa.RISCV64.Comb (TabAt)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-- The curve as the code has it. -/
abbrev c : Cfg := p256

/-- Code without frames keeps the comb's table, apart from the regions it may write. -/
theorem wp_tab {cd : Prog isa} (hn : cd.noFrames = true) {s : State} {base : Addr} {Q : State → Prop}
    (hT : TabAt base s) (hwr : ∀ r ∈ s.wr, Region.Disjoint (Comb.tabRegion s) r) (h : WP isa cd s Q) :
    WP isa cd s fun s' => Q s' ∧ TabAt base s' := by
  obtain ⟨t, s', he, hq⟩ := h
  obtain ⟨r, -, -, f⟩ := Exec.regions he hn
  exact ⟨t, s', he, hq, hT.of_frame (Exec.syms he) r f hwr⟩

/-- `b` in Montgomery's form, as `zeroR` sets it. -/
theorem bp_val : Cfg.mont p256 p256.C.b % 2 ^ (64 * 4) = W.b * 2 ^ 256 % W.p := by decide

/-- What `zeroR` writes. -/
abbrev zW : List (Nat × Nat) :=
  [(p256.sl RX, 32), (p256.sl RY, 32), (p256.sl RZ, 32), (p256.sl BP, 32)]

/-- The slots of `R`, and those of `O`'s coordinates. -/
theorem slR : ∀ i ∈ [RX, RY, RZ, ZERO, ONEP], p256.sl i % 8 = 0 ∧ p256.sl i + 8 * 4 ≤ 4096 := by decide

/-- One coordinate of `R`, at slot `o`, set to the one at slot `b` if the mask
`a7` is all ones (`z`), as it is if it is zero. -/
theorem selR_ok {s : State} {base : Addr} (hw : WsReg s base) (z : Bool)
    (hc : s.gpr .a7 = (if z then BitVec.allOnes 64 else 0)) {o b : Nat}
    (ho : o ∈ [RX, RY, RZ]) (hb : b ∈ [ZERO, ONEP]) :
    WP isa (.block (sel 4 (p256.sl o) (p256.sl o) (p256.sl b))) s fun s' =>
      sv base s' o = (if z then sv base s b else sv base s o) ∧ Rest [.t0, .t1] s s' ∧
      Outside base (p256.sl o) (8 * 4) s.mem s'.mem := by
  have h1 := slR o (by simp at ho ⊢; omega)
  have h2 := slR b (by simp at hb ⊢; omega)
  have hsep : p256.sl o ≤ p256.sl b ∨ p256.sl b + 8 * 4 ≤ p256.sl o := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hb
    rcases ho with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  exact sel_ok z 4 hw hc h1.1 h1.1 h2.1 h1.2 h1.2 h2.2 (.inl (Nat.le_refl _)) hsep

/-- `R = O` if the number at slot `a` is zero, else `R` as it is, and `b` to `BP`. -/
theorem zeroR_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base) (hz : sv base s ZERO = 0)
    (ho : sv base s ONEP = 1 * 2 ^ 256 % W.p) {a : Nat} (ha : a = UU ∨ a = VV) {P : Point W}
    (hR : sv base s a ≠ 0 → PtOk base s (p256.pt RX RY RZ) P) :
    WP isa (.block (VerifyComb.Cfg.zeroR p256 a)) s fun s' =>
      Rest [.t0, .t1, .t3, .t4, .a7] s s' ∧ Unch base zW s.mem s'.mem ∧
      PtOk base s' (p256.pt RX RY RZ) (if sv base s a = 0 then .infinity else P) ∧
      sv base s' BP = W.b * 2 ^ 256 % W.p := by
  have hp0 : 0 < W.p := by decide
  have hsa : p256.sl a % 8 = 0 ∧ p256.sl a + 8 * 4 ≤ 4096 := by rcases ha with rfl | rfl <;> decide
  rw [VerifyComb.Cfg.zeroR, List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok (n := 4) hw hsa.1 hsa.2) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  generalize hzb : decide (sv base s a = 0) = z
  have hc₁ : s₁.gpr .a7 = (if z then BitVec.allOnes 64 else 0) := by
    rw [k₁, ← hzb]
  have e₁ : ∀ i ∈ [RX, RY, RZ, ZERO, ONEP], sv base s₁ i = sv base s i := fun i _ => by
    show wordsVal s₁.mem _ _ _ = wordsVal s.mem _ _ _; rw [m₁]
  rw [show VerifyComb.Cfg.oPt p256 = p256.pt ZERO ONEP ZERO from rfl, selPt, List.append_assoc,
    List.append_assoc]
  refine WP.block_append (WP.mono (selR_ok hw₁ z hc₁ (o := RX) (b := ZERO) (by simp) (by simp))
    fun s₂ ⟨x₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  have hc₂ : s₂.gpr .a7 = _ := (r₂.gpr .a7 (by decide)).trans hc₁
  refine WP.block_append (WP.mono (selR_ok hw₂ z hc₂ (o := RY) (b := ONEP) (by simp) (by simp))
    fun s₃ ⟨y₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  have hc₃ : s₃.gpr .a7 = _ := (r₃.gpr .a7 (by decide)).trans hc₂
  refine WP.block_append (WP.mono (selR_ok hw₃ z hc₃ (o := RZ) (b := ZERO) (by simp) (by simp))
    fun s₄ ⟨z₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine WP.mono (setConst_ok 4 hw₄ (o := p256.sl BP) (x := Cfg.mont p256 p256.C.b) (by decide) (by decide))
    fun s₅ ⟨r₅, O₅, b₅⟩ => ⟨?_, ?_, ?_, by rw [← bp_val]; exact b₅⟩
  · exact (r₁.mono (ws' := [.t0, .t1, .t3, .t4, .a7]) (by decide)).trans
      ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans ((r₄.mono (by decide)).trans (r₅.mono (by decide)))))
  · rw [← m₁]
    exact (((O₂.unch.trans O₃.unch).trans O₄.unch).trans O₅.unch).mono (by decide)
  · -- Each coordinate, through the later steps.
    have U₂₅ := ((O₃.unch.trans O₄.unch).trans O₅.unch)
    have U₃₅ := (O₄.unch.trans O₅.unch)
    have fx : sv base s₅ RX = sv base s₂ RX := sv_unch U₂₅ RX (by decide)
    have fy : sv base s₅ RY = sv base s₃ RY := sv_unch U₃₅ RY (by decide)
    have fz : sv base s₅ RZ = sv base s₄ RZ := sv_unch O₅.unch RZ (by decide)
    have gy : sv base s₂ RY = sv base s₁ RY := sv_unch O₂.unch RY (by decide)
    have gz : sv base s₃ RZ = sv base s₁ RZ := sv_unch (O₂.unch.trans O₃.unch) RZ (by decide)
    have g0 : sv base s₂ ZERO = sv base s₁ ZERO := sv_unch O₂.unch ZERO (by decide)
    have g1 : sv base s₂ ONEP = sv base s₁ ONEP := sv_unch O₂.unch ONEP (by decide)
    have g0' : sv base s₃ ZERO = sv base s₁ ZERO := sv_unch (O₂.unch.trans O₃.unch) ZERO (by decide)
    have ex : sv base s₅ RX = if z then 0 else sv base s RX := by
      rw [fx, x₂, e₁ ZERO (by simp), e₁ RX (by simp), hz]
    have ey : sv base s₅ RY = if z then 1 * 2 ^ 256 % W.p else sv base s RY := by
      rw [fy, y₃, g1, gy, e₁ ONEP (by simp), e₁ RY (by simp), ho]
    have ez : sv base s₅ RZ = if z then 0 else sv base s RZ := by
      rw [fz, z₄, g0', gz, e₁ ZERO (by simp), e₁ RZ (by simp), hz]
    by_cases h0 : sv base s a = 0
    · rw [ite_eq_left h0]
      have hz' : z = true := by rw [← hzb]; exact decide_eq_true h0
      rw [hz'] at ex ey ez
      simp only [↓reduceIte] at ex ey ez
      refine ⟨?_, by show sv base s₅ RX < W.p; rw [ex]; exact hp0,
        by show sv base s₅ RY < W.p; rw [ey]; exact Nat.mod_lt _ hp0,
        by show sv base s₅ RZ < W.p; rw [ez]; exact hp0⟩
      show Rep W (tmv W 4 base s₅ (p256.sl RX)) (tmv W 4 base s₅ (p256.sl RY)) (tmv W 4 base s₅ (p256.sl RZ)) _
      have t0 : tmv W 4 base s₅ (p256.sl RX) = 0 := by simp only [tmv]; rw [show wordsVal _ _ _ _ = 0 from ex]; exact toM_zero _ _
      have t1 : tmv W 4 base s₅ (p256.sl RY) = 1 := by
        simp only [tmv]; rw [show wordsVal _ _ _ _ = 1 * 2 ^ 256 % W.p from ey]; exact toM_one unit
      have t2 : tmv W 4 base s₅ (p256.sl RZ) = 0 := by simp only [tmv]; rw [show wordsVal _ _ _ _ = 0 from ez]; exact toM_zero _ _
      rw [t0, t1, t2]
      exact rep_infinity' hL
    · rw [ite_eq_right h0]
      have hz' : z = false := by rw [← hzb]; exact decide_eq_false h0
      rw [hz'] at ex ey ez
      simp only [Bool.false_eq_true, ↓reduceIte] at ex ey ez
      exact (hR h0).of_eq ex ey ez

end VG.Proof.Ecdsa.RISCV64.P256.JointComb
