module

-- separate module: P-384's verification is its only importer, but it builds on both callees' proofs
-- (the windows' and the comb's), which then build in parallel with the rest of its imports

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Window
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombVerified
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Tail
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.CombLit
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulLit
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Check

/-!
# ECDSA verification over P-384 on RISC-V: `[u]G` by the comb and `[v]Q` by windows

`VerifyComb.Cfg.joint p384` leaves in `R` a representative of `[u]G + [v]Q`
(`jointComb_ok`), as the joint ladder's `JointJ.jointJ_ok` does: `[v]Q` by the
call of `vg_p384_mul` (`Window.mul_rv`), `O` instead if `v = 0` (`zeroR_ok`),
moved to `P = (GX : CPX : CPY)`; `[u]G` by the call of `vg_p384_mul_g`
(`Comb.mulG_rv`), with the comb's table, which the first call leaves alone
(`wp_tab`: code without frames changes memory only in its writable regions),
and `O` instead if `u = 0`; then their sum by the complete addition
(`Joint.addPt_ok`). The calls' contracts give their results for scalars in
`[1, n - 1]` and keep the rest of the working space but `b`'s slot, which
`zeroR` sets again.
-/

set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P384.JointComb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Ecdsa.RISCV64.VerifyComb
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W unit mulRVc MC)
open VG.Proof.Ecdsa.RISCV64.P384.Joint (PtOk addPt_ok JPre jSl addW mul_zero')
open VG.Proof.Ecdh.RISCV64.P384 (TailConsts sv_unch sl_eq FL mulKW unch_of_mulKeeps coord_sv point_eq dq
  rep_of_represents wsCallR_ok)
open VG.Proof.Ecdsa.RISCV64.P384.Comb (TabAt)
open VG.Proof.Ecdsa.RISCV64.P384.Window (copyPt_ok)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-- Code without frames keeps the comb's table, apart from the regions it may write. -/
theorem wp_tab {cd : Prog isa} (hn : cd.noFrames = true) {s : State} {base : Addr} {Q : State → Prop}
    (hT : TabAt base s) (hwr : s.wr = [⟨base, 8192⟩]) (h : WP isa cd s Q) :
    WP isa cd s fun s' => Q s' ∧ TabAt base s' := by
  obtain ⟨t, s', he, hq⟩ := h
  obtain ⟨r, -, -, f⟩ := Exec.regions he hn
  exact ⟨t, s', he, hq, hT.of_frame (Exec.syms he) r f (by rw [hwr]; simpa using hT.disj)⟩

/-- `b` in Montgomery's form, as `zeroR` sets it. -/
theorem bp_val : Cfg.mont p384 p384.C.b % 2 ^ (64 * 6) = W.b * 2 ^ 384 % W.p := by decide

/-- What `zeroR` writes. -/
abbrev zW : List (Nat × Nat) :=
  [(p384.sl RX, 48), (p384.sl RY, 48), (p384.sl RZ, 48), (p384.sl BP, 48)]

/-- The slots of `R`, and those of `O`'s coordinates. -/
theorem slR : ∀ i ∈ [RX, RY, RZ, ZERO, ONEP], p384.sl i % 8 = 0 ∧ p384.sl i + 8 * 6 ≤ 4096 := by decide

/-- One coordinate of `R`, at slot `o`, set to the one at slot `b` if the mask
`a7` is all ones (`z`), as it is if it is zero. -/
theorem selR_ok {s : State} {base : Addr} (hw : WsReg s base) (z : Bool)
    (hc : s.gpr .a7 = (if z then BitVec.allOnes 64 else 0)) {o b : Nat}
    (ho : o ∈ [RX, RY, RZ]) (hb : b ∈ [ZERO, ONEP]) :
    WP isa (.block (sel 6 (p384.sl o) (p384.sl o) (p384.sl b))) s fun s' =>
      sv base s' o = (if z then sv base s b else sv base s o) ∧ Rest [.t0, .t1] s s' ∧
      Outside base (p384.sl o) (8 * 6) s.mem s'.mem := by
  have h1 := slR o (by simp at ho ⊢; omega)
  have h2 := slR b (by simp at hb ⊢; omega)
  have hsep : p384.sl o ≤ p384.sl b ∨ p384.sl b + 8 * 6 ≤ p384.sl o := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho hb
    rcases ho with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  exact sel_ok z 6 hw hc h1.1 h1.1 h2.1 h1.2 h1.2 h2.2 (.inl (Nat.le_refl _)) hsep

/-- `R = O` if the number at slot `a` is zero, else `R` as it is, and `b` to `BP`. -/
theorem zeroR_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base) (hz : sv base s ZERO = 0)
    (ho : sv base s ONEP = 1 * 2 ^ 384 % W.p) {a : Nat} (ha : a = UU ∨ a = VV) {P : Point W}
    (hR : sv base s a ≠ 0 → PtOk base s (p384.pt RX RY RZ) P) :
    WP isa (.block (VerifyComb.Cfg.zeroR p384 a)) s fun s' =>
      Rest [.t0, .t1, .t3, .t4, .a7] s s' ∧ Unch base zW s.mem s'.mem ∧
      PtOk base s' (p384.pt RX RY RZ) (if sv base s a = 0 then .infinity else P) ∧
      sv base s' BP = W.b * 2 ^ 384 % W.p := by
  have hp0 : 0 < W.p := by decide
  have hsa : p384.sl a % 8 = 0 ∧ p384.sl a + 8 * 6 ≤ 4096 := by rcases ha with rfl | rfl <;> decide
  rw [VerifyComb.Cfg.zeroR, List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok (n := 6) hw hsa.1 hsa.2) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  generalize hzb : decide (sv base s a = 0) = z
  have hc₁ : s₁.gpr .a7 = (if z then BitVec.allOnes 64 else 0) := by
    rw [k₁, ← hzb]
  have e₁ : ∀ i ∈ [RX, RY, RZ, ZERO, ONEP], sv base s₁ i = sv base s i := fun i _ => by
    show wordsVal s₁.mem _ _ _ = wordsVal s.mem _ _ _; rw [m₁]
  rw [show VerifyComb.Cfg.oPt p384 = p384.pt ZERO ONEP ZERO from rfl, selPt, List.append_assoc,
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
  refine WP.mono (setConst_ok 6 hw₄ (o := p384.sl BP) (x := Cfg.mont p384 p384.C.b) (by decide) (by decide))
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
    have ey : sv base s₅ RY = if z then 1 * 2 ^ 384 % W.p else sv base s RY := by
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
      show Rep W (tmv W 6 base s₅ (p384.sl RX)) (tmv W 6 base s₅ (p384.sl RY)) (tmv W 6 base s₅ (p384.sl RZ)) _
      have t0 : tmv W 6 base s₅ (p384.sl RX) = 0 := by simp only [tmv]; rw [show wordsVal _ _ _ _ = 0 from ex]; exact toM_zero _ _
      have t1 : tmv W 6 base s₅ (p384.sl RY) = 1 := by
        simp only [tmv]; rw [show wordsVal _ _ _ _ = 1 * 2 ^ 384 % W.p from ey]; exact toM_one unit
      have t2 : tmv W 6 base s₅ (p384.sl RZ) = 0 := by simp only [tmv]; rw [show wordsVal _ _ _ _ = 0 from ez]; exact toM_zero _ _
      rw [t0, t1, t2]
      exact rep_infinity' hL
    · rw [ite_eq_right h0]
      have hz' : z = false := by rw [← hzb]; exact decide_eq_false h0
      rw [hz'] at ex ey ez
      simp only [Bool.false_eq_true, ↓reduceIte] at ex ey ez
      exact (hR h0).of_eq ex ey ez

/-! ## The calls -/

/-- The result of a call, as the contracts give it, in `R`'s slots. -/
theorem ptOk_of_result (hL : Law W) {base : Addr} {m : Mem} {s' : State} {k : Nat} {P : Point W}
    (hR : MC.ResultInRange k P base m s'.mem) (h1 : 1 ≤ k) (hn : k < W.n) :
    PtOk base s' (p384.pt RX RY RZ) (mul k P) := by
  obtain ⟨⟨bx, by', bz⟩, hrep⟩ := hR.1 h1 hn
  simp only [Impl.Weierstrass.Point.Curve.pointAt] at bx by' bz hrep
  have c0 : MC.toPoint.coordAt s'.mem base MC.pAt = sv base s' RX := coord_sv _ _ RX
  have c1 : MC.toPoint.coordAt s'.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
    sv base s' RY := coord_sv _ _ RY
  have c2 : MC.toPoint.coordAt s'.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
    sv base s' RZ := coord_sv _ _ RZ
  rw [c0, c1, c2] at hrep
  rw [c0] at bx; rw [c1] at by'; rw [c2] at bz
  rw [dq hL, dq hL, dq hL] at hrep
  exact ⟨rep_of_represents hrep, bx, by', bz⟩

/-- `R = [k]Q` by the call of `vg_p384_mul`, for `k` at `K` and `Q` in `R`'s
first two slots. -/
theorem mulCall_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hc : TailConsts base s) (hx : sv base s RX < W.p) (hy : sv base s RY < W.p) {P : Point W}
    (hP : Point.affine (toM W.p (2 ^ 384) (sv base s RX)) (toM W.p (2 ^ 384) (sv base s RY)) = P)
    (hon : onCurve W P = true) :
    WP isa (Cfg.wsCall "vg_p384_mul" mulP384) s fun s' => Kp s s' ∧
      MC.ResultInRange (sv base s K) P base s.mem s'.mem := by
  refine wsCallR_ok Impl.Ecdsa.RISCV64.mulP384_noFrames (mul_rv hL) hw h3
    (fun t r w a m => ?_) fun s₂' s₂ K₂ mm₂ t a₂ m₂ hp₂ => ⟨K₂, ?_⟩
  · refine ⟨r, by rw [w, a], by rw [a]; exact hw.nowrap, by rw [a]; exact hw.al, ?_, ?_⟩
    · rw [a, m]
      exact ⟨(coord_sv _ _ MP).trans hc.mp, (coord_sv _ _ ZERO).trans hc.zero,
        (coord_sv _ _ ONEP).trans hc.onep, (coord_sv _ _ AP).trans hc.ap, (coord_sv _ _ B3P).trans hc.b3p⟩
    · rw [a, m]
      refine ⟨?_, ?_, ?_⟩
      · show MC.toPoint.coordAt s.mem base (p384.sl RX) < W.p
        rw [coord_sv _ _ RX]; exact hx
      · show MC.toPoint.coordAt s.mem base (p384.sl RY) < W.p
        rw [coord_sv _ _ RY]; exact hy
      rw [point_eq hL]; exact hP ▸ hon
  · have := hp₂
    simp only [mulRVc, State.withRegions_mem] at this
    rw [a₂, m₂, ← mm₂] at this
    have hk : MC.scalar base s.mem = sv base s K := coord_sv _ _ K
    rw [hk, point_eq hL] at this
    exact hP ▸ this

/-- `R = [k]G` by the call of `vg_p384_mul_g`, for `k` at `K`, with the
table its readable region. -/
theorem combCall_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (hc : TailConsts base s)
    (hbp : sv base s BP = W.b * 2 ^ 384 % W.p) (hT : TabAt base s) :
    WP isa (Cfg.wsCall Comb.mulGP384Name Comb.mulGP384) s fun s' => Kp s s' ∧
      MC.ResultInRange (sv base s K) (Spec.Weierstrass.G W) base s.mem s'.mem := by
  rw [Cfg.wsCall]
  refine WP.seq (WP.seq (WP.cons (exec_addi (by decide)) (WP.block_nil ?_)))
  generalize hs₂ : s.write .a0 (s.gpr wb + BitVec.ofInt 64 0) = s₂
  have u₂ : Upd s s₂ .a0 (s.gpr wb + BitVec.ofInt 64 0) := hs₂ ▸ Upd.write _ _ _
  have sy₂ : s₂.syms = s.syms := by rw [← hs₂]; rfl
  have K₂ : Kp s s₂ := Kp.of_upd u₂
  have a0₂ : s₂.gpr .a0 = base := by rw [u₂.gpr, hw.s0]; simp
  have hcov : Covers [⟨base, 8192⟩] s₂.wr := VG.Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.wr]; exact hw.wr
  have htab : Covers [Comb.tabRegion s₂] s₂.rd := VG.Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.rd, Comb.tabRegion, sy₂]; exact hT.rd
  have e0 : (s₂.callEntry.withRegions [Comb.tabRegion s₂] [⟨base, 8192⟩]).gpr .a0 = base := by
    simp only [State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), a0₂]
  have em : (s₂.callEntry.withRegions [Comb.tabRegion s₂] [⟨base, 8192⟩]).mem = s.mem := by
    simp only [State.withRegions_mem, State.callEntry_mem, u₂.mem]
  have esy : (s₂.callEntry.withRegions [Comb.tabRegion s₂] [⟨base, 8192⟩]).syms = s.syms := sy₂
  refine WP.call (Comb.mulG_rv hL) (rd := [Comb.tabRegion s₂]) (wr := [⟨base, 8192⟩]) ?_ (Covers.append htab hcov)
    hcov (fun s₃ r₃ w₃ p₃ _ G₃ _ hp => ?_) Impl.Ecdsa.RISCV64.Comb.mulGP384_noFrames
  · refine ⟨rfl, by rw [e0]; rfl, by rw [e0]; exact hw.nowrap, by rw [e0]; exact hw.al, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, em]
      exact ⟨(coord_sv _ _ MP).trans hc.mp, (coord_sv _ _ ZERO).trans hc.zero,
        (coord_sv _ _ ONEP).trans hc.onep, (coord_sv _ _ AP).trans hc.ap, (coord_sv _ _ B3P).trans hc.b3p⟩
    · rw [e0, em]; exact hbp
    · rw [em, esy]; exact hT.held
    · rw [esy]; exact hT.al
    · rw [esy]; exact hT.fit
    · rw [e0]; simp only [Comb.tabRegion]; rw [esy]; exact hT.disj
  -- `s0` from `s3`.
  refine wp_mv fun s₄ u₄ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₄.rd, r₃, K₂.rd], by rw [u₄.wr, w₃, K₂.wr],
    by rw [u₄.sp, p₃, K₂.sp]⟩, ?_⟩
  · by_cases h : r = .s0
    · subst h; rw [u₄.gpr, G₃ _ (by decide), K₂.gpr _ (by decide), h3, hw.s0]
    · rw [u₄.other _ h, G₃ _ hr, K₂.gpr _ hr]
  · have := hp
    simp only [Comb.mulGRVc, State.withRegions_mem] at this
    rw [e0] at this
    rw [show s₂.callEntry.mem = s.mem by rw [State.callEntry_mem, u₂.mem]] at this
    have hk : MC.scalar base s.mem = sv base s K := coord_sv _ _ K
    rw [hk] at this
    rw [u₄.mem]
    exact this

/-! ## `[u]G + [v]Q` -/

/-- What `joint` writes. -/
abbrev combW : List (Nat × Nat) :=
  [(p384.sl K, 48), (p384.sl RX, 48), (p384.sl RY, 48)] ++ mulKW ++ zW ++
    [(p384.sl GX, 48), (p384.sl CPX, 48), (p384.sl CPY, 48), (p384.sl K, 48)] ++ mulKW ++ zW ++
    addW (p384.pt TX TY TZ) ++ [(p384.sl RX, 48), (p384.sl RY, 48), (p384.sl RZ, 48)]

theorem wsCall_noFrames {f : String} {b : Prog isa} (h : b.noFrames = true) : (Cfg.wsCall f b).noFrames = true := by
  simp only [Cfg.wsCall, Code.noFrames, h, Bool.and_self]

/-- A copy of a number between slots below the flag's. -/
theorem copySl_ok {s : State} {base : Addr} (hw : WsReg s base) {o a : Nat} (ho : o < 44) (ha : a < 44)
    (hsep : p384.sl o ≤ p384.sl a ∨ p384.sl a + 8 * 6 ≤ p384.sl o) :
    WP isa (.block (copy 6 (p384.sl o) (p384.sl a))) s fun s' =>
      sv base s' o = sv base s a ∧ Rest [.t0] s s' ∧ Unch base [(p384.sl o, 48)] s.mem s'.mem := by
  have h1 : p384.sl o % 8 = 0 ∧ p384.sl o + 8 * 6 ≤ 4096 := by rw [sl_eq]; omega
  have h2 : p384.sl a % 8 = 0 ∧ p384.sl a + 8 * 6 ≤ 4096 := by rw [sl_eq]; omega
  exact WP.mono (copy_ok 6 hw h1.1 h2.1 h1.2 h2.2 hsep) fun s' ⟨e, r, O⟩ => ⟨e, r, O.unch⟩

theorem jointComb_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} (hp : JPre base s Q)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hT : TabAt base s) (hwr : s.wr = [⟨base, 8192⟩])
    (hu : sv base s UU < W.n) (hv : sv base s VV < W.n) :
    WP isa (VerifyComb.Cfg.joint p384 "vg_p384_mul" mulP384 Comb.mulGP384Name Comb.mulGP384) s fun s' =>
      Kc s s' ∧ Unch base combW s.mem s'.mem ∧
      PtOk base s' (p384.pt RX RY RZ) (Spec.Weierstrass.add (mul (sv base s UU) (Spec.Weierstrass.G W))
        (mul (sv base s VV) Q)) := by
  have hw := hp.ws
  have hp0 : 0 < W.p := by decide
  rw [VerifyComb.Cfg.joint, show p384.n = 6 from rfl]
  -- `K = v`, `Q` to `R`'s first two slots.
  have B1 : WP isa (.block (copy 6 (p384.sl K) (p384.sl VV) ++ copy 6 (p384.sl RX) (p384.sl CPX) ++
      copy 6 (p384.sl RY) (p384.sl CPY))) s fun s₁ =>
      sv base s₁ K = sv base s VV ∧ sv base s₁ RX = sv base s CPX ∧ sv base s₁ RY = sv base s CPY ∧
      Rest [.t0] s s₁ ∧ Unch base [(p384.sl K, 48), (p384.sl RX, 48), (p384.sl RY, 48)] s.mem s₁.mem := by
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (copySl_ok hw (o := K) (a := VV) (by decide) (by decide) (by decide))
      fun t₁ ⟨k₁, r₁, U₁⟩ => ?_)
    refine WP.block_append (WP.mono (copySl_ok (hw.of_rest r₁) (o := RX) (a := CPX) (by decide) (by decide)
      (by decide)) fun t₂ ⟨x₂, r₂, U₂⟩ => ?_)
    refine WP.mono (copySl_ok ((hw.of_rest r₁).of_rest r₂) (o := RY) (a := CPY) (by decide) (by decide)
      (by decide)) fun t₃ ⟨y₃, r₃, U₃⟩ => ⟨?_, ?_, ?_, r₁.trans (r₂.trans r₃), (U₁.trans U₂).trans U₃⟩
    · exact (sv_unch (U₂.trans U₃) K (by decide)).trans k₁
    · exact ((sv_unch U₃ RX (by decide)).trans x₂).trans (sv_unch U₁ CPX (by decide))
    · exact y₃.trans (sv_unch (U₁.trans U₂) CPY (by decide))
  refine WP.seq (WP.mono (wp_tab rfl hT hwr B1) fun s₁ ⟨⟨k₁, x₁, y₁, r₁, U₁⟩, T₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  have hwr₁ : s₁.wr = [⟨base, 8192⟩] := r₁.wr.trans hwr
  have hc₁ := hc.of_unch U₁ (by decide)
  have eQ : Point.affine (toM W.p (2 ^ 384) (sv base s₁ RX)) (toM W.p (2 ^ 384) (sv base s₁ RY)) = Q := by
    rw [x₁, y₁]; exact hp.q
  -- `[v]Q`.
  refine WP.seq (WP.mono (wp_tab (wsCall_noFrames Impl.Ecdsa.RISCV64.mulP384_noFrames) T₁ hwr₁
    (mulCall_ok hL hw₁ ((r₁.gpr .s3 (by decide)).trans h3) hc₁ (by rw [x₁]; exact hp.qx) (by rw [y₁]; exact hp.qy)
      eQ hp.on)) fun s₂ ⟨⟨K₂, R₂⟩, T₂⟩ => ?_)
  rw [k₁] at R₂
  have U₂ : Unch base mulKW s₁.mem s₂.mem := unch_of_mulKeeps R₂.2
  have hw₂ := hw₁.of_kp K₂
  have hc₂ := hc₁.of_unch U₂ (by decide)
  have v₂ : sv base s₂ VV = sv base s VV := (sv_unch U₂ VV (by decide)).trans (sv_unch U₁ VV (by decide))
  -- `O` if `v = 0`, `P = R`, `K = u`.
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (Comb.WP.mono_syms (zeroR_ok hL hw₂ hc₂.zero hc₂.onep (a := VV) (.inr rfl) (P := mul (sv base s VV) Q)
    (fun h0 => ptOk_of_result hL R₂ (by rw [v₂] at h0; omega) hv)) fun s₃ ⟨r₃, U₃, pR₃, bp₃⟩ sy₃ => ?_))
  rw [v₂] at pR₃
  have pR₃' : PtOk base s₃ (p384.pt RX RY RZ) (mul (sv base s VV) Q) := by
    by_cases h0 : sv base s VV = 0
    · rw [ite_eq_left h0] at pR₃; rw [h0, mul_zero']; exact pR₃
    · rw [ite_eq_right h0] at pR₃; exact pR₃
  have hw₃ := hw₂.of_rest r₃
  rw [WindowA.Cfg.copyPt, show p384.n = 6 from rfl, List.append_assoc, List.append_assoc]
  refine WP.block_append (Comb.WP.mono_syms (copySl_ok hw₃ (o := GX) (a := RX) (by decide) (by decide) (by decide))
    fun t₁ ⟨cx, q₁, V₁⟩ sy₄a => ?_)
  refine WP.block_append (Comb.WP.mono_syms (copySl_ok (hw₃.of_rest q₁) (o := CPX) (a := RY) (by decide) (by decide)
    (by decide)) fun t₂ ⟨cy, q₂, V₂⟩ sy₄b => ?_)
  refine WP.block_append (Comb.WP.mono_syms (copySl_ok ((hw₃.of_rest q₁).of_rest q₂) (o := CPY) (a := RZ) (by decide)
    (by decide) (by decide)) fun s₄ ⟨cz, q₃, V₃⟩ sy₄c => ?_)
  have r₄ : Rest [.t0] s₃ s₄ := q₁.trans (q₂.trans q₃)
  have U₄ : Unch base [(p384.sl GX, 48), (p384.sl CPX, 48), (p384.sl CPY, 48)] s₃.mem s₄.mem :=
    (V₁.trans V₂).trans V₃
  have ex₄ : sv base s₄ GX = sv base s₃ RX :=
    ((sv_unch (V₂.trans V₃) GX (by decide)).trans cx)
  have ey₄ : sv base s₄ CPX = sv base s₃ RY :=
    ((sv_unch V₃ CPX (by decide)).trans cy).trans (sv_unch V₁ RY (by decide))
  have ez₄ : sv base s₄ CPY = sv base s₃ RZ := cz.trans (sv_unch (V₁.trans V₂) RZ (by decide))
  have pP₄ : PtOk base s₄ (p384.pt GX CPX CPY) (mul (sv base s VV) Q) := pR₃'.move ex₄ ey₄ ez₄
  have hw₄ := hw₃.of_rest r₄
  refine Comb.WP.mono_syms (copySl_ok hw₄ (o := K) (a := UU) (by decide) (by decide) (by decide))
    fun s₅ ⟨k₅, r₅, U₅⟩ sy₅ => ?_
  have hw₅ := hw₄.of_rest r₅
  have sy₂₅ : s₅.syms = s₂.syms := by rw [sy₅, sy₄c, sy₄b, sy₄a, sy₃]
  have rd₂₅ : s₅.rd = s₂.rd := by rw [r₅.rd, r₄.rd, r₃.rd]
  have U₃₅ := (U₃.trans U₄).trans U₅
  have T₅ : TabAt base s₅ := T₂.of_unch sy₂₅ rd₂₅ (by decide) U₃₅
  have hc₅ := hc₂.of_unch U₃₅ (by decide)
  have bp₅ : sv base s₅ BP = W.b * 2 ^ 384 % W.p := (sv_unch (U₄.trans U₅) BP (by decide)).trans bp₃
  have uU : sv base s₄ UU = sv base s UU :=
    (sv_unch ((U₁.trans U₂).trans (U₃.trans U₄)) UU (by decide))
  have u₅ : sv base s₅ K = sv base s UU := k₅.trans uU
  have h3₅ : s₅.gpr .s3 = base := by
    rw [r₅.gpr .s3 (by decide), r₄.gpr .s3 (by decide), r₃.gpr .s3 (by decide), K₂.gpr _ (by decide),
      r₁.gpr .s3 (by decide), h3]
  -- `[u]G`.
  refine WP.seq (WP.mono (combCall_ok hL hw₅ h3₅ hc₅ bp₅ T₅) fun s₆ ⟨K₆, R₆⟩ => ?_)
  rw [u₅] at R₆
  have U₆ : Unch base mulKW s₅.mem s₆.mem := unch_of_mulKeeps R₆.2
  have hw₆ := hw₅.of_kp K₆
  have hc₆ := hc₅.of_unch U₆ (by decide)
  have u₆ : sv base s₆ UU = sv base s UU :=
    ((sv_unch (U₅.trans U₆) UU (by decide))).trans uU
  -- `O` if `u = 0`.
  refine WP.seq (WP.mono (zeroR_ok hL hw₆ hc₆.zero hc₆.onep (a := UU) (.inl rfl)
    (P := mul (sv base s UU) (Spec.Weierstrass.G W))
    (fun h0 => ptOk_of_result hL R₆ (by rw [u₆] at h0; omega) hu)) fun s₇ ⟨r₇, U₇, pR₇, bp₇⟩ => ?_)
  rw [u₆] at pR₇
  have pR₇' : PtOk base s₇ (p384.pt RX RY RZ) (mul (sv base s UU) (Spec.Weierstrass.G W)) := by
    by_cases h0 : sv base s UU = 0
    · rw [ite_eq_left h0] at pR₇; rw [h0, mul_zero']; exact pR₇
    · rw [ite_eq_right h0] at pR₇; exact pR₇
  have hw₇ := hw₆.of_rest r₇
  have U₅₇ := (U₅.trans U₆).trans U₇
  have pP₇ : PtOk base s₇ (p384.pt GX CPX CPY) (mul (sv base s VV) Q) :=
    pP₄.of_eq (sv_unch U₅₇ GX (by decide)) (sv_unch U₅₇ CPX (by decide)) (sv_unch U₅₇ CPY (by decide))
  have hc₇ := hc₆.of_unch U₇ (by decide)
  -- `T = R + P`.
  refine WP.seq (WP.mono (addPt_ok hL hw₇ hc₇.ap bp₇ (p := p384.pt RX RY RZ) (q := p384.pt GX CPX CPY)
    (o := p384.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide)
    (hL.onCurve_mul VG.Proof.P384.onCurve_G _) (hL.onCurve_mul hp.on _) pR₇' pP₇) fun s₈ ⟨K₈, U₈, pT₈⟩ => ?_)
  have hw₈ := hw₇.of_kp K₈
  -- `R = T`.
  refine WP.mono (copyPt_ok hw₈ (o := p384.pt RX RY RZ) (p := p384.pt TX TY TZ) (by decide) (by decide)
    (by decide) (by decide)) fun s₉ ⟨ex₉, ey₉, ez₉, r₉, U₉⟩ => ⟨?_, ?_, pT₈.move ex₉ ey₉ ez₉⟩
  · exact (Kc.of_rest r₁).trans (K₂.kc.trans ((Kc.of_rest r₃).trans ((Kc.of_rest r₄).trans ((Kc.of_rest r₅).trans
      (K₆.kc.trans ((Kc.of_rest r₇).trans (K₈.kc.trans (Kc.of_rest r₉))))))))
  · exact (((((((U₁.trans U₂).trans U₃).trans U₄).trans U₅).trans U₆).trans U₇).trans U₈ |>.trans U₉).cover
      (by decide)

end VG.Proof.Ecdsa.RISCV64.P384.JointComb
