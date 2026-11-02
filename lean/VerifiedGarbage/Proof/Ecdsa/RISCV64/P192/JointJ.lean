module

-- separate module: P-192's verification is its only importer, but it builds on both
-- the joint ladder's proofs and the windows', which its importers need not re-check

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyJ
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Joint
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.Window
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Ecdh.RISCV64.Masks

/-!
# ECDSA verification over P-192 on RISC-V: the joint ladder with Jacobian doublings

`VerifyJ.Cfg.joint p192 dblJ` leaves in `R` a representative of
`[u]G + [v]Q` (`jointJ_ok`), as the joint ladder of `Joint.lean` does: the same
table (`Joint.build_ok`) and window entries (`Joint.select_ok`), and each step's
`T = 4 R` by two Jacobian doublings for `a = -3` (`quad2_ok`, from the windows' `toJ`, `dblJ`
and `fromJ`, `Window.lean`) before `R = T + E`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192.JointJ

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P192 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Joint
open VG.Proof.Ecdsa.RISCV64.P192.Joint (PtOk addPt_ok keepU JPre JTab select_ok build_ok)
open VG.Proof.Ecdsa.RISCV64.P192.Window (wS wLay wShort S3 quadW quadWl KC dblStep_ok toJStep_ok
  dblJ_apart_DT dblJ_apart_TD)
open VG.Proof.Ecdsa.RISCV64.P192.Window (d2)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point Fe mul onCurve)

/-- The curve as the code has it. -/
abbrev c : Cfg := p192

theorem fromJT_apart : RcbApart S3 (c.pt DX DY DZ) (WindowA.Cfg.zeroPt c) (c.pt TX TY TZ) := ⟨by decide, by decide⟩

/-- `D` back in projective coordinates in `T`. -/
theorem fromJTStep_ok {base : Addr} {s : State} {V : List Nat} {E : Nat → Fe W}
    (hI : Inv 4 base W.p wS V E s) (hV : ∀ x ∈ rcbR S3 (c.pt DX DY DZ) (WindowA.Cfg.zeroPt c), x ∈ V) :
    WP isa (fprog p192Field (fromJ S3 (c.pt DX DY DZ) (WindowA.Cfg.zeroPt c) (c.pt TX TY TZ))) s fun s' =>
      KeepR 4 base (rcbW S3 (c.pt TX TY TZ)) s s' ∧
      ∃ E', Inv 4 base W.p wS ([c.sl TX, c.sl TY, c.sl TZ] ++ V) E' s' ∧
        (E' (c.sl TX), E' (c.sl TY), E' (c.sl TZ)) =
          (E (c.sl DX) * E (c.sl DZ), E (c.sl DY) + E (c.sl ZERO),
            E (c.sl DZ) * E (c.sl DZ) * E (c.sl DZ)) ∧
        ∀ x, x ∉ rcbW S3 (c.pt TX TY TZ) → E' x = E x := by
  rw [fromJ_eq]
  refine WP.mono (ofN_ok (F := p192Field) field_ok rfl wLay wShort unit fromJN_ok fromJT_apart (by decide) hI hV)
    fun s' ⟨k, I, v, kp⟩ => ⟨k, _, I, v.trans (fromJN_run _), kp⟩

/-- `T = 4 R`, for `R` representing `P`. -/
theorem quad2_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base) (hK : KC base s) {P : Point W}
    (hP : onCurve W P = true) (hR : PtOk base s (c.pt RX RY RZ) P) :
    WP isa (VerifyJ.Cfg.quad2 c dblJ) s fun s' => Kp s s' ∧ Unch base quadW s.mem s'.mem ∧
      PtOk base s' (c.pt TX TY TZ) (d2 (d2 P)) := by
  have hp0 : 0 < W.p := by decide
  have hn := hw.nowrap
  rw [VerifyJ.Cfg.quad2, VerifyJ.Cfg.jSlots_am3 _ rfl]
  simp only [progs]
  -- The start: `a`, `b`, zero and `R`.
  have hI : Inv 4 base W.p wS [c.sl AP, c.sl 40, c.sl ZERO, c.sl RX, c.sl RY, c.sl RZ]
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, by decide, fun x hx => ?_, fun x _ => rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK.ap]; exact Nat.mod_lt _ hp0
    · rw [hK.bp]; exact Nat.mod_lt _ hp0
    · rw [hK.zero]; exact hp0
    exacts [hR.x, hR.y, hR.z]
  have e0 : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (c.sl ZERO) 4) = 0 := by
    rw [hK.zero]; exact toM_zero _ _
  -- To Jacobian coordinates.
  refine WP.seq (WP.mono (toJStep_ok hL hI (by decide) hR.rep e0) fun s₁ ⟨k₁, E₁, I₁, J₁, p₁⟩ => ?_)
  -- Two doublings.
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_DT (by decide) I₁ (by decide) hP J₁)
    fun s₂ ⟨k₂, E₂, I₂, J₂, p₂⟩ => ?_)
  refine WP.seq (WP.mono (dblStep_ok hL dblJ_apart_TD (by decide) I₂ (by decide) (hL.onCurve_add hP hP) J₂)
    fun s₃ ⟨k₃, E₃, I₃, J₃, p₃⟩ => ?_)
  -- Back to projective coordinates, in `T`.
  refine WP.seq (WP.mono (fromJTStep_ok I₃ (by decide)) fun s₆ ⟨k₆, E₆, I₆, v₆, p₆⟩ => ?_)
  have z₅ : E₃ (c.sl ZERO) = 0 := by
    rw [p₃ _ (by decide), p₂ _ (by decide), p₁ _ (by decide)]; exact e0
  simp only [Prod.mk.injEq] at v₆
  obtain ⟨vx, vy, vz⟩ := v₆
  rw [z₅, Lean.Grind.AddCommMonoid.add_zero] at vy
  have hw₆ := I₆.ws
  have hn₆ := hw₆.nowrap
  have ltx := I₆.lt (c.sl TX) (by decide)
  have lty := I₆.lt (c.sl TY) (by decide)
  have ltz := I₆.lt (c.sl TZ) (by decide)
  have vx' : tmv W 4 base s₆ (c.sl TX) = E₆ (c.sl TX) := I₆.val (c.sl TX) (by decide)
  have vy' : tmv W 4 base s₆ (c.sl TY) = E₆ (c.sl TY) := I₆.val (c.sl TY) (by decide)
  have vz' : tmv W 4 base s₆ (c.sl TZ) = E₆ (c.sl TZ) := I₆.val (c.sl TZ) (by decide)
  -- `Y = 1` where `Z = 0`.
  have KK : KeepR 4 base quadWl s s₆ :=
    (((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans (k₆.mono (by decide))))
  have UK : Unch base (quadWl.map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]) s.mem s₆.mem := KK.mem
  have onep₆ : wordsVal s₆.mem base (c.sl ONEP) 4 = 2 ^ 256 % W.p := by
    rw [UK.wordsVal (by decide) (by decide)]; exact hK.onep
  refine WP.block_append (WP.mono (zeroMask_ok hw₆ (n := 4) (a := c.sl TZ) (by decide) (by decide))
    fun s₇ ⟨r₇, m₇, a7₇⟩ => ?_)
  have hw₇ := hw₆.of_rest r₇
  refine WP.mono (sel_ok (decide (wordsVal s₆.mem base (c.sl TZ) 4 = 0)) 4 hw₇ a7₇
    (o := c.sl TY) (a := c.sl TY) (b := c.sl ONEP) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (Nat.le_refl _)) (by decide)) fun s₈ ⟨e₈, r₈, O₈⟩ => ?_
  rw [m₇] at e₈ O₈
  have ex : wordsVal s₈.mem base (c.sl TX) 4 = wordsVal s₆.mem base (c.sl TX) 4 :=
    O₈.wordsVal (by decide) (by decide)
  have ez : wordsVal s₈.mem base (c.sl TZ) 4 = wordsVal s₆.mem base (c.sl TZ) 4 :=
    O₈.wordsVal (by decide) (by decide)
  have hZ : (wordsVal s₆.mem base (c.sl TZ) 4 = 0) ↔ E₃ (c.sl DZ) = 0 := by
    rw [← toM_eq_zero_iff unit ltz]
    show tmv W 4 base s₆ (c.sl TZ) = 0 ↔ _
    rw [vz', vz]
    exact ⟨fun h => by_contra fun hz => cube_ne_zero hL hz h, fun h => by rw [h]; grind⟩
  have hrep := InvJ.out hL J₃
  refine ⟨KK.kp.trans ((Kp.of_rest r₇).trans (Kp.of_rest r₈)), (UK.trans O₈.unch).cover (by decide), ⟨?_, ?_, ?_, ?_⟩⟩
  · show Rep W (tmv W 4 base s₈ (c.sl TX)) (tmv W 4 base s₈ (c.sl TY)) (tmv W 4 base s₈ (c.sl TZ)) _
    simp only [tmv]
    rw [ex, ez]
    show Rep W (tmv W 4 base s₆ (c.sl TX)) _ (tmv W 4 base s₆ (c.sl TZ)) _
    rw [vx', vz', vx, vz, e₈]
    by_cases h0 : E₃ (c.sl DZ) = 0
    · have hc : decide (wordsVal s₆.mem base (c.sl TZ) 4 = 0) = true := decide_eq_true (hZ.mpr h0)
      have h0' : E₃ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₃ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₃ (c.pt DX DY DZ).y) = 1 from
        by simp [h0']] at hrep
      simp only [hc, ↓reduceIte]
      rw [onep₆, toM_one unit]
      exact hrep
    · have hc : decide (wordsVal s₆.mem base (c.sl TZ) 4 = 0) = false :=
        decide_eq_false fun h => h0 (hZ.mp h)
      have h0' : ¬E₃ (c.pt DX DY DZ).z = 0 := h0
      rw [show (if E₃ (c.pt DX DY DZ).z = 0 then (1 : Fe W) else E₃ (c.pt DX DY DZ).y) =
        E₃ (c.pt DX DY DZ).y from by simp [h0']] at hrep
      simp only [hc, ↓reduceIte, Bool.false_eq_true]
      show Rep W _ (tmv W 4 base s₆ (c.sl TY)) _ _
      rw [vy', vy]
      exact hrep
  · show wordsVal s₈.mem base (c.sl TX) 4 < W.p
    rw [ex]; exact ltx
  · show wordsVal s₈.mem base (c.sl TY) 4 < W.p
    rw [e₈]; split
    · rw [onep₆]; exact Nat.mod_lt _ (by decide)
    · exact lty
  · show wordsVal s₈.mem base (c.sl TZ) 4 < W.p
    rw [ez]; exact ltz


/-! ## The steps -/

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure LPre (base : Addr) (s₀ : State) (G Q : Point W) (u v : Nat) : Prop where
  ap : wordsVal s₀.mem base (p192.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s₀.mem base (p192.sl BP) 4 = W.b * 2 ^ 256 % W.p
  zero : wordsVal s₀.mem base (p192.sl ZERO) 4 = 0
  onep : wordsVal s₀.mem base (p192.sl ONEP) 4 = 2 ^ 256 % W.p
  uu : wordsVal s₀.mem base (p192.sl UU) 4 = u
  vv : wordsVal s₀.mem base (p192.sl VV) 4 = v
  tab : JTab base s₀ G Q
  g : onCurve W G = true
  q : onCurve W Q = true

/-- What the steps write. -/
abbrev stepW : List (Nat × Nat) := [(512, 480), (1920, 96), (3840, 256)]

/-- The loop's invariant at `s1 = j`: `R` represents `[u >>> 2 j]G + [v >>> 2 j]Q`. -/
structure LInv (base : Addr) (s₀ s : State) (G Q : Point W) (u v j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (p192.pt RX RY RZ) (jp G Q u v j)

/-- A step: from `[u >>> 2 j]G + [v >>> 2 j]Q` to `[u >>> 2 (j - 1)]G + [v >>> 2 (j - 1)]Q`. -/
theorem stepJ_ok (hL : Law W) {base : Addr} {s₀ : State} {G Q : Point W} {u v : Nat} (hP : LPre base s₀ G Q u v)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 128) {s : State} (hI : LInv base s₀ s G Q u v j) :
    WP isa (VerifyJ.Cfg.step p192 dblJ) s fun s' => LInv base s₀ s' G Q u v (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → (d + 32 ≤ 3840 ∨ 2048 ≤ d) → d + 32 ≤ 3584 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 h4 =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hT : JTab base s G Q := hP.tab.of_eq fun d h1 h2 => uS d (by omega) (by omega) (.inr h1) h2
  rw [VerifyJ.Cfg.step]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr (hT.of_eq fun d _ _ => by rw [u₁.mem]))
    fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, uS _ (by decide) (by decide) (by decide) (by decide), uS _ (by decide) (by decide) (by decide) (by decide), hP.uu, hP.vv] at pE
  rw [u₁.mem] at O₂
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → (d + 32 ≤ 3840 ∨ 2048 ≤ d) → d + 32 ≤ 3584 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 h4 => by
    rw [O₂.wordsVal (by omega) (by omega), uS d h1 h2 h3 h4]
  have pR₂ : PtOk base s₂ (p192.pt RX RY RZ) (jp G Q u v j) :=
    hI.rep.of_eq (O₂.wordsVal (by decide) (by decide)) (O₂.wordsVal (by decide) (by decide))
      (O₂.wordsVal (by decide) (by decide))
  have ap₂ : wordsVal s₂.mem base (p192.sl AP) 4 = W.a * 2 ^ 256 % W.p := by
    rw [e₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hP.ap
  have bp₂ : wordsVal s₂.mem base (p192.sl BP) 4 = W.b * 2 ^ 256 % W.p := by
    rw [e₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hP.bp
  have hX := ent_curve hL hP.g hP.q (u >>> (2 * j)) (v >>> (2 * j))
  have hD := hL.onCurve_add hX hX
  have hT4 := hL.onCurve_add hD hD
  have hE := ent_curve hL hP.g hP.q ((u >>> (2 * (j - 1))) % 4) ((v >>> (2 * (j - 1))) % 4)
  have hK₂ : KC base s₂ :=
    ⟨ap₂, bp₂, by rw [e₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hP.zero,
      by rw [e₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hP.onep⟩
  -- `T = 4 R`.
  refine WP.seq (WP.mono (quad2_ok hL hw₂ hK₂ hX pR₂) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₂.of_kp K₄
  have k₄ : ∀ d ∈ [p192.sl AP, p192.sl BP, p192.sl p192.EX, p192.sl p192.EY, p192.sl p192.EZ],
      wordsVal s₄.mem base d 4 = wordsVal s₂.mem base d 4 := fun d hd =>
    U₄.wordsVal (fun w hw => by
      have := (by decide : ∀ d ∈ [p192.sl AP, p192.sl BP, p192.sl p192.EX, p192.sl p192.EY,
        p192.sl p192.EZ], ∀ w ∈ quadW, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) d hd w hw
      exact this) (by have := (by decide : ∀ d ∈ [p192.sl AP, p192.sl BP, p192.sl p192.EX,
        p192.sl p192.EY, p192.sl p192.EZ], d < 2048) d hd; omega)
  have pE₄ := pE.of_eq (k₄ _ (by decide)) (k₄ _ (by decide)) (k₄ _ (by decide))
  -- `R = T + E`.
  refine WP.mono (addPt_ok hL hw₄ ((k₄ _ (by decide)).trans ap₂) ((k₄ _ (by decide)).trans bp₂)
    (p := p192.pt TX TY TZ) (q := p192.pt p192.EX p192.EY p192.EZ) (o := p192.pt RX RY RZ) ⟨by decide, by decide⟩ (by decide)
    hT4 hE pT pE₄) fun s₅ ⟨K₅, U₅, pR₅⟩ => ?_
  refine ⟨hw₄.of_kp K₅, ?_, ?_, ?_, ?_⟩
  · rw [K₅.gpr _ (by decide), K₄.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₄.kc.trans K₅.kc)
  · exact (((hI.unch.trans (show Unch base [(1920, 96)] s.mem s₂.mem from O₂.unch)).trans U₄).trans
      U₅).cover (by decide)
  · have e := jstep hL hP.g hP.q u v (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pR₅

/-! ## The joint ladder -/

/-- What `joint` writes. -/
abbrev jointW : List (Nat × Nat) := [(512, 480), (1536, 480), (2048, 1536), (3840, 256)]

/-- `R = [u]G + [v]Q`, for `u` and `v` in their slots and `Q` in the check's. -/
theorem jointJ_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} (hp : JPre base s Q) :
    WP isa (VerifyJ.Cfg.joint p192 dblJ) s fun s' => Kc s s' ∧ Unch base jointW s.mem s'.mem ∧
      PtOk base s' (p192.pt RX RY RZ) (Spec.Weierstrass.add (mul (wordsVal s.mem base (p192.sl UU) 4)
        (Spec.Weierstrass.G W)) (mul (wordsVal s.mem base (p192.sl VV) 4) Q)) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [VerifyJ.Cfg.joint]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, T₁⟩ => ?_)
  have hw₁ := hp.ws.of_kp K₁
  have e₁ : ∀ d ∈ [p192.sl ZERO, p192.sl ONEP, p192.sl AP, p192.sl BP, p192.sl UU, p192.sl VV],
      wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 := keepU U₁ (by decide)
  rw [show p192.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy_ok 4 hw₁ (o := p192.sl RX) (a := p192.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, r₂, O₂⟩ => ?_))
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 4 hw₂ (o := p192.sl RY) (a := p192.sl ONEP) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨y₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (copy_ok 4 hw₃ (o := p192.sl RZ) (a := p192.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨z₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine wp_li (imm := 128) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have r₅ : Rest [.t0, .s1] s₁ s₅ :=
    ((r₂.trans (r₃.trans r₄)).mono (by decide)).trans (u₅.rest (by decide))
  have hw₅ : WsReg s₅ base := hw₄.of_kc (Kc.of_rest (u₅.rest (ws := [.s1]) (by decide)))
  have U₅ : Unch base [(512, 96)] s₁.mem s₅.mem := by
    rw [u₅.mem]
    exact ((O₂.unch.trans O₃.unch).trans O₄.unch).cover (by decide)
  have e₅ : ∀ d ∈ [p192.sl ZERO, p192.sl ONEP, p192.sl AP, p192.sl BP, p192.sl UU, p192.sl VV],
      wordsVal s₅.mem base d 4 = wordsVal s.mem base d 4 := fun d hd =>
    (keepU U₅ (D := [p192.sl ZERO, p192.sl ONEP, p192.sl AP, p192.sl BP, p192.sl UU, p192.sl VV]) (by decide) d hd).trans
      (e₁ d hd)
  have T₅ : JTab base s₅ (Spec.Weierstrass.G W) Q := T₁.of_eq fun d h1 h2 => U₅.wordsVal (by simp; omega) (by omega)
  -- The start: `R = O`.
  generalize hu : wordsVal s.mem base (p192.sl UU) 4 = u
  generalize hv : wordsVal s.mem base (p192.sl VV) 4 = v
  have hu' : u < 2 ^ 256 := hu ▸ wordsVal_lt _ _ _ _
  have hv' : v < 2 ^ 256 := hv ▸ wordsVal_lt _ _ _ _
  have hP : LPre base s₅ (Spec.Weierstrass.G W) Q u v :=
    ⟨(e₅ _ (by decide)).trans hp.ap, (e₅ _ (by decide)).trans hp.bp, (e₅ _ (by decide)).trans hp.zero,
      by rw [e₅ _ (by decide), hp.onep, Nat.one_mul], (e₅ _ (by decide)).trans hu,
      (e₅ _ (by decide)).trans hv, T₅, VG.Proof.P192.onCurve_G, hp.on⟩
  have rx : wordsVal s₅.mem base (p192.sl RX) 4 = 0 := by
    rw [u₅.mem, O₄.wordsVal (by decide) (by decide), O₃.wordsVal (by decide) (by decide), x₂,
      e₁ _ (by decide), hp.zero]
  have ry : wordsVal s₅.mem base (p192.sl RY) 4 = 1 * 2 ^ 256 % W.p := by
    rw [u₅.mem, O₄.wordsVal (by decide) (by decide), y₃, O₂.wordsVal (by decide) (by decide),
      e₁ _ (by decide), hp.onep]
  have rz : wordsVal s₅.mem base (p192.sl RZ) 4 = 0 := by
    rw [u₅.mem, z₄, O₃.wordsVal (by decide) (by decide), O₂.wordsVal (by decide) (by decide),
      e₁ _ (by decide), hp.zero]
  have hI : LInv base s₅ s₅ (Spec.Weierstrass.G W) Q u v 128 := by
    refine ⟨hw₅, u₅.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [jp_top (n := 4) _ _ hu' hv']
      show Rep W (tmv W 4 base s₅ (p192.sl RX)) (tmv W 4 base s₅ (p192.sl RY)) (tmv W 4 base s₅ (p192.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (p192.sl RX) 4 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (p192.sl RY) 4 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p192.sl RZ) 4 < _; rw [rz]; exact hp0
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => LInv base s₅ s' (Spec.Weierstrass.G W) Q u v j) (n := 128)
    (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => stepJ_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest r₅)).trans hi.keep, ((U₁.trans U₅).trans hi.unch).cover (by decide), ?_⟩
  rw [← jp_zero]
  exact hi.rep

end VG.Proof.Ecdsa.RISCV64.P192.JointJ
