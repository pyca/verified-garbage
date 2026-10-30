module

public import VerifiedGarbage.Proof.Ed25519.Arm.CombSelect
public import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.AccumulateStep
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.WindowNibble
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Proof.X25519.Field

/-!
# The ARMv7 comb's loop

After the selection, slots 4–6 hold the entry's coordinates (`sel_env`); `combNeg` negates it
for a negative digit, and `addAffineOps` adds it to the accumulator exactly as the
specification's `pointAdd` (`mixedResult_eq`). After step `j` of the loop, the accumulator
(slots 0–3) represents `[17 G + Σ_{i < j} d_i 16^i]B` (`digitSum64`); after the 64 steps, the
scalar's multiple (`comb64_total`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519 VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm VG.Proof.Ed25519 Edwards

theorem maskB_eq (b : Bool) : maskB b = 0 - BitVec.ofNat 32 b.toNat := by cases b <;> decide

theorem magOf_eq (n : Nat) : magOf n = mag n := rfl

/-! ## Limbs and slots -/

theorem val16_digits16 (v : Nat) : ∀ n, val16 (fun k => v / 2 ^ (16 * k) % 2 ^ 16) n = v % 2 ^ (16 * n)
  | 0 => by simp [val16, Nat.mod_one]
  | n + 1 => by
    rw [val16_succ, val16_digits16 v n, show 16 * (n + 1) = 16 * n + 16 by omega, Nat.pow_add,
      Nat.mod_mul]

/-- The selected entry's coordinate `c` in slot `4 + c`, with limbs below `2¹⁶`. -/
theorem sel_env {m : Mem} {b : BitVec 32} {i a : Nat}
    (h : ∀ q < 48, wd m (State.addr b) (320 + 4 * q) = selLimb i a (q / 16) (q % 16))
    (sl : Slot) (c : Nat) (hc : c < 3) (hs : sl.val = 4 + c) :
    env m b sl = combCoord (combCached64 i a) c ∧ Lim m (State.addr b) (offset sl) := by
  have hl : ∀ k < 16, limb m (State.addr b) (offset sl) k = selLimb i a c k := fun k hk => by
    have e := h (16 * c + k) (by omega)
    rw [show (16 * c + k) / 16 = c by omega, show (16 * c + k) % 16 = k by omega,
      show 320 + 4 * (16 * c + k) = offset sl + 4 * k by simp only [offset, hs]; omega] at e
    exact e
  refine ⟨?_, fun k hk => by rw [hl k hk]; exact selLimb_lt _ _ _ _⟩
  have hv : V m (State.addr b) (offset sl) = (combCoord (combCached64 i a) c).val := by
    rw [V, val16_congr hl]
    unfold selLimb
    rw [val16_digits16, Nat.mod_eq_of_lt (Nat.lt_trans (combCoord (combCached64 i a) c).isLt (by decide))]
  simp only [env, FS, hv, VG.Proof.X25519.toFe_self]

/-- The slots apart from `R` are as they were. -/
theorem env_frame {m m' : Mem} {b : BitVec 32} {R : Region} (hf : Frame [R] m m') (sl : Slot)
    (hd : ∀ k < 16, (⟨State.addr b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint R) :
    env m' b sl = env m b sl ∧ (Lim m (State.addr b) (offset sl) → Lim m' (State.addr b) (offset sl)) := by
  have hl : ∀ k < 16, limb m' (State.addr b) (offset sl) k = limb m (State.addr b) (offset sl) k :=
    fun k hk => wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact hd k hk
  exact ⟨by simp only [env, FS, V, val16_congr hl], fun h k hk => by rw [hl k hk]; exact h k hk⟩

/-- The region `[d, d + n)` of the workspace is apart from slot `sl` unless they meet. -/
theorem slot_apart {b : BitVec 32} (sl : Slot) {d n : Nat} (h : d + n ≤ offset sl ∨ offset sl + 64 ≤ d)
    (hn : d + n ≤ 8192) :
    ∀ k < 16, (⟨State.addr b + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint
      ⟨State.addr b + BitVec.ofNat 64 d, n⟩ := fun k hk =>
  Offset.disjoint _ (by omega) (by simp only [offset] at h ⊢; have := sl.isLt; omega) (by omega)

/-- Nibble `i` of the scalar's bytes is the decoded scalar's. -/
theorem nibAt_eq (m : Mem) (p : Addr) {i : Nat} (hi : i < 64) :
    nibAt m p i = nib (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32)) i := by
  rw [nib, decodeLE_nibble, nibbleOf, nibAt]
  have hg : (Spec.Ed25519.bytesAt m p 32).getD (i / 2) 0 = m (p + BitVec.ofNat 64 (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < 32 by omega]
  rw [hg]
  have := (m (p + BitVec.ofNat 64 (i / 2))).isLt
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, ite_eq_right (by decide), pow_zero, Nat.div_one]
  · rw [h, ite_eq_left rfl, pow_one]; omega

/-! ## The addition -/

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addAffineOps_formula (e : Env) :
    point (evalOps addAffineOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) :=
  rfl

/-! ## The step -/

/-- The regions a step writes: the sign's mask and the field area. -/
abbrev stepRegions (b : BitVec 32) : List Region := [⟨State.addr b + BitVec.ofNat 64 56, 4⟩, FA b]

/-- What the loop never changes: where the scalar's copy is, and the tables. -/
structure CombEnv (s₀ : State) (b p T : BitVec 32) : Prop where
  hp : b + BitVec.ofNat 32 SCAL = p
  fit : p.toNat + 32 ≤ 2 ^ 32
  readable : ∀ k < 32, InRegions (s₀.rd ++ s₀.wr) (State.addr p + BitVec.ofNat 64 k) 1
  sep : ∀ r ∈ stepRegions b, (⟨State.addr p, 32⟩ : Region).Disjoint r
  tbl : TblAt s₀ T
  apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (b p T : BitVec 32) (S : Nat) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  ctx : Ctx b s
  r11 : s.gpr .r11 = BitVec.ofNat 32 j
  lim : AllLim s.mem b
  zero : env s.mem b 21 = 0
  acc : Rep (point (env s.mem b) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S j) • baseAff)
  keep : PointKeep b s₀ s
  scalar : S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr p) 32)
  syms : s.syms combSym = T

theorem stepRegions_keep {b : BitVec 32} {s t : State} (hr : Rest powersClob s t)
    (hf : Frame (stepRegions b) s.mem t.mem) : PointKeep b s t :=
  ⟨hr, hf.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by decide) (by decide)
    · exact Offset.sub _ (by decide) (by decide)⟩⟩

theorem stepRegions_ws {b : BitVec 32} {m m' : Mem} (hf : Frame (stepRegions b) m m') :
    Frame [⟨State.addr b, 8192⟩] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩

private theorem next_fact : ∀ j < 64, BitVec.ofNat 32 j + (1 : BitVec 32) = BitVec.ofNat 32 (j + 1) ∧
    (BitVec.ofNat 32 (j + 1) - (64 : BitVec 32) == 0) = decide (j + 1 = 64) := by decide

private theorem slot_cases : ∀ sl : Slot, sl.val = 4 ∨ sl.val = 5 ∨ sl.val = 6 ∨
    sl.val < 4 ∨ 7 ≤ sl.val := by decide

private theorem swap_low : ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) →
    swapSlot 4 5 true (swapSlot 6 7 true i) = i := by decide

/-- The negation's exchanges leave the slots outside 4–7 alone. -/
theorem swapNeg_low (sw : Bool) (e : Env) (i : Slot) (hi : i.val < 4 ∨ 8 ≤ i.val) :
    swapEnvs [(4, 5), (6, 7)] sw e i = e i := by
  cases sw
  · rfl
  · exact congrArg e (swap_low i hi)

theorem swapNeg_vals (sw : Bool) (e : Env) :
    swapEnvs [(4, 5), (6, 7)] sw e 4 = (if sw then e 5 else e 4) ∧
      swapEnvs [(4, 5), (6, 7)] sw e 5 = (if sw then e 4 else e 5) ∧
      swapEnvs [(4, 5), (6, 7)] sw e 6 = (if sw then e 7 else e 6) := by
  cases sw <;> exact ⟨rfl, rfl, rfl⟩

theorem combStep_ok {s₀ s : State} {b p T : BitVec 32} {S j : Nat} (E : CombEnv s₀ b p T)
    (h : CombInv s₀ b p T S j s) (hj : j < 64) :
    WP isa combStep s fun t => isa.eval .ne t = some (decide (j + 1 ≠ 64)) ∧
      CombInv s₀ b p T S (j + 1) t := by
  suffices H : WP isa combStep s fun t => t.syms = s.syms →
      isa.eval .ne t = some (decide (j + 1 ≠ 64)) ∧ CombInv s₀ b p T S (j + 1) t from
    WP.mono_syms H fun t k hs => k hs
  have nf := next_fact j hj
  have n_lt := nibAt_lt s.mem (State.addr p) j
  -- The scalar and the tables, as at the start.
  have ws₀ : Frame [⟨State.addr b, 8192⟩] s₀.mem s.mem := h.keep.frame.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by
      simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.keep.rest.rd, h.keep.rest.wr]
  have hT : TblAt s T := E.tbl.of_frame hrr ws₀ (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  have hnib : nibAt s.mem (State.addr p) j = nib S j := by rw [nibAt_eq _ _ hj, ← h.scalar]
  -- The digit and the selection.
  rw [combStep]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (combDigit_ok h.ctx hj E.hp h.r11 E.fit (by rw [hrr]; exact E.readable _ (by omega)))
    fun u ⟨ru, mu, _, _, gm⟩ syu => ?_
  have fu : Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have cu := h.ctx.of_rest ru (by decide)
  have hTu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr])
    (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (show 56 + 4 ≤ 8192 by decide)⟩)
    (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  refine WP.mono (combSelect_ok (a := magOf (nibAt s.mem (State.addr p) j)) cu hj
    (magOf_le n_lt) ((ru.gpr _ (by decide)).trans h.r11) gm hTu (by rw [syu]; exact h.syms) E.apart)
    fun v ⟨rv, fv, lv⟩ => ?_
  -- The slots after the selection.
  have envu : ∀ sl : Slot, env u.mem b sl = env s.mem b sl ∧ Lim u.mem (State.addr b) (offset sl) := fun sl =>
    let e := env_frame fu sl (slot_apart sl (by have := sl.isLt; simp only [offset]; omega) (by decide))
    ⟨e.1, e.2 (h.lim sl)⟩
  have envv : ∀ sl : Slot, (sl.val < 4 ∨ 7 ≤ sl.val) → env v.mem b sl = env s.mem b sl ∧
      Lim v.mem (State.addr b) (offset sl) := fun sl hs => by
    have e := env_frame fv sl (slot_apart sl (by simp only [offset]; have := sl.isLt; omega) (by decide))
    exact ⟨e.1.trans (envu sl).1, e.2 (envu sl).2⟩
  have ent : ∀ c < 3, ∀ sl : Slot, sl.val = 4 + c →
      env v.mem b sl = combCoord (combCached64 j (magOf (nibAt s.mem (State.addr p) j))) c ∧
        Lim v.mem (State.addr b) (offset sl) := fun c hc sl hs => sel_env lv sl c hc hs
  have limv : AllLim v.mem b := fun sl => by
    rcases slot_cases sl with h4 | h5 | h6 | hl | hh
    · exact (ent 0 (by decide) sl h4).2
    · exact (ent 1 (by decide) sl h5).2
    · exact (ent 2 (by decide) sl h6).2
    · exact (envv sl (.inl hl)).2
    · exact (envv sl (.inr hh)).2
  have cv := cu.of_rest rv (by decide)
  have sgn : v.mem.readW (State.addr b + BitVec.ofNat 64 SGN) 32 =
      maskB (decide (nibAt s.mem (State.addr p) j < 8)) := by
    rw [fv.readW (r := ⟨State.addr b + BitVec.ofNat 64 56, 4⟩) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), mu, Mem.readW_writeW_self32]
  -- The negation.
  refine WP.seq ?_
  rw [combNeg, List.singleton_append, WP.seq_iff]
  refine WP.mono (fieldCode_ok [.sub 7 21 6] cv limv) fun w ⟨kw, lw, ew⟩ => ?_
  have cw := kw.ctx cv
  refine ldr0_ok cw (by decide) fun x₀ ux => ?_
  have sgnw : w.mem.readW (State.addr b + BitVec.ofNat 64 SGN) 32 =
      maskB (decide (nibAt s.mem (State.addr p) j < 8)) := by
    rw [kw.frame.readW (r := ⟨State.addr b + BitVec.ofNat 64 56, 4⟩) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), sgn]
  have cx₀ := cw.of_rest (ux.rest (ws := [.r9]) (by decide)) (by decide)
  refine WP.mono (swapFields_ok cx₀ (by rw [ux.mem]; exact lw) [(4, 5), (6, 7)] (by decide)
    (sw := decide (nibAt s.mem (State.addr p) j < 8)) (by rw [ux.gpr, sgnw, maskB_eq]))
    fun x ⟨kx, lx, _, ex⟩ => ?_
  have cx := kx.ctx cx₀
  -- The addition.
  refine WP.seq (WP.mono (fieldCode_ok addAffineOps cx lx) fun y ⟨ky, ly, ey⟩ => ?_)
  have cy := ky.ctx cx
  -- The counter.
  refine wp_dp (op2_imm (by decide)) fun z₀ uz => wp_cmp (op2_imm (by decide)) fun z fz zz => WP.block_nil ?_
  have r11y : y.gpr .r11 = BitVec.ofNat 32 j := by
    rw [ky.rest.gpr _ (by decide), kx.rest.gpr _ (by decide), ux.other _ (by decide),
      kw.rest.gpr _ (by decide), rv.gpr _ (by decide), ru.gpr _ (by decide), h.r11]
  have r11z : z.gpr .r11 = BitVec.ofNat 32 (j + 1) := by
    rw [fz.gpr, uz.gpr, dpVal, r11y, nf.1]
  -- What the step changed.
  have restz : Rest powersClob s z :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans (kw.rest.mono (by decide) |>.trans
      ((ux.rest (ws := powersClob) (by decide)).trans ((kx.rest.mono (by decide)).trans
      ((ky.rest.mono (by decide)).trans ((uz.rest (ws := powersClob) (by decide)).trans
      (fz.rest _)))))))
  have memz : z.mem = y.mem := by rw [fz.mem, uz.mem]
  have fz' : Frame (stepRegions b) s.mem z.mem := by
    rw [memz]
    refine (fu.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans ?_
    refine ((fv.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩).trans ?_)
    refine (kw.frame.mono (by simp)).trans ?_
    have kxf := kx.frame
    rw [ux.mem] at kxf
    exact (kxf.mono (by simp)).trans (ky.frame.mono (by simp))
  have pk := stepRegions_keep restz fz'
  -- The entry's coordinates.
  obtain ⟨q, hq, hqz, hrq⟩ := combEntry64_ok j (nib S j) hj (nib_lt S j)
  rw [hnib] at ent sgn
  have e4 := (ent 0 (by decide) 4 rfl).1
  have e5 := (ent 1 (by decide) 5 rfl).1
  have e6 := (ent 2 (by decide) 6 rfl).1
  have e21 : env v.mem b 21 = 0 := (envv 21 (.inr (by decide))).1.trans h.zero
  have ex' : env x.mem b = swapEnvs [(4, 5), (6, 7)] (decide (nib S j < 8)) (env w.mem b) := by
    rw [ex, ux.mem, hnib]
  have w4 : env w.mem b 4 = env v.mem b 4 := by rw [ew]; rfl
  have w5 : env w.mem b 5 = env v.mem b 5 := by rw [ew]; rfl
  have w6 : env w.mem b 6 = env v.mem b 6 := by rw [ew]; rfl
  have w7 : env w.mem b 7 = env v.mem b 21 - env v.mem b 6 := by rw [ew]; rfl
  have hx : ∀ i : Slot, i.val < 4 → env x.mem b i = env s.mem b i := fun i hi => by
    rw [ex', swapNeg_low _ _ _ (.inl hi), ew,
      evalOps_unchanged _ _ _ (by
        simp only [List.mem_singleton, forall_eq, fieldDest]; intro e; subst e; exact absurd hi (by decide))]
    exact (envv i (.inl hi)).1
  have cq : env x.mem b 4 = q.Y - q.X ∧ env x.mem b 5 = q.Y + q.X ∧
      env x.mem b 6 = q.T * 2 * Spec.Ed25519.d := by
    obtain ⟨s4, s5, s6⟩ := swapNeg_vals (decide (nib S j < 8)) (env w.mem b)
    have c0 : ∀ p, combCoord p 0 = p.X := fun _ => rfl
    have c1 : ∀ p, combCoord p 1 = p.Y := fun _ => rfl
    have c2 : ∀ p, combCoord p 2 = p.Z := fun _ => rfl
    rw [c0, magOf_eq] at e4
    rw [c1, magOf_eq] at e5
    rw [c2, magOf_eq] at e6
    rw [ex', s4, s5, s6, w4, w5, w6, w7, e4, e5, e6, e21]
    have hc := congrArg (fun p => (p.X, p.Y, p.Z)) hq
    simp only [cache, Prod.mk.injEq] at hc
    by_cases hlt : nib S j < 8
    · simp only [hlt, decide_true, ↓reduceIte, negCached] at hc ⊢
      exact hc
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      exact hc
  refine fun hsz => ⟨?_, ⟨by omega, cy.of_rest ((uz.rest (ws := [.r11]) (by decide)).trans (fz.rest _)) (by decide), r11z,
    by rw [memz]; exact ly, ?_, ?_, h.keep.trans pk, ?_, ?_⟩⟩
  · rw [eval_ne, zz, uz.gpr, dpVal, r11y, nf.1, nf.2]
    simp
  · -- Slot 21 is still zero.
    rw [memz, ey, evalOps_unchanged _ _ _ (by simp only [addAffineOps, List.mem_cons,
      forall_eq_or_imp, fieldDest, List.not_mem_nil, false_implies, implies_true]; decide), ex']
    rw [swapNeg_low _ _ _ (.inr (by decide)), ew, evalOps_unchanged _ _ _ (by simp only [List.mem_singleton, forall_eq, fieldDest]; decide)]
    exact e21
  · -- The accumulator.
    rw [memz, ey, addAffineOps_formula, cq.1, cq.2.1, cq.2.2, hx 0 (by decide), hx 1 (by decide),
      hx 2 (by decide), hx 3 (by decide)]
    have e := mixedResult_eq (point (env s.mem b) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e, digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc (by simpa only [sdig] using hrq)
  · rw [h.scalar]
    unfold Spec.Ed25519.bytesAt
    exact congrArg _ (List.map_congr_left fun n hn => (fz'.bytes (R := ⟨State.addr p, 32⟩) E.sep
      (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)).symm)
  · rw [hsz]; exact h.syms

/-- The loop, from step `j₀ < 64` to the end. -/
theorem combSteps_ok {s₀ s : State} {b p T : BitVec 32} {S j₀ : Nat} (E : CombEnv s₀ b p T)
    (h : CombInv s₀ b p T S j₀ s) (hj₀ : j₀ < 64) :
    WP isa (.loop combStep .ne) s fun t => CombInv s₀ b p T S 64 t := by
  apply WP.loop (fun n t => CombInv s₀ b p T S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64 - j₀)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok E ht (by omega)) fun u ⟨ue, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by rw [ue]; rfl, hu⟩
    · refine Or.inr ⟨by rw [ue]; simp only [show 64 - (k + 1) + 1 ≠ 64 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨by rw [show 64 - (64 - j₀) = j₀ by omega]; exact h, by omega, by omega⟩

/-! ## The scalar's copy -/

/-- The scalar's copy in the workspace. -/
abbrev scalR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 SCAL, 32⟩

private theorem byte_rt (x : BitVec 8) : (x.setWidth 32).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega_arith

theorem combCopy_ok {s : State} {b P : BitVec 32} (hc : Ctx b s) (hp : s.gpr .r12 = P)
    (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint (scalR b)) :
    WP isa (.block combCopy) s fun t => Rest [.r1] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ k < 32, t.mem (State.addr b + BitVec.ofNat 64 (SCAL + k)) =
        s.mem (State.addr P + BitVec.ofNat 64 k) := by
  have hfb := hc.fit
  have src : ∀ k < 32, ∀ m : Mem, Frame [scalR b] s.mem m →
      m (State.addr P + BitVec.ofNat 64 k) = s.mem (State.addr P + BitVec.ofNat 64 k) := fun k hk m hf =>
    hf.bytes (R := ⟨State.addr P, 32⟩) (by simpa only [List.mem_singleton, forall_eq] using hsep)
      (show (32 : Nat) ≤ 2 ^ 64 by decide) hk
  refine wp_range_flatMap (M := isa) (fun (k : Nat) (t : State) => Rest [.r1] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ i < k, t.mem (State.addr b + BitVec.ofNat 64 (SCAL + i)) = s.mem (State.addr P + BitVec.ofNat 64 i))
    (fun (k : Nat) (t : State) hk ⟨rt, ft, ct⟩ => ?_) 32 le_rfl s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine wp_ldrb (a := State.addr P + BitVec.ofNat 64 k) (by omega)
    (by rw [rt.gpr _ (by decide), hp]; exact addr_add (by omega))
    (by rw [rt.rd, rt.wr]; exact hr k hk) fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (SCAL + k)) (by simp only [SCAL]; omega)
    (by rw [u₁.other _ (by decide), rt.gpr _ (by decide), hc.r0]; exact addr_add (by simp only [SCAL]; omega))
    (by rw [u₁.wr, rt.wr]; exact in_base hc.wr (by simp only [SCAL]; omega) (by simp only [SCAL]; omega))
    fun t₂ u₂ => WP.block_nil ?_
  have m2 : t₂.mem = t.mem.writeW (State.addr b + BitVec.ofNat 64 (SCAL + k))
      (t.mem (State.addr P + BitVec.ofNat 64 k)) := by
    rw [u₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine ⟨rt.trans ((u₁.rest (by decide)).trans (u₂.rest _)), ?_, fun i hi => ?_⟩
  · rw [m2]
    exact ft.writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega))
  · rw [m2, VG.WriteBytes.writeW8_apply]
    by_cases hik : i = k
    · subst hik
      rw [ite_eq_left rfl]
      exact src i hk _ ft
    · have hne : State.addr b + BitVec.ofNat 64 (SCAL + i) ≠ State.addr b + BitVec.ofNat 64 (SCAL + k) :=
        fun he => Offset.disjoint (State.addr b) (d := SCAL + i) (n := 1) (e := SCAL + k) (k := 1)
          (by omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) _
          (Region.contains_self _ _) (he ▸ Region.contains_self _ _)
      rw [ite_eq_right hne]
      exact ct i (by omega)

/-! ## The start -/

private def combStartCheck (p : Spec.Ed25519.Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check :
    combStartCheck (Spec.Ed25519.pointMul (17 * combGVal) Spec.Ed25519.basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * combGVal) • baseAff) := by
  have hp := pointMul_rep (17 * combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact combPt_rep (q := combStartAff) hp hx hy

/-! ## The multiplication -/

theorem combPrepare_ok {s : State} {b P T : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.gpr .r12 = P) (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa combPrepare s fun w => PointKeep b s w ∧ CombEnv w b (b + BitVec.ofNat 32 SCAL) T ∧
      CombInv w b (b + BitVec.ofNat 32 SCAL) T
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32)) 0 w := by
  have hfb := hc.fit
  have sub : (scalR b).Sub ⟨State.addr b, 8192⟩ := Offset.sub_base _ (by decide)
  rw [combPrepare]
  refine WP.seq (WP.mono_syms (combCopy_ok hc hp hfit hr (hsep.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_)
  have ku : PointKeep b s u := PointKeep.of_small ru (by decide) fu (by decide) (by decide)
  have hcu := ku.ctx hc
  have lu : AllLim u.mem b := fun sl =>
    (env_frame fu sl (slot_apart sl (.inr (by simp only [offset, SCAL]; have := sl.isLt; omega))
      (by decide))).2 (hl sl)
  rw [combInit, WP.seq_iff]
  refine WP.mono_syms (fieldCode_ok _ hcu lu) fun v ⟨kv, lv, ev⟩ syv => ?_
  refine WP.mono_syms (Q := fun w => Upd v w .r11 ((0 : BitVec 16).setWidth 32))
    (wp_movw fun w uw => WP.block_nil uw) fun w uw syw => ?_
  -- Where the loop starts.
  let p := b + BitVec.ofNat 32 SCAL
  have hpa : State.addr p = State.addr b + BitVec.ofNat 64 SCAL := addr_add (by simp only [SCAL]; omega)
  have hpn : p.toNat = b.toNat + SCAL := by
    simp only [p, BitVec.toNat_add, BitVec.toNat_ofNat, SCAL]
    rw [Nat.mod_eq_of_lt (by omega : 2048 < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  have frw : Frame [FA b] u.mem w.mem := by rw [uw.mem]; exact kv.frame
  have tu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr]) fu fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  have tw : TblAt w T := tu.of_frame (by rw [uw.rd, uw.wr, kv.rest.rd, kv.rest.wr]) frw fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right (Offset.sub_base _ (by decide))
  have scal : Spec.Ed25519.bytesAt w.mem (State.addr p) 32 = Spec.Ed25519.bytesAt s.mem (State.addr P) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => ?_
    have hn := List.mem_range.mp hn
    rw [hpa, frw.bytes (R := ⟨State.addr b + BitVec.ofNat 64 SCAL, 32⟩)
      (by simp only [List.mem_singleton, forall_eq]
          exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide))
      (show (32 : Nat) ≤ 2 ^ 64 by decide) hn, Offset.add_add]
    exact cu n hn
  have E : CombEnv w b p T := by
    refine ⟨rfl, by rw [hpn]; simp only [SCAL]; omega, fun k hk => ?_, ?_, tw, apart⟩
    · rw [hpa, Offset.add_add, uw.rd, uw.wr, kv.rest.rd, kv.rest.wr]
      have hw : (⟨State.addr b, 4096 + 4096⟩ : Region) ∈ u.wr := hcu.wr
      exact in_base (List.mem_append_right _ hw) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega)
    · intro r hr
      rw [hpa]
      simp only [stepRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  have hcw : Ctx b w := (kv.ctx hcu).of_rest (uw.rest (ws := [.r11]) (by decide)) (by decide)
  have kvw : PointKeep b v w := ⟨uw.rest (by decide), by rw [uw.mem]; exact Frame.refl _ _⟩
  have I : CombInv w b p T (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32)) 0 w := by
    refine ⟨by decide, hcw, by rw [uw.gpr]; rfl, by rw [uw.mem]; exact lv, by rw [uw.mem, ev]; rfl, ?_,
      PointKeep.refl _ _, by rw [scal], by rw [syw, syv, syu]; exact hsym⟩
    rw [uw.mem, ev, evalOps, List.foldl_append, ← evalOps, ← evalOps, constPoint_eval]
    simpa only [digitSum64, add_zero, natCast_zsmul] using combStart_ok
  exact ⟨ku.trans ((PointKeep.of_keep kv).trans kvw), E, I⟩

theorem combMultiply_ok {s : State} {b P T : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hp : s.gpr .r12 = P) (hfit : P.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (State.addr P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨State.addr P, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa combMultiply s fun t => PointKeep b s t ∧ AllLim t.mem b ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32) • baseAff) := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combPrepare_ok hc hl hp hfit hr hsep hT hsym apart) fun w ⟨kw, E, I⟩ => ?_)
  refine WP.mono (combSteps_ok E I (by decide)) fun t ht => ⟨kw.trans ht.keep, ht.lim, ?_⟩
  have hS := decodeLE_lt32 s.mem (State.addr P)
  have e := comb64_total (S := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr P) 32))
    (by simpa using hS)
  have := ht.acc
  rw [e, natCast_zsmul] at this
  exact this

end VG.Proof.Ed25519.Arm
