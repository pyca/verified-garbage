module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleCall
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Bignum.Arm.DoubleCall
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # R-squared's doublings, by inline code or by a call

`Doubling` is one modular doubling of array four, as code that keeps
`DoubleLoopReady` and may write `regions`; `DoubleCall.loop` repeats it.
`inlineDoubling` is the inline doubling (`doubleLoopMultiply`).
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

structure Doubling (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region) where
  dbl : Prog isa
  workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions
  stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
    Rest roundClobbers s t → P s → P t
  dbl_ok : ∀ (s : State) (c : Nat), DoubleLoopReady base len w c s →
    1 < numAt s.mem (State.addr base) w 0 → P s → WP isa dbl s fun t => DoubleLoopReady base len w c t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t

/-- What a doubling needs of a state: the loop's workspace, a modulus above
one and the property `P`. -/
abbrev DoubleInput (base : BitVec 32) (len w : Nat) (P : State → Prop) (c : Nat) (s : State) : Prop :=
  DoubleLoopReady base len w c s ∧ 1 < numAt s.mem (State.addr base) w 0 ∧ P s

structure DoublingTiming {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (D : Doubling base len w P regions) : Prop where
  dbl_ct : ∀ c, RelCT isa (fun s t => DoubleInput base len w P c s ∧
    DoubleInput base len w P c t ∧ s.sp = t.sp) D.dbl (fun _ _ => True)

/-- One doubling and the count down. -/
theorem Doubling.body_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (D : Doubling base len w P regions) (s : State) {c : Nat}
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0)
    (hp : P s) (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa (.seq D.dbl (.block doubleCount)) s fun t => DoubleLoopReady base len w (c - 1) t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      t.z = decide (c = 1) ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (D.dbl_ok s c h large hp) ?_
  rintro u ⟨ready, value, modulus, pu, frame, rest⟩
  have fits := ready.layout.2.2.1
  have size : 212 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  refine WP.mono (doubleCount_ok u ready.workspace size ready.ptr hc hc' ready.counter) ?_
  rintro t ⟨mem, zero, keep⟩
  obtain ⟨state, frameT, number, modT⟩ := ready.after_count mem keep
  have restT : Rest roundClobbers u t := keep.mono (by decide)
  refine ⟨state, number.trans value, modT.trans modulus, zero, D.stable frameT restT pu,
    frame.trans (frameT.mono (by
      intro r hr; have er := List.mem_singleton.mp hr; subst r; exact D.workspace)),
    rest.trans restT⟩

/-- `c` doublings multiply array four by `2 ^ c`. -/
theorem Doubling.loop_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (D : Doubling base len w P regions) (s : State) {c : Nat}
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0)
    (hp : P s) (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa (DoubleCall.loop D.dbl) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 ^ c * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun k t => ∃ i, i + k = c ∧ 0 < k ∧ DoubleLoopReady base len w k t ∧
    numAt t.mem (State.addr base) w 4 =
      (2 ^ i * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
    numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
    P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold DoubleCall.loop
  refine WP.loop (M := isa) inv ?_ c s ?_
  · intro k t hi
    obtain ⟨i, hik, hk, ready, number, modulus, pt, frame, rest⟩ := hi
    refine WP.mono (D.body_ok t ready (by rw [modulus]; exact large) pt hk (by omega_using [hc', hik])) ?_
    rintro u ⟨next, value, modU, zero, pu, frameU, restU⟩
    have step : numAt u.mem (State.addr base) w 4 =
        (2 ^ (i + 1) * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 := by
      rw [value, number, modulus, double_power_step]
    have oldM := modU.trans modulus
    have wholeFrame := frame.trans frameU
    have wholeRest := rest.trans restU
    by_cases exit : k = 1
    · left
      refine ⟨?_, ?_, ?_, oldM, pu, wholeFrame, wholeRest⟩
      · change some (!u.z) = some false
        simp only [zero, exit, decide_true, Bool.not_true]
      · simpa only [exit, Nat.sub_self] using next
      · simpa only [show i + 1 = c by omega_using [hik, exit]] using step
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hk, exit],
        next, step, oldM, pu, wholeFrame, wholeRest⟩
      change some (!u.z) = some true
      simp only [zero, exit, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], hc, h, ?_, rfl, hp, Frame.refl _ _, Rest.refl _ _⟩
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt h.operand]

theorem Doubling.loop_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (D : Doubling base len w P regions) (ct : DoublingTiming D) {c : Nat} (hc : 0 < c) (hc' : c < 2 ^ 32) :
    RelCT isa (fun s t => DoubleInput base len w P c s ∧ DoubleInput base len w P c t ∧ s.sp = t.sp)
      (DoubleCall.loop D.dbl) (fun _ _ => True) := by
  let I := fun k (s t : State) => 0 < k ∧ k < 2 ^ 32 ∧ DoubleInput base len w P k s ∧
    DoubleInput base len w P k t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq D.dbl (.block doubleCount)) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨hk, hk', hs, ht, sp⟩ := h
    have count : RelCT isa (fun s t => DoubleLoopReady base len w k s ∧ DoubleLoopReady base len w k t)
        (.block doubleCount) (fun _ _ => True) := by
      apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
      intro s t h
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact h.1.ptr.trans h.2.ptr.symm
    have body := (ct.dbl_ct k).wp (fun s t h =>
      ⟨WP.mono (D.dbl_ok s k h.1.1 h.1.2.1 h.1.2.2) (fun _ h => h.1),
        WP.mono (D.dbl_ok t k h.2.1.1 h.2.1.2.1 h.2.1.2.2) (fun _ h => h.1)⟩)
    obtain ⟨trace, _⟩ := (body.seq (count.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)))
      s t tr1 tr2 u v ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, u', eu, hu, _, mu, zu, pu, _, ru⟩ := D.body_ok s hs.1 hs.2.1 hs.2.2 hk hk'
    obtain ⟨_, v', ev, hv, _, mv, zv, pv, _, rv⟩ := D.body_ok t ht.1 ht.2.1 ht.2.2 hk hk'
    obtain ⟨-, rfl⟩ := Exec.det e1 eu
    obtain ⟨-, rfl⟩ := Exec.det e2 ev
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · intro branch
      have ne : k ≠ 1 := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega_using [hk], by omega_using [hk, ne], by omega_using [hk'],
        ⟨hu, by rw [mu]; exact hs.2.1, pu⟩, ⟨hv, by rw [mv]; exact ht.2.1, pv⟩, ru.sp.trans (sp.trans rv.sp.symm)⟩
  exact (RelCT.loop I step c).mono (fun _ _ h => ⟨hc, hc', h⟩) (fun _ _ h => h)

/-- The inline doubling, for any frame property that unrelated writes keep. -/
def inlineDoubling (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region)
    (workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions)
    (stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
      Rest roundClobbers s t → P s → P t) : Doubling base len w P regions where
  dbl := doubleLoopMultiply
  workspace := workspace
  stable := stable
  dbl_ok := by
    intro s c h _ hp
    refine WP.mono (doubleLoopMultiply_ok s h) ?_
    rintro t ⟨ready, value, modulus, frame, rest⟩
    exact ⟨ready, value, modulus, stable frame rest hp, frame.mono (by
      intro r hr; have er := List.mem_singleton.mp hr; subst r; exact workspace), rest⟩

theorem inlineDoublingTiming (base : BitVec 32) (len w : Nat) (P : State → Prop) (regions : List Region)
    (workspace : (⟨State.addr base, 8 * len⟩ : Region) ∈ regions)
    (stable : ∀ {s t : State}, Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem →
      Rest roundClobbers s t → P s → P t) :
    DoublingTiming (inlineDoubling base len w P regions workspace stable) := by
  constructor
  intro c s t tr1 tr2 u v h e1 e2
  obtain ⟨hs, ht, sp⟩ := h
  have hw : 2 ≤ w := hs.1.width ▸ hs.1.layout.1
  have fits : arrAt w 8 ≤ 8 * len := hs.1.width ▸ hs.1.layout.2.2.1
  have tmp := Nat.le_trans (array_end_le (w := w) (j := 3) (k := 8) (by decide)) fits
  exact doubleLoopMultiply_ct (base := base) (c := c) (by omega_using [hw, tmp]) (by omega_using [hw])
    s t tr1 tr2 u v ⟨hs.1, ht.1, sp⟩ e1 e2

end VG.Proof.Bignum.Arm.TwoExp
