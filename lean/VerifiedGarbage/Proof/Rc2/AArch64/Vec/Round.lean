import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Mix
import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Rc2.AArch64.Rounds

/-!
# Reverse mixing rounds on eight blocks

The schedule is in `v16`–`v23` (`SchedV`); `keyBcast_ok` broadcasts a key
word from it, `rmix_ok` is a reverse mix on a set (`VWords`), and
`rmixRound_ok` a reverse mixing round on both sets.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- The schedule at `p` in `v16`–`v23`. -/
def SchedV (s : State) (m : Mem) (p : Addr) : Prop :=
  ∀ r < 8, s.v (treg r) = m.read (p + BitVec.ofNat 64 (16 * r)) 16

/-- A lane's low 16 bits are its first two bytes. -/
theorem lw_bytes (x : BitVec 128) (b : Nat) :
    lw x b = (vbyte x (4 * b)).setWidth 16 ||| (vbyte x (4 * b + 1)).setWidth 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [lw, vword, vbyte, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
  by_cases h8 : t < 8
  · simp [h8, show t < 32 by omega, show 8 * (4 * b) + t = 32 * b + t by omega]
  · simp [h8, show t < 32 by omega, show t - 8 < 8 by omega, show t - 8 < 16 by omega,
      show 8 * (4 * b + 1) + (t - 8) = 32 * b + t by omega]

theorem exec_dupE (s : State) (d n : VReg) {i : Nat} (hi : i < 4) :
    exec (.vop (.dupE .s4 d n i)) s =
      some (s.setV d (VArr.s4.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0)) := by
  simp [exec, VOp.eval, VArr.esize, show i < 4 from hi]

theorem exec_rev (s : State) (op : VRevOp) (d n : VReg) :
    exec (.vop (.rev op d n)) s = some (s.setV d (op.eval (s.v n))) := rfl

theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

/-- Key word `k` broadcast. -/
theorem keyBcast_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p) {k : Nat} (hk : k < 64) :
    ∃ s', runBlock isa (keyBcast k) s = some s' ∧
      (∀ b < 4, lw (s'.v kb) b = (Spec.Rc2.scheduleAt m p).getD k 0) ∧
      (∀ r, r ≠ kb → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let S := s.v (treg (k / 8))
  let D : BitVec 128 := VArr.s4.map2 (fun w _ _ => S.extractLsb' (w * (k % 8 / 2)) w) 0 0
  let s₁ := s.setV kb D
  have hS : S = m.read (p + BitVec.ofNat 64 (16 * (k / 8))) 16 := hs _ (by omega)
  -- Byte `e` of lane `b` of the broadcast.
  have dB : ∀ b < 4, ∀ e < 4, vbyte D (4 * b + e) = m (p + BitVec.ofNat 64 (2 * (k / 2 * 2) + e)) := by
    intro b hb e he
    have hv : vword D b = vword S (k % 8 / 2) := by
      simp only [D, vword_map2 _ _ _ hb]; rfl
    have : vbyte D (4 * b + e) = (vword D b).extractLsb' (8 * e) 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro t ht
      simp [vbyte, vword, ht, show 8 * e + t < 32 by omega, show 8 * (4 * b + e) + t = 32 * b + (8 * e + t) by omega]
    rw [this, hv]
    have : (vword S (k % 8 / 2)).extractLsb' (8 * e) 8 = vbyte S (4 * (k % 8 / 2) + e) := by
      apply BitVec.eq_of_getLsbD_eq; intro t ht
      simp [vbyte, vword, ht, show 8 * e + t < 32 by omega,
        show 8 * (4 * (k % 8 / 2) + e) + t = 32 * (k % 8 / 2) + (8 * e + t) by omega]
    rw [this, hS, vbyte_read _ _ (by omega), Offset.add_add,
      show 16 * (k / 8) + (4 * (k % 8 / 2) + e) = 2 * (k / 2 * 2) + e by omega]
  have key : ∀ b < 4, lw (s₁.v kb) b = (m (p + BitVec.ofNat 64 (2 * (k / 2 * 2)))).setWidth 16 |||
      (m (p + BitVec.ofNat 64 (2 * (k / 2 * 2) + 1))).setWidth 16 <<< 8 := by
    intro b hb
    rw [show s₁.v kb = D from v_setV_self _ _ _, lw_bytes _ b,
      show 4 * b = 4 * b + 0 by omega, dB b hb 0 (by decide), dB b hb 1 (by decide)]
    rfl
  by_cases hp : k % 2 = 1
  · let s₂ := s₁.setV kb (VRevOp.rev32h.eval (s₁.v kb))
    refine ⟨s₂, ?_, fun b hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [keyBcast, ite_eq_left hp, List.singleton_append, runBlock_cons, exec_dupE _ _ _ (by omega),
        runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil]
    · rw [show s₂.v kb = VRevOp.rev32h.eval (s₁.v kb) from v_setV_self _ _ _, lw_bytes _ b,
        VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hk]
      simp only [VRevOp.eval, vbyte_ofVBytes _ (show 4 * b < 16 by omega),
        vbyte_ofVBytes _ (show 4 * b + 1 < 16 by omega),
        show 4 * (4 * b / 4) + (4 * b % 4 + 2) % 4 = 4 * b + 2 by omega,
        show 4 * ((4 * b + 1) / 4) + ((4 * b + 1) % 4 + 2) % 4 = 4 * b + 3 by omega]
      rw [show s₁.v kb = D from v_setV_self _ _ _, dB b hb 2 (by decide), dB b hb 3 (by decide),
        show 2 * (k / 2 * 2) + 2 = 2 * k by omega, show 2 * (k / 2 * 2) + 3 = 2 * k + 1 by omega]
    · simp only [s₂, s₁, v_setV_of_ne _ _ hr]
  · refine ⟨s₁, ?_, fun b hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [keyBcast, ite_eq_right hp, List.append_nil, runBlock_cons, exec_dupE _ _ _ (by omega),
        runStep_some, runBlock_nil]
    · rw [key b hb, VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hk, show k / 2 * 2 = k by omega]
    · simp only [s₁, v_setV_of_ne _ _ hr]

/-! ## A reverse mix on a set -/

theorem wreg_mod (h i : Nat) : wreg h i = wreg h (i % 4) := by simp [wreg]

theorem mixRegs (h i : Nat) (hh : h < 2) (hi : i < 4) :
    MixRegs (wreg h i) (wreg h (i + 1)) (wreg h (i + 2)) (wreg h (i + 3)) (tmp h 0) (tmp h 1)
      (tmp h 2) := by
  constructor <;> (revert hi; revert i; revert hh; revert h; decide)

/-- The registers a set's reverse mix writes, and the set's other words. -/
theorem regs_other (h i i' : Nat) (hh : h < 2) (hi : i < 4) (hi' : i' < 4) (he : i' ≠ i) :
    wreg h i' ≠ wreg h i ∧ wreg h i' ≠ tmp h 0 ∧ wreg h i' ≠ tmp h 1 ∧ wreg h i' ≠ tmp h 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (revert he; revert hi'; revert i'; revert hi; revert i; revert hh; revert h; decide)

/-- The registers a set's reverse mix writes, and the other set's words. -/
theorem regs_cross (h i i' : Nat) (hh : h < 2) (hi : i < 4) (hi' : i' < 4) :
    wreg (1 - h) i' ≠ wreg h i ∧ wreg (1 - h) i' ≠ tmp h 0 ∧ wreg (1 - h) i' ≠ tmp h 1 ∧
      wreg (1 - h) i' ≠ tmp h 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (revert hi'; revert i'; revert hi; revert i; revert hh; revert h; decide)

/-- The registers a set's reverse mix writes, and the key, mask and schedule. -/
theorem regs_fixed (h i : Nat) (hh : h < 2) (hi : i < 4) :
    kb ≠ wreg h i ∧ m16 ≠ wreg h i ∧ m16 ≠ tmp h 0 ∧ m16 ≠ tmp h 1 ∧ m16 ≠ tmp h 2 ∧
      kb ≠ tmp h 0 ∧ kb ≠ tmp h 1 ∧ kb ≠ tmp h 2 ∧
      (∀ r < 8, treg r ≠ wreg h i ∧ treg r ≠ tmp h 0 ∧ treg r ≠ tmp h 1 ∧ treg r ≠ tmp h 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (revert hr; revert r; revert hi; revert i; revert hh; revert h; decide)
    | (revert hi; revert i; revert hh; revert h; decide)

theorem getD_set (v : Spec.Rc2.State) {i i' : Nat} (hi' : i' < 4) (x : BitVec 16) :
    (v.set! i x).getD i' 0 = if i' = i then x else v.getD i' 0 := by
  rw [vector_getD _ i' hi', vector_getD _ i' hi', Vector.getElem_set! hi']
  by_cases h : i' = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem rmix_ok {s : State} {h i : Nat} (hh : h < 2) (hi : i < 4) {vs : Nat → Spec.Rc2.State}
    (hv : VWords s h vs) {K : BitVec 16} (hk : ∀ b < 4, lw (s.v kb) b = K)
    (hm : s.v m16 = mask16) (k : Spec.Rc2.Schedule) {j : Nat} (hK : k.getD j 0 = K) :
    ∃ s', runBlock isa (rmix h i) s = some s' ∧
      VWords s' h (fun b => Spec.Rc2.reverseMix k j i (vs b)) ∧
      (∀ r, r ≠ wreg h i → r ≠ tmp h 0 → r ≠ tmp h 1 → r ≠ tmp h 2 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hn := VG.Proof.Rc2.AArch64.rotation_bounds i
  obtain ⟨s', run, lane, other, g, me, rd, wr, sp⟩ :=
    rmixCode_ok (s := s) (mixRegs h i hh hi) hn.1 hn.2 hm
  refine ⟨s', by rw [rmix_eq]; exact run, fun i' hi' b hb => ?_, other, g, me, rd, wr, sp⟩
  simp only [Spec.Rc2.reverseMix]
  rw [getD_set _ hi']
  by_cases he : i' = i
  · subst he
    rw [ite_eq_left rfl, lane b hb, hk b hb, hv i' hi' b hb, wreg_mod h (i' + 3), wreg_mod h (i' + 2),
      wreg_mod h (i' + 1), hv _ (Nat.mod_lt _ (by decide)) b hb, hv _ (Nat.mod_lt _ (by decide)) b hb,
      hv _ (Nat.mod_lt _ (by decide)) b hb, hK]
  · obtain ⟨o1, o2, o3, o4⟩ := regs_other h i i' hh hi hi' he
    rw [ite_eq_right he, other _ o1 o2 o3 o4, hv i' hi' b hb]

/-! ## A reverse mixing round on both sets -/

/-- The words of both sets: block `b` of the eight is `vs b`. -/
def Sets (s : State) (vs : Nat → Spec.Rc2.State) : Prop :=
  ∀ h < 2, VWords s h (fun b => vs (4 * h + b))

/-- What the rounds keep: the general registers but `x9` and `x6`, memory,
the regions, the stack pointer, the schedule and the mask. -/
structure VKeep (s s' : State) : Prop where
  keep : Keep [.x9, .x6] s s'
  sp : s'.sp = s.sp
  sched : ∀ r < 8, s'.v (treg r) = s.v (treg r)
  mask : s'.v m16 = s.v m16

theorem VKeep.trans {s s' s'' : State} (h : VKeep s s') (h' : VKeep s' s'') : VKeep s s'' :=
  ⟨h.keep.trans h'.keep, h'.sp.trans h.sp, fun r hr => (h'.sched r hr).trans (h.sched r hr),
    h'.mask.trans h.mask⟩

theorem SchedV.keep {s s' : State} {m : Mem} {p : Addr} (hs : SchedV s m p) (h : VKeep s s') :
    SchedV s' m p := fun r hr => (h.sched r hr).trans (hs r hr)

theorem VWords.keep {s s' : State} {h : Nat} {vs : Nat → Spec.Rc2.State} (hv : VWords s h vs)
    (hk : ∀ i < 4, s'.v (wreg h i) = s.v (wreg h i)) : VWords s' h vs :=
  fun i hi b hb => by rw [hk i hi]; exact hv i hi b hb

theorem treg_ne_kb : ∀ r < 8, treg r ≠ kb ∧ treg r ≠ m16 := by decide

/-- Key word `4 j + i` broadcast, and word `i` of both sets reverse mixed. -/
theorem mixStep_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p) (hm : s.v m16 = mask16)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) {j i : Nat} (hi : i < 4) (hj : j < 16) :
    ∃ s', runBlock isa (keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i) s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i (vs b)) ∧
      VKeep s s' := by
  obtain ⟨s₁, r₁, k₁, o₁, g₁, me₁, rd₁, wr₁, sp₁⟩ := keyBcast_ok hs (k := 4 * j + i) (by omega)
  have v₁ : Sets s₁ vs := fun h hh =>
    (hv h hh).keep fun i' hi' => o₁ _ (regs_fixed h i' hh hi').1.symm
  have m₁ : s₁.v m16 = mask16 := (o₁ m16 (by decide)).trans hm
  obtain ⟨s₂, r₂, w₂, o₂, g₂, me₂, rd₂, wr₂, sp₂⟩ :=
    rmix_ok (h := 0) (by decide) hi (v₁ 0 (by decide)) k₁ m₁ (Spec.Rc2.scheduleAt m p) rfl
  have f₀ := regs_fixed 0 i (by decide) hi
  have k₂ : ∀ b < 4, lw (s₂.v kb) b = (Spec.Rc2.scheduleAt m p).getD (4 * j + i) 0 := by
    intro b hb; rw [o₂ kb f₀.1 f₀.2.2.2.2.2.1 f₀.2.2.2.2.2.2.1 f₀.2.2.2.2.2.2.2.1]; exact k₁ b hb
  have m₂ : s₂.v m16 = mask16 := by
    rw [o₂ m16 f₀.2.1 f₀.2.2.1 f₀.2.2.2.1 f₀.2.2.2.2.1]; exact m₁
  have v₂ : VWords s₂ 1 (fun b => vs (4 * 1 + b)) := (v₁ 1 (by decide)).keep fun i' hi' => by
    obtain ⟨a, b, c, d⟩ := regs_cross 0 i i' (by decide) hi hi'
    exact o₂ _ a b c d
  obtain ⟨s₃, r₃, w₃, o₃, g₃, me₃, rd₃, wr₃, sp₃⟩ :=
    rmix_ok (h := 1) (by decide) hi v₂ k₂ m₂ (Spec.Rc2.scheduleAt m p) rfl
  have f₁ := regs_fixed 1 i (by decide) hi
  have w₃' : VWords s₃ 0 (fun b => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i
      (vs (4 * 0 + b))) := w₂.keep fun i' hi' => by
    obtain ⟨a, b, c, d⟩ := regs_cross 1 i i' (by decide) hi hi'
    exact o₃ _ a b c d
  refine ⟨s₃, runBlock_cat_some (runBlock_cat_some r₁ r₂) r₃, fun h hh => ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · match h, hh with
    | 0, _ => exact w₃'
    | 1, _ => exact w₃
  · exact ⟨fun r _ => by rw [g₃, g₂, g₁], by rw [me₃, me₂, me₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
  · rw [sp₃, sp₂, sp₁]
  · intro r hr
    have f₀ := f₀.2.2.2.2.2.2.2.2 r hr
    have f₁ := f₁.2.2.2.2.2.2.2.2 r hr
    rw [o₃ _ f₁.1 f₁.2.1 f₁.2.2.1 f₁.2.2.2, o₂ _ f₀.1 f₀.2.1 f₀.2.2.1 f₀.2.2.2,
      o₁ _ (treg_ne_kb r hr).1]
  · rw [o₃ m16 f₁.2.1 f₁.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1, o₂ m16 f₀.2.1 f₀.2.2.1 f₀.2.2.2.1
      f₀.2.2.2.2.1, o₁ m16 (by decide)]

theorem mixSteps_ok {m : Mem} {p : Addr} {j : Nat} (hj : j < 16) (is : List Nat)
    (his : ∀ i ∈ is, i < 4) {s : State} (hs : SchedV s m p) (hm : s.v m16 = mask16)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (is.flatMap fun i => keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i) s =
        some s' ∧
      Sets s' (fun b => is.foldl (fun r i =>
        Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i r) (vs b)) ∧
      VKeep s s' := by
  induction is generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons i is ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := mixStep_ok hs hm hv (his i (by simp)) hj
    obtain ⟨s₂, r₂, v₂, k₂⟩ := ih (fun i hi => his i (by simp [hi])) (hs.keep k₁)
      (k₁.mask.trans hm) v₁
    exact ⟨s₂, by rw [List.flatMap_cons]; exact runBlock_cat_some r₁ r₂, v₂, k₁.trans k₂⟩

theorem rmixRound_ok {m : Mem} {p : Addr} {j : Nat} (hj : j < 16) {s : State}
    (hs : SchedV s m p) (hm : s.v m16 = mask16) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (rmixRound j) s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt m p) j (vs b)) ∧
      VKeep s s' :=
  mixSteps_ok hj [3, 2, 1, 0] (by decide) hs hm hv

end VG.Proof.Rc2.AArch64.Vec
