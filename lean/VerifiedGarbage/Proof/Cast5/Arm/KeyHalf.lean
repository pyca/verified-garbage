import VerifiedGarbage.Proof.Cast5.Arm.KeyStep

/-!
# CAST5 key expansion on ARMv7: the steps of a half, run

`keyStep_ok`: step `j` of a half (its number in `r2`) is the spec's `stepRun`;
`half_ok`: the 40 steps of a half compute `halfImpl` (`runSteps_half`),
writing its sixteen subkeys from `lr`.
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.Arm VG.Proof.Cast5

/-! ## Facts about the steps, by evaluation -/

def isKey : Step → Bool
  | .line _ (.key _) => true
  | _ => false

/-- The number of subkey steps. -/
def countKeys (ss : List Step) : Nat := (ss.filter isKey).length

theorem ws_length : ∀ (ss : List Step) (k : KSt), (runSteps ss k).ws.length = k.ws.length + countKeys ss
  | [], _ => rfl
  | s :: ss, k => by
    rw [runSteps_cons, ws_length ss]
    unfold countKeys
    rcases s with ⟨⟩ | ⟨l, ⟨⟩ | ⟨⟩⟩ <;> simp [stepRun, isKey, List.filter_cons] <;> omega

/-- The bytes a step looks up: `S5[a], S6[b], S7[c], S8[d]`. -/
def stepPos : Step → Pos × Pos × Pos × Pos
  | .extras a b c d => (a, b, c, d)
  | .line l _ => l.main

theorem Step.gather_eq (st : Step) :
    st.gather = gather (stepPos st).1 (stepPos st).2.1 (stepPos st).2.2.1 (stepPos st).2.2.2 := by
  cases st <;> rfl

/-- What each step needs, and the place of each subkey, checked by evaluation. -/
def stepsOk : Bool :=
  halfSteps.length == 40 && (List.range 40).all fun j =>
    let st := halfSteps.getD j default
    stepOk st && (stepPos st).1.2 < 16 && (stepPos st).2.1.2 < 16 && (stepPos st).2.2.1.2 < 16 &&
      (stepPos st).2.2.2.2 < 16 &&
      match st with
      | .line _ (.key jj) => countKeys (halfSteps.take j) == jj
      | _ => true

theorem stepsOk_true : stepsOk = true := by decide +kernel

theorem halfSteps_length : halfSteps.length = 40 := by
  have := stepsOk_true
  simp only [stepsOk, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

theorem step_facts {j : Nat} (hj : j < 40) :
    stepOk (halfSteps.getD j default) = true ∧ (stepPos (halfSteps.getD j default)).1.2 < 16 ∧
      (stepPos (halfSteps.getD j default)).2.1.2 < 16 ∧ (stepPos (halfSteps.getD j default)).2.2.1.2 < 16 ∧
      (stepPos (halfSteps.getD j default)).2.2.2.2 < 16 ∧
      (∀ l jj, halfSteps.getD j default = .line l (.key jj) → countKeys (halfSteps.take j) = jj) := by
  have := stepsOk_true
  simp only [stepsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  have h := this.2 j hj
  simp only [decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun l jj e => ?_⟩
  rw [e] at h6
  simpa using h6

theorem take_succ_steps {j : Nat} (hj : j < 40) :
    halfSteps.take (j + 1) = halfSteps.take j ++ [halfSteps.getD j default] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]

theorem getD_map_steps {α : Type} (f : Step → α) (d : α) {j : Nat} (hj : j < 40) :
    (halfSteps.map f).getD j d = f (halfSteps.getD j default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]

theorem ofNat_setWidth8 (x : Byte) : BitVec.ofNat 8 (x.setWidth 32).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem setWidth8_lt (x : Byte) : (x.setWidth 32).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega

/-! ## A step -/

theorem acc_val (tab : Nat → Nat → BitVec 32) (htab : ∀ j k, j < 256 → k < 4 → tab j k = tabOf Spec.Cast5.S8
    Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5 j k) (x : Byte) {k : Nat} (hk : k < 4) :
    tab (x.setWidth 32).toNat k =
      tabOf Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5 (x.setWidth 32).toNat k :=
  htab _ _ (setWidth8_lt x) hk

/-- The registers a step writes. -/
def stepRegs : List Reg := [.r0, .r1, .r2, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem keyStep_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k0 : KSt} {j hh : Nat} (hj : j < 40)
    (h : KS m0 cb kb u (runSteps (halfSteps.take j) k0)) (h2 : u.gpr .r2 = BitVec.ofNat 32 j)
    (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa Impl.Cast5.Arm.step u fun v => KS m0 cb kb v (runSteps (halfSteps.take (j + 1)) k0) ∧
      v.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧ v.z = decide (j + 1 = 40) ∧ Keep stepRegs u v := by
  obtain ⟨hok, p1, p2, p3, p4, hkeys⟩ := step_facts hj
  obtain ⟨st, hst⟩ : ∃ st, halfSteps.getD j default = st := ⟨_, rfl⟩
  rw [hst] at hok p1 p2 p3 p4 hkeys
  obtain ⟨kj, hkj⟩ : ∃ kj, runSteps (halfSteps.take j) k0 = kj := ⟨_, rfl⟩
  rw [hkj] at h
  have hnext : runSteps (halfSteps.take (j + 1)) k0 = stepRun st kj := by
    rw [take_succ_steps hj, runSteps_append, hkj, hst]; rfl
  rw [hnext]
  have hlen40 : 0 + (halfSteps.map Step.gather).length ≤ 256 := by simp [halfSteps_length]
  unfold Impl.Cast5.Arm.step
  -- The step's bytes.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega) hlen40 h2
    fun u1 g1 m1 rd1 wr1 sp1 => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst, Step.gather_eq]
  have h1 : KS m0 cb kb u1 kj := h.update (g1 _) (by rw [m1]; exact h.mem) (fun i hi => by rw [m1]; exact h.ex i hi)
    h.len wr1
  refine WP.mono (gather_ok h1 p1 p2 p3 p4) fun v ⟨v4, v5, v6, v7, vk, vm⟩ => ?_
  have hv : KS m0 cb kb v kj := h1.update (vk.gpr _ (by decide)) (by rw [vm]; exact h1.mem)
    (fun i hi => by rw [vm]; exact h1.ex i hi) h1.len vk.wr
  -- The scan.
  have hidx : ∀ i < 4, (v.gpr (idxReg i)).toNat < 256 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · show (v.gpr .r4).toNat < 256; rw [v4]; exact setWidth8_lt _
    · show (v.gpr .r5).toNat < 256; rw [v5]; exact setWidth8_lt _
    · show (v.gpr .r6).toNat < 256; rw [v6]; exact setWidth8_lt _
    · show (v.gpr .r7).toNat < 256; rw [v7]; exact setWidth8_lt _
  refine WP.seq (WP.mono (scan_ok v tab5678 hidx) fun w ⟨wa, wk, wm⟩ => ?_)
  have hw : KS m0 cb kb w kj := hv.update (wk.gpr _ (by decide)) (by rw [wm]; exact hv.mem)
    (fun i hi => by rw [wm]; exact hv.ex i hi) hv.len wk.wr
  have a0 : w.gpr .r8 = Spec.Cast5.S8 (kj.xz.get (stepPos st).2.2.2) := by
    have := wa 0 (by decide)
    rw [show idxReg 0 = .r4 from rfl, v4, tab5678_eq (setWidth8_lt _) (by decide)] at this
    rw [show Reg.r8 = accReg 0 from rfl, this]; simp only [tabOf, ofNat_setWidth8]
  have a1 : w.gpr .r9 = Spec.Cast5.S7 (kj.xz.get (stepPos st).2.2.1) := by
    have := wa 1 (by decide)
    rw [show idxReg 1 = .r5 from rfl, v5, tab5678_eq (setWidth8_lt _) (by decide)] at this
    rw [show Reg.r9 = accReg 1 from rfl, this]; simp only [tabOf, ofNat_setWidth8]
  have a2 : w.gpr .r10 = Spec.Cast5.S6 (kj.xz.get (stepPos st).2.1) := by
    have := wa 2 (by decide)
    rw [show idxReg 2 = .r6 from rfl, v6, tab5678_eq (setWidth8_lt _) (by decide)] at this
    rw [show Reg.r10 = accReg 2 from rfl, this]; simp only [tabOf, ofNat_setWidth8]
  have a3 : w.gpr .r11 = Spec.Cast5.S5 (kj.xz.get (stepPos st).1) := by
    have := wa 3 (by decide)
    rw [show idxReg 3 = .r7 from rfl, v7, tab5678_eq (setWidth8_lt _) (by decide)] at this
    rw [show Reg.r11 = accReg 3 from rfl, this]; simp only [tabOf, ofNat_setWidth8]
  have kuw : Keep stepRegs u w := (Keep.mono (show Keep [.r4, .r5, .r6, .r7] u v from
    ⟨fun r hr => (vk.gpr r hr).trans (g1 r), vk.rd.trans rd1, vk.wr.trans wr1, vk.sp.trans sp1⟩) (by decide)).trans
    (wk.mono (by decide))
  have w2 : w.gpr .r2 = BitVec.ofNat 32 j := by rw [wk.gpr _ (by decide), vk.gpr _ (by decide), g1, h2]
  have wlr : w.gpr .lr = kb + BitVec.ofNat 32 (64 * hh) := by rw [kuw.gpr _ (by decide), hlr]
  -- What it does with the values.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega) (by simp [halfSteps_length]) w2
    fun x gx mx rdx wrx spx => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst]
  have hx : KS m0 cb kb x kj := hw.update (gx _) (by rw [mx]; exact hw.mem) (fun i hi => by rw [mx]; exact hw.ex i hi)
    hw.len wrx
  have tail (y : State) (hy : KS m0 cb kb y (stepRun st kj)) (ky : Keep stepRegs u y)
      (y2 : y.gpr .r2 = BitVec.ofNat 32 j) :
      WP isa (.block [.dp .add .r2 .r2 (.imm 1), .cmp .r2 (.imm 40)]) y fun z =>
        KS m0 cb kb z (stepRun st kj) ∧ z.gpr .r2 = BitVec.ofNat 32 (j + 1) ∧ z.z = decide (j + 1 = 40) ∧
          Keep stepRegs u z := by
    crun [y2]
    refine ⟨hy.update rfl hy.mem hy.ex hy.len rfl, by rw [BitVec.ofNat_add]; rfl, ?_,
      ky.trans ⟨fun r hr => by
        simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact hr (by decide)), rfl, rfl, rfl⟩⟩
    by_cases he : j = 39
    · subst he; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 j + 1 - 40 ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
        simp at this; omega
      simpa using this
  cases st with
  | extras a b c d =>
    refine WP.mono (postE_ok hx a b c d (exVal kj.xz a b c d) fun i hi => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans ⟨fun r _ => gx r, rdx, wrx, spx⟩).trans (ky.mono (by decide)))
        (by rw [ky.gpr _ (by decide), gx, w2])) fun z hz => hz
    · rw [gx]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
  | line l store =>
    refine WP.mono (postL_ok hx hok (by rw [gx]; exact a0) (by rw [gx]; exact a1) (by rw [gx]; exact a2)
      (by rw [gx]; exact a3) (by rw [gx]; exact wlr) fun jj e => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans ⟨fun r _ => gx r, rdx, wrx, spx⟩).trans (ky.mono (by decide)))
        (by rw [ky.gpr _ (by decide), gx, w2])) fun z hz => hz
    subst e
    have hc := hkeys l jj rfl
    have hl := ws_length (halfSteps.take j) k0
    rw [hkj] at hl
    have hlim : countKeys (halfSteps.take j) < 16 := by
      have := hok; simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at this; omega
    exact ⟨by rw [hl, hc, hlen0], by rw [hl, hlen0]; omega⟩

/-! ## A half -/

/-- The registers a half writes. -/
def halfRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem take_steps_40 : halfSteps.take 40 = halfSteps := by
  rw [List.take_of_length_le (by rw [halfSteps_length])]

theorem half_ok {m0 : Mem} {cb kb : BitVec 32} {u : State} {k0 : KSt} {hh : Nat} (h : KS m0 cb kb u k0)
    (hlr : u.gpr .lr = kb + BitVec.ofNat 32 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa half u fun v => ∃ k, KS m0 cb kb v k ∧ k.xz = (halfImpl k0.xz).2 ∧ k.ws = k0.ws ++ (halfImpl k0.xz).1 ∧
      v.gpr .lr = kb + BitVec.ofNat 32 (64 * (hh + 1)) ∧ v.gpr .r3 = u.gpr .r3 - 1 ∧
      v.z = (u.gpr .r3 - 1 == 0) ∧ Keep halfRegs u v := by
  unfold half
  refine WP.seq ?_
  crun
  obtain ⟨u0, hu0⟩ : ∃ u0, u.setReg .r2 0 = u0 := ⟨_, rfl⟩
  rw [hu0]
  have k0u : Keep stepRegs u u0 := by
    rw [← hu0]; exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by intro e; subst e; exact hr (by decide)), rfl, rfl, rfl⟩
  have h0 : KS m0 cb kb u0 (runSteps (halfSteps.take 0) k0) := by
    rw [← hu0]; exact h.update rfl h.mem h.ex h.len rfl
  have loop : WP isa (.loop Impl.Cast5.Arm.step .ne) u0
      (fun v => KS m0 cb kb v (runSteps halfSteps k0) ∧ Keep stepRegs u v) := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = 40 - j ∧ j < 40 ∧
      KS m0 cb kb v (runSteps (halfSteps.take j) k0) ∧ v.gpr .r2 = BitVec.ofNat 32 j ∧ Keep stepRegs u v)
      ?_ 40 u0 ⟨0, rfl, by decide, h0, by rw [← hu0]; rfl, k0u⟩
    rintro m v ⟨j, rfl, hj, hv, v2, kv⟩
    refine WP.mono (keyStep_ok hj hv v2 (by rw [kv.gpr _ (by decide), hlr]) hlen0 hhh) fun w ⟨hw, w2, wz, kw⟩ => ?_
    by_cases he : j + 1 = 40
    · refine .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, ?_, kv.trans kw⟩
      rw [he, take_steps_40] at hw; exact hw
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 40 - (j + 1), by omega, j + 1, rfl,
        by omega, hw, w2, kv.trans kw⟩
  refine WP.seq (WP.mono loop fun v ⟨hv, kv⟩ => ?_)
  have vlr : v.gpr .lr = kb + BitVec.ofNat 32 (64 * hh) := by rw [kv.gpr _ (by decide), hlr]
  have v3 : v.gpr .r3 = u.gpr .r3 := kv.gpr _ (by decide)
  crun [vlr, v3]
  obtain ⟨hx, hw⟩ := runSteps_half k0
  refine ⟨runSteps halfSteps k0, hv.update (by simp only [gpr_setReg, gpr_sub, reduceCtorEq, ite_false]) hv.mem
    hv.ex hv.len rfl, hx, hw, ?_, (kv.mono (by decide)).trans ⟨?_, rfl, rfl, rfl⟩⟩
  rotate_left
  · intro r hr
    have h3 : ¬r = .r3 := by intro e; subst e; exact hr (by decide)
    have hl : ¬r = .lr := by intro e; subst e; exact hr (by decide)
    rw [gpr_setReg_of_ne _ _ h3, gpr_sub, gpr_setReg_of_ne _ _ hl]
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl]

end VG.Proof.Cast5.Arm
