module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.KeyStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# CAST5 key expansion on PPC64LE: the steps of a half, run

`keyStep_ok`: step `j` of a half (its number in `stp`) is the spec's
`stepRun`; `half_ok`: the 40 steps of a half compute `halfImpl`
(`runSteps_half`), writing its sixteen subkeys from `out`.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE

open VG VG.PPC64LE VG.Impl.Cast5 VG.Impl.Cast5.PPC64LE VG.Proof.Cast5

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
    rcases s with ⟨⟩ | ⟨l, ⟨⟩ | ⟨⟩⟩ <;> simp [stepRun, isKey, List.filter_cons] <;> omega_arith

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

theorem ofNat_setWidth8 (x : Byte) : BitVec.ofNat 8 (x.setWidth 64).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith

theorem setWidth8_lt (x : Byte) : (x.setWidth 64).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega_arith

/-! ## A step -/

theorem keyStep_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k0 : KSt} {j hh : Nat} (hj : j < 40)
    (h : KS m0 cb kb T u (runSteps (halfSteps.take j) k0)) (h2 : u.gpr stp = BitVec.ofNat 64 j)
    (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa Impl.Cast5.PPC64LE.step u fun v => KS m0 cb kb T v (runSteps (halfSteps.take (j + 1)) k0) ∧
      v.gpr stp = BitVec.ofNat 64 (j + 1) ∧ v.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ∧
      Keep stepRegs u v := by
  obtain ⟨hok, p1, p2, p3, p4, hkeys⟩ := step_facts hj
  obtain ⟨st, hst⟩ : ∃ st, halfSteps.getD j default = st := ⟨_, rfl⟩
  rw [hst] at hok p1 p2 p3 p4 hkeys
  obtain ⟨kj, hkj⟩ : ∃ kj, runSteps (halfSteps.take j) k0 = kj := ⟨_, rfl⟩
  rw [hkj] at h
  have hnext : runSteps (halfSteps.take (j + 1)) k0 = stepRun st kj := by
    rw [take_succ_steps hj, runSteps_append, hkj, hst]; rfl
  rw [hnext]
  have hlen40 : 0 + (halfSteps.map Step.gather).length ≤ 2 ^ 15 := by simp [halfSteps_length]
  unfold Impl.Cast5.PPC64LE.step
  -- The step's bytes.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) hlen40 h2
    fun u1 k1 m1 => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst, Step.gather_eq]
  have h1 : KS m0 cb kb T u1 kj := h.update k1 (by rw [m1]; exact h.mem) (fun i hi => by rw [m1]; exact h.ex i hi)
    h.len
  refine WP.mono (gather_ok h1 p1 p2 p3 p4) fun v ⟨v4, v5, v6, v7, vk, vm⟩ => ?_
  have hv : KS m0 cb kb T v kj := h1.update vk (by rw [vm]; exact h1.mem)
    (fun i hi => by rw [vm]; exact h1.ex i hi) h1.len
  -- The scan.
  have hidx : ∀ i < 4, (v.gpr (idxReg i)).toNat < 256 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · show (v.gpr .r14).toNat < 256; rw [v4]; exact setWidth8_lt _
    · show (v.gpr .r15).toNat < 256; rw [v5]; exact setWidth8_lt _
    · show (v.gpr .r16).toNat < 256; rw [v6]; exact setWidth8_lt _
    · show (v.gpr .r17).toNat < 256; rw [v7]; exact setWidth8_lt _
  have sp : ScanPre v := ⟨hidx, hv.zero, by rw [hv.tblR]; exact hv.trd⟩
  refine WP.seq (WP.mono (scan_ok v sp) fun w ⟨wa, wk, wm⟩ => ?_)
  have hw : KS m0 cb kb T w kj := hv.update wk (by rw [wm]; exact hv.mem) (fun i hi => by rw [wm]; exact hv.ex i hi)
    hv.len
  have ent (i : Nat) (hi : i < 4) (x : Byte) (hx : v.gpr (idxReg i) = x.setWidth 64) :
      lo (w.gpr (accReg i)) = tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5
        (x.setWidth 64).toNat i := by
    rw [wa i hi, hx, lo_ext, hv.tblR]; exact ent_table hv.held (setWidth8_lt _) hi
  have a0 : lo (w.gpr .r18) = Spec.Cast5.S8 (kj.xz.get (stepPos st).2.2.2) := by
    rw [show Reg.r18 = accReg 0 from rfl, ent 0 (by decide) _ v4]; simp only [tableEnt, ofNat_setWidth8]
  have a1 : lo (w.gpr .r19) = Spec.Cast5.S7 (kj.xz.get (stepPos st).2.2.1) := by
    rw [show Reg.r19 = accReg 1 from rfl, ent 1 (by decide) _ v5]; simp only [tableEnt, ofNat_setWidth8]
  have a2 : lo (w.gpr .r20) = Spec.Cast5.S6 (kj.xz.get (stepPos st).2.1) := by
    rw [show Reg.r20 = accReg 2 from rfl, ent 2 (by decide) _ v6]; simp only [tableEnt, ofNat_setWidth8]
  have a3 : lo (w.gpr .r21) = Spec.Cast5.S5 (kj.xz.get (stepPos st).1) := by
    rw [show Reg.r21 = accReg 3 from rfl, ent 3 (by decide) _ v7]; simp only [tableEnt, ofNat_setWidth8]
  have kuw' := (k1.trans vk).trans wk
  have kuw : Keep stepRegs u w := kuw'.mono (by decide)
  have w2 : w.gpr stp = BitVec.ofNat 64 j := by rw [kuw'.gpr (by decide), h2]
  have wout : w.gpr out = kb + BitVec.ofNat 64 (64 * hh) := by rw [kuw'.gpr (by decide), hout]
  -- What it does with the values.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) (by simp [halfSteps_length]) w2
    fun x kx mx => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst]
  have hx : KS m0 cb kb T x kj := hw.update kx (by rw [mx]; exact hw.mem) (fun i hi => by rw [mx]; exact hw.ex i hi)
    hw.len
  have gx (q : Reg) (hq : q ≠ tmp) : x.gpr q = w.gpr q := kx.gpr (by simpa using hq)
  have tail (y : State) (hy : KS m0 cb kb T y (stepRun st kj)) (ky : Keep stepRegs u y)
      (y2 : y.gpr stp = BitVec.ofNat 64 j) :
      WP isa (.block [.addi stp stp 1, .subi tmp stp 40]) y fun z =>
        KS m0 cb kb T z (stepRun st kj) ∧ z.gpr stp = BitVec.ofNat 64 (j + 1) ∧
          z.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ∧ Keep stepRegs u z := by
    refine wp_addi (by decide) (by decide) fun z₁ h₁ => wp_subi (by decide) (by decide) fun z₂ h₂ => wp_nil ?_
    have kz : Keep [stp, tmp] y z₂ := (h₁.keep.trans h₂.keep).mono (by decide)
    refine ⟨hy.update kz (by rw [h₂.mem, h₁.mem]; exact hy.mem) (fun i hi => by rw [h₂.mem, h₁.mem]; exact hy.ex i hi)
      hy.len, ?_, ?_, (ky.trans kz).mono (by decide)⟩
    · rw [h₂.other _ (by decide), h₁.gpr, y2, BitVec.ofNat_add]
    · rw [h₂.gpr, h₁.gpr, y2, BitVec.ofNat_add]
  cases st with
  | extras a b c d =>
    refine WP.mono (postE_ok hx a b c d (exVal kj.xz a b c d) fun i hi => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans kx).trans ky |>.mono (by decide))
        (by rw [ky.gpr (by decide), gx _ (by decide), w2])) fun z hz => hz
    · rw [gx _ (by unfold accReg; split <;> decide)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
  | line l store =>
    refine WP.mono (postL_ok hx hok (by rw [gx _ (by decide)]; exact a0) (by rw [gx _ (by decide)]; exact a1)
      (by rw [gx _ (by decide)]; exact a2) (by rw [gx _ (by decide)]; exact a3)
      (by rw [gx _ (by decide)]; exact wout) fun jj e => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans kx).trans ky |>.mono (by decide))
        (by rw [ky.gpr (by decide), gx _ (by decide), w2])) fun z hz => hz
    subst e
    have hc := hkeys l jj rfl
    have hl := ws_length (halfSteps.take j) k0
    rw [hkj] at hl
    have hlim : countKeys (halfSteps.take j) < 16 := by
      have := hok; simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at this; omega
    exact ⟨by rw [hl, hc, hlen0], by rw [hl, hlen0]; omega_arith⟩

/-! ## A half -/

/-- The registers a half writes. -/
def halfRegs : List Reg := stepRegs ++ [out, hlv]

theorem take_steps_40 : halfSteps.take 40 = halfSteps := by
  rw [List.take_of_length_le (by rw [halfSteps_length])]

theorem tmp_step_ne {j : Nat} (hj : j < 40) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 != 0) = !decide (j + 1 = 40) := by
  by_cases he : j + 1 = 40
  · rw [he]; rfl
  · rw [decide_eq_false he]
    have : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      simp at this; omega
    simpa using this

theorem half_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k0 : KSt} {hh : Nat} (h : KS m0 cb kb T u k0)
    (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa half u fun v => ∃ k, KS m0 cb kb T v k ∧ k.xz = (halfImpl k0.xz).2 ∧
      k.ws = k0.ws ++ (halfImpl k0.xz).1 ∧ v.gpr out = kb + BitVec.ofNat 64 (64 * (hh + 1)) ∧
      v.gpr hlv = u.gpr hlv - 1#64 ∧ Keep halfRegs u v := by
  unfold half
  refine WP.seq (wp_li (by decide) fun u0 hu0 => wp_nil ?_)
  have k0u : Keep stepRegs u u0 := hu0.keep.mono (by decide)
  have h0 : KS m0 cb kb T u0 (runSteps (halfSteps.take 0) k0) :=
    h.update hu0.keep (by rw [hu0.mem]; exact h.mem) (fun i hi => by rw [hu0.mem]; exact h.ex i hi) h.len
  have loop : WP isa (.loop Impl.Cast5.PPC64LE.step (.nonzero .d tmp)) u0
      (fun v => KS m0 cb kb T v (runSteps halfSteps k0) ∧ Keep stepRegs u v) := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = 40 - j ∧ j < 40 ∧
      KS m0 cb kb T v (runSteps (halfSteps.take j) k0) ∧ v.gpr stp = BitVec.ofNat 64 j ∧ Keep stepRegs u v)
      ?_ 40 u0 ⟨0, rfl, by decide, h0, hu0.gpr, k0u⟩
    rintro m v ⟨j, rfl, hj, hv, v2, kv⟩
    refine WP.mono (keyStep_ok hj hv v2 (by rw [kv.gpr (by decide), hout]) hlen0 hhh)
      fun w ⟨hw, w2, wt, kw⟩ => ?_
    have ev : isa.eval (.nonzero .d tmp) w = some (!decide (j + 1 = 40)) := by
      rw [eval_nonzero, wt, tmp_step_ne hj]
    by_cases he : j + 1 = 40
    · refine .inl ⟨by rw [ev, decide_eq_true he]; rfl, ?_, (kv.trans kw).mono (by decide)⟩
      rw [he, take_steps_40] at hw; exact hw
    · exact .inr ⟨by rw [ev, decide_eq_false he]; rfl, 40 - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, hw, w2, (kv.trans kw).mono (by decide)⟩
  refine WP.seq (WP.mono loop fun v ⟨hv, kv⟩ => ?_)
  refine wp_addi (by decide) (by decide) fun v₁ h₁ => wp_subi (by decide) (by decide) fun v₂ h₂ => wp_nil ?_
  obtain ⟨hx, hw⟩ := runSteps_half k0
  have k12 : Keep [out, hlv] v v₂ := (h₁.keep.trans h₂.keep).mono (by decide)
  refine ⟨runSteps halfSteps k0, hv.update k12 (by rw [h₂.mem, h₁.mem]; exact hv.mem)
    (fun i hi => by rw [h₂.mem, h₁.mem]; exact hv.ex i hi) hv.len, hx, hw, ?_, ?_, (kv.trans k12).mono (by decide)⟩
  · rw [h₂.other _ (by decide), h₁.gpr, kv.gpr (by decide), hout, Offset.add_add, Nat.mul_succ]
  · rw [h₂.gpr, h₁.other _ (by decide), kv.gpr (by decide)]

end VG.Proof.Cast5.PPC64LE
