import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Digit
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-!
# Ed448 verification on AArch64: one window of the challenge

Untrusted: everything here is checked by Lean. `window sh`, in the windows'
state `WCtx` (the table of `tabPts P` stored, 1 in slot 20, zero in slot 19): `Q` (slots 3–5) doubled four times, the
entry of the challenge's digit selected into slots 6–8, and added
(`window_ok`): `Q` becomes `wstep P Q n`, and slots 0–2 are kept.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf ops_append)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-- Four doublings. -/
def dbl4 (Q : Point) : Point :=
  VG.Proof.Ed448.double (VG.Proof.Ed448.double (VG.Proof.Ed448.double (VG.Proof.Ed448.double Q)))

/-- A window: `Q` doubled four times, plus entry `n`. -/
def wstep (P Q : Point) (n : Nat) : Point := addPt (dbl4 Q) (tabPts P n)

theorem genEnv_345 (e : Env) : pt (genEnv 3 4 5 6 7 8 e) 3 4 5 = genPt (pt e 3 4 5) (pt e 6 7 8) (e 19) := rfl

theorem TabOk.of_outside2 {m m' : Mem} {base : Addr} {P : Point} {k : Nat} (h : TabOk m base P k)
    (ho : Outside2 base 64 2816 ACC 1152 m m') (hk : k ≤ 16) : TabOk m' base P k := by
  have hw : ∀ e < 16, ∀ w < 24, tw m' base e w = tw m base e w := fun e he w hw => by
    unfold tw
    exact ho.word (Or.inr (by simp only [TAB]; omega)) (Or.inr (by simp only [ACC, TAB]; omega))
      (by simp only [TAB]; omega)
  intro e he
  refine ⟨by rw [TPt_of_tw (hw e (by omega))]; exact (h e he).1, fun w hw' => ?_⟩
  rw [hw e (by omega) w hw']; exact (h e he).2 w hw'

/-- The windows' state, from the state `s₀` at their start, for the table of `P`. -/
structure WCtx (s₀ : State) (base : Addr) (P : Point) (s : State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  one : EV s.mem base 20 = 1
  z5 : Bnd Mb s.mem base (slot (5 : Index).val)
  tab : TabOk s.mem base P 16
  lr : s.gpr .x30 = s₀.gpr .x30
  chk : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside2 base 64 2816 ACC 1152 s₀.mem s.mem

theorem WCtx.of_fkeep {s₀ s t : State} {base : Addr} {P : Point} (h : WCtx s₀ base P s)
    (k : FKeep base s t) (b : BEnv t.mem base) (z : ∀ w < 8, limbs t.mem base (slot (19 : Index).val) w = 0)
    (o : EV t.mem base 20 = 1) (z5 : Bnd Mb t.mem base (slot (5 : Index).val)) : WCtx s₀ base P t :=
  ⟨k.scr h.scr, b, z, o, z5, h.tab.of_outside2 k.mem (by decide),
    (k.regs.1 _ (by decide)).trans h.lr, (k.regs.1 _ (by decide)).trans h.chk,
    k.regs.2.1.trans h.rd, k.regs.2.2.trans h.wr, h.mem.trans k.mem⟩

/-- Slots other than 3–5 and the temporaries, kept. -/
def Kept (base : Addr) (m m' : Mem) : Prop :=
  ∀ i : Index, i ∉ temps ++ [3, 4, 5, 6, 7, 8] → ∀ j < 8, limbs m' base (slot i.val) j = limbs m base (slot i.val) j

theorem Kept.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Kept base m₁ m₂) (h₂ : Kept base m₂ m₃) :
    Kept base m₁ m₃ := fun i hi j hj => (h₂ i hi j hj).trans (h₁ i hi j hj)

theorem Kept.of_same {base : Addr} {l : List Index} {m m' : Mem} (h : Same base l m m')
    (hl : ∀ i ∈ l, i ∈ temps ++ [3, 4, 5, 6, 7, 8]) : Kept base m m' := fun i hi j hj =>
  h i (fun e => hi (hl i e)) j hj

theorem Kept.env {base : Addr} {m m' : Mem} (h : Kept base m m') {i : Index} (hi : i ∉ temps ++ [3, 4, 5, 6, 7, 8]) :
    EV m' base i = EV m base i := congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (h i hi))

/-! ## The doublings -/

theorem dbl_step {s₀ s : State} {base : Addr} {P : Point} (h : WCtx s₀ base P s) :
    WP isa (ops (Impl.Ed448.AArch64.dblOps (slot (3 : Index).val) (slot (4 : Index).val) (slot (5 : Index).val))) s
      fun t => WCtx s₀ base P t ∧ pt (EV t.mem base) 3 4 5 = VG.Proof.Ed448.double (pt (EV s.mem base) 3 4 5) ∧
        Kept base s.mem t.mem ∧ t.gpr .x19 = s.gpr .x19 ∧ t.gpr .x1 = s.gpr .x1 := by
  refine WP.mono (dblOps_ok 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.scr
    h.env h.z5) fun t ⟨k, b, sm, _, _, mz, e⟩ => ?_
  refine ⟨h.of_fkeep k b (fun w hw => by rw [sm 19 (by decide) w hw]; exact h.zero w hw)
    (by rw [Same.env sm (i := 20) (by decide)]; exact h.one) mz, ?_,
    Kept.of_same sm (by decide), k.regs.1 _ (by decide), k.regs.1 _ (by decide)⟩
  rw [e, dblEnv_345, h.one, dblPt_eq]

theorem setX1_ok (s : State) :
    WP isa (.block [.movz .w .x1 4 0]) s fun t => t.gpr .x1 = BitVec.ofNat 64 4 ∧ Keeps [.x1] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl⟩, rfl⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

private theorem dec_x1 : ∀ n < 4, BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 n ∧
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

theorem decX1_ok (s : State) {n : Nat} (hn : n < 4) (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (1 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc,
    (dec_x1 n hn).1, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

/-- `Q` doubled `n` times. -/
def dblN (Q : Point) : Nat → Point
  | 0 => Q
  | n + 1 => VG.Proof.Ed448.double (dblN Q n)

theorem dbl4_ok {s₀ s : State} {base : Addr} {P : Point} (h : WCtx s₀ base P s) :
    WP isa dbl4Loop s
      fun t => WCtx s₀ base P t ∧ pt (EV t.mem base) 3 4 5 = dbl4 (pt (EV s.mem base) 3 4 5) ∧
        Kept base s.mem t.mem ∧ t.gpr .x19 = s.gpr .x19 := by
  unfold dbl4Loop
  refine WP.seq (WP.mono (setX1_ok s) fun s₁ ⟨c₁, k₁, m₁⟩ => ?_)
  have h₁ : WCtx s₀ base P s₁ :=
    ⟨h.scr.of_keeps k₁ (by decide), by rw [m₁]; exact h.env, by rw [m₁]; exact h.zero,
      by rw [m₁]; exact h.one, by rw [m₁]; exact h.z5, by rw [m₁]; exact h.tab,
      by rw [k₁.1 _ (by decide)]; exact h.lr, by rw [k₁.1 _ (by decide)]; exact h.chk,
      by rw [k₁.2.1]; exact h.rd, by rw [k₁.2.2]; exact h.wr, by rw [m₁]; exact h.mem⟩
  refine WP.loop (M := isa) (fun n (t : State) => 1 ≤ n ∧ n ≤ 4 ∧ t.gpr .x1 = BitVec.ofNat 64 n ∧
      WCtx s₀ base P t ∧ pt (EV t.mem base) 3 4 5 = dblN (pt (EV s.mem base) 3 4 5) (4 - n) ∧
      Kept base s.mem t.mem ∧ t.gpr .x19 = s.gpr .x19) ?_ 4 s₁
    ⟨by decide, by decide, c₁, h₁, by rw [m₁]; rfl, fun _ _ _ _ => by rw [m₁],
      k₁.1 _ (by decide)⟩
  intro n t ⟨n1, n4, ct, ht, qt, kt, xt⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (block_codeOf (dbl_step ht)) fun u ⟨hu, qu, ku, xu, x1u⟩ => ?_
  have cu : u.gpr .x1 = BitVec.ofNat 64 (k + 1) := x1u.trans ct
  refine WP.mono (decX1_ok u (by omega) cu) fun v ⟨cv, kv, mv⟩ => ?_
  have hv : WCtx s₀ base P v :=
    ⟨hu.scr.of_keeps kv (by decide), by rw [mv]; exact hu.env, by rw [mv]; exact hu.zero,
      by rw [mv]; exact hu.one, by rw [mv]; exact hu.z5, by rw [mv]; exact hu.tab,
      by rw [kv.1 _ (by decide)]; exact hu.lr, by rw [kv.1 _ (by decide)]; exact hu.chk,
      by rw [kv.2.1]; exact hu.rd, by rw [kv.2.2]; exact hu.wr, by rw [mv]; exact hu.mem⟩
  have qv : pt (EV v.mem base) 3 4 5 = dblN (pt (EV s.mem base) 3 4 5) (4 - k) := by
    rw [mv, qu, qt, show 4 - k = (4 - (k + 1)) + 1 by omega]; rfl
  have kv' : Kept base s.mem v.mem := kt.trans (by rw [mv]; exact ku)
  have xv : v.gpr .x19 = s.gpr .x19 := by rw [kv.1 _ (by decide), xu, xt]
  simp only [eval, State.read, BitVec.setWidth_eq, cv, (dec_x1 k (by omega)).2]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact .inl ⟨rfl, hv, by rw [qv]; rfl, kv', xv⟩
  · exact .inr ⟨congrArg some (decide_eq_true (by omega)), k, by omega, by omega, by omega, rfl, hv, qv, kv', xv⟩

/-! ## The selected entry -/

theorem dst_slot {c i : Nat} (hi : i < 8) : dst (8 * c + i) = slot (6 + c) + 8 * i := by
  simp only [dst, slot]; omega

theorem select_env {s t : State} {base : Addr} {P : Point} {n : Nat} (hn : n < 16)
    (hsel : ∀ w < 24, word t.mem base (dst w) = tw s.mem base n w) (ho : Outside base 832 384 s.mem t.mem)
    (hb : BEnv s.mem base) (htab : TabOk s.mem base P 16) :
    BEnv t.mem base ∧ pt (EV t.mem base) 6 7 8 = tabPts P n ∧ Kept base s.mem t.mem ∧
      (∀ i : Index, (i.val < 6 ∨ 9 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j) := by
  have keep : ∀ i : Index, (i.val < 6 ∨ 9 ≤ i.val) → ∀ j < 8,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := fun i hi j hj => by
    have := i.isLt
    exact ho.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) (by omega)
  have hc : ∀ c < 3, FV t.mem base (slot (6 + c)) = FV s.mem base (TAB + 192 * n + 64 * c) := fun c hc =>
    (FV_entry s.mem t.mem base (e := n) (c := c) rfl (fun i hi => by rw [← hsel _ (by omega), dst_slot hi])).symm
  refine ⟨fun i => ?_, ?_, fun i hi j hj => keep i ?_ j hj, keep⟩
  · by_cases h : i.val < 6 ∨ 9 ≤ i.val
    · exact fun j hj => by rw [keep i h j hj]; exact hb i j hj
    · intro j hj
      have hi' : i.val = 6 + (i.val - 6) := by omega
      show (word t.mem base (slot i.val + 8 * j)).toNat < Ib
      rw [hi', ← dst_slot (c := i.val - 6) hj, hsel _ (by omega)]
      exact (htab n hn).2 _ (by omega)
  · rw [← (htab n hn).1]
    show (⟨FV t.mem base (slot (6 + 0)), FV t.mem base (slot (6 + 1)), FV t.mem base (slot (6 + 2))⟩ : Point) = _
    rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide)]
    simp only [TPt, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  · by_contra h
    have := i.isLt
    apply hi
    simp only [temps, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases i with ⟨i, hlt⟩
    simp only [Fin.ext_iff] at *
    omega

/-! ## A window -/

/-- **A window**, for byte `j` of the challenge's copy at `KB` (`x19 = j`), at shift `sh`. -/
theorem window_ok {s₀ s : State} {base : Addr} {P : Point} (h : WCtx s₀ base P s) {j : Nat} (hj : j < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) {sh : Nat} (hsh : sh = 0 ∨ sh = 4) :
    WP isa (window sh) s fun t =>
      WCtx s₀ base P t ∧
      pt (EV t.mem base) 3 4 5 = wstep P (pt (EV s.mem base) 3 4 5) (nibOf (s₀.mem (off base (KB + j))) sh) ∧
      pt (EV t.mem base) 0 1 2 = pt (EV s.mem base) 0 1 2 ∧ t.gpr .x19 = s.gpr .x19 := by
  unfold window
  refine WP.seq (WP.mono (dbl4_ok h) fun t1 ⟨h1, q1, k1, c1⟩ => ?_)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (digitOf_ok h1.scr hj (c1.trans hc) hsh) fun t2 ⟨d2, k2, m2⟩ => ?_
  have hs2 : Scr t2 base := h1.scr.of_keeps k2 (by decide)
  -- The byte read is the copy's at the windows' start.
  have hbyte : t1.mem (off base (KB + j)) = s₀.mem (off base (KB + j)) := by
    have hn := h1.scr.nowrap
    have ho : ofs base (off base (KB + j)) = KB + j := ofs_off0' base (by simp only [KB]; omega)
    exact h1.mem _ (Or.inr (by rw [ho]; simp only [KB]; omega)) (Or.inl (by rw [ho]; simp only [KB, ACC]; omega))
  rw [hbyte] at d2
  have hn := nibOf_lt (s₀.mem (off base (KB + j))) sh
  rw [WP.block_append_iff]
  refine WP.mono (selectEntry_ok hs2 hn d2) fun t3 ⟨w3, o3, k3⟩ => ?_
  have hs3 : Scr t3 base := hs2.of_keeps k3 (by decide)
  obtain ⟨b3, e3, kp3, kk3⟩ := select_env hn w3 o3 (by rw [m2]; exact h1.env) (by rw [m2]; exact h1.tab)
  have o3' : Outside2 base 64 2816 ACC 1152 t2.mem t3.mem := fun x a _ => o3 x (by omega)
  have keepE : ∀ i : Index, (i.val < 6 ∨ 9 ≤ i.val) → EV t3.mem base i = EV t1.mem base i := fun i hi => by
    rw [← m2]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (kk3 i hi))
  have h3 : WCtx s₀ base P t3 :=
    ⟨hs3, b3, fun w hw => by rw [kk3 19 (by decide) w hw, m2]; exact h1.zero w hw,
      by rw [keepE 20 (by decide)]; exact h1.one,
      fun w hw => by rw [kk3 5 (by decide) w hw, m2]; exact h1.z5 w hw,
      (by rw [m2] at o3'; exact h1.tab.of_outside2 o3' (by decide)),
      by rw [k3.1 _ (by decide), k2.1 _ (by decide)]; exact h1.lr,
      by rw [k3.1 _ (by decide), k2.1 _ (by decide)]; exact h1.chk,
      by rw [k3.2.1, k2.2.1]; exact h1.rd, by rw [k3.2.2, k2.2.2]; exact h1.wr,
      by rw [m2] at o3'; exact h1.mem.trans o3'⟩
  refine WP.mono (block_codeOf (addOps_ok 3 4 5 6 7 8 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hs3 b3 (zero_env h3.zero).2))
    fun t4 ⟨k4, b4, s4, _, _, m5, e4⟩ => ?_
  refine ⟨h3.of_fkeep k4 b4 (fun w hw => by rw [s4 19 (by decide) w hw]; exact h3.zero w hw)
    (by rw [Same.env s4 (i := 20) (by decide)]; exact h3.one) m5, ?_, ?_, ?_⟩
  · rw [e4, genEnv_345, (zero_env h3.zero).1, VG.Proof.X448.AArch64.Base.genPt_eq, e3, wstep, ← q1]
    simp only [pt]
    rw [keepE 3 (by decide), keepE 4 (by decide), keepE 5 (by decide)]
  · have k14 : Kept base s.mem t4.mem := (k1.trans (by rw [m2] at kp3; exact kp3)).trans
      (Kept.of_same s4 (by decide))
    simp only [pt]
    rw [k14.env (i := 0) (by decide), k14.env (i := 1) (by decide), k14.env (i := 2) (by decide)]
  · rw [k4.regs.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide), c1]

end VG.Proof.Ed448.AArch64.Window
