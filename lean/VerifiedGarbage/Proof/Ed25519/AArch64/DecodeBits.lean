import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Impl.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Impl.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.RootPower
import VerifiedGarbage.Impl.Ed25519.AArch64.FieldCheck
import VerifiedGarbage.Impl.Ed25519.AArch64.RecoverSign
import VerifiedGarbage.Proof.Ed25519.Signing

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Freeze`. -/
section

/-! Full reduction of four limbs to the canonical residue. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.X25519 (P)

theorem freezeFold_ok (s : State) (hz : s.gpr .x10 = 0) (h19 : s.gpr .x11 = 19)
    (hl : s.gpr .x2 = low63) :
    WP isa (.block freezeFold) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) % P =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % P ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) < 2 ^ 255 + 19 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x3] s t := by
  have hm (x : VG.Proof.Ed25519.Word64.Word) : ((x >>> 63) * 19).toNat = 19 * (x.toNat / 2 ^ 63) := by
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (19 : VG.Proof.Ed25519.Word64.Word).toNat = 19 from rfl, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  apply WP.of_runBlock
  simp only [freezeFold, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := fold_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    (s.gpr .x7 &&& low63) ((s.gpr .x7 >>> 63) * 19) (hm _) (and_low63 _)
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem freezeCandidate_ok (s : State) (hz : s.gpr .x10 = 0) (h19 : s.gpr .x11 = 19)
    (hl : s.gpr .x2 = low63)
    (hx : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) < 2 ^ 255 + 19) :
    WP isa (.block freezeCandidate) s fun t =>
      t.gpr .x3 = mask (decide (P ≤ val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7))) ∧
      (P ≤ val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) →
        val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) - P) ∧
      Keeps [.x21, .x22, .x23, .x24, .x8, .x3] s t := by
  apply WP.of_runBlock
  simp only [freezeCandidate, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, hz, h19, hl, show 63 < Size.x.bits from by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have H := add19_top (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) hx
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits, low63] at H ⊢
    exact H.2
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem select4_ok (s : State) {sw : Bool} (hm : s.gpr .x3 = mask sw) :
    WP isa (.block select4) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (if sw then val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
          else val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [select4, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, hm, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', xor_sel']
  refine ⟨by cases sw <;> rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-- The result is the unique representative below p. -/
theorem freeze_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat} (ha : FieldRange a large) :
    WP isa (.block (freeze a)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base a % P ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [freeze, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (fieldInit_ok s 19) fun s₀ ⟨hz, h19, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₀ .x2 low63) fun s₁ ⟨hl, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs₁ ha (by decide)) fun s₂ ⟨w4, w5, w6, w7, k2⟩ => ?_
  have hz2 : s₂.gpr .x10 = 0 := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans hz)
  have h192 : s₂.gpr .x11 = 19 := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h19)
  have hl2 : s₂.gpr .x2 = low63 := (k2.gpr _ (by decide)).trans hl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freezeFold_ok s₂ hz2 h192 hl2) fun s₃ ⟨e3, b3, k3⟩ => ?_
  have hz3 := (k3.gpr .x10 (by decide)).trans hz2
  have h193 := (k3.gpr .x11 (by decide)).trans h192
  have hl3 := (k3.gpr .x2 (by decide)).trans hl2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freezeCandidate_ok s₃ hz3 h193 hl3 b3) fun s₄ ⟨m4, v4, k4⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.select4_ok s₄ m4) fun s₅ ⟨v5, k5⟩ => ?_
  have K : Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s s₅ :=
    ((((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      (k3.mono (by decide))).trans (k4.mono (by decide)) |>.trans (k5.mono (by decide))
  rw [k4.gpr .x4 (by decide), k4.gpr .x5 (by decide), k4.gpr .x6 (by decide),
    k4.gpr .x7 (by decide)] at v5
  rw [w4, w5, w6, w7, k1.mem, k0.mem] at e3
  refine ⟨?_, K⟩
  rw [v5, ← e3]
  generalize val4 (s₃.gpr .x4) (s₃.gpr .x5) (s₃.gpr .x6) (s₃.gpr .x7) = x at b3 v4 ⊢
  by_cases h : P ≤ x
  · simp only [decide_eq_true h, ite_true]
    rw [v4 h]
    simp only [P] at h b3 ⊢
    omega_using [h, b3]
  · simp only [decide_eq_false h, Bool.false_eq_true, ite_false]
    exact (Nat.mod_eq_of_lt (by omega)).symm

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Power`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PowerEnv`. -/
section
/-! Compositional field exponentiation and fixed-count squaring loops. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

/-- What the inversion keeps: the registers but `clob` and `x19`, the regions,
and the memory outside `[512, 640)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outside base 512 128 s.mem s'.mem

theorem IKeep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Ed25519.AArch64.IKeep base s₁ s₂)
    (h₂ : VG.Proof.Ed25519.AArch64.IKeep base s₂ s₃) : VG.Proof.Ed25519.AArch64.IKeep base s₁ s₃ :=
  ⟨fun r hr hb => (h₂.gpr r hr hb).trans (h₁.gpr r hr hb), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₁.mem.trans h₂.mem⟩

theorem IKeep.scr {base : Addr} {s s' : State} (h : VG.Proof.Ed25519.AArch64.IKeep base s s') (hs : Scr s base large) :
    Scr s' base large :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `c` changes the slots by `f`, and keeps everything else (`IKeep`). -/
def ISpec (base : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base large → WP isa c s fun s' => VG.Proof.Ed25519.AArch64.IKeep base s s' ∧ env s'.mem base = f (env s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env} (h₁ : VG.Proof.Ed25519.AArch64.ISpec (large := large) base c₁ f)
    (h₂ : VG.Proof.Ed25519.AArch64.ISpec (large := large) base c₂ g) : VG.Proof.Ed25519.AArch64.ISpec (large := large) base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem ISpec.append {base : Addr} {l₁ l₂ : List Instr} {f g : Env → Env}
    (h₁ : VG.Proof.Ed25519.AArch64.ISpec (large := large) base (.block l₁) f) (h₂ : VG.Proof.Ed25519.AArch64.ISpec (large := large) base (.block l₂) g) :
    VG.Proof.Ed25519.AArch64.ISpec (large := large) base (.block (l₁ ++ l₂)) fun e => g (f e) := fun s hs => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩

/-- A slot of the inversion's: 14 to 17. -/
abbrev ISlot (o : Slot) : Prop := 14 ≤ o.val ∧ o.val < 18

/-- A multiplication into a slot of the inversion's, which also keeps `x19`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) (ho : VG.Proof.Ed25519.AArch64.ISlot o) :
    WP isa (.block (fieldMul (offset o) (offset a) (offset b))) s fun s' =>
      VG.Proof.Ed25519.AArch64.IKeep base s s' ∧ s'.gpr .x19 = s.gpr .x19 ∧ env s'.mem base = VG.Proof.Ed25519.AArch64.opMul o a b (env s.mem base) :=
  WP.mono (mul_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a) (slot_rangeWith (large := large) b)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      h.gpr _ (by decide), by rw [env_update o h.mem, e]; rfl⟩

theorem mulI (base : Addr) (o a b : Slot) (ho : VG.Proof.Ed25519.AArch64.ISlot o) :
    VG.Proof.Ed25519.AArch64.ISpec (large := large) base (.block (fieldMul (offset o) (offset a) (offset b))) (VG.Proof.Ed25519.AArch64.opMul o a b) := fun _ hs =>
  WP.mono (VG.Proof.Ed25519.AArch64.mulI_ok hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-- A squaring into a slot of the inversion's, which also keeps `x19`. -/
theorem sqrI_ok {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) (ho : VG.Proof.Ed25519.AArch64.ISlot o) :
    WP isa (.block (fieldSqr (offset o) (offset a))) s fun s' =>
      VG.Proof.Ed25519.AArch64.IKeep base s s' ∧ s'.gpr .x19 = s.gpr .x19 ∧ env s'.mem base = VG.Proof.Ed25519.AArch64.opMul o a a (env s.mem base) :=
  WP.mono (sqr_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩,
      h.gpr _ (by decide), by rw [env_update o h.mem, e]; rfl⟩

theorem sqrI (base : Addr) (o a : Slot) (ho : VG.Proof.Ed25519.AArch64.ISlot o) :
    VG.Proof.Ed25519.AArch64.ISpec (large := large) base (.block (fieldSqr (offset o) (offset a))) (VG.Proof.Ed25519.AArch64.opMul o a a) := fun _ hs =>
  WP.mono (VG.Proof.Ed25519.AArch64.sqrI_ok hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-! ## Runs of squarings -/

theorem decX19_ok {s : State} {k : Nat} (hb : s.gpr .x19 = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 k ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem counter_nonzero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k != 0) = decide (k ≠ 0) := by
  by_cases h : k = 0
  · subst k; rfl
  · rw [decide_eq_true h]
    apply bne_iff_ne.mpr
    intro he
    have he' := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, show (0 : BitVec 64).toNat = 0 from rfl] at he'
    exact h he'

/-- Slot `o` becomes slot `a` squared `n` times. -/
def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    VG.Proof.Ed25519.AArch64.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.Ed25519.AArch64.opMul, Function.update_self, Function.update_idem]

/-- The loop of `sqn`, with the counter `x19 = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : Scr s₀ base large) (o : Slot) (ho : VG.Proof.Ed25519.AArch64.ISlot o)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → VG.Proof.Ed25519.AArch64.IKeep base s₀ s → s.gpr .x19 = BitVec.ofNat 64 m →
      env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (fieldSqr (offset o) (offset o) ++
          ([.subImm .x .x19 .x19 1] : List Instr))) (.nonzero .x .x19)) s fun s' =>
        VG.Proof.Ed25519.AArch64.IKeep base s₀ s' ∧ env s'.mem base = Function.update (env s₀.mem base) o (sqn x n) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ VG.Proof.Ed25519.AArch64.IKeep base s₀ s ∧
    s.gpr .x19 = BitVec.ofNat 64 m ∧
    env s.mem base = Function.update (env s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrI_ok (hk.scr hs₀) o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.decX19_ok (b1.trans hb)) fun s2 ⟨b2, kdec⟩ => ?_
  have k2 : VG.Proof.Ed25519.AArch64.IKeep base s₀ s2 := hk.trans (k1.trans ⟨fun r _ hr => kdec.gpr r (by simpa only [List.mem_singleton] using hr), kdec.rd, kdec.wr, kdec.sp,
    by rw [kdec.mem]; exact Outside.refl _ _ _ _⟩)
  have e2 : env s2.mem base = Function.update (env s₀.mem base) o (sqn x (n - m)) := by
    rw [kdec.mem, e1, he, VG.Proof.Ed25519.AArch64.opMul_update]
    congr 2
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, read_x, b2, VG.Proof.Ed25519.AArch64.counter_nonzero (by omega : m < 2 ^ 64)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_true (by omega : m ≠ 0)], m, by omega,
      by omega, by omega, k2, rfl, e2⟩

/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : Slot) (ho : VG.Proof.Ed25519.AArch64.ISlot o) (n : Nat) (hn : 2 ≤ n)
    (hn' : n < 2 ^ 32) :
    VG.Proof.Ed25519.AArch64.ISpec (large := large) base (Impl.Ed25519.AArch64.sqn (offset o) (offset a) n) (VG.Proof.Ed25519.AArch64.opSqn o a n) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  intro s hs
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrI_ok hs o a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (const64_ok s1 .x19 (BitVec.ofNat 64 (n - 1))) fun s2 ⟨b2, kdec⟩ => ?_
  have k2 : VG.Proof.Ed25519.AArch64.IKeep base s s2 := k1.trans ⟨fun r _ hr => kdec.gpr r (by simpa only [List.mem_singleton] using hr), kdec.rd, kdec.wr, kdec.sp,
    by rw [kdec.mem]; exact Outside.refl _ _ _ _⟩
  refine VG.Proof.Ed25519.AArch64.sqLoop_ok hs o ho (env s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [kdec.mem, e1, show n - (n - 1) = 1 by omega]
  rfl


end VG.Proof.Ed25519.AArch64
end

/-! The shared addition chain computes inversion and square-root powers. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def power250Env (e : Env) : Env :=
  VG.Proof.Ed25519.AArch64.opMul 15 16 15 (VG.Proof.Ed25519.AArch64.opSqn 16 16 50 (VG.Proof.Ed25519.AArch64.opMul 16 17 16 (VG.Proof.Ed25519.AArch64.opSqn 17 16 100
    (VG.Proof.Ed25519.AArch64.opMul 16 16 15 (VG.Proof.Ed25519.AArch64.opSqn 16 15 50 (VG.Proof.Ed25519.AArch64.opMul 15 16 15 (VG.Proof.Ed25519.AArch64.opSqn 16 16 10 (VG.Proof.Ed25519.AArch64.opMul 16 17 16 (VG.Proof.Ed25519.AArch64.opSqn 17 16 20
    (VG.Proof.Ed25519.AArch64.opMul 16 16 15 (VG.Proof.Ed25519.AArch64.opSqn 16 15 10 (VG.Proof.Ed25519.AArch64.opMul 15 16 15 (VG.Proof.Ed25519.AArch64.opSqn 16 15 5 (VG.Proof.Ed25519.AArch64.opMul 15 15 16
    (VG.Proof.Ed25519.AArch64.opMul 16 14 14 (VG.Proof.Ed25519.AArch64.opMul 14 14 15 (VG.Proof.Ed25519.AArch64.opMul 15 2 15 (VG.Proof.Ed25519.AArch64.opMul 15 15 15 (VG.Proof.Ed25519.AArch64.opMul 15 14 14
    (VG.Proof.Ed25519.AArch64.opMul 14 2 2 e))))))))))))))))))))

theorem power250_spec (base : Addr) : VG.Proof.Ed25519.AArch64.ISpec (large := large) base power250 VG.Proof.Ed25519.AArch64.power250Env := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : VG.Proof.Ed25519.AArch64.ISpec (large := large) base _ _ :=
    (VG.Proof.Ed25519.AArch64.sqrI base 14 2 ⟨by decide, by decide⟩).seq <|
    ((VG.Proof.Ed25519.AArch64.sqrI base 15 14 ⟨by decide, by decide⟩).append
      (VG.Proof.Ed25519.AArch64.sqrI base 15 15 ⟨by decide, by decide⟩)).seq <|
    ((((VG.Proof.Ed25519.AArch64.mulI base 15 2 15 ⟨by decide, by decide⟩).append
      (VG.Proof.Ed25519.AArch64.mulI base 14 14 15 ⟨by decide, by decide⟩)).append
      (VG.Proof.Ed25519.AArch64.sqrI base 16 14 ⟨by decide, by decide⟩)).append
      (VG.Proof.Ed25519.AArch64.mulI base 15 15 16 ⟨by decide, by decide⟩)).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 16 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 16 15 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 17 16 ⟨by decide, by decide⟩ 20 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 16 16 ⟨by decide, by decide⟩ 10 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 15 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 16 15 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 16 16 15 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 17 16 ⟨by decide, by decide⟩ 100 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 16 17 16 ⟨by decide, by decide⟩).seq <|
    (VG.Proof.Ed25519.AArch64.sqnI base 16 16 ⟨by decide, by decide⟩ 50 (by decide) (by decide)).seq <|
    (VG.Proof.Ed25519.AArch64.mulI base 15 16 15 ⟨by decide, by decide⟩)
  exact h

def invEnv (e : Env) : Env := VG.Proof.Ed25519.AArch64.opMul 15 15 14 (VG.Proof.Ed25519.AArch64.opSqn 15 15 5 (VG.Proof.Ed25519.AArch64.power250Env e))
def rootEnv (e : Env) : Env := VG.Proof.Ed25519.AArch64.opMul 15 15 2 (VG.Proof.Ed25519.AArch64.opSqn 15 15 2 (VG.Proof.Ed25519.AArch64.power250Env e))

theorem invert_spec (base : Addr) : VG.Proof.Ed25519.AArch64.ISpec (large := large) base invert VG.Proof.Ed25519.AArch64.invEnv := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : VG.Proof.Ed25519.AArch64.ISpec (large := large) base _ _ := (VG.Proof.Ed25519.AArch64.power250_spec base).seq ((VG.Proof.Ed25519.AArch64.sqnI base 15 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (VG.Proof.Ed25519.AArch64.mulI base 15 15 14 ⟨by decide, by decide⟩))
  exact h

theorem rootPower_spec (base : Addr) : VG.Proof.Ed25519.AArch64.ISpec (large := large) base Impl.Ed25519.AArch64.rootPower VG.Proof.Ed25519.AArch64.rootEnv := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have h : VG.Proof.Ed25519.AArch64.ISpec (large := large) base _ _ := (VG.Proof.Ed25519.AArch64.power250_spec base).seq ((VG.Proof.Ed25519.AArch64.sqnI base 15 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (VG.Proof.Ed25519.AArch64.mulI base 15 15 2 ⟨by decide, by decide⟩))
  exact h

theorem invEnv_eval (e : Env) : VG.Proof.Ed25519.AArch64.invEnv e 15 = VG.Proof.X25519.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.Ed25519.AArch64.invEnv, VG.Proof.Ed25519.AArch64.power250Env, VG.Proof.Ed25519.AArch64.opMul, VG.Proof.Ed25519.AArch64.opSqn, Function.update_apply]
  rfl

theorem rootEnv_eval (e : Env) : VG.Proof.Ed25519.AArch64.rootEnv e 15 = VG.Proof.Ed25519.rootPower (e 2) := by
  simp only [↓reduceIte, VG.Proof.Ed25519.AArch64.rootEnv, VG.Proof.Ed25519.AArch64.power250Env, VG.Proof.Ed25519.AArch64.opMul, VG.Proof.Ed25519.AArch64.opSqn, Function.update_apply]
  rfl

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa invert s fun t => VG.Proof.Ed25519.AArch64.IKeep base s t ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) :=
  WP.mono (VG.Proof.Ed25519.AArch64.invert_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, VG.Proof.Ed25519.AArch64.invEnv_eval]⟩

theorem rootPower_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa Impl.Ed25519.AArch64.rootPower s fun t => VG.Proof.Ed25519.AArch64.IKeep base s t ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) :=
  WP.mono (VG.Proof.Ed25519.AArch64.rootPower_spec base s hs) fun _ ⟨hk, hv⟩ => ⟨hk, by rw [hv, VG.Proof.Ed25519.AArch64.rootEnv_eval]⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.PointAffine`. -/
section
/-! Normalize extended coordinates with the verified inversion chain. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

theorem pointAffine_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pointAffine s fun t => CounterKeep base s t ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  rw [pointAffine]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.invert_ok hs) fun t ⟨hk, hv⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (hk.scr hs)) fun u ⟨ku, vu⟩ => ?_
  refine ⟨⟨fun r hr hb => (ku.gpr r hr).trans (hk.gpr r hr hb), ku.rd.trans hk.rd,
    ku.wr.trans hk.wr, ku.sp.trans hk.sp,
    (hk.mem.mono (by decide) (by decide)).trans ku.mem⟩, ?_, ?_⟩
  · rw [vu, (VG.Proof.Ed25519.AArch64.affine_eval _).1, hv]
    have he : env t.mem base 0 = env s.mem base 0 := by
      change F t.mem base 64 = F s.mem base 64
      unfold F; rw [hk.mem.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]
  · rw [vu, (VG.Proof.Ed25519.AArch64.affine_eval _).2, hv]
    have he : env t.mem base 1 = env s.mem base 1 := by
      change F t.mem base 96 = F s.mem base 96
      unfold F; rw [hk.mem.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.AArch64
end

/-! Canonical point encoding in four machine words. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem freezeField_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (freeze (offset a))) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = (env s.mem base a).val ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x21, .x22, .x23, .x24] s t :=
  VG.Proof.Ed25519.AArch64.freeze_ok hs (slot_range a)

theorem sign_word (w : BitVec 64) :
    (w &&& 1) <<< 63 = BitVec.ofNat 64 ((w.toNat % 2) * 2 ^ 63) := by
  have he : w &&& 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [he]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> decide

theorem pointSign_ok (s : State) :
    WP isa (.block pointSign) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2) * 2 ^ 63) ∧
      Keeps [.x19, .x9] s t := by
  have hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 = (s.gpr .x4).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [pointSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.w.bits from by decide, show (63 : Nat) < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [hv]; exact VG.Proof.Ed25519.AArch64.sign_word _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem encodeSign_ok (s : State) (x y : Nat) (hy : y < 2 ^ 255)
    (hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = y)
    (hs : s.gpr .x19 = BitVec.ofNat 64 ((x % 2) * 2 ^ 63)) :
    WP isa (.block [.add .x .x7 .x7 .x19]) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = y + (x % 2) * 2 ^ 255 ∧
      Keeps [.x7] s t := by
  have hb : (s.gpr .x7).toNat < 2 ^ 63 := by simp only [val4] at hv; omega
  have hm : ((x % 2) * 2 ^ 63) < 2 ^ 64 := by omega
  have ha : (s.gpr .x7 + s.gpr .x19).toNat = (s.gpr .x7).toNat + (x % 2) * 2 ^ 63 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [val4, ha] at hv ⊢; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem pointEncode_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pointEncode s fun t => CounterKeep base s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val +
        ((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 255 := by
  rw [pointEncode]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.pointAffine_ok hs) fun a ⟨ka, ax, ay⟩ => ?_)
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freezeField_ok (ka.scr hs) 0) fun b ⟨bx, kb⟩ => ?_
  have kbe : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.pointSign_ok b) fun c ⟨cx, kc⟩ => ?_
  have kce : CounterKeep base b c := CounterKeep.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freezeField_ok (kce.scr (kbe.scr (ka.scr hs))) 1) fun d ⟨dy, kd⟩ => ?_
  have kde : CounterKeep base c d := CounterKeep.of_keeps kd (by decide)
  have dx : d.gpr .x19 = BitVec.ofNat 64
      (((env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).val % 2) * 2 ^ 63) := by
    rw [kd.gpr .x19 (by decide), cx, bx, ax]
  rw [kc.mem, kb.mem, ay] at dy
  refine WP.mono (VG.Proof.Ed25519.AArch64.encodeSign_ok d _ _ (by
    exact Nat.lt_trans (env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2)).isLt
      (by decide : Spec.X25519.P < 2 ^ 255)) dy dx) fun t ⟨hv, kt⟩ => ?_
  exact ⟨(((ka.trans kbe).trans kce).trans kde).trans (CounterKeep.of_keeps kt (by decide)), hv⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.FieldCheck`. -/
section
/-! Compare field elements through canonical representatives. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem wordsZero_flag (a b c d : BitVec 64) :
    (((a ||| b) ||| c) ||| d == 0#64) = decide (val4 a b c d = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq, val4]
  constructor
  · rintro ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩; rfl
  · intro h
    have ha : a.toNat = 0 := by omega
    have hb : b.toNat = 0 := by omega
    have hc : c.toNat = 0 := by omega
    have hd : d.toNat = 0 := by omega
    exact ⟨⟨⟨BitVec.eq_of_toNat_eq ha, BitVec.eq_of_toNat_eq hb⟩,
      BitVec.eq_of_toNat_eq hc⟩, BitVec.eq_of_toNat_eq hd⟩

theorem wordsZero_ok (s : State) :
    WP isa (.block wordsZero) s fun t =>
      (t.gpr .x8 == 0) = decide (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = 0) ∧
      Keeps [.x8] s t := by
  apply WP.of_runBlock
  simp only [wordsZero, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed25519.AArch64.wordsZero_flag _ _ _ _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem fieldZero_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (fieldZero a)) s fun t =>
      (t.gpr .x8 == 0) = decide (env s.mem base a = 0) ∧ Keep base s t ∧ t.mem = s.mem := by
  rw [fieldZero, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.freezeField_ok hs a) fun u ⟨uv, ku⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.wordsZero_ok u) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, (Keep.of_keeps ku (by decide)).trans (Keep.of_keeps kt (by decide)), kt.mem.trans ku.mem⟩
  rw [tz, uv]
  have he : (env s.mem base a).val = 0 ↔ env s.mem base a = 0 := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Slot) :
    WP isa (.block (fieldEqual a b)) s fun t =>
      (t.gpr .x8 == 0) = decide (env s.mem base a = env s.mem base b) ∧ Keep base s t ∧
      ∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i := by
  rw [fieldEqual, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 21 a b] hs) fun u ⟨ku, vu⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.fieldZero_ok (ku.scr hs) 21) fun t ⟨tz, kt, tm⟩ => ?_
  refine ⟨?_, ku.trans kt, ?_⟩
  · rw [tz, vu]
    change decide (env s.mem base a - env s.mem base b = 0) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      fun _ _ => ⟨fun _ => by grind, fun _ => by grind⟩]
  · intro i hi
    rw [tm, vu]
    change Function.update (env s.mem base) 21 (env s.mem base a - env s.mem base b) i = _
    exact Function.update_of_ne hi _ _

end VG.Proof.Ed25519.AArch64
end

/-! The public sign bit is compared to the canonical x-coordinate. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

def signWord (b : Bool) : BitVec 64 := if b then 1 else 0

theorem parity_flag (w : BitVec 64) (b : Bool) :
    ((w &&& BitVec.ofNat 64 1) ^^^ VG.Proof.Ed25519.AArch64.signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have hw : w &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (BitVec.ofNat 64 1).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [hw]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} (b : Bool) (hs : s.gpr .x1 = VG.Proof.Ed25519.AArch64.signWord b) :
    WP isa (.block recoverParity) s fun t =>
      (t.gpr .x8 == 0) = (((val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 == 1) == b)) ∧
      Keeps [.x9, .x8] s t := by
  have hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 = (s.gpr .x4).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [recoverParity, runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, ite_true, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', hs, hv]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact VG.Proof.Ed25519.AArch64.parity_flag _ b
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.movz .w .x8 (if b then 1 else 0) 0]) s fun t =>
      t.gpr .x8 = VG.Proof.Ed25519.AArch64.signWord b ∧ Keeps [.x8] s t := by
  cases b <;> apply WP.of_runBlock <;>
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, ite_true,
      Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Ed25519.AArch64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits`. -/
section

/-! Load the encoded y-coordinate and its separate sign bit. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem decodeLE_inputWords (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      val4 (m.readW (off p 0) 64) (m.readW (off p 8) 64)
        (m.readW (off p 16) 64) (m.readW (off p 24) 64) := by
  rw [decodeLE_eq, show off p 0 = p from BitVec.add_zero p, val4]
  exact VG.Proof.X25519.leNum_bytesAt_words64 m p

private theorem encoded_top (m : Mem) (p : Addr) :
    ((m.readW (off p 24) 64) >>> 63).toNat =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) / 2 ^ 255 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, decodeLE_inputWords, val4]
  have h0 := (m.readW (off p 0) 64).isLt
  have h1 := (m.readW (off p 8) 64).isLt
  have h2 := (m.readW (off p 16) 64).isLt
  omega

theorem loadSign_ok (s : State) (p : Addr) (hp : s.gpr .x2 = p)
    (hr : InRegions (s.rd ++ s.wr) (off p 24) 8) :
    WP isa (.block loadSign) s fun t =>
      t.gpr .x1 = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      Keeps [.x1] s t := by
  have hn := decodeLE_lt (Spec.Ed25519.bytesAt s.mem p 32)
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [hl] at hn
  have hv : (s.mem.readW (off p 24) 64) >>> 63 =
      signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) := by
    have h : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 0 ∨
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 = 1 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [encoded_top]
    rcases h with h | h <;> rw [h] <;> rfl
  apply WP.of_runBlock
  simp only [loadSign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bytes, hp, hr, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul,
    and_self, show 63 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨hv, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem clearYSign_ok (s : State) (hl : s.gpr .x8 = low63) :
    WP isa (.block [.logic .and .x .x7 .x7 .x8]) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 ^ 255 ∧
      Keeps [.x7] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, hl, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [val4, low63, and_low63]
    have h0 := (s.gpr .x4).isLt
    have h1 := (s.gpr .x5).isLt
    have h2 := (s.gpr .x6).isLt
    omega
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem loadY_ok (s : State) (p : Addr) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadY) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  change WP isa (.block (loadWords .x2 ++ const64 .x8 low63 ++
    ([.logic .and .x .x7 .x7 .x8] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWords_ok s .x2 (by decide) (by rw [hp]; exact hr)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok a .x8 low63) fun b ⟨bl, kb⟩ => ?_
  refine WP.mono (clearYSign_ok b bl) fun t ⟨tv, kt⟩ => ?_
  refine ⟨?_, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [tv, val4, kb.gpr .x4 (by decide), kb.gpr .x5 (by decide),
    kb.gpr .x6 (by decide), kb.gpr .x7 (by decide)]
  rw [← val4, av, hp, decodeLE_inputWords]

end VG.Proof.Ed25519.AArch64

end
