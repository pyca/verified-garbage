module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Update
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Ed25519 and X25519 on AArch64: the ends of the inversion

`start` sets `f = p`, `a = 0`, `b = 2^-590` and `g` to the input modulo `p`
(`start_ok`); `finish` leaves `a` or `2 p - a` in slot 15 (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)

variable {large : Bool}

theorem Scr.setFrame {rs : List Reg} {s s' : State} (k : Keeps rs s s') {m : Mem} {t : State}
    (ht : t = { s' with mem := m }) : KeepRegs rs s t :=
  ⟨fun r hr => by rw [ht]; exact k.gpr r hr, by rw [ht]; exact k.rd, by rw [ht]; exact k.wr, by rw [ht]; exact k.sp⟩

theorem set4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o) {v : Nat}
    (hv : v < 2 ^ 256) :
    WP isa (.block (set4 o v)) s fun t =>
      fe t.mem base o = v ∧ Outside base o 32 s.mem t.mem ∧ KeepRegs updRegs s t := by
  simp only [set4, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s _ _) fun s₁ ⟨v₁, q₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ _ _) fun s₂ ⟨v₂, q₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ _ _) fun s₃ ⟨v₃, q₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₃ _ _) fun s₄ ⟨v₄, q₄⟩ => ?_
  have k : Keeps updRegs s s₄ := (((q₁.mono (by decide)).trans (q₂.mono (by decide))).trans
    (q₃.mono (by decide))).trans (q₄.mono (by decide))
  refine WP.mono (stp4_ok (hs.of_keeps k (by decide)) ho _ _ _ _) fun t ht => ⟨?_, ?_, Scr.setFrame k ht⟩
  · rw [ht]
    refine (fe_st4 _ _ (by omega_using [ho.2]) _ _ _ _).trans ?_
    rw [v₄, q₄.gpr .x8 (by decide), v₃, q₄.gpr .x3 (by decide), q₃.gpr .x3 (by decide), v₂, q₄.gpr .x2 (by decide),
      q₃.gpr .x2 (by decide), q₂.gpr .x2 (by decide), v₁]
    simp only [val4, BitVec.toNat_ofNat]
    omega_using [hv]
  · rw [ht, ← k.mem]; exact st4_outside _ _ (by omega_using [ho.2]) _ _ _ _

theorem foldTop_arith {t0 t1 t2 t3 y c w x9 s0 s1 s2 s3 d0 d1 d2 d3 : Nat}
    (l0 : t0 < 2 ^ 64) (l1 : t1 < 2 ^ 64) (l2 : t2 < 2 ^ 64) (l3 : t3 < 2 ^ 64)
    (b0 : y + 2 ^ 64 * c = t3 + t3 + 0) (ly : y < 2 ^ 64) (hx : x9 = y / 2) (hw : w = 19 * c)
    (d0e : s0 + 2 ^ 64 * d0 = t0 + w + 0) (d1e : s1 + 2 ^ 64 * d1 = t1 + 0 + d0)
    (d2e : s2 + 2 ^ 64 * d2 = t2 + 0 + d1) (d3e : s3 + 2 ^ 64 * d3 = x9 + 0 + d2) :
    s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 =
      (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) % 2 ^ 255 +
        19 * ((t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) / 2 ^ 255) := by
  have e : x9 + 2 ^ 63 * c = t3 := by omega_using [b0, hx, ly]
  have lx : x9 < 2 ^ 63 := by omega_using [hx, ly]
  have q : (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) / 2 ^ 255 = c := by
    rw [← e]; omega_using [l0, l1, l2, lx]
  have m : (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3) % 2 ^ 255 =
      t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * x9 := by
    rw [← e]; omega_using [l0, l1, l2, lx]
  rw [q, m]
  have hc : c ≤ 1 := by omega_using [b0, l3]
  omega_using [d0e, d1e, d2e, d3e, hw, lx, l0, l1, l2, hc]

theorem foldTop_ok (s : State) :
    WP isa (.block foldTop) s fun t =>
      lo t = lo s % 2 ^ 255 + 19 * (lo s / 2 ^ 255) ∧ t.gpr .x16 = 0 ∧ t.gpr .x17 = 19 ∧
      Keeps [.x2, .x3, .x8, .x9, .x11, .x16, .x17] s t := by
  have hw (c : Bool) : (if c = true then BitVec.setWidth 64 19#16 <<< (16 * 0) else
      BitVec.setWidth 64 0#16 <<< (16 * 0)).toNat = 19 * c.toNat := by cases c <;> decide
  apply WP.of_runBlock
  simp only [foldTop, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, RegUpd.c_write, lo, val4,
    show 1 < Size.x.bits from by decide, show 16 * 0 < Size.x.bits from by decide,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by decide, by decide, by row_frame⟩
  dsimp only [Size.bits]
  exact foldTop_arith (s.gpr .x2).isLt (s.gpr .x3).isLt (s.gpr .x8).isLt (s.gpr .x9).isLt
    (addCarry_value (s.gpr .x9) (s.gpr .x9) false) (BitVec.isLt _) (lsr1 _) (hw _)
    (addCarry_value _ _ false) (addCarry_value _ _ _) (addCarry_value _ _ _) (addCarry_value _ _ _)

theorem plus19_ok (s : State) (hz : s.gpr .x16 = 0) (h17 : s.gpr .x17 = 19) (h : lo s < 2 ^ 255 + 19) :
    WP isa (.block plus19) s fun t =>
      opd t = lo s + 19 ∧ Keeps [.x11, .x12, .x13, .x14] s t := by
  have e := add4_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) 19 0 0 0 false
  dsimp only [addCarry, carryOut] at e
  have c : val4 (19 : Word) 0 0 0 = 19 := by decide
  rw [c] at e
  have run : WP isa (.block plus19) s fun t =>
      (∃ k, opd t + 2 ^ 256 * k = lo s + 19) ∧ Keeps [.x11, .x12, .x13, .x14] s t := by
    apply WP.of_runBlock
    simp only [plus19, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, opd, hz, h17,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
    exact ⟨⟨_, e⟩, by row_frame⟩
  refine WP.mono run fun t ⟨⟨k, hk⟩, kt⟩ => ⟨?_, kt⟩
  have := opd_lt t
  omega_using [hk, this, h]

theorem reduceOnce_ok (s : State) :
    WP isa (.block reduceOnce) s fun t =>
      lo t = (if 2 ^ 255 ≤ opd s then opd s - 2 ^ 255 else lo s) ∧ Keeps [.x2, .x3, .x8, .x9, .x14] s t := by
  have hm := opd_msb s
  have hsh : ((s.gpr .x14 + s.gpr .x14) >>> 1).toNat = (s.gpr .x14).toNat % 2 ^ 63 := by
    rw [lsr1, BitVec.toNat_add]; omega_using []
  apply WP.of_runBlock
  simp only [reduceOnce, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, CondCode.holds,
    ↓RegUpd.gpr_write, lo, BitVec.and_self, show 1 < Size.x.bits from by decide, RegUpd.nf_write, hm,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · by_cases h : 2 ^ 255 ≤ opd s
    · simp only [h, decide_true, ↓reduceIte, val4]
      rw [hsh]
      unfold opd val4 at h ⊢
      have := (s.gpr .x11).isLt; have := (s.gpr .x12).isLt; have := (s.gpr .x13).isLt; have := (s.gpr .x14).isLt
      omega_arith
    · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem bySign_ok (s : State) :
    WP isa (.block bySign) s fun t =>
      lo t = (if (s.gpr .x10).msb = true then lo s else opd s) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  apply WP.of_runBlock
  simp only [bySign, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, CondCode.holds,
    ↓RegUpd.gpr_write, lo, opd, BitVec.and_self, RegUpd.nf_write,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨by cases (s.gpr .x10).msb <;> rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The registers the inversion writes. -/
abbrev invRegs : List Reg :=
  [.x20, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19]

theorem counters_ok (s : State) :
    WP isa (.block counters) s fun t => t.gpr .x20 = 0 ∧ t.gpr .x19 = BitVec.ofNat 64 10 ∧ Keeps [.x20, .x19] s t := by
  apply WP.of_runBlock
  simp only [counters, runBlock_cons, runStep_some, runBlock_nil, exec,
    ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨by decide, by decide, by row_frame⟩

theorem start_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block start) s fun t =>
      fe t.mem base oF = Spec.X25519.P ∧ fe t.mem base oA = 0 ∧ fe t.mem base oB = b0 ∧
      fe t.mem base oG = fe s.mem base 128 % Spec.X25519.P ∧
      t.gpr .x20 = 0 ∧ t.gpr .x19 = BitVec.ofNat 64 10 ∧
      Outside base 192 512 s.mem t.mem ∧ KeepRegs invRegs s t := by
  simp only [start, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (set4_ok hs (o := oF) (by decide) (by decide)) fun s₁ ⟨v₁, o₁, k₁⟩ => ?_
  have hs₁ := Scr.of_keepRegs' hs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (set4_ok hs₁ (o := oA) (by decide) (by decide)) fun s₂ ⟨v₂, o₂, k₂'⟩ => ?_
  have k₂ := k₁.trans k₂'
  have hs₂ := Scr.of_keepRegs' hs k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (set4_ok hs₂ (o := oB) (by decide) (by decide)) fun s₃ ⟨v₃, o₃, k₃'⟩ => ?_
  have k₃ := k₂.trans k₃'
  have hs₃ := Scr.of_keepRegs' hs k₃ (by decide)
  have X : fe s₃.mem base 128 = fe s.mem base 128 := by
    rw [o₃.fe (by decide) (by decide), o₂.fe (by decide) (by decide), o₁.fe (by decide) (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (ldp4_ok hs₃ (o := 128) (by decide) (by decide)) fun s₄ ⟨a, b, c, d, q₄⟩ => ?_
  have l₄ : lo s₄ = fe s.mem base 128 := by rw [← X]; unfold lo; rw [a, b, c, d]
  rw [WP.block_append_iff]
  refine WP.mono (foldTop_ok s₄) fun s₅ ⟨v₅, c16, c17, q₅⟩ => ?_
  rw [l₄] at v₅
  have hl : fe s.mem base 128 < 2 ^ 256 := val4_lt _ _ _ _
  have b₅ : lo s₅ < 2 ^ 255 + 19 := by rw [v₅]; omega_using [hl]
  rw [WP.block_append_iff]
  refine WP.mono (plus19_ok s₅ c16 c17 b₅) fun s₆ ⟨v₆, q₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceOnce_ok s₆) fun s₇ ⟨v₇, q₇⟩ => ?_
  have l₆ : lo s₆ = lo s₅ := by
    unfold lo; rw [q₆.gpr _ (by decide), q₆.gpr _ (by decide), q₆.gpr _ (by decide), q₆.gpr _ (by decide)]
  rw [l₆, v₆] at v₇
  have v₇' : lo s₇ = fe s.mem base 128 % Spec.X25519.P := by
    rw [v₇, show Spec.X25519.P = 2 ^ 255 - 19 from rfl]
    generalize fe s.mem base 128 = X at *
    generalize lo s₅ = Y at *
    split <;> omega_using [v₅, hl, b₅, ‹_›]
  have q : Keeps invRegs s₃ s₇ := (((q₄.mono (by decide)).trans (q₅.mono (by decide))).trans
    (q₆.mono (by decide))).trans (q₇.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (stp4_ok (hs₃.of_keeps q (by decide)) (o := oG) (by decide) _ _ _ _) fun s₈ h₈ => ?_
  have k₈ := (k₃.mono (by decide)).trans (Scr.setFrame q h₈)
  have o₈ : Outside base oG 32 s₃.mem s₈.mem := by
    rw [h₈, ← q.mem]; exact st4_outside _ _ (by decide) _ _ _ _
  refine WP.mono (counters_ok s₈) fun t ⟨c20, c19, q₉⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, c20, c19, ?_, ?_⟩
  · rw [q₉.mem, o₈.fe (by decide) (by decide), o₃.fe (by decide) (by decide), o₂.fe (by decide) (by decide), v₁]
  · rw [q₉.mem, o₈.fe (by decide) (by decide), o₃.fe (by decide) (by decide), v₂]
  · rw [q₉.mem, o₈.fe (by decide) (by decide), v₃]
  · rw [q₉.mem, h₈, fe_st4 _ _ (by decide)]; exact v₇'
  · rw [q₉.mem]
    exact (((o₁.mono (by decide) (by decide)).trans (o₂.mono (by decide) (by decide))).trans
      (o₃.mono (by decide) (by decide))).trans (o₈.mono (by decide) (by decide))
  · exact k₈.trans ⟨fun r hr => q₉.gpr r fun h => hr ((by decide : ∀ a ∈ ([.x20, .x19] : List Reg), a ∈ invRegs) r h),
      q₉.rd, q₉.wr, q₉.sp⟩

theorem finish_ok {s : State} {base : Addr} (hs : Scr s base large) (hA : fe s.mem base oA < abMax) :
    WP isa (.block finish) s fun t =>
      fe t.mem base 544 = (if 2 ^ 255 ≤ fe s.mem base oF then 2 ^ 256 - 38 - fe s.mem base oA else fe s.mem base oA) ∧
      Outside base 192 512 s.mem t.mem ∧ KeepRegs invRegs s t := by
  have hc := workSize_ge large
  simp only [finish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldp4_ok hs (o := oA) (by decide) (by decide)) fun s₁ ⟨a, b, c, d, q₁⟩ => ?_
  have k₁ : Keeps invRegs s s₁ := q₁.mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ldOpd_ok (hs.of_keeps k₁ (by decide)) (o := oA) (by decide)) fun s₂ ⟨v₂, q₂⟩ => ?_
  have k₂ : Keeps invRegs s s₂ := k₁.trans (q₂.mono (by decide))
  have l₁ : lo s₁ = fe s.mem base oA := by unfold lo; rw [a, b, c, d]
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps k₂ (by decide)) (d := oF + 24) (by decide) (by unfold oF; omega_using [hc]) .x10)
    fun s₃ ⟨v₃, q₃⟩ => ?_
  have k₃ : Keeps invRegs s s₃ := k₂.trans (q₃.mono (by decide))
  rw [WP.block_append_iff]
  have z : WP isa (.block ([.movz .x .x16 0 0] : List Instr)) s₃ fun t => t.gpr .x16 = 0 ∧ Keeps [.x16] s₃ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide,
      ↓reduceIte, Option.some.injEq, exists_eq_left']
    exact ⟨by decide, by row_frame⟩
  refine WP.mono z fun s₄ ⟨c16, q₄⟩ => ?_
  have k₄ : Keeps invRegs s s₄ := k₃.trans (q₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (twoP_ok s₄ c16) fun s₅ ⟨c15, c17, q₅⟩ => ?_
  have k₅ : Keeps invRegs s s₅ := k₄.trans (q₅.mono (by decide))
  have l₅ : lo s₅ = fe s.mem base oA := by
    rw [← l₁]; unfold lo
    rw [q₅.gpr _ (by decide), q₅.gpr _ (by decide), q₅.gpr _ (by decide), q₅.gpr _ (by decide),
      q₄.gpr _ (by decide), q₄.gpr _ (by decide), q₄.gpr _ (by decide), q₄.gpr _ (by decide),
      q₃.gpr _ (by decide), q₃.gpr _ (by decide), q₃.gpr _ (by decide), q₃.gpr _ (by decide),
      q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide), q₂.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (negRow_ok s₅ c15 c17 (by rw [l₅]; unfold abMax at hA; omega_using [hA])) fun s₆ ⟨v₆, q₆⟩ => ?_
  have k₆ : Keeps invRegs s s₆ := k₅.trans (q₆.mono (by decide))
  rw [l₅] at v₆
  have p₆ : opd s₆ = fe s.mem base oA := by
    rw [opd_keeps q₆ (by decide), opd_keeps q₅ (by decide), opd_keeps q₄ (by decide), opd_keeps q₃ (by decide), v₂,
      k₁.mem]
  have w₆ : s₆.gpr .x10 = word s.mem base (oF + 24) := by
    rw [q₆.gpr _ (by decide), q₅.gpr _ (by decide), q₄.gpr _ (by decide), v₃, k₂.mem]
  rw [WP.block_append_iff]
  refine WP.mono (bySign_ok s₆) fun s₇ ⟨v₇, q₇⟩ => ?_
  have k₇ : Keeps invRegs s s₇ := k₆.trans (q₇.mono (by decide))
  have hsl : offset 15 = 544 := rfl
  refine WP.mono (stores_ok (hs.of_keeps k₇ (by decide)) (o := offset 15) ⟨by decide, by rw [hsl]; omega_using [hc]⟩ _ _ _ _)
    fun t ht => ⟨?_, ?_, Scr.setFrame k₇ ht⟩
  · rw [ht, hsl]
    refine (fe_st4 _ _ (by decide) _ _ _ _).trans ?_
    show lo s₇ = _
    have hm : (s₆.gpr .x10).msb = decide (2 ^ 255 ≤ fe s.mem base oF) := by
      rw [w₆, BitVec.msb_eq_decide]
      apply decide_eq_decide.mpr
      have := (word s.mem base oF).isLt; have := (word s.mem base (oF + 8)).isLt
      have := (word s.mem base (oF + 16)).isLt; have := (word s.mem base (oF + 24)).isLt
      simp only [fe, val4]
      constructor <;> intro <;> omega_arith
    rw [v₇, hm, p₆]
    by_cases h : 2 ^ 255 ≤ fe s.mem base oF
    · simp only [h, decide_true, ↓reduceIte]
      omega_using [v₆]
    · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]
  · rw [ht, ← k₇.mem, hsl]
    exact (st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide)

end VG.Proof.Ed25519.AArch64.Divstep
