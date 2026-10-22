module

public import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ffdh_check_domain` on i686: the checks

`body_ok`: the status of `body` is 1 exactly when the domain is valid
(`domainValid`), from the stages: p a valid modulus (RSA's check of its
bytes), `1 < g < p − 1`, and with q, q odd with `2 < q < p − 1`
(`withQ_ok`), q dividing `p − 1` (a Montgomery reduction modulo q is zero,
`divides_ok`) and `g^q mod p = 1` (`subgroup_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckDomain

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.CheckDomain (subgroup divides withQ checked)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len dlen : Nat}
  {args : Nat → BitVec 32}

/-- `g^q mod p = 1`, for p, g and q in the wide slots 9, 10 and 11. -/
theorem subgroup_ok (h : In Ex base bytes len args s) {p g q : Nat} (h9 : sv s.mem base len .wide 9 = p)
    (h10 : sv s.mem base len .wide 10 = g) (h11 : sv s.mem base len .wide 11 = q) (gt : 1 < p)
    (odd : p % 2 = 1) :
    WP isa subgroup s (Res base len s (if g ^ q % p = 1 then 1 else 0)) := by
  unfold subgroup
  refine WP.seq (WP.mono (powP_ok h (b := 10) (e := 11) (by decide) (by decide) (by decide) (by decide)
    (by rw [h9, safeM_of gt odd])) fun u ⟨C, V6, V3, F, _, K⟩ => ?_)
  refine WP.mono (eqStatus_res C.inp (a := 6) (b := 3) (by decide) (by decide)) fun t R => ?_
  rw [V6, V3, h10, h11] at R
  exact (Step.ops h F K).res R

/-- `divides` up to its branch. -/
abbrev dividesFront : List (Prog isa) :=
  [copy (.slot .wide 11) (.slot .wide 0) (one .wide), prepare .wide, copy (.slot .wide 15) (.slot .wide 5) (one .wide),
    CrtRt.mul .wide 6 5 3, zero (.slot .wide 17) (one .wide), equal (.slot .wide 6) (.slot .wide 17) (one .wide),
    Impl.Ffdh.X86.testMask]

theorem divides_eq : divides = Prog.chain dividesFront (.ite .e (Impl.Ffdh.X86.ret 0) subgroup) := rfl

/-- The context of q, and ZF telling whether q does not divide `p − 1`. -/
theorem dividesFront_ok (h : In Ex base bytes len args s) {p q : Nat}
    (h11 : sv s.mem base len .wide 11 = q) (h15 : sv s.mem base len .wide 15 = p - 1) (qodd : q % 2 = 1)
    (q2 : 2 < q) :
    WP isa (Prog.chain dividesFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (¬ (p - 1) % q = 0) ∧
      ∀ j, 9 ≤ j → j ≤ 19 → j ≠ 17 → sv u.mem base len .wide j = sv s.mem base len .wide j := by
  -- The context of q.
  refine WP.seq (WP.mono (copyIn_ok h (j := 11) (d := 0) (by decide) (by decide) (by decide))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  have k₁ := kept_slot h (a := 0) O₁
  refine WP.seq (WP.mono (prepCtx_ok S₁.inp .wide) fun u₂ ⟨C₂, one₂, _, F₂, K₂⟩ => ?_)
  rw [V₁, h11, safeM_of (by omega) qodd] at C₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.ops S₁.inp (stR_widen F₂ (prepR_in S₁.inp .wide 0)) K₂
  have k₂ := kept_ops S₁.inp (stR_widen F₂ (prepR_in S₁.inp .wide 0)) S₁.inp.room
  -- `p − 1` in slot 5, and its Montgomery reduction modulo q in slot 6.
  refine WP.seq (WP.mono (copyIn_ok C₂.inp (j := 15) (d := 5) (by decide) (by decide) (by decide))
    fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.slot C₂.inp (by decide) O₃ K₃
  have k₃ := kept_slot C₂.inp (a := 5) O₃
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e5 := lo_wide len 5
  have e8 := lo_wide len 8
  have nb : numBase = 3336 := rfl
  have C₃ : CtxOk Ex base bytes len args .wide q u₃ :=
    C₂.keepF K₃ (by decide) (by decide) (ws := [(lo len (.slot .wide 5), bc len .wide)])
      (frameR_of_outside O₃ (by omega) (by simp)) (by intro r hr; rw [List.mem_singleton.mp hr]; dsimp only; omega)
      (by intro r hr; rw [List.mem_singleton.mp hr]; dsimp only; omega)
  have one₃ : sv u₃.mem base len .wide 3 = 1 := by rw [slotKeep C₂.inp (by decide) (by decide) O₃, one₂]
  have five₃ : sv u₃.mem base len .wide 5 = p - 1 := by
    rw [V₃, k₂.slot_eq, k₁.slot_eq, h15]
  refine WP.seq (WP.mono (cmul_ok C₃ (o := 6) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [one₃]; omega)) fun u₄ ⟨C₄, K₄, F₄, L₄, V₄⟩ => ?_)
  rw [five₃, one₃, Nat.mul_one] at V₄
  have S₄ : Step Ex base bytes len args u₃ u₄ :=
    Step.ops C₃.inp (stR_widen F₄ (mulR_in C₃.inp .wide (j := 6) (by decide) 0)) K₄
  have k₄ := kept_ops C₃.inp (stR_widen F₄ (mulR_in C₃.inp .wide (j := 6) (by decide) 0)) C₃.inp.room
  -- The reduction compared with zero.
  refine WP.seq (WP.mono (zeroW_ok C₄.inp (a := 17) (by decide)) fun u₅ ⟨O₅, Z₅, K₅⟩ => ?_)
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.slot C₄.inp (by decide) O₅ K₅
  have k₅ := kept_slot C₄.inp (a := 17) O₅
  have six₅ : sv u₅.mem base len .wide 6 = sv u₄.mem base len .wide 6 := slotKeep C₄.inp (by decide) (by decide) O₅
  refine WP.seq (WP.mono (eqW_ok S₅.inp (a := 6) (b := 17) (by decide) (by decide)) fun u₆ ⟨m₆, e₆, K₆⟩ => ?_)
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.regs S₅.inp m₆ K₆
  refine WP.seq (WP.mono (testMask_ok e₆) fun u₇ ⟨z₇, m₇, K₇⟩ => WP.block_nil ?_)
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.regs S₆.inp m₇ K₇
  have S := ((((((S₁.trans S₂).trans S₃).trans S₄).trans S₅).trans S₆).trans S₇)
  rw [six₅, Z₅] at z₇
  have red := VG.Proof.Ffdh.redc_zero (r := sv u₄.mem base len .wide 6) (Q := q) (X := p - 1)
    (n := 8 * bc len .wide) qodd L₄ V₄
  refine ⟨S, Gate.of_eval z₇ ?_, fun j h9 h19 h17 => ?_⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact not_congr red
  · have hj' : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ ([] : List Nat) := ⟨h9, h19, by simp⟩
    have hj5 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [5] := ⟨h9, h19, by simp; omega⟩
    have hj0 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [0] := ⟨h9, h19, by simp; omega⟩
    have hj17 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [17] := ⟨h9, h19, by simp; omega⟩
    rw [m₇, m₆, k₅.slot_eq hj17, k₄.slot_eq hj', k₃.slot_eq hj5, k₂.slot_eq hj', k₁.slot_eq hj0]

theorem divides_ok (h : In Ex base bytes len args s) {p g q : Nat} (h9 : sv s.mem base len .wide 9 = p)
    (h10 : sv s.mem base len .wide 10 = g) (h11 : sv s.mem base len .wide 11 = q)
    (h15 : sv s.mem base len .wide 15 = p - 1) (gt : 1 < p) (odd : p % 2 = 1) (q2 : 2 < q) (qodd : q % 2 = 1) :
    WP isa divides s (Res base len s (if (p - 1) % q = 0 ∧ g ^ q % p = 1 then 1 else 0)) := by
  rw [divides_eq]
  refine WP.chain_split (dividesFront_ok h h11 h15 qodd q2) fun u ⟨S, G, kk⟩ => WP.gate G
    (fun nd => WP.mono (ret_res (base := base) (len := len)) fun t R => S.res ?_) (fun dv => ?_)
  · simp only [nd, false_and, ↓reduceIte]; exact R
  · have dv : (p - 1) % q = 0 := Classical.not_not.mp dv
    refine WP.mono (subgroup_ok S.inp (p := p) (g := g) (q := q) (by rw [kk 9 (by decide) (by decide) (by decide), h9])
      (by rw [kk 10 (by decide) (by decide) (by decide), h10]) (by rw [kk 11 (by decide) (by decide) (by decide), h11])
      gt odd) fun t R => S.res ?_
    simp only [dv, true_and]; exact R

/-- `withQ` up to its branch. -/
abbrev withQFront : List (Prog isa) :=
  [load (.slot .wide 11) (one .wide) 6 7, setSmall (.slot .wide 16) (one .wide) 2,
    lessThan (.slot .wide 16) (.slot .wide 11) (one .wide), .block [.store (sc maskOff) .ecx],
    lessThan (.slot .wide 11) (.slot .wide 15) (one .wide),
    .block ([.alu .and .ecx (.mem (sc maskOff))] ++ Impl.Ffdh.X86.CheckDomain.oddMask), Impl.Ffdh.X86.testMask]

theorem withQ_eq : withQ = Prog.chain withQFront (.ite .e (Impl.Ffdh.X86.ret 0) divides) := rfl

/-- q into slot 11, and ZF telling whether q is not odd with `2 < q < p − 1`. -/
theorem withQFront_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len (3 * len) s.rd s.wr)
    {p : Nat} (h15 : sv s.mem base len .wide 15 = p - 1) :
    WP isa (Prog.chain withQFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (¬ (comp s.mem args len 2 % 2 = 1 ∧ 2 < comp s.mem args len 2 ∧ comp s.mem args len 2 < p - 1)) ∧
      sv u.mem base len .wide 11 = comp s.mem args len 2 ∧
      ∀ j, 9 ≤ j → j ≤ 19 → j ≠ 11 → j ≠ 16 → sv u.mem base len .wide j = sv s.mem base len .wide j := by
  generalize hq : comp s.mem args len 2 = q
  have mo : maskOff = 12 := rfl
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (loadComp_ok h G (k := 2) (j := 11) (by decide) (by omega) (by decide))
    fun u₁ ⟨V₁, O₁, K₁⟩ => ?_)
  rw [hq] at V₁
  have S₁ : Step Ex base bytes len args s u₁ := Step.slot h (by decide) O₁ K₁
  have k₁ := kept_slot h (a := 11) O₁
  refine WP.seq (WP.mono (setW_ok S₁.inp (a := 16) (v := 2) (by decide) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot S₁.inp (by decide) O₂ K₂
  have k₂ := kept_slot S₁.inp (a := 16) O₂
  have q₂ : sv u₂.mem base len .wide 11 = q := by rw [k₂.slot_eq, V₁]
  refine WP.seq (WP.mono (lessW_ok S₂.inp (a := 16) (b := 11) (by decide) (by decide)) fun u₃ ⟨m₃, e₃, K₃⟩ => ?_)
  rw [V₂, q₂] at e₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.regs S₂.inp m₃ K₃
  refine WP.seq (WP.mono (storeMask_ok S₃.inp (d := maskOff) (by omega) e₃) fun u₄ ⟨_, O₄, W₄, _, K₄⟩ => ?_)
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.word S₃.inp (by omega) O₄ K₄
  have k₄ := kept_word S₃.inp (d := maskOff) (by omega) (by decide) O₄
  have q₄ : sv u₄.mem base len .wide 11 = q := by rw [k₄.slot_eq, m₃, q₂]
  have p₄ : sv u₄.mem base len .wide 15 = p - 1 := by
    rw [k₄.slot_eq, m₃, k₂.slot_eq, k₁.slot_eq, h15]
  refine WP.seq (WP.mono (lessW_ok S₄.inp (a := 11) (b := 15) (by decide) (by decide)) fun u₅ ⟨m₅, e₅, K₅⟩ => ?_)
  rw [q₄, p₄] at e₅
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.regs S₄.inp m₅ K₅
  have W₅ : w32 u₅.mem base maskOff = (cmask (decide (2 < q))).toNat := by rw [m₅]; exact W₄
  refine WP.seq (WP.block_append (WP.mono (andMask_ok S₅.inp (d := maskOff) (by omega) e₅ W₅)
    fun u₆ ⟨e₆, m₆, K₆⟩ => WP.mono (oddMask_ok (S₅.inp.regs K₆ m₆) e₆) fun u₇ ⟨e₇, m₇, K₇⟩ => ?_))
  have S₆ : Step Ex base bytes len args u₅ u₆ := Step.regs S₅.inp m₆ K₆
  have S₇ : Step Ex base bytes len args u₆ u₇ := Step.regs S₆.inp m₇ K₇
  rw [m₆, m₅, q₄] at e₇
  refine WP.seq (WP.mono (testMask_ok e₇) fun u₈ ⟨z₈, m₈, K₈⟩ => WP.block_nil ?_)
  have S₈ : Step Ex base bytes len args u₇ u₈ := Step.regs S₇.inp m₈ K₈
  have S := ((((((S₁.trans S₂).trans S₃).trans S₄).trans S₅).trans S₆).trans S₇).trans S₈
  refine ⟨S, Gate.of_eval z₈ ?_, by rw [m₈, m₇, m₆, m₅, q₄], fun j h9 h19 h11 h16 => ?_⟩
  · by_cases a : q % 2 = 1 <;> by_cases b : 2 < q <;> by_cases c : q < p - 1 <;> simp [a, b, c]
  · have h16' : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [16] := ⟨h9, h19, by simp; omega⟩
    have h11' : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ [11] := ⟨h9, h19, by simp; omega⟩
    have h0 : 9 ≤ j ∧ j ≤ 19 ∧ j ∉ ([] : List Nat) := ⟨h9, h19, by simp⟩
    rw [m₈, m₇, m₆, m₅, k₄.slot_eq h0, m₃, k₂.slot_eq h16', k₁.slot_eq h11']

/-- q (the domain's third component) odd with `2 < q < p − 1`, then `divides`. -/
theorem withQ_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len (3 * len) s.rd s.wr)
    {p g : Nat} (h9 : sv s.mem base len .wide 9 = p) (h10 : sv s.mem base len .wide 10 = g)
    (h15 : sv s.mem base len .wide 15 = p - 1) (gt : 1 < p) (odd : p % 2 = 1) :
    WP isa withQ s (Res base len s
      (if (comp s.mem args len 2 % 2 = 1 ∧ 2 < comp s.mem args len 2 ∧ comp s.mem args len 2 < p - 1) ∧
        ((p - 1) % comp s.mem args len 2 = 0 ∧ g ^ comp s.mem args len 2 % p = 1) then 1 else 0)) := by
  rw [withQ_eq]
  refine WP.chain_split (withQFront_ok h G h15) fun u ⟨S, Gt, q₈, kk⟩ => ?_
  generalize hq : comp s.mem args len 2 = q at Gt q₈ ⊢
  refine WP.gate Gt (fun nc => WP.mono (ret_res (base := base) (len := len)) fun t R => S.res ?_) (fun c => ?_)
  · simp only [nc, false_and, ↓reduceIte]; exact R
  · have c := Classical.not_not.mp c
    refine WP.mono (divides_ok S.inp (p := p) (g := g) (q := q)
      (by rw [kk 9 (by decide) (by decide) (by decide) (by decide), h9])
      (by rw [kk 10 (by decide) (by decide) (by decide) (by decide), h10]) q₈
      (by rw [kk 15 (by decide) (by decide) (by decide) (by decide), h15]) gt odd c.2.1 c.1) fun t R => S.res ?_
    simp only [c, true_and, and_self]; exact R

theorem argNum_comp (m : Mem) (args : Nat → BitVec 32) (len : Nat) : argNum m args 2 len = comp m args len 0 := by
  simp only [argNum, comp, Nat.zero_mul]
  congr 2
  exact (BitVec.add_zero _).symm

/-- The domain's bytes. -/
abbrev domBytes (m : Mem) (args : Nat → BitVec 32) (dlen : Nat) : List Byte :=
  Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen

/-- `checked` up to its first branch. -/
abbrev checkedFront : List (Prog isa) :=
  [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5, Impl.Ffdh.X86.rangeMask 10, Impl.Ffdh.X86.testMask]

theorem checked_eq : checked = Prog.chain checkedFront (.ite .e (Impl.Ffdh.X86.ret 0)
    (.seq (.block Impl.Ffdh.X86.qTest) (.ite .e (Impl.Ffdh.X86.ret 1) withQ))) := rfl

/-- p, one, g and `p − 1` into slots 9, 14, 10 and 15, and ZF telling whether g is out of range. -/
theorem checkedFront_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40))
    (valid : Spec.Rsa.modulusValid (comp s.mem args len 0) len = true) :
    WP isa (Prog.chain checkedFront (.block [])) s fun u => Step Ex base bytes len args s u ∧
      Gate u (¬ (1 < comp s.mem args len 1 ∧ comp s.mem args len 1 < comp s.mem args len 0 - 1)) ∧
      sv u.mem base len .wide 9 = comp s.mem args len 0 ∧ sv u.mem base len .wide 10 = comp s.mem args len 1 ∧
      sv u.mem base len .wide 15 = comp s.mem args len 0 - 1 := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  generalize hP : comp s.mem args len 0 = p at valid
  generalize hG : comp s.mem args len 1 = g
  have mv := valid
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, k₁, V9, V14, V15, K₁⟩ => ?_)
  rw [argNum_comp, hP] at V9 V15
  have V15 := V15 (by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega)
  have S₁ : Step Ex base bytes len args s u₁ := ⟨I₁, F₁, K₁⟩
  -- g, and its range.
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₂ ⟨V₂, O₂, K₂⟩ => ?_)
  rw [comp_keep h G hb40 F₁ (by omega), hG] at V₂
  have S₂ : Step Ex base bytes len args u₁ u₂ := Step.slot I₁ (by decide) O₂ K₂
  have k₂ := kept_slot I₁ (a := 10) O₂
  refine WP.seq (WP.mono (rangeMask_ok S₂.inp (a := 10) (by decide)) fun u₃ ⟨I₃, e₃, O₃, K₃⟩ => ?_)
  rw [V₂, k₂.slot_eq, k₂.slot_eq, V14, V15] at e₃
  have S₃ : Step Ex base bytes len args u₂ u₃ := Step.word S₂.inp (by decide) O₃ K₃
  have k₃ := kept_word S₂.inp (d := maskOff) (by decide) (by decide) O₃
  refine WP.seq (WP.mono (testMask_ok e₃) fun u₄ ⟨z₄, m₄, K₄⟩ => WP.block_nil ?_)
  have S₄ : Step Ex base bytes len args u₃ u₄ := Step.regs S₃.inp m₄ K₄
  refine ⟨((S₁.trans S₂).trans S₃).trans S₄, Gate.of_eval z₄ ?_, ?_, ?_, ?_⟩
  · by_cases a : 1 < g <;> by_cases b : g < p - 1 <;> simp [a, b]
  · rw [m₄, k₃.slot_eq, k₂.slot_eq, V9]
  · rw [m₄, k₃.slot_eq, V₂]
  · rw [m₄, k₃.slot_eq, k₂.slot_eq, V15]

/-- For a valid modulus p: `1 < g < p − 1`, then q if there is one. -/
theorem checked_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40))
    (valid : Spec.Rsa.modulusValid (comp s.mem args len 0) len = true) :
    WP isa checked s (Res base len s
      (if Spec.Ffdh.domainValid len (domBytes s.mem args dlen) then 1 else 0)) := by
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega
  have hp := comp_p s.mem args h2
  have hg := comp_g s.mem args h2
  rw [checked_eq]
  refine WP.chain_split (checkedFront_ok h G hb40 valid) fun u₄ ⟨S, Gt, V9, V10, V15⟩ => ?_
  generalize hP : comp s.mem args len 0 = p at valid hp V9 V15 Gt
  generalize hG : comp s.mem args len 1 = g at hg V10 Gt
  have mv := valid
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  have podd : p % 2 = 1 := mv.1.1.1
  have pgt : 1 < p := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega
  have iff := VG.Proof.Ffdh.domainValid_iff len (domBytes s.mem args dlen)
  rw [← hp, ← hg] at iff
  refine WP.gate Gt (fun bad => WP.mono (ret_res (base := base) (len := len)) fun t R => S.res ?_) (fun grange => ?_)
  · have nv : Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = false := by
      cases e : Spec.Ffdh.domainValid len (domBytes s.mem args dlen)
      · rfl
      · exact absurd (iff.mp e).2.1 bad
    simp only [nv, Bool.false_eq_true, ↓reduceIte]; exact R
  have grange : 1 < g ∧ g < p - 1 := Classical.not_not.mp grange
  have G₄ := G.keep ⟨rfl, rfl⟩ S.keeps
  refine WP.seq (WP.mono (qTest_ok S.inp G.e3 G.e12 dl) fun u₅ ⟨z₅, m₅, K₅⟩ => ?_)
  have S₅ : Step Ex base bytes len args u₄ u₅ := Step.regs S.inp m₅ K₅
  have S' := S.trans S₅
  refine WP.ite _ z₅ (fun hb => WP.mono (ret_res (base := base) (len := len)) fun t R => S'.res ?_) (fun hb => ?_)
  · have e2 : dlen = 2 * len := by simpa using hb
    have nq : (Spec.Ffdh.domainOf len (domBytes s.mem args dlen)).q = none := by
      rw [domBytes, e2]; exact VG.Proof.Ffdh.domainOf_q2 _ _ (by omega)
    have vv : Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = true :=
      iff.mpr ⟨valid, grange, fun q hq => by rw [nq] at hq; cases hq⟩
    simp only [vv, ↓reduceIte]; exact R
  · have e3 : dlen = 3 * len := by
      have : ¬ dlen = 2 * len := by simpa using hb
      omega
    subst e3
    have hq := comp_q (len := len) s.mem args
    refine WP.mono (withQ_ok S₅.inp (G.keep ⟨rfl, rfl⟩ S'.keeps) (p := p) (g := g) (by rw [m₅, V9])
      (by rw [m₅, V10]) (by rw [m₅, V15]) pgt podd) fun t R => S'.res ?_
    rw [comp_keep h G hb40 S'.frame (by omega)] at R
    generalize hQ : comp s.mem args len 2 = Q at R hq
    have key : Spec.Ffdh.domainValid len (domBytes s.mem args (3 * len)) = true ↔
        ((Q % 2 = 1 ∧ 2 < Q ∧ Q < p - 1) ∧ ((p - 1) % Q = 0 ∧ g ^ Q % p = 1)) := by
      rw [iff]
      constructor
      · rintro ⟨_, _, hc⟩
        obtain ⟨⟨a, b, c⟩, d, e⟩ := hc _ hq
        exact ⟨⟨a, by omega, c⟩, d, e⟩
      · rintro ⟨⟨a, b, c⟩, d, e⟩
        refine ⟨valid, grange, fun q' hq' => ?_⟩
        rw [hq] at hq'
        cases hq'
        exact ⟨⟨a, by omega, c⟩, d, e⟩
    by_cases hc : (Q % 2 = 1 ∧ 2 < Q ∧ Q < p - 1) ∧ ((p - 1) % Q = 0 ∧ g ^ Q % p = 1)
    · have v := key.mpr hc
      simp only [v, ↓reduceIte]
      simp only [hc, and_self, ↓reduceIte] at R
      exact R
    · have v : Spec.Ffdh.domainValid len (domBytes s.mem args (3 * len)) = false := by
        cases e : Spec.Ffdh.domainValid len (domBytes s.mem args (3 * len))
        · rfl
        · exact absurd (key.mp e) hc
      simp only [v, Bool.false_eq_true, ↓reduceIte]
      rw [show (if (Q % 2 = 1 ∧ 2 < Q ∧ Q < p - 1) ∧ ((p - 1) % Q = 0 ∧ g ^ Q % p = 1) then 1 else 0) = 0 from
        ite_eq_right_iff.mpr fun h' => absurd h' hc] at R
      exact R

/-- RSA's check of p's bytes: ZF telling whether p is a valid modulus. -/
theorem bodyFront_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr) :
    WP isa (.seq (.block PublicFn.modulusArgs) (.block modulusCheck)) s fun v => Step Ex base bytes len args s v ∧
      v.mem = s.mem ∧ Gate v (Spec.Rsa.modulusValid (comp s.mem args len 0) len = true) := by
  have fit := G.fit
  have dl := G.dl
  have lw := G.lower
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
    (h.arg (i := 3) (by decide))) fun u ⟨P, C, M, K⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u := Step.regs h M K
  have rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
    rw [P, K.2.1, K.2.2]
    have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega) rd (by rw [C, G.e3]))
    fun v ⟨Z, Mv, Kv⟩ => ?_
  rw [P, M, show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) = comp s.mem args len 0 from
    argNum_comp s.mem args len] at Z
  exact ⟨S₁.trans (Step.regs S₁.inp Mv Kv), Mv.trans M, Gate.of_eval Z Iff.rfl⟩

/-- `vg_ffdh_check_domain`'s body: 1 exactly when the domain is valid. -/
theorem body_ok (h : In Ex base bytes len args s) (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 40)) :
    WP isa Impl.Ffdh.X86.CheckDomain.body s (Res base len s
      (if Spec.Ffdh.domainValid len (domBytes s.mem args dlen) then 1 else 0)) := by
  have fit := G.fit
  have dl := G.dl
  have lw := G.lower
  unfold Impl.Ffdh.X86.CheckDomain.body
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
    (h.arg (i := 3) (by decide))) fun u ⟨P, C, M, K⟩ => ?_)
  have S₁ : Step Ex base bytes len args s u := Step.regs h M K
  have rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
    rw [P, K.2.1, K.2.2]
    have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine WP.seq (WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega) rd (by rw [C, G.e3]))
    fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have S₂ : Step Ex base bytes len args u v := Step.regs S₁.inp Mv Kv
  have S := S₁.trans S₂
  have Mvs : v.mem = s.mem := Mv.trans M
  have e0 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) = comp s.mem args len 0 :=
    argNum_comp s.mem args len
  rw [e0] at Z
  refine WP.ite _ Z (fun valid => ?_) (fun invalid => WP.mono (ret_res (base := base) (len := len))
    fun t R => S.res ?_)
  · refine WP.mono (checked_ok S.inp (G.keep ⟨rfl, rfl⟩ S.keeps) (by rw [S.esp]; exact hb40)
      (by rw [Mvs]; exact valid)) fun t R => S.res ?_
    rw [Mvs] at R; exact R
  · have nv : Spec.Ffdh.domainValid len (domBytes s.mem args dlen) = false := by
      cases e : Spec.Ffdh.domainValid len (domBytes s.mem args dlen)
      · rfl
      · have := VG.Proof.Ffdh.domainValid_mod e
        rw [← comp_p s.mem args (by omega), invalid] at this
        cases this
    simp only [nv, Bool.false_eq_true, ↓reduceIte]; exact R

end VG.Proof.Ffdh.X86.CheckDomain
