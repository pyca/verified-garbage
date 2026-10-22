module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Table
import VerifiedGarbage.Proof.Framework.Omega

/-! # Building the table of a run-time-width windowed exponentiation

Entries 0 and 1 copied from one and the base in Montgomery form, and each
next entry the product of the one below and the base (`buildTable_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The ranges `buildTable` changes. -/
abbrev tabR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(te len c 0, 16 * bc len c), (lo len (.slot c 7), bc len c), (lo len (.slot c 1), 3 * bc len c + 56)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- The pointers of a copy of slot `x` into entry `j`. -/
theorem copySetup_ok (h : In Ex base bytes len args s) {x j : Nat} (hx : x ≤ 8) (hj : j ≤ 15) {Q : State → Prop}
    (k : ∀ w, Keeps [.ebx, .ecx, .edx, .ebp, .edi] s w → w.mem = s.mem →
      PtrAt w base .ebp (lo len (.slot c x)) → PtrAt w base .ebx (te len c j) →
      (w.gpr .edi).toNat = 4 * cwc len c → w.gpr .ecx = cmask true → Q w) :
    WP isa (.block (([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++ ptrTo (.slot c x) .ebp .edx ++
      entryPtr c .ebx j .edx ++ cntTo (one c) .edi)) s Q := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bl := h.bytes_lt
  have hx8 : lo len (.slot c x) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hx; simp only [lo]; omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun w₁ u₁ _ => ?_
  have h₁ := h.regs u₁.keeps u₁.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h₁.edi h₁.width h.upper' (by omega)
    fun w₂ K₂ m₂ p₂ => ?_
  have h₂ := h₁.regs K₂ m₂
  refine entryPtr_ok (c := c) (j := j) (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    h₂.edi h₂.width h.upper' (by omega) fun w₃ K₃ m₃ p₃ => ?_
  have h₃ := h₂.regs K₃ m₃
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) h₃.width h.upper' (one_ok c).extra fun w₄ K₄ m₄ c₄ => WP.block_nil ?_
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  refine k w₄ ((((u₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
    (K₄.mono (by decide))) (by rw [m₄, m₃, m₂, u₁.mem]) ?_ ?_ ?_ ?_
  · rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂
  · rw [PtrAt, K₄.1 _ (by decide)]; exact p₃
  · rw [cnt_toNat h.upper' (one_ok c) c₄, cw1]
  · rw [K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide), u₁.gpr]; rfl

/-- A copy of slot `x` into entry `j`, then `P`. -/
theorem copyEntry_ok (h : In Ex base bytes len args s) {x j : Nat} (hx : x ≤ 8) (hj : j ≤ 15) {P : Prog isa}
    {Q : State → Prop}
    (k : ∀ u, Outside base (te len c j) (bc len c) s.mem u.mem →
      val32 u.mem base (te len c j) (cwc len c) = sv s.mem base len c x →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u → WP isa P u Q) :
    WP isa (.seq (.block (([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++ ptrTo (.slot c x) .ebp .edx ++
      entryPtr c .ebx j .edx ++ cntTo (one c) .edi)) (.seq (.seq selectLoop (.block restoreEdi)) P)) s Q := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have hx8 : lo len (.slot c x) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hx; simp only [lo]; omega
  have hj16 : te len c j + bc len c ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega)
    rw [Nat.succ_mul] at this
    show lo len (.slot .wide 20) + j * bc len c + bc len c ≤ lo len (.slot .wide 20) + 16 * bc len c
    omega
  have t0 : te len c 0 ≤ te len c j := by simp [te]
  have t0' : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have est : st len c = 2 * bc len c + 32 := rfl
  refine WP.seq (copySetup_ok (c := c) h hx hj fun w K m pe pb ce ck => ?_)
  refine WP.seq (WP.mono (selectTail_ok h (K.mono (by decide)) m (x := lo len (.slot c x)) (d := te len c j)
    (N := cwc len c) (k := true) (by omega) (by omega) (by omega) (by omega)
    pe pb ce ck) fun u ⟨O, V, _, Ku⟩ => k u ?_ ?_ Ku)
  · rw [← m, bw]; exact O
  · rw [V, m]; simp

end

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- The table at entry `i` of its loop: entries below `i` filled, slot 7 the last, `esi` at entry `i`. -/
structure TabInv (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (c : Ctx) (M b : Nat) (s₀ : State)
    (i : Nat) (t : State) : Prop where
  ctx : CtxOk Ex base bytes len args c M t
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ t
  frame : Frame (frameR base (s₀.gpr .esp) (tabR len c)) s₀.mem t.mem
  table : ∀ j < i, val32 t.mem base (te len c j) (cwc len c) = b ^ j * 2 ^ (8 * bc len c) % M
  last : sv t.mem base len c 7 = b ^ (i - 1) * 2 ^ (8 * bc len c) % M
  ptr : PtrAt t base .esi (te len c i)

theorem tabR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ tabR len c, p.1 + p.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e7 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  have e48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have t16 : te len c 0 + 16 * bc len c = te len c 16 := by simp [te]
  intro p hp
  simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega

/-- The table's ranges lie past slot 0 and the header. -/
theorem tabR_past (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ tabR len c, numBase + bc len c ≤ p.1 := by
  have T := h.table_fit c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le c (by decide)
  have e17 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  intro p hp
  simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega

/-- A multiplication into slot 7 keeps the table. -/
theorem mulR7_te (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (mulR len c 7)) m m') (R : CallRoom sp base bytes) {j : Nat} (hj : j < 16) :
    val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e17 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have tj : te len c j + bc len c ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega)
    simp only [te]; rw [Nat.succ_mul] at this; omega
  have tj0 : te len c 0 ≤ te len c j := by simp only [te]; omega
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ ?_ <;>
    intro p hp <;> simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- The table's ranges keep slot 5. -/
theorem tabR_slot5 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (tabR len c)) m m') (R : CallRoom sp base bytes) :
    val32 m' base (lo len (.slot c 5)) (cwc len c) = val32 m base (lo len (.slot c 5)) (cwc len c) := by
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e5 : lo len (.slot c 5) = numBase + 5 * st len c := rfl
  have e57 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega
  refine frameR_val32 F R h.scratch.nowrap (by omega) ?_ (tabR_fit h c)
  intro p hp; simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega

end

/-- Two pointers into the working space are equal exactly when their offsets are. -/
theorem ptr_beq {s : State} {W : Addr} {r q : Reg} {a b : Nat} (ha : PtrAt s W r a) (hb : PtrAt s W q b)
    (hn : W.toNat + a < 2 ^ 32) (hn' : W.toNat + b < 2 ^ 32) : (s.gpr r - s.gpr q == 0) = decide (a = b) := by
  by_cases e : a = b
  · subst e
    have : s.gpr r = s.gpr q := BitVec.eq_of_toNat_eq (ha.trans hb.symm)
    simp [this]
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have : s.gpr r = s.gpr q := by
      have := congrArg (· + s.gpr q) hz; simp only [BitVec.sub_add_cancel] at this; exact this.trans (BitVec.zero_add _)
    have := congrArg BitVec.toNat this
    rw [ha, hb, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn'] at this
    omega

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

theorem tableStep_ok {s₀ : State} {b i : Nat} (hb₀ : sv s₀.mem base len c 5 = b * 2 ^ (8 * bc len c) % M)
    (hi2 : 2 ≤ i) (hi : i < 16) {t : State} (I : TabInv Ex base bytes len args c M b s₀ i t) :
    WP isa (tableStep c) t fun u => TabInv Ex base bytes len args c M b s₀ (i + 1) u ∧
      u.zf = some (decide (i + 1 = 16)) := by
  have C := I.ctx
  have h := C.inp
  have nw' := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have est : st len c = 2 * bc len c + 32 := rfl
  have e57 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  have e45 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 5) := sl_le c (by decide)
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have tsucc : ∀ j, te len c (j + 1) = te len c j + bc len c := fun j => by simp only [te]; rw [Nat.succ_mul]; omega
  have ti16 : te len c (i + 1) ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show i + 1 ≤ 16 by omega); simp only [te]; omega
  have ti0 : te len c 0 ≤ te len c i := by simp only [te]; omega
  have ti1 := tsucc i
  have t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega
  have hM := C.gt
  have sp₀ : t.gpr .esp = s₀.gpr .esp := I.keeps.1 _ (by decide)
  have fit := tabR_fit h c
  have room₀ : CallRoom (s₀.gpr .esp) base bytes := sp₀ ▸ h.room
  -- The base keeps its value.
  have B : sv t.mem base len c 5 = b * 2 ^ (8 * bc len c) % M := by
    simp only [sv]
    rw [tabR_slot5 h I.frame room₀]
    exact hb₀
  unfold tableStep
  -- Slot 7 times the base.
  refine WP.seq (WP.mono (cmul_ok C (o := 7) (a := 7) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B]; exact Nat.mod_lt _ (by omega))) fun u₁ ⟨C₁, cs₁, F₁, L₁, V₁⟩ => ?_)
  have P₁ : sv u₁.mem base len c 7 = b ^ i * 2 ^ (8 * bc len c) % M := by
    have v := VG.Proof.Dsa.mont_product C.coprime (a := b ^ (i - 1)) (b := b)
      (by rw [I.last, Nat.mod_mod]) (by rw [B, Nat.mod_mod]) V₁
    rw [Nat.mod_eq_of_lt L₁] at v
    rw [v, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ i)]
  have h₁ := C₁.inp
  have esi₁ : u₁.gpr .esi = t.gpr .esi := cs₁.1 _ (by decide)
  -- The pointers of the copy into entry `i`.
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS rfl fun w₁ a₁ _ => ?_)
  have hw₁ := h₁.regs a₁.keeps a₁.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (x := .slot c 7) (by decide) (by decide) hw₁.edi hw₁.width h.upper'
    (by omega) fun w₂ K₂ m₂ p₂ => wp_movS rfl fun w₃ a₃ _ => ?_
  have hw₃ := hw₁.regs ((K₂.mono (by decide)).trans (a₃.keeps.mono (by decide)) : Keeps [.ebx, .edx, .ebp] w₁ w₃)
    (by rw [a₃.mem, m₂])
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) hw₃.width h.upper' (one_ok c).extra fun w₄ K₄ m₄ c₄ => WP.block_nil ?_
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have Kw : Keeps [.ebx, .ecx, .edx, .ebp, .edi] u₁ w₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (K₄.mono (by decide))
  have mw : w₄.mem = u₁.mem := by rw [m₄, a₃.mem, m₂, a₁.mem]
  have pe : PtrAt w₄ base .ebp (lo len (.slot c 7)) := by
    rw [PtrAt, K₄.1 _ (by decide), a₃.other _ (by decide)]; exact p₂
  have pb : PtrAt w₄ base .ebx (te len c i) := by
    rw [PtrAt, K₄.1 _ (by decide), a₃.gpr, K₂.1 _ (by decide), a₁.other _ (by decide), esi₁]; exact I.ptr
  have ce : (w₄.gpr .edi).toNat = 4 * cwc len c := by rw [cnt_toNat h.upper' (one_ok c) c₄, cw1]
  have ck : w₄.gpr .ecx = cmask true := by
    rw [K₄.1 _ (by decide), a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]; rfl
  -- The copy.
  refine WP.seq (WP.mono (selectTail_ok h₁ (Kw.mono (by decide)) mw (x := lo len (.slot c 7)) (d := te len c i)
    (N := cwc len c) (k := true) (by omega) (by omega) (by omega) (by omega) pe pb ce ck)
    fun u₂ ⟨O₂, V₂, pb₂, K₂'⟩ => ?_)
  have h₂ := h₁.keep (K₂'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₁ u₂) (by decide) (by decide)
    (by rw [← mw]; exact O₂.mono (Nat.zero_le _) (by omega))
  -- `esi` past entry `i`, and the comparison with the table's end.
  refine wp_movS rfl fun v₁ b₁ _ => ?_
  have hv₁ := h₂.regs b₁.keeps b₁.mem
  refine entryPtr_ok (c := c) (j := 16) (r := .edx) (t := .eax) (by decide) (by decide) (by decide) (by decide)
    hv₁.edi hv₁.width h.upper' (by decide) fun v₂ K₅ m₅ p₅ => wp_cmpS rfl fun v₃ f₃ z₃ => WP.block_nil ?_
  have esi₂ : PtrAt v₂ base .esi (te len c (i + 1)) := by
    rw [PtrAt, K₅.1 _ (by decide), b₁.gpr, tsucc, bw]; exact pb₂
  have esi₃ : PtrAt v₃ base .esi (te len c (i + 1)) := by rw [PtrAt, f₃.gpr]; exact esi₂
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t v₃ :=
    ((((cs₁.mono (by decide)).trans (K₂'.mono (by decide))).trans (b₁.keeps.mono (by decide))).trans
      (K₅.mono (by decide))).trans (f₃.keeps _)
  have m₃ : v₃.mem = u₂.mem := by rw [f₃.mem, m₅, b₁.mem]
  have O₂' : Outside base (te len c 0) (16 * bc len c) u₁.mem u₂.mem := by
    rw [← mw]; exact O₂.mono (by omega) (by omega)
  have F₂ : Frame (frameR base (s₀.gpr .esp) (tabR len c)) u₁.mem v₃.mem := by
    rw [m₃]; exact frameR_of_outside O₂' (by omega) (by simp)
  have F₁' : Frame (frameR base (s₀.gpr .esp) (tabR len c)) t.mem u₁.mem := by
    rw [← sp₀]; exact frameR_mono F₁ (by simp)
  have C₃ : CtxOk Ex base bytes len args c M v₃ := by
    have C₂ := C₁.keepF (K₂'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₁ u₂) (by decide)
      (by decide) (ws := [(te len c 0, 16 * bc len c)]) (frameR_of_outside O₂' (by omega) (by simp))
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only
          have z0 : lo len (.slot c 0) = numBase := sl_zero len c
          have e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
          omega)
    exact C₂.regs ((b₁.keeps.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₂ v₁).trans
      ((K₅.mono (by decide)).trans (f₃.keeps _))) (by rw [f₃.mem, m₅, b₁.mem])
  -- Values.
  have keepU : ∀ d, d + 4 * cwc len c ≤ bytes → (d + 4 * cwc len c ≤ te len c i ∨ te len c i + bc len c ≤ d) →
      val32 v₃.mem base d (cwc len c) = val32 u₁.mem base d (cwc len c) := fun d hd hdi => by
    rw [m₃, ← mw]; exact O₂.val32 (by omega) (by omega)
  refine ⟨⟨C₃, I.keeps.trans Kall, I.frame.trans (F₁'.trans F₂), fun j hj => ?_, ?_, esi₃⟩, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [m₃, V₂]; simp only [↓reduceIte, mw]; exact P₁
    · have hj' : j < i := by omega
      have tj : te len c j + bc len c ≤ te len c i := by
        have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ i by omega); simp only [te]; rw [Nat.succ_mul] at this; omega
      have tj0 : te len c 0 ≤ te len c j := by simp only [te]; omega
      rw [keepU (te len c j) (by omega) (.inl (by omega))]
      rw [mulR7_te h F₁ h.room (by omega)]
      exact I.table j hj'
  · simp only [sv]
    rw [keepU (lo len (.slot c 7)) (by omega) (.inl (by omega)), Nat.add_sub_cancel]
    exact P₁
  · rw [z₃, ptr_beq esi₂ p₅ (by omega) (by omega)]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e
      have e' : (i + 1) * bc len c = 16 * bc len c := by simp only [te] at e; omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) e'
    · intro e; rw [e]

/-- The table: entry `j` holds `b^j R mod M`, from one and the base in Montgomery form. -/
theorem buildTable_ok {b : Nat} (C : CtxOk Ex base bytes len args c M s)
    (h6 : sv s.mem base len c 6 = 2 ^ (8 * bc len c) % M) (h5 : sv s.mem base len c 5 = b * 2 ^ (8 * bc len c) % M) :
    WP isa (buildTable c) s fun u => TabInv Ex base bytes len args c M b s 16 u := by
  have h := C.inp
  have nw := h.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e57 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have t1 : te len c 1 = te len c 0 + bc len c := by simp [te]
  have t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have fit := tabR_fit h c
  unfold buildTable
  refine copyEntry_ok (c := c) h (x := 6) (j := 0) (by decide) (by decide) fun u₁ O₁ V₁ K₁ => ?_
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine copyEntry_ok (c := c) h₁ (x := 5) (j := 1) (by decide) (by decide) fun u₂ O₂ V₂ K₂ => ?_
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₂ (x := .slot c 5) (d := .slot c 7) (one_ok c) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; exact .inr (by omega))) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by rw [cb1]; omega))
  rw [← List.append_nil (entryPtr c .esi 2 .edx)]
  refine WP.seq (entryPtr_ok (c := c) (j := 2) (r := .esi) (t := .edx) (by decide) (by decide) (by decide)
    (by decide) h₃.edi h₃.width h.upper' (by decide) fun w K₄ m₄ p₄ => WP.block_nil ?_)
  rw [cb1] at O₃
  rw [cw1] at V₃
  -- The state after the setup.
  have F₁ : Frame (frameR base (s.gpr .esp) (tabR len c)) s.mem u₁.mem :=
    frameR_of_outside (O₁.mono (o' := te len c 0) (n' := 16 * bc len c) (Nat.le_refl _) (by omega)) (by omega) (by simp)
  have F₂ : Frame (frameR base (s.gpr .esp) (tabR len c)) u₁.mem u₂.mem :=
    frameR_of_outside (O₂.mono (o' := te len c 0) (n' := 16 * bc len c) (by omega) (by omega)) (by omega) (by simp)
  have F₃ : Frame (frameR base (s.gpr .esp) (tabR len c)) u₂.mem w.mem := by
    rw [m₄]; exact frameR_of_outside O₃ (by omega) (by simp)
  have F : Frame (frameR base (s.gpr .esp) (tabR len c)) s.mem w.mem := F₁.trans (F₂.trans F₃)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w :=
    (((K₁.trans K₂).trans K₃).mono (by decide)).trans (K₄.mono (by decide))
  have S5 : sv u₂.mem base len c 5 = sv s.mem base len c 5 := tabR_slot5 h (F₁.trans F₂) h.room
  have I₂ : TabInv Ex base bytes len args c M b s 2 w := by
    refine ⟨C.keepF K (by decide) (by decide) F fit (tabR_past h c), K, F, fun j hj => ?_, ?_, p₄⟩
    · rw [m₄]
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [O₃.val32 (.inr (by omega)) (by omega), O₂.val32 (.inl (by omega)) (by omega), V₁, h6]; simp
      · rw [O₃.val32 (.inr (by omega)) (by omega), V₂]
        simp only [sv] at h5 ⊢; rw [O₁.val32 (.inl (by omega)) (by omega), h5]; simp
    · simp only [sv]; rw [m₄, V₃]; simp only [sv] at S5 h5; rw [S5, h5]; simp
  -- The loop.
  refine PublicRt.countLoop (N := 14) (by decide) (fun j t => TabInv Ex base bytes len args c M b s (j + 2) t)
    (fun j t hj I => WP.mono (tableStep_ok h5 (by omega) (by omega) I) fun u ⟨I', z⟩ => ⟨I', ?_⟩) I₂
  rw [z]; congr 1

end

end VG.Proof.Bignum.X86.CrtRt
