module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
public import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
public import VerifiedGarbage.Proof.Bignum.CrtNatural
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Export
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Load
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Recombine
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top

/-! # The trace of the table of a windowed power

What a power's run keeps between its pieces (`WSt`): the context, some of
its slots and the table's first entries below its modulus. Each
multiplication keeps it (`mul_wst`), so the table's runs leak the same
trace (`buildTable_relCT`): its setup and each step's copy are checked by
the taint analysis, each step's product related by `mul_relCT`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both)

/-- A run of a power: the context's modulus `M`, the slots `ks` and the table's first `E` entries below
it, the arguments apart and `esp`. -/
def WSt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (c : Ctx) (ks : List Nat)
    (E : Nat) (s : State) : Prop :=
  ∃ M, CtxOk base bytes len args c M s ∧ (∀ j ∈ ks, sv s.mem base len c j < M) ∧
    (∀ j < E, val32 s.mem base (te len c j) (cwc len c) < M) ∧ ArgsOk s ∧ s.gpr .esp = sp

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {sp : BitVec 32}

theorem WSt.agree {ks ks' : List Nat} {E E' : Nat} (W₁ : WSt base bytes len args sp c ks E s)
    (W₂ : WSt base bytes len args sp c ks' E' t) : VG.X86.Taint.Agree τA s t := by
  obtain ⟨_, C₁, -, -, A₁, e₁⟩ := W₁
  obtain ⟨_, C₂, -, -, A₂, e₂⟩ := W₂
  exact agreeA C₁.inp C₂.inp A₁ A₂ (e₁.trans e₂.symm)

theorem WSt.agreeS {ks ks' : List Nat} {E E' : Nat} (W₁ : WSt base bytes len args sp c ks E s)
    (W₂ : WSt base bytes len args sp c ks' E' t) {x : Nat} (p₁ : PtrAt s base .esi x) (p₂ : PtrAt t base .esi x) :
    VG.X86.Taint.Agree τAs s t := by
  obtain ⟨_, C₁, -, -, A₁, e₁⟩ := W₁
  obtain ⟨_, C₂, -, -, A₂, e₂⟩ := W₂
  exact agreeAs C₁.inp C₂.inp A₁ A₂ (e₁.trans e₂.symm) (BitVec.eq_of_toNat_eq (p₁.trans p₂.symm))

theorem WSt.mulIn {ks : List Nat} {E : Nat} (W : WSt base bytes len args sp c ks E s) {b : Nat} (hb : b ∈ ks) :
    MulIn base bytes len args sp c b s :=
  let ⟨M, C, Hk, _, A, e⟩ := W
  ⟨⟨M, C, Hk b hb⟩, A, e⟩

theorem WSt.mono {ks ks' : List Nat} {E E' : Nat} (W : WSt base bytes len args sp c ks E s)
    (hks : ∀ j ∈ ks', j ∈ ks := by decide) (hE : E' ≤ E := by decide) : WSt base bytes len args sp c ks' E' s :=
  let ⟨M, C, Hk, He, A, e⟩ := W
  ⟨M, C, fun j hj => Hk j (hks j hj), fun j hj => He j (by omega), A, e⟩

/-- A multiplication into slot `o` of the context keeps the table. -/
theorem mulR_te (h : In base bytes len args s) {m m' : Mem} {o : Nat}
    (F : Frame (frameR base sp (mulR len c o)) m m') (R : CallRoom sp base bytes) (ho : o ≤ 8) {j : Nat}
    (hj : j < 16) : val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have eo : lo len (.slot c o) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) ho; simp only [lo]; omega
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have f8 := h.slot_fit c (j := 8) (by decide)
  have tj : te len c j + bc len c ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega)
    simp only [te]; rw [Nat.succ_mul] at this; omega
  have tj0 : te len c 0 ≤ te len c j := by simp only [te]; omega
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have T8 : lo len (.slot c 8) + st len c ≤ te len c 0 := by
    have := ctx_in h c (j := 8) (by decide)
    have W := bc_le_wide len c
    have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
    have estw : st len .wide = 2 * bc len .wide + 32 := rfl
    omega
  refine frameR_val32 F R h.crt.scratch.nowrap (by omega) ?_ ?_ <;>
    intro p hp <;> simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl <;> dsimp only <;> omega

theorem mul_wst {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8)
    {ks ks' : List Nat} {E : Nat} (hbk : b ∈ ks) (hE : E ≤ 16)
    (hks : ∀ j ∈ ks', j = o ∨ (j ∈ ks ∧ 3 ≤ j ∧ j ≤ 8)) (W : WSt base bytes len args sp c ks E s) :
    WP isa (CrtRt.mul c o a b) s fun u => WSt base bytes len args sp c ks' E u ∧ Keeps [.eax, .ecx, .edx] s u := by
  obtain ⟨M, C, Hk, He, A, sp₀⟩ := W
  refine WP.mono (cmul_ok C ho3 ho ha3 ha hb3 hb (Hk b hbk)) fun u ⟨Cu, K, F, L, _⟩ =>
    ⟨⟨M, Cu, fun j hj => ?_, fun j hj => ?_, A.keep K, (K.1 _ (by decide)).trans sp₀⟩, K⟩
  · by_cases e : j = o
    · subst e; exact L
    · rcases hks j hj with e' | ⟨hj', j3, j8⟩
      · exact absurd e' e
      · rw [mulR_sv C.inp F C.inp.crt.room ho3 ho j3 j8 e]; exact Hk j hj'
  · rw [mulR_te C.inp F C.inp.crt.room ho (by omega)]; exact He j hj

/-- A multiplication's relation, from the runs' `WSt`. -/
theorem mul_wst_relCT {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8) (hb3 : 3 ≤ b)
    (hb : b ≤ 8) (hT : (VG.Taint.check taint τF (.block (mulArgs c o a b)) (.block [])).isSome = true)
    {ks ks' : List Nat} {E : Nat} (hbk : b ∈ ks) (hE : E ≤ 16)
    (hks : ∀ j ∈ ks', j = o ∨ (j ∈ ks ∧ 3 ≤ j ∧ j ≤ 8)) {X X' : State → Prop}
    (hX : ∀ s u, X s → Keeps [.eax, .ecx, .edx] s u → X' u) :
    RelCT isa (Both fun s => WSt base bytes len args sp c ks E s ∧ X s) (CrtRt.mul c o a b)
      (Both fun u => WSt base bytes len args sp c ks' E u ∧ X' u) :=
  mul_both sp ho3 ho ha3 ha hb3 hb hT (fun _ h => h.1.mulIn hbk)
    fun _ h => WP.mono (mul_wst ho3 ho ha3 ha hb3 hb hbk hE hks h.1) fun _ ⟨W, K⟩ => ⟨W, hX _ _ h.2 K⟩

theorem mul_wst_relCT0 {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8) (hb3 : 3 ≤ b)
    (hb : b ≤ 8) (hT : (VG.Taint.check taint τF (.block (mulArgs c o a b)) (.block [])).isSome = true)
    {ks ks' : List Nat} {E : Nat} (hbk : b ∈ ks) (hE : E ≤ 16)
    (hks : ∀ j ∈ ks', j = o ∨ (j ∈ ks ∧ 3 ≤ j ∧ j ≤ 8)) :
    RelCT isa (Both (WSt base bytes len args sp c ks E)) (CrtRt.mul c o a b)
      (Both (WSt base bytes len args sp c ks' E)) :=
  mul_both sp ho3 ho ha3 ha hb3 hb hT (fun _ h => h.mulIn hbk)
    fun _ h => WP.mono (mul_wst ho3 ho ha3 ha hb3 hb hbk hE hks h) fun _ hu => hu.1

/-! ## The table -/

/-- The copy of slot 7 into entry `i` and the next entry's pointer. -/
def tableTail (c : Ctx) : Prog isa :=
  .seq (.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (.slot c 7) .ebp .edx ++
    [.mov .ebx (.reg .esi)] ++ cntTo (one c) .edi)) <|
  .seq (.seq selectLoop (.block restoreEdi))
    (.block ([.mov .esi (.reg .ebx)] ++ entryPtr c .edx 16 .eax ++ [.alu .cmp .esi (.reg .edx)]))

theorem tableStep_eq (c : Ctx) : tableStep c = .seq (CrtRt.mul c 7 7 5) (tableTail c) := rfl

theorem tableTail_ok (h : In base bytes len args s) {i : Nat} (hi2 : 2 ≤ i) (hi : i < 16)
    (p : PtrAt s base .esi (te len c i)) :
    WP isa (tableTail c) s fun u =>
      Outside base (te len c i) (bc len c) s.mem u.mem ∧
      val32 u.mem base (te len c i) (cwc len c) = sv s.mem base len c 7 ∧
      PtrAt u base .esi (te len c (i + 1)) ∧ u.zf = some (decide (i + 1 = 16)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have est : st len c = 2 * bc len c + 32 := rfl
  have e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have tsucc : ∀ j, te len c (j + 1) = te len c j + bc len c := fun j => by simp only [te]; rw [Nat.succ_mul]; omega
  have ti16 : te len c (i + 1) ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show i + 1 ≤ 16 by omega); simp only [te]; omega
  have ti0 : te len c 0 ≤ te len c i := by simp only [te]; omega
  have ti1 := tsucc i
  have t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega
  have T8 : lo len (.slot c 8) + st len c ≤ te len c 0 := by
    have := ctx_in h c (j := 8) (by decide)
    have W := bc_le_wide len c
    have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
    have estw : st len .wide = 2 * bc len .wide + 32 := rfl
    omega
  unfold tableTail
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS rfl fun w₁ a₁ _ => ?_)
  have hw₁ := h.regs a₁.keeps a₁.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (x := .slot c 7) (by decide) (by decide) hw₁.edi hw₁.width h.upper'
    (by omega) fun w₂ K₂ m₂ p₂ => wp_movS rfl fun w₃ a₃ _ => ?_
  have hw₃ := hw₁.regs ((K₂.mono (by decide)).trans (a₃.keeps.mono (by decide)) : Keeps [.ebx, .edx, .ebp] w₁ w₃)
    (by rw [a₃.mem, m₂])
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) hw₃.width h.upper' (one_ok c).extra fun w₄ K₄ m₄ c₄ => WP.block_nil ?_
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have Kw : Keeps [.ebx, .ecx, .edx, .ebp, .edi] s w₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (K₄.mono (by decide))
  have mw : w₄.mem = s.mem := by rw [m₄, a₃.mem, m₂, a₁.mem]
  have pe : PtrAt w₄ base .ebp (lo len (.slot c 7)) := by
    rw [PtrAt, K₄.1 _ (by decide), a₃.other _ (by decide)]; exact p₂
  have pb : PtrAt w₄ base .ebx (te len c i) := by
    rw [PtrAt, K₄.1 _ (by decide), a₃.gpr, K₂.1 _ (by decide), a₁.other _ (by decide)]; exact p
  have ce : (w₄.gpr .edi).toNat = 4 * cwc len c := by rw [cnt_toNat h.upper' (one_ok c) c₄, cw1]
  have ck : w₄.gpr .ecx = cmask true := by
    rw [K₄.1 _ (by decide), a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]; rfl
  refine WP.seq (WP.mono (selectTail_ok h (Kw.mono (by decide)) mw (x := lo len (.slot c 7)) (d := te len c i)
    (N := cwc len c) (k := true) (by omega) (by omega) (by omega) (by omega) pe pb ce ck)
    fun u₂ ⟨O₂, V₂, pb₂, K₂'⟩ => ?_)
  have h₂ := h.keep (K₂'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₂) (by decide) (by decide)
    (by rw [← mw]; exact O₂.mono (Nat.zero_le _) (by omega))
  refine wp_movS rfl fun v₁ b₁ _ => ?_
  have hv₁ := h₂.regs b₁.keeps b₁.mem
  refine entryPtr_ok (c := c) (j := 16) (r := .edx) (t := .eax) (by decide) (by decide) (by decide) (by decide)
    hv₁.edi hv₁.width h.upper' (by decide) fun v₂ K₅ m₅ p₅ => wp_cmpS rfl fun v₃ f₃ z₃ => WP.block_nil ?_
  have esi₂ : PtrAt v₂ base .esi (te len c (i + 1)) := by
    rw [PtrAt, K₅.1 _ (by decide), b₁.gpr, tsucc, bw]; exact pb₂
  have m₃ : v₃.mem = u₂.mem := by rw [f₃.mem, m₅, b₁.mem]
  refine ⟨by rw [m₃, ← mw, bw]; exact O₂, by rw [m₃, V₂]; simp only [↓reduceIte, mw, sv],
    by rw [PtrAt, f₃.gpr]; exact esi₂, ?_,
    (((K₂'.mono (by decide)).trans (b₁.keeps.mono (by decide))).trans (K₅.mono (by decide))).trans (f₃.keeps _)⟩
  rw [z₃, ptr_beq esi₂ p₅ (by omega) (by omega)]
  congr 1
  apply decide_eq_decide.mpr
  constructor
  · intro e
    have e' : (i + 1) * bc len c = 16 * bc len c := by simp only [te] at e; omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) e'
  · intro e; rw [e]

/-- A table step's run: entries up to `i` and slots 3, 5 and 6 below the modulus, `esi` at entry `i`. -/
abbrev TSt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (c : Ctx) (ks : List Nat)
    (i : Nat) (s : State) : Prop :=
  WSt base bytes len args sp c ks i s ∧ PtrAt s base .esi (te len c i)

theorem tableTail_wst {i : Nat} (hi2 : 2 ≤ i) (hi : i < 16) (W : TSt base bytes len args sp c [3, 5, 6, 7] i s) :
    WP isa (tableTail c) s fun u => TSt base bytes len args sp c [3, 5, 6] (i + 1) u ∧
      u.zf = some (decide (i + 1 = 16)) := by
  obtain ⟨⟨M, C, Hk, He, A, sp₀⟩, p⟩ := W
  have h := C.inp
  have bl := h.bytes_lt
  have T := h.table_fit c
  have bw := bc_eq_cwc len c
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have ti16 : te len c (i + 1) ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show i + 1 ≤ 16 by omega); simp only [te]; omega
  have ti0 : te len c 0 ≤ te len c i := by simp only [te]; omega
  have ti1 : te len c (i + 1) = te len c i + bc len c := by simp only [te]; rw [Nat.succ_mul]; omega
  have T8 : lo len (.slot c 8) + st len c ≤ te len c 0 := by
    have := ctx_in h c (j := 8) (by decide)
    have W := bc_le_wide len c
    have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
    have estw : st len .wide = 2 * bc len .wide + 32 := rfl
    omega
  refine WP.mono (tableTail_ok h hi2 hi p) fun u ⟨O, V, pu, zu, K⟩ => ⟨⟨⟨M, ?_, fun j hj => ?_, fun j hj => ?_,
    A.keep K, (K.1 _ (by decide)).trans sp₀⟩, pu⟩, zu⟩
  · exact C.keepF K (by decide) (by decide) (ws := [(te len c i, bc len c)]) (frameR_of_outside O (by omega) (by simp))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only
          have z0 : lo len (.slot c 0) = numBase := sl_zero len c
          have e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
          omega)
  · have j8 : j ≤ 8 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
    have hj' : j ∈ [3, 5, 6, 7] := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega
    have := Nat.mul_le_mul_right (st len c) j8
    have ej : lo len (.slot c j) = numBase + j * st len c := rfl
    have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
    simp only [sv]
    rw [Outside.val32 O (.inl (by omega)) (by omega)]
    exact Hk j hj'
  · by_cases e : j = i
    · subst e; rw [V]; exact Hk 7 (by decide)
    · have tj : te len c j + bc len c ≤ te len c i := by
        have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ i by omega); simp only [te]; rw [Nat.succ_mul] at this; omega
      have tj0 : te len c 0 ≤ te len c j := by simp only [te]; omega
      rw [Outside.val32 O (.inl (by omega)) (by omega)]
      exact He j (by omega)

theorem tableStep_relCT (hT : (VG.Taint.check taint τF (.block (mulArgs c 7 7 5)) (.block [])).isSome = true)
    (hT' : (VG.Taint.check taint τAs (tableTail c) (VG.Taint.hintOf taint τAs (tableTail c))).isSome = true)
    {i : Nat} (hi2 : 2 ≤ i) (hi : i < 16) :
    RelCT isa (Both (TSt base bytes len args sp c [3, 5, 6] i)) (tableStep c)
      (Both fun u => TSt base bytes len args sp c [3, 5, 6] (i + 1) u ∧ u.zf = some (decide (i + 1 = 16))) := by
  rw [tableStep_eq]
  refine VG.RelCT.seq (mul_wst_relCT (X := fun s => PtrAt s base .esi (te len c i))
    (X' := fun s => PtrAt s base .esi (te len c i)) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hT (ks' := [3, 5, 6, 7]) (by decide) (by omega) (by decide)
    fun s u p K => by rw [PtrAt, K.1 _ (by decide)]; exact p) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.1.agreeS W₂.1 W₁.2 W₂.2) _ hT' fun _ W => tableTail_wst hi2 hi W

/-- The table's setup: entries 0 and 1 from slots 6 and 5, slot 7 from slot 5, `esi` at entry 2. -/
def tableSetup (c : Ctx) : List (Prog isa) :=
  [.block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (.slot c 6) .ebp .edx ++ entryPtr c .ebx 0 .edx ++
    cntTo (one c) .edi), .seq selectLoop (.block restoreEdi),
   .block ([.mov .ecx (.imm (BitVec.allOnes 32))] ++ ptrTo (.slot c 5) .ebp .edx ++ entryPtr c .ebx 1 .edx ++
    cntTo (one c) .edi), .seq selectLoop (.block restoreEdi),
   copy (.slot c 5) (.slot c 7) (one c), .block (entryPtr c .esi 2 .edx)]

theorem buildTable_eq (c : Ctx) : buildTable c = Prog.chain (tableSetup c) (.loop (tableStep c) .ne) := rfl

theorem tableSetup_wst (W : WSt base bytes len args sp c [3, 5, 6] 0 s) :
    WP isa (Prog.chain (tableSetup c) (.block [])) s (TSt base bytes len args sp c [3, 5, 6] 2) := by
  obtain ⟨M, C, Hk, -, A, sp₀⟩ := W
  have h := C.inp
  have nw := h.crt.scratch.nowrap
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
  show WP isa (.seq _ (.seq (.seq selectLoop (.block restoreEdi)) (.seq _ (.seq (.seq selectLoop (.block restoreEdi))
    (.seq (copy (.slot c 5) (.slot c 7) (one c)) (.seq (.block (entryPtr c .esi 2 .edx)) (.block []))))))) s _
  refine copyEntry_ok (c := c) h (x := 6) (j := 0) (by decide) (by decide) fun u₁ O₁ V₁ K₁ => ?_
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine copyEntry_ok (c := c) h₁ (x := 5) (j := 1) (by decide) (by decide) fun u₂ O₂ V₂ K₂ => ?_
  have h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (copy_ok h₂ (x := .slot c 5) (d := .slot c 7) (one_ok c) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; exact .inr (by omega))) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  have h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by rw [cb1]; omega))
  rw [← List.append_nil (entryPtr c .esi 2 .edx)]
  refine WP.seq (entryPtr_ok (c := c) (j := 2) (r := .esi) (t := .edx) (by decide) (by decide) (by decide)
    (by decide) h₃.edi h₃.width h.upper' (by decide) fun w K₄ m₄ p₄ => WP.block_nil (WP.block_nil ?_))
  rw [cb1] at O₃
  have F₁ : Frame (frameR base (s.gpr .esp) (tabR len c)) s.mem u₁.mem :=
    frameR_of_outside (O₁.mono (o' := te len c 0) (n' := 16 * bc len c) (Nat.le_refl _) (by omega)) (by omega) (by simp)
  have F₂ : Frame (frameR base (s.gpr .esp) (tabR len c)) u₁.mem u₂.mem :=
    frameR_of_outside (O₂.mono (o' := te len c 0) (n' := 16 * bc len c) (by omega) (by omega)) (by omega) (by simp)
  have F₃ : Frame (frameR base (s.gpr .esp) (tabR len c)) u₂.mem w.mem := by
    rw [m₄]; exact frameR_of_outside O₃ (by omega) (by simp)
  have F : Frame (frameR base (s.gpr .esp) (tabR len c)) s.mem w.mem := F₁.trans (F₂.trans F₃)
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w :=
    (((K₁.trans K₂).trans K₃).mono (by decide)).trans (K₄.mono (by decide))
  refine ⟨⟨M, C.keepF K (by decide) (by decide) F fit (tabR_past h c), fun j hj => ?_, fun j hj => ?_,
    A.keep K, (K.1 _ (by decide)).trans sp₀⟩, p₄⟩
  · have j3 : 3 ≤ j := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
    have j8 : j ≤ 8 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
    have j7 : j ≠ 7 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
    rw [tabR_sv h F h.crt.room j3 j8 j7]; exact Hk j hj
  · rw [m₄]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [O₃.val32 (.inr (by omega)) (by omega), O₂.val32 (.inl (by omega)) (by omega), V₁]; exact Hk 6 (by decide)
    · rw [O₃.val32 (.inr (by omega)) (by omega), V₂]
      simp only [sv]; rw [O₁.val32 (.inl (by omega)) (by omega)]; exact Hk 5 (by decide)

theorem buildTable_relCT (hT : (VG.Taint.check taint τF (.block (mulArgs c 7 7 5)) (.block [])).isSome = true)
    (hT' : (VG.Taint.check taint τAs (tableTail c) (VG.Taint.hintOf taint τAs (tableTail c))).isSome = true)
    (hS : (VG.Taint.check taint τA (Prog.chain (tableSetup c) (.block []))
      (VG.Taint.hintOf taint τA (Prog.chain (tableSetup c) (.block [])))).isSome = true) :
    RelCT isa (Both (WSt base bytes len args sp c [3, 5, 6] 0)) (buildTable c)
      (Both (TSt base bytes len args sp c [3, 5, 6] 16)) := by
  rw [buildTable_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hS fun _ W => tableSetup_wst W)
    ?_)
  exact relCT_countLoop (I := fun j => TSt base bytes len args sp c [3, 5, 6] (j + 2)) (N := 14) (by decide)
    fun j hj => tableStep_relCT hT hT' (by omega) (by omega)

end

end VG.Proof.Bignum.X86.CrtRt
