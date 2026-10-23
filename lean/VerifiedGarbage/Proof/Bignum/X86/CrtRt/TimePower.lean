module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.PowerInit

/-! # The trace of a factor's power and of the coefficient

Each is a sequence of copies and context setups, which the taint analysis
checks, and multiplications, related by `mul_relCT` from what each run
keeps (`WSt`), among them the squares that end a context's setup
(`prepare_relCT`): `power_relCT` (either width, by the factor's length, which
both runs share) and `coefficient_relCT`, from the runs' `Run` to their
`Run`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem WSt.run {c : Ctx} {ks : List Nat} {E : Nat} (W : WSt Ex base bytes len args sp c ks E s) :
    Run Ex base bytes len args sp s :=
  let ⟨_, C, _, _, A, e⟩ := W
  ⟨C.inp, A, e⟩

theorem Run.keep (R : Run Ex base bytes len args sp s) {regs : List Reg} (K : Keeps regs s t)
    (O : Outside base 0 bytes s.mem t.mem) (di : .edi ∉ regs := by decide) (spn : .esp ∉ regs := by decide) :
    Run Ex base bytes len args sp t :=
  ⟨R.1.keep K di spn O, R.2.1.keep K spn, (K.1 _ spn).trans R.2.2⟩

theorem prepBase_wst (R : Run Ex base bytes len args sp s) (c : Ctx) :
    WP isa (prepBase c) s (WSt Ex base bytes len args sp c [3, 4] 0) := by
  refine WP.mono (prepBase_ok R.1 c) fun u ⟨F, M, one, R2, I, K⟩ =>
    ⟨_, ⟨R.1.keepF K (by decide) (by decide) F (baseR_fit R.1 c), M, safeM_gt _, safeM_odd _, I⟩,
      fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
  have hM := safeM_gt (sv s.mem base len c 0)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [one]; exact hM
  · rw [R2]; exact Nat.mod_lt _ (by omega)

/-- The taint checks of a context's setup. -/
structure PrepChecks (c : Ctx) : Prop where
  base : XCheck (prepBase c)
  count : ACheck (.block [.mov .esi (.imm (BitVec.ofNat 32 6))])
  dec : ACheck (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])
  m444 : MulCheck c 4 4 4

theorem prepChecks (c : Ctx) : PrepChecks c := by
  cases c <;> constructor <;> (try dsimp only [MulCheck, ACheck, XCheck]) <;> taint_decide

/-- A run of the squares of a context's setup, with `n` of them left. -/
abbrev SqSt (c : Ctx) (n : Nat) (s : State) : Prop :=
  WSt Ex base bytes len args sp c [3, 4] 0 s ∧ s.gpr .esi = BitVec.ofNat 32 n

theorem sqCount_wst {c : Ctx} (W : WSt Ex base bytes len args sp c [3, 4] 0 s) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 6))]) s (SqSt (Ex := Ex) (base := base) (bytes := bytes)
      (len := len) (args := args) (sp := sp) c 6) := by
  obtain ⟨M, C, Hk, He, A, sp₀⟩ := W
  refine wp_movS rfl fun u a _ => WP.block_nil ⟨⟨M, C.regs a.keeps a.mem, by rw [a.mem]; exact Hk,
    by rw [a.mem]; exact He, A.keep a.keeps, (a.keeps.1 _ (by decide)).trans sp₀⟩, a.gpr⟩

theorem sqDec_wst {c : Ctx} {n : Nat} (hn0 : 0 < n) (hn : n < 2 ^ 32)
    (W : SqSt (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp) c n s) :
    WP isa (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]) s fun u =>
      SqSt (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp) c (n - 1) u ∧
        u.zf = some (decide (n = 1)) := by
  obtain ⟨⟨M, C, Hk, He, A, sp₀⟩, e⟩ := W
  refine wp_subS rfl fun u a _ => wp_cmpS rfl fun w aw zw => WP.block_nil ?_
  have K : Keeps [.esi] s w := a.keeps.trans (aw.keeps [.esi])
  have m : w.mem = s.mem := aw.mem.trans a.mem
  have sub : BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := VG.Proof.Mont.X86.Dynamic.counter_sub hn hn0
  have ew : w.gpr .esi = BitVec.ofNat 32 (n - 1) := by rw [aw.gpr, a.gpr, e, sub]
  refine ⟨⟨⟨M, C.regs K m, by rw [m]; exact Hk, by rw [m]; exact He, A.keep K, (K.1 _ (by decide)).trans sp₀⟩,
    ew⟩, ?_⟩
  rw [zw, a.gpr, e, sub, VG.Proof.Mont.X86.Dynamic.counter_zero hn hn0]

theorem squares4_relCT {c : Ctx} (hc : PrepChecks c) :
    RelCT isa (Both (WSt Ex base bytes len args sp c [3, 4] 0))
      (VG.Impl.Mont.X86.Dynamic.repeatSquaresWith (mul c 4 4 4) 6)
      (Both (WSt Ex base bytes len args sp c [3, 4] 0)) := by
  unfold VG.Impl.Mont.X86.Dynamic.repeatSquaresWith
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.count fun _ W => sqCount_wst W) ?_
  refine (relCT_countLoop (N := 6) (I := fun j => SqSt (Ex := Ex) (base := base) (bytes := bytes) (len := len)
    (args := args) (sp := sp) c (6 - j)) (by decide) fun j hj => ?_).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.1.1, h.2.1⟩
  unfold VG.Impl.Mont.X86.Dynamic.squareStepWith
  refine VG.RelCT.seq (mul_wst_relCT (X := fun s => s.gpr .esi = BitVec.ofNat 32 (6 - j))
    (X' := fun s => s.gpr .esi = BitVec.ofNat 32 (6 - j)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m444 (ks' := [3, 4]) (by decide) (by decide) (by decide)
    fun _ _ e K => (K.1 _ (by decide)).trans e) ?_
  refine (taint_both (fun _ _ W₁ W₂ => W₁.1.agree W₂.1) _ hc.dec
    fun _ W => sqDec_wst (n := 6 - j) (by omega) (by omega) W).mono (fun _ _ h => h) ?_
  rintro s t ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩
  have e : 6 - j - 1 = 6 - (j + 1) := by omega
  have d : (6 - j = 1) = (j + 1 = 6) := propext (by omega)
  rw [e] at W₁ W₂
  simp only [d] at z₁ z₂
  exact ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩

theorem prepare_relCT (c : Ctx) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (prepare c) (Both (WSt Ex base bytes len args sp c [3, 4] 0)) :=
  have hc := prepChecks c
  VG.RelCT.seq (PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τA (fun _ _ h => h.1.agree h.2) hc.base)
    fun _ R => prepBase_wst R c)
    (squares4_relCT hc)

theorem copyDown_run {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hd : d ≤ 8) (R : Run Ex base bytes len args sp s) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) s (Run Ex base bytes len args sp) := by
  have f := R.1.slot_fit .wide (j := d) (by omega)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  exact WP.mono (copyDown_ok R.1 hj9 hj hd) fun u ⟨O, _, K⟩ => R.keep K (O.mono (Nat.zero_le _) (by omega))

theorem copyDown_wst {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hd1 : 1 ≤ d) (hd : d ≤ 8) {ks : List Nat} {E : Nat}
    (hks : ∀ i ∈ ks, i ≠ d ∧ i ≤ 8) (hE : E ≤ 16) (W : WSt Ex base bytes len args sp .wide ks E s) :
    WP isa (copy (.slot .wide j) (.slot .wide d) (one .wide)) s (WSt Ex base bytes len args sp .wide ks E) := by
  obtain ⟨M, C, Hk, He, A, sp₀⟩ := W
  have h := C.inp
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have ed : lo len (.slot .wide d) = numBase + d * st len .wide := rfl
  have e8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have d8 := Nat.mul_le_mul_right (st len .wide) hd
  have d1 := Nat.mul_le_mul_right (st len .wide) hd1
  have T8 : lo len (.slot .wide 8) + st len .wide ≤ te len .wide 0 := by
    have := ctx_in h .wide (j := 8) (by decide)
    have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
    have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
    omega
  refine WP.mono (copyDown_ok h hj9 hj hd) fun u ⟨O, _, K⟩ => ⟨M, ?_, fun i hi => ?_, fun i hi => ?_,
    A.keep K, (K.1 _ (by decide)).trans sp₀⟩
  · exact C.keepF K (by decide) (by decide) (ws := [(lo len (.slot .wide d), bc len .wide)])
      (frameR_of_outside O (by omega) (by simp))
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
      (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; dsimp only; omega)
  · obtain ⟨hne, hi8⟩ := hks i hi
    have i8 := Nat.mul_le_mul_right (st len .wide) hi8
    have ei : lo len (.slot .wide i) = numBase + i * st len .wide := rfl
    have ap : lo len (.slot .wide i) + 4 * cwc len .wide ≤ lo len (.slot .wide d) ∨
        lo len (.slot .wide d) + bc len .wide ≤ lo len (.slot .wide i) := by
      rcases slot_apart len .wide hne with a | a
      · exact .inl (by omega)
      · exact .inr a
    simp only [sv]
    rw [Outside.val32 O ap (by omega)]
    exact Hk i hi
  · obtain ⟨tj0, tj⟩ := te_le (len := len) (c := .wide) (by omega : i < 16)
    have := h.table_fit .wide
    rw [Outside.val32 O (.inr (by omega)) (by omega)]; exact He i hi

theorem saveResult_run {c : Ctx} {o : Nat} (ho9 : 9 ≤ o) (ho : o ≤ 19) {ks : List Nat} {E : Nat}
    (W : WSt Ex base bytes len args sp c ks E s) :
    WP isa (saveResult c o) s (Run Ex base bytes len args sp) := by
  have R := W.run
  have f := R.1.wide_fit ho
  exact WP.mono (saveResult_ok R.1 c ho9 ho) fun u ⟨O, _, K⟩ =>
    R.keep K (O.mono (Nat.zero_le _) (by omega))

/-! ## A factor's power -/

/-- The factor and the input into the wide context, before it is set up. -/
abbrev reduceHead (f : Nat) : List (Prog isa) :=
  [copy (.slot .wide f) (.slot .wide 0) (one .wide), copy (.slot .wide 15) (.slot .wide 5) (one .wide)]

/-- The input reduced, the factor and the exponent into the half context, before it is set up. -/
abbrev narrowMid (f e o : Nat) : List (Prog isa) :=
  [copy (.slot .wide 5) (.slot .wide o) (one .wide), copy (.slot .wide f) (.slot .half 0) (one .half),
    copy (.slot .wide o) (.slot .half 5) (one .half), copy (.slot .wide e) (.slot .half 8) (one .half)]

/-- The factor, the input and the exponent into the wide context, before it is set up. -/
abbrev wideHead (f e : Nat) : List (Prog isa) :=
  [copy (.slot .wide f) (.slot .wide 0) (one .wide), copy (.slot .wide 15) (.slot .wide 5) (one .wide),
    copy (.slot .wide e) (.slot .wide 8) (one .wide)]

/-- The comparison of the factor's length with half the width. -/
abbrev powerTest (l : Nat) : List Instr :=
  [.mov .eax (.mem (argAt 0 l))] ++ widthC 0 .half .edx ++ [.alu .add .edx (.imm 1), .alu .cmp .eax (.reg .edx)]

theorem narrowPower_eq (f e o : Nat) : narrowPower f e o = Prog.chain (reduceHead f)
    (.seq (prepare .wide) (.seq (CrtRt.mul .wide 5 5 4) (.seq (CrtRt.mul .wide 5 5 3)
      (Prog.chain (narrowMid f e o) (.seq (prepare .half) (.seq (windowPower .half) (saveResult .half o))))))) := rfl

theorem widePower_eq (f e o : Nat) : widePower f e o = Prog.chain (wideHead f e)
    (.seq (prepare .wide) (.seq (windowPower .wide) (saveResult .wide o))) := rfl

/-- The taint checks of a factor's power. -/
structure PowChecks (f e o l : Nat) : Prop where
  head : ACheck (Prog.chain (reduceHead f) (.block []))
  mid : ACheck (Prog.chain (narrowMid f e o) (.block []))
  wide : ACheck (Prog.chain (wideHead f e) (.block []))
  saveH : ACheck (saveResult .half o)
  saveW : ACheck (saveResult .wide o)
  test : ACheck (.block (powerTest l))
  m554 : MulCheck .wide 5 5 4
  m553 : MulCheck .wide 5 5 3

theorem reduceHead_run {f : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (R : Run Ex base bytes len args sp s) :
    WP isa (Prog.chain (reduceHead f) (.block [])) s (Run Ex base bytes len args sp) :=
  WP.seq (WP.mono (copyDown_run hf9 (by omega) (by decide) R) fun _ R₁ =>
    WP.seq (WP.mono (copyDown_run (by decide) (by decide) (by decide) R₁) fun _ R₂ => WP.block_nil R₂))

theorem wideHead_run {f e : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (R : Run Ex base bytes len args sp s) :
    WP isa (Prog.chain (wideHead f e) (.block [])) s (Run Ex base bytes len args sp) :=
  WP.seq (WP.mono (copyDown_run hf9 (by omega) (by decide) R) fun _ R₁ =>
    WP.seq (WP.mono (copyDown_run (by decide) (by decide) (by decide) R₁) fun _ R₂ =>
      WP.seq (WP.mono (copyDown_run he9 (by omega) (by decide) R₂) fun _ R₃ => WP.block_nil R₃)))

theorem narrowMid_run {f e o : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15) (ho16 : 16 ≤ o)
    (ho : o ≤ 17) {ks : List Nat} {E : Nat} (W : WSt Ex base bytes len args sp .wide ks E s) :
    WP isa (Prog.chain (narrowMid f e o) (.block [])) s (Run Ex base bytes len args sp) := by
  have R := W.run
  have h := R.1
  obtain ⟨est, l0, l5, l8, l9, l15, l16, l18, f1, f2, o1, o2, fit, nb⟩ := WideLay.mk' h hf9 hf ho16 ho
  have bw := bc_eq_cwc len .wide
  have bl := h.bytes_lt
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  show WP isa (.seq (copy (.slot .wide 5) (.slot .wide o) (one .wide)) (.seq _ (.seq _ (.seq _
    (.block []))))) s _
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 5) (d := .slot .wide o) (one_ok .wide)
    (by rw [cb1, l5]; omega) (by rw [cb1]; omega)
    (by rw [cb1, l5]; exact .inr (by omega))) fun u₁ ⟨O₁, _, K₁⟩ => ?_)
  rw [cb1] at O₁
  have R₁ := R.keep K₁ (O₁.mono (Nat.zero_le _) (by omega))
  refine narrowCopies_ok R₁.1 hf9 hf he9 he ho16 ho rfl rfl rfl fun u₄ h₄ _ _ _ _ K₄ => ?_
  exact WP.block_nil ⟨h₄, R₁.2.1.keep K₄, (K₄.1 _ (by decide)).trans R₁.2.2⟩

theorem powerTest_run {l : Nat} (hl : l < 18) (R : Run Ex base bytes len args sp s) :
    WP isa (.block (powerTest l)) s fun u => Run Ex base bytes len args sp u ∧
      isa.eval .b u = some (decide ((args l).toNat < bc len .half + 1)) := by
  have h := R.1
  have hb := bc_le h.upper' .half
  simp only [powerTest, List.cons_append]
  refine wp_movS (h.arg hl) fun u₁ a₁ _ => ?_
  have h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  have m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  have eax : u₃.gpr .eax = args l := by rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]
  have edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  rw [eax, edx] at c₄
  exact ⟨R.keep K₄ (by rw [m₄]; exact Outside.refl _ _ _ _), c₄⟩

theorem narrowPower_relCT {f e o l : Nat} (hc : PowChecks f e o l) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (narrowPower f e o) (Both (Run Ex base bytes len args sp)) := by
  rw [narrowPower_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.head
    fun _ R => reduceHead_run hf9 hf R) ?_)
  refine VG.RelCT.seq (prepare_relCT .wide) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m554 (ks' := [3]) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m553 (ks' := []) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.mid
    fun _ W => narrowMid_run hf9 hf he9 he ho16 ho W) ?_)
  refine VG.RelCT.seq (prepare_relCT .half) ?_
  refine VG.RelCT.seq (windowPower_relCT (winChecks .half)) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.saveH fun _ W => saveResult_run (by omega) (by omega) W

theorem widePower_relCT {f e o l : Nat} (hc : PowChecks f e o l) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (widePower f e o) (Both (Run Ex base bytes len args sp)) := by
  rw [widePower_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.wide
    fun _ R => wideHead_run hf9 hf he9 he R) ?_)
  refine VG.RelCT.seq (prepare_relCT .wide) ?_
  refine VG.RelCT.seq (windowPower_relCT (winChecks .wide)) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.saveW fun _ W => saveResult_run (by omega) (by omega) W

theorem power_relCT {f e o l : Nat} (hc : PowChecks f e o l) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e)
    (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) (hl : l < 18) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (power f e o l) (Both (Run Ex base bytes len args sp)) := by
  unfold power
  refine VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.test fun _ R => powerTest_run hl R) ?_
  refine VG.RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm)
    ((narrowPower_relCT hc hf9 hf he9 he ho16 ho).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
    ((widePower_relCT hc hf9 hf he9 he ho16 ho).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)

/-! ## The coefficient -/

abbrev coHead : List (Prog isa) :=
  [copy (.slot .wide 16) (.slot .wide 6) (one .wide), copy (.slot .wide 17) (.slot .wide 5) (one .wide),
    copy (.slot .wide 14) (.slot .wide 8) (one .wide)]

theorem coefficient_eq : coefficient = .seq (copy (.slot .wide 10) (.slot .wide 0) (one .wide))
    (.seq (prepare .wide) (Prog.chain coHead (.seq (CrtRt.mul .wide 5 5 4) (.seq (CrtRt.mul .wide 5 5 3) (.seq (subMod .wide 7 6 5)
      (.seq (CrtRt.mul .wide 8 8 4) (CrtRt.mul .wide 7 7 8))))))) := rfl

/-- The taint checks of the coefficient. -/
structure CoChecks : Prop where
  copy : ACheck (copy (.slot .wide 10) (.slot .wide 0) (one .wide))
  head : ACheck (Prog.chain coHead (.block []))
  sub : ACheck (subMod .wide 7 6 5)
  m554 : MulCheck .wide 5 5 4
  m553 : MulCheck .wide 5 5 3
  m884 : MulCheck .wide 8 8 4
  m778 : MulCheck .wide 7 7 8

theorem coHead_wst (W₂ : WSt Ex base bytes len args sp .wide [3, 4] 0 s) :
    WP isa (Prog.chain coHead (.block [])) s (WSt Ex base bytes len args sp .wide [3, 4] 0) :=
  WP.seq (WP.mono (copyDown_wst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) W₂)
    fun _ W₃ =>
  WP.seq (WP.mono (copyDown_wst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) W₃)
    fun _ W₄ =>
  WP.seq (WP.mono (copyDown_wst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) W₄)
    fun _ W₅ => WP.block_nil W₅)))

theorem subMod_wst (W : WSt Ex base bytes len args sp .wide [3, 4, 5] 0 s) :
    WP isa (subMod .wide 7 6 5) s (WSt Ex base bytes len args sp .wide [4] 0) := by
  obtain ⟨M, C, Hk, -, A, sp₀⟩ := W
  refine WP.mono (subMod_raw C) fun u ⟨Cu, F, _, K⟩ => ⟨M, Cu, fun j hj => ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _), A.keep K, (K.1 _ (by decide)).trans sp₀⟩
  rw [List.mem_singleton.mp hj, subR_sv C.inp .wide F C.inp.room (by decide) (by decide) (by decide)]
  exact Hk 4 (by decide)

theorem coefficient_relCT (hc : CoChecks) :
    RelCT isa (Both (Run Ex base bytes len args sp)) coefficient (Both (Run Ex base bytes len args sp)) := by
  rw [coefficient_eq]
  refine VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.copy
    fun _ R => copyDown_run (by decide) (by decide) (by decide) R) ?_
  refine VG.RelCT.seq (prepare_relCT .wide) ?_
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.head
    fun _ W => coHead_wst W) ?_)
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m554 (ks' := [3, 4, 5]) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 5) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m553 (ks' := [3, 4, 5]) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.sub fun _ W => subMod_wst W) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 8) (a := 8) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m884 (ks' := [8]) (by decide) (by decide) (by decide)) ?_
  exact (mul_wst_relCT0 (o := 7) (a := 7) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m778 (ks' := []) (by decide) (by decide) (by decide)).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.1.run, h.2.run⟩

end

end VG.Proof.Bignum.X86.CrtRt
