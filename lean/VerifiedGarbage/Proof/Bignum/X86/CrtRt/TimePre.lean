module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TopP
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TopP
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The trace of `vg_rsa_private_crt_precomputed` on x86

As `vg_rsa_private_crt`'s (`TimeTop.lean`), with the factors' contexts set up
from `pre` (`preparePre`), whose addresses and counts come from arguments 7,
9 and 18: the taint analysis checks it with the arguments up to 18 public
(`τP`, `agreeP`), from what each run keeps of `pre` (`PreC`). Which factor's
value `loadHead` reads is in the header, which the analysis does not know
public: it checks `preparePre` up to `loadHead`, whose registers are then
functions of the arguments in both runs (`MidP`), and the rest with them
public (`τQ`, `agreeQ`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)

/-- `τA` with argument 18 public too. -/
def τP : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 80 }

/-- The return address and the nineteen arguments lie apart from every writable region. -/
def ArgsOkP (s : State) : Prop :=
  (s.gpr .esp).toNat + 80 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 80⟩ r

theorem τP_wf {s : State} (A : ArgsOkP s) : VG.X86.Taint.Wf τP s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

/-- The return address and the first eighteen arguments, and argument 18, make the nineteen. -/
theorem args19_disjoint {s : State} (top : (s.gpr .esp).toNat + 80 ≤ 2 ^ 32) {r : Region}
    (h76 : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ r)
    (h18 : Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩ r) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 80⟩ r := by
  have sa : VG.Proof.Dsa.X86.stackAddress s preArg = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 76 :=
    addr_eq (by simp only [preArg]; omega_using [top])
  rw [sa] at h18
  intro a ha hr
  simp only [Region.Contains] at ha
  by_cases h : (a - (s.gpr .esp).setWidth 64).toNat < 76
  · exact h76 a (by simp only [Region.Contains]; omega_using [h]) hr
  · refine h18 a ?_ hr
    simp only [Region.Contains]
    rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
    have := (a - (s.gpr .esp).setWidth 64).isLt
    omega_using [ha, h]

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem agreeP {s₁ s₂ : State} (h₁ : In Ex base bytes len args s₁) (h₂ : In Ex base bytes len args s₂)
    {i₁ i₂ p₁ p₂ : Nat} (P₁ : PreR2 s₁ base bytes len args i₁ p₁) (P₂ : PreR2 s₂ base bytes len args i₂ p₂)
    (A₁ : ArgsOkP s₁) (A₂ : ArgsOkP s₂) (sp : s₁.gpr .esp = s₂.gpr .esp) : VG.X86.Taint.Agree τP s₁ s₂ := by
  have f₁ := A₁.1
  have f₂ := A₂.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τP_wf A₁, τP_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τP, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h₁.edi.trans h₂.edi.symm)
    · exact sp
  · simp only [τP] at hk
    rw [show VG.X86.Taint.depth τP.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    refine congrArg _ (show arg s₁ _ = arg s₂ _ from ?_)
    rcases Nat.lt_or_ge ((k - 4) / 4) 18 with hl | hg
    · exact (h₁.stack _ hl).value.trans (h₂.stack _ hl).value.symm
    · rw [show (k - 4) / 4 = preArg by simp only [preArg]; omega_using [hk, hg]]
      exact P₁.arg.value.trans P₂.arg.value.symm

/-- Argument 18 apart from every writable region. -/
def ArgWr (s : State) : Prop := ∀ r ∈ s.wr, Region.Disjoint ⟨VG.Proof.Dsa.X86.stackAddress s preArg, 4⟩ r

theorem ArgWr.keep (W : ArgWr s) {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs := by decide) :
    ArgWr t := by
  intro r hr
  rw [show VG.Proof.Dsa.X86.stackAddress t preArg = VG.Proof.Dsa.X86.stackAddress s preArg by
    simp only [VG.Proof.Dsa.X86.stackAddress, K.1 _ sp]]
  exact W r (by rw [← K.2.2]; exact hr)

theorem argsOkP_of (A : ArgsOk s) {i p : Nat} (P : PreR2 s base bytes len args i p) (W : ArgWr s) : ArgsOkP s :=
  ⟨P.top, fun r hr => args19_disjoint P.top (A.2 r hr) (W r hr)⟩

/-- What a run of `preparePre c` from factor `i`'s cached value needs: a run, factor `i`'s cached value
of the modulus in slot 0, argument 18 apart from what it writes, and the header words naming it. -/
def PrepP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (c : Ctx) (i : Nat) (s : State) : Prop :=
  Run Ex base bytes len args sp s ∧ PreR2 s base bytes len args i (safeM (sv s.mem base len c 0)) ∧ ArgWr s ∧
    PreHdr s base args i

theorem preparePre_wst {c : Ctx} {i : Nat} (X : PrepP Ex base bytes len args sp c i s)
    (fits : 8 * preW args i ≤ bc len c) :
    WP isa (preparePre c) s (WSt Ex base bytes len args sp c [3, 4] 0) := by
  obtain ⟨R, P, -, H⟩ := X
  refine WP.mono (preparePre_ok R.1 P H fits) fun u ⟨C, one, R2, _, K⟩ =>
    ⟨_, C, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
  have hM := safeM_gt (sv s.mem base len c 0)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [one]; exact hM
  · rw [R2]; exact Nat.mod_lt _ (by omega_arith)

/-- `τP` with the registers `loadHead` sets for `loadTail` public too: they are functions of the
public arguments (`MidP`). -/
def τQ : VG.X86.Taint.T := { regs := .ofList [.edi, .esp, .ecx, .edx, .esi, .ebp], flags := false, argLen := 80 }

theorem τQ_wf {s : State} (A : ArgsOkP s) : VG.X86.Taint.Wf τQ s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

/-- A run after `loadHead`: a run, factor `i`'s cached value, argument 18 apart, and the registers
`loadHead` set, which the arguments determine. -/
def MidP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (c : Ctx) (i : Nat) (s : State) : Prop :=
  Run Ex base bytes len args sp s ∧ (∃ p, PreR2 s base bytes len args i p) ∧ ArgWr s ∧
    s.gpr .edx = BitVec.ofNat 32 (8 * preW args i) ∧ s.gpr .ecx = BitVec.ofNat 32 (8 * preW args i) ∧
    PtrAt s (byteAddr (args preArg)) .esi (preOff args i) ∧ PtrAt s base .ebp (lo len (.slot c 4))

theorem agreeQ {c : Ctx} {i : Nat} {s₁ s₂ : State} (X₁ : MidP Ex base bytes len args sp c i s₁)
    (X₂ : MidP Ex base bytes len args sp c i s₂) : VG.X86.Taint.Agree τQ s₁ s₂ := by
  obtain ⟨R₁, ⟨p₁, P₁⟩, W₁, d₁, c₁, e₁, b₁⟩ := X₁
  obtain ⟨R₂, ⟨p₂, P₂⟩, W₂, d₂, c₂, e₂, b₂⟩ := X₂
  have A₁ := argsOkP_of R₁.2.1 P₁ W₁
  have A₂ := argsOkP_of R₂.2.1 P₂ W₂
  have sp := R₁.2.2.trans R₂.2.2.symm
  obtain G := agreeP R₁.1 R₂.1 P₁ P₂ A₁ A₂ sp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τQ_wf A₁, τQ_wf A₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, G.argMem⟩
  simp only [τQ, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact BitVec.eq_of_toNat_eq (R₁.1.edi.trans R₂.1.edi.symm)
  · exact sp
  · exact c₁.trans c₂.symm
  · exact d₁.trans d₂.symm
  · exact BitVec.eq_of_toNat_eq (e₁.trans e₂.symm)
  · exact BitVec.eq_of_toNat_eq (b₁.trans b₂.symm)

theorem prepHead_mid {c : Ctx} {i : Nat} (X : PrepP Ex base bytes len args sp c i s)
    (fits : 8 * preW args i ≤ bc len c) :
    WP isa (.seq (prepBasePre c) (loadHead c)) s (MidP Ex base bytes len args sp c i) := by
  obtain ⟨R, P, W, H⟩ := X
  have h := R.1
  obtain fit := prepR_fit2 h c
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have bl := h.bytes_lt
  refine WP.seq (WP.mono (prepBasePre_ok h c) fun u₈ ⟨h₈, F₈, _, _, _, K₈⟩ => ?_)
  obtain P₈ := P.keepF h.room K₈ (by decide) F₈ fit.2
  obtain H₈ := H.keepF h F₈ fit.2 (baseR_hdr len c)
  refine WP.mono (loadHead_ok h₈ P₈ H₈ fits) fun u ⟨hu, edx, ecx, esi, ebp, _, O, K⟩ => ?_
  obtain K' := K₈.trans (K.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₈ u)
  exact ⟨⟨hu, R.2.1.keep K', (K'.1 _ (by decide)).trans R.2.2⟩,
    ⟨_, P₈.keepO K (by decide) (O.mono (Nat.zero_le _) (by omega_arith)) (by omega_arith)⟩, W.keep K', edx, ecx,
    esi, ebp⟩

/-- The taint checks of `preparePre`: up to `loadHead` from `τP`, and from there from `τQ`. -/
abbrev PCheck (p : Prog isa) : Prop := (VG.Taint.check sseTaint τP p (VG.Taint.hintOf sseTaint τP p)).isSome = true
abbrev QCheck (p : Prog isa) : Prop := (VG.Taint.check sseTaint τQ p (VG.Taint.hintOf sseTaint τQ p)).isSome = true

/-- The part of `preparePre c` after `loadHead`. -/
abbrev prepTail (c : Ctx) : Prog isa := .seq (loadTail c) (.ite .e (.block []) (.loop (doubleStep c) .ne))

theorem prepPChecks : PCheck (.seq (prepBasePre .half) (loadHead .half)) ∧
    PCheck (.seq (prepBasePre .wide) (loadHead .wide)) ∧ QCheck (prepTail .half) ∧ QCheck (prepTail .wide) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [PCheck, QCheck] <;> taint_decide

theorem preparePre_relCT {c : Ctx} {i : Nat} (fits : 8 * preW args i ≤ bc len c) :
    RelCT isa (Both (PrepP Ex base bytes len args sp c i)) (preparePre c)
      (Both (WSt Ex base bytes len args sp c [3, 4] 0)) := by
  have H := prepPChecks
  obtain ⟨hp, hq⟩ : PCheck (.seq (prepBasePre c) (loadHead c)) ∧ QCheck (prepTail c) := by
    cases c
    exacts [⟨H.2.1, H.2.2.2⟩, ⟨H.1, H.2.2.1⟩]
  have hx : RelCT isa (Both (PrepP Ex base bytes len args sp c i)) (.seq (prepBasePre c) (loadHead c))
      (Both (MidP Ex base bytes len args sp c i)) :=
    PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τP (fun _ _ h =>
      agreeP h.1.1.1 h.2.1.1 h.1.2.1 h.2.2.1 (argsOkP_of h.1.1.2.1 h.1.2.1 h.1.2.2.1)
        (argsOkP_of h.2.1.2.1 h.2.2.1 h.2.2.2.1) (h.1.1.2.2.trans h.2.1.2.2.symm)) hp)
      fun _ X => prepHead_mid X fits
  have hy : RelCT isa (Both (MidP Ex base bytes len args sp c i)) (prepTail c) fun _ _ => True :=
    VG.RelCT.taint (A := sseTaint) τQ (fun _ _ h => agreeQ h.1 h.2) hq
  exact PublicRt.relCT_both (VG.RelCT.assoc (VG.RelCT.seq hx hy)) fun _ X => preparePre_wst X fits

end

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

/-- A wide slot from 9 on into the half slot `d`, from a run: what it changes and the value. -/
theorem toHalf_val {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hd : d ≤ 8) (R : Run Ex base bytes len args sp s) :
    WP isa (copy (.slot .wide j) (.slot .half d) (one .half)) s fun u => Run Ex base bytes len args sp u ∧
      Outside base (lo len (.slot .half d)) (bc len .half) s.mem u.mem ∧
      sv u.mem base len .half d = val32 s.mem base (lo len (.slot .wide j)) (cwc len .half) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u ∧ Outside base 0 bytes s.mem u.mem := by
  have h := R.1
  have bl := h.bytes_lt
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  have W18 := h.wide_fit (j := 18) (by decide)
  have bhw := bc_le_wide len .half
  have estw : st len .wide = 2 * bc len .wide + 32 := rfl
  have ej : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have j9 := Nat.mul_le_mul_right (st len .wide) hj9
  have j17 := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 18 by omega_arith)
  rw [Nat.succ_mul] at j17
  have ed : lo len (.slot .half d) = numBase + d * st len .half := rfl
  have d8 := Nat.mul_le_mul_right (st len .half) hd
  have cb1 : cb len (one .half) = bc len .half := by simp [cb, one]
  have cw1 : cw len (one .half) = cwc len .half := by simp [cw, cwc, cb, one]
  refine WP.mono (copy_ok h (x := .slot .wide j) (d := .slot .half d) (one_ok .half) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inl (by omega_arith))) fun u ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨R.keep K (O.mono (Nat.zero_le _) (by omega_arith)), O, V, K, O.mono (Nat.zero_le _) (by omega_arith)⟩

/-- What the copies before a context's setup with `pre` need: a run, factor `i`'s cached value of the
factor in the wide slot `f` (its `k` low words), argument 18 apart from what is written, and the header
words naming the factor. -/
def HeadP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (f k i : Nat) (s : State) : Prop :=
  Run Ex base bytes len args sp s ∧
    PreR2 s base bytes len args i (safeM (val32 s.mem base (lo len (.slot .wide f)) k)) ∧ ArgWr s ∧
    PreHdr s base args i

theorem narrowHeadP_run {f e i : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (X : HeadP Ex base bytes len args sp f (cwc len .half) i s) :
    WP isa (Prog.chain (narrowHead f e) (.block [])) s (PrepP Ex base bytes len args sp .half i) := by
  obtain ⟨R, P, W, H⟩ := X
  have h := R.1
  have bl := h.bytes_lt
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  have bw := bc_eq_cwc len .half
  have nb : numBase = 3336 := rfl
  have f8 := h.slot_fit .half (j := 8) (by decide)
  have esth : st len .half = 2 * bc len .half + 32 := rfl
  have h8' : lo len (.slot .half 8) = numBase + 8 * st len .half := rfl
  refine WP.seq (WP.mono (toHalf_val hf9 (by omega_arith) (by decide) R) fun u₁ ⟨R₁, O₁, V₁, K₁, B₁⟩ =>
    WP.seq (WP.mono (toHalf_val he9 (by omega_arith) (by decide) R₁) fun u₂ ⟨R₂, O₂, V₂, K₂, B₂⟩ =>
      WP.block_nil ⟨R₂, ?_, W.keep (K₁.trans K₂), (H.keepO O₁ (by simp only [lo]; omega_arith)).keepO O₂
        (by simp only [lo]; omega_arith)⟩))
  have M : sv u₂.mem base len .half 0 = val32 s.mem base (lo len (.slot .wide f)) (cwc len .half) := by
    simp only [sv] at V₁ ⊢
    rw [h0, VG.Proof.Mont.Outside.val32 O₂ (d := numBase) (k := cwc len .half) (.inl (by omega_arith))
      (by omega_arith), ← h0, V₁]
  rw [M]
  exact (P.keepO K₁ (by decide) B₁ (by omega_arith)).keepO K₂ (by decide) B₂ (by omega_arith)

theorem wideHeadP_run {f e i : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (X : HeadP Ex base bytes len args sp f (cwc len .wide) i s) :
    WP isa (Prog.chain (wideHead f e) (.block [])) s (PrepP Ex base bytes len args sp .wide i) := by
  obtain ⟨R, P, W, H⟩ := X
  have h := R.1
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have l0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have l5 : lo len (.slot .wide 5) = numBase + 5 * st len .wide := rfl
  have l8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  have bw := bc_eq_cwc len .wide
  have nb : numBase = 3336 := rfl
  refine WP.seq (WP.mono (copyDown_ok h hf9 (by omega_arith) (d := 0) (by decide)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have R₁ := R.keep K₁ (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copyDown_ok R₁.1 (j := 15) (d := 5) (by decide) (by decide) (by decide))
    fun u₂ ⟨O₂, _, K₂⟩ => ?_)
  have R₂ := R₁.keep K₂ (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copyDown_ok R₂.1 he9 (by omega_arith) (d := 8) (by decide)) fun u₃ ⟨O₃, _, K₃⟩ => ?_)
  have R₃ := R₂.keep K₃ (O₃.mono (Nat.zero_le _) (by omega_arith))
  refine WP.block_nil ⟨R₃, ?_, ((W.keep K₁).keep K₂).keep K₃,
    ((H.keepO O₁ (by omega_arith)).keepO O₂ (by omega_arith)).keepO O₃ (by omega_arith)⟩
  have M : sv u₃.mem base len .wide 0 = val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) := by
    simp only [sv] at V₁ ⊢
    rw [O₃.val32 (d := lo len (.slot .wide 0)) (k := cwc len .wide) (.inl (by omega_arith)) (by omega_arith),
      O₂.val32 (d := lo len (.slot .wide 0)) (k := cwc len .wide) (.inl (by omega_arith)) (by omega_arith), V₁]
  rw [M]
  exact ((P.keepO K₁ (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith)) (by omega_arith)).keepO K₂ (by decide)
    (O₂.mono (Nat.zero_le _) (by omega_arith)) (by omega_arith)).keepO K₃ (by decide)
    (O₃.mono (Nat.zero_le _) (by omega_arith)) (by omega_arith)

end

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem narrowPowerP_eq (f e o : Nat) : narrowPower f e o true = Prog.chain (narrowHead f e)
    (.seq (preparePre .half) (.seq (reduceHalf 15) (.seq (windowPower .half) (saveResult .half o)))) := rfl

theorem widePowerP_eq (f e o : Nat) : widePower f e o true = Prog.chain (wideHead f e)
    (.seq (preparePre .wide) (.seq (windowPower .wide) (saveResult .wide o))) := rfl

theorem narrowPowerP_relCT {f e o i : Nat} (fits : 8 * preW args i ≤ bc len .half)
    (hc : PowChecks f e o) (hr : RHChecks 15) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (HeadP Ex base bytes len args sp f (cwc len .half) i)) (narrowPower f e o true)
      (Both (Run Ex base bytes len args sp)) := by
  rw [narrowPowerP_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.head
    fun _ X => narrowHeadP_run hf9 hf he9 he X) ?_)
  refine VG.RelCT.seq (preparePre_relCT fits) ?_
  refine VG.RelCT.seq (reduceHalf_relCT hr (by decide) (by decide) (ks := [3, 4]) (by decide) (by decide)
    (by decide)) ?_
  refine VG.RelCT.seq (windowPower_relCT (winChecks .half)) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.saveH fun _ W => saveResult_run (by omega_arith) (by omega_arith) W

theorem widePowerP_relCT {f e o i : Nat} (fits : 8 * preW args i ≤ bc len .wide)
    (hc : PowChecks f e o) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (HeadP Ex base bytes len args sp f (cwc len .wide) i)) (widePower f e o true)
      (Both (Run Ex base bytes len args sp)) := by
  rw [widePowerP_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.wide
    fun _ X => wideHeadP_run hf9 hf he9 he X) ?_)
  refine VG.RelCT.seq (preparePre_relCT fits) ?_
  refine VG.RelCT.seq (windowPower_relCT (winChecks .wide)) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.saveW fun _ W => saveResult_run (by omega_arith) (by omega_arith) W

theorem powerTestP_run {W : Nat} (R : Run Ex base bytes len args sp s) (hW : w32 s.mem base lenOff = W) :
    WP isa (.block powerTest) s fun u => Run Ex base bytes len args sp u ∧
      isa.eval .b u = some (decide (W < bc len .half + 1)) ∧ u.mem = s.mem ∧ Keeps [.eax, .edx] s u := by
  have h := R.1
  have hb := bc_le h.upper' .half
  have f0 := h.slot_fit .half (j := 0) (by decide)
  have lo0 : numBase ≤ lo len (.slot .half 0) := by simp [lo]
  simp only [powerTest, List.cons_append]
  refine wp_movS (readSrc_sc h.scratch (d := lenOff) (by simp only [lenOff, numBase] at *; omega_arith))
    fun u₁ a₁ _ => ?_
  have h₁ := h.regs a₁.keeps a₁.mem
  refine widthC_ok (k := 0) (c := .half) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_cmpC rfl fun u₄ f₄ c₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] s u₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (f₄.keeps _)
  have m₄ : u₄.mem = s.mem := by rw [f₄.mem, a₃.mem, m₂, a₁.mem]
  have eax : (u₃.gpr .eax).toNat = W := by rw [a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]; exact hW
  have edx : (u₃.gpr .edx).toNat = bc len .half + 1 := by
    rw [a₃.gpr, e₂, BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  rw [eax, edx] at c₄
  exact ⟨R.keep K₄ (by rw [m₄]; exact Outside.refl _ _ _ _), c₄, m₄, K₄⟩

/-- The cached value holds after a stage that changes no memory. -/
theorem PreR2.keepM {i p : Nat} (P : PreR2 s base bytes len args i p) {regs : List Reg} (K : Keeps regs s t)
    (spn : .esp ∉ regs) (m : t.mem = s.mem) : PreR2 t base bytes len args i p :=
  P.keep K spn (rs := []) (by rw [m]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- What a factor's power with `pre` needs of a run: its factor's length `W` at `lenOff`, factor `i`'s
cached value of the factor in the wide slot `f`, whose low half is the factor if `W` fits half the width,
in which case the value fits half the width too. -/
def PowP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (f i W : Nat) (s : State) : Prop :=
  HeadP Ex base bytes len args sp f (cwc len .wide) i s ∧ w32 s.mem base lenOff = W ∧
    (W ≤ bc len .half → val32 s.mem base (lo len (.slot .wide f)) (cwc len .half) =
      val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide) ∧ 8 * preW args i ≤ bc len .half)

/-- After the test of a factor's power: a run, what the test read, and the state it started from. -/
def TestP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (f i W : Nat) (u : State) : Prop :=
  ∃ v, PowP Ex base bytes len args sp f i W v ∧ Run Ex base bytes len args sp u ∧
    isa.eval .b u = some (decide (W < bc len .half + 1)) ∧ u.mem = v.mem ∧ Keeps [.eax, .edx] v u

theorem TestP.head {f i W : Nat} (T : TestP Ex base bytes len args sp f i W s) (k : Nat)
    (hk : val32 s.mem base (lo len (.slot .wide f)) k = val32 s.mem base (lo len (.slot .wide f)) (cwc len .wide)) :
    HeadP Ex base bytes len args sp f k i s := by
  obtain ⟨v, ⟨⟨_, P, A, H⟩, _⟩, R, _, m, K⟩ := T
  refine ⟨R, ?_, A.keep K, ⟨by rw [m]; exact H.len, by rw [m]; exact H.left⟩⟩
  rw [hk, m]
  exact P.keepM K (by decide) m

theorem powerP_relCT_W {f e o i W : Nat} (fitsW : 8 * preW args i ≤ bc len .wide)
    (fitsH : W ≤ bc len .half → 8 * preW args i ≤ bc len .half)
    (hc : PowChecks f e o) (hr : RHChecks 15) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (PowP Ex base bytes len args sp f i W)) (power f e o true)
      (Both (Run Ex base bytes len args sp)) := by
  unfold power
  refine VG.RelCT.seq (PublicRt.relCT_both (F := TestP Ex base bytes len args sp f i W)
    (VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.1.1.agree h.2.1.1) hc.test)
    fun x X => WP.mono (powerTestP_run X.1.1 X.2.1) fun u ⟨R, e, m, K⟩ => ⟨x, X, R, e, m, K⟩) ?_
  refine VG.RelCT.ite (fun _ _ h => by
    obtain ⟨_, _, _, e₁, _⟩ := h.1
    obtain ⟨_, _, _, e₂, _⟩ := h.2
    exact e₁.trans e₂.symm) ?_ ?_
  · by_cases hW : W ≤ bc len .half
    · have narrow : ∀ {u}, TestP Ex base bytes len args sp f i W u → HeadP Ex base bytes len args sp f (cwc len .half) i u :=
        fun {u} T => T.head _ (by
          obtain ⟨v, ⟨_, _, N⟩, _, _, m, _⟩ := T
          rw [m]; exact (N hW).1)
      exact (narrowPowerP_relCT (fitsH hW) hc hr hf9 hf he9 he ho16 ho).mono
        (fun _ _ h => ⟨narrow h.1.1, narrow h.1.2⟩) fun _ _ h => h
    · intro s₁ s₂ t₁ t₂ s₁' s₂' h
      obtain ⟨⟨⟨_, _, _, e₁, _⟩, _⟩, b⟩ := h
      have : decide (W < bc len .half + 1) = true := Option.some.inj (e₁.symm.trans b)
      exact absurd (of_decide_eq_true this) (by omega_arith)
  · exact (widePowerP_relCT fitsW hc hf9 hf he9 he ho16 ho).mono
      (fun _ _ h => ⟨h.1.1.head _ rfl, h.1.2.head _ rfl⟩) fun _ _ h => h

/-- A factor's power with `pre`, from runs whose factors' lengths agree. -/
theorem powerP_relCT {f e o i : Nat} (fitsW : 8 * preW args i ≤ bc len .wide)
    (hc : PowChecks f e o) (hr : RHChecks 15) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (fun s₁ s₂ => ∃ W, Both (PowP Ex base bytes len args sp f i W) s₁ s₂)
      (power f e o true) (Both (Run Ex base bytes len args sp)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨W, h⟩
  exact powerP_relCT_W fitsW (fun hW => ((h.1.2.2 hW).2)) hc hr hf9 hf he9 he ho16 ho _ _ _ _ _ _ h


/-! ## The coefficient with `pre` -/

theorem wideCoefficientP_eq : wideCoefficient true = .seq (copy (.slot .wide 10) (.slot .wide 0) (one .wide))
    (.seq (preparePre .wide) (Prog.chain coHead (.seq (CrtRt.mul .wide 5 5 4) (.seq (CrtRt.mul .wide 5 5 3)
      (.seq (subMod .wide 7 6 5) (.seq (CrtRt.mul .wide 8 8 4) (CrtRt.mul .wide 7 7 8))))))) := rfl

theorem coCopyP_wide (X : HeadP Ex base bytes len args sp 10 (cwc len .wide) 0 s) :
    WP isa (copy (.slot .wide 10) (.slot .wide 0) (one .wide)) s (PrepP Ex base bytes len args sp .wide 0) := by
  obtain ⟨R, P, W, H⟩ := X
  have h := R.1
  have bl := h.bytes_lt
  have f8 := h.slot_fit .wide (j := 8) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have bw := bc_eq_cwc len .wide
  have nb : numBase = 3336 := rfl
  have l0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have l8 : lo len (.slot .wide 8) = numBase + 8 * st len .wide := rfl
  refine WP.mono (copyDown_ok h (j := 10) (d := 0) (by decide) (by decide) (by decide)) fun u ⟨O, V, K⟩ =>
    ⟨R.keep K (O.mono (Nat.zero_le _) (by omega_arith)), ?_, W.keep K, H.keepO O (by omega_arith)⟩
  rw [V]
  exact P.keepO K (by decide) (O.mono (Nat.zero_le _) (by omega_arith)) (by omega_arith)

theorem wideCoefficientP_relCT (hc : CoChecks) (fits : 8 * preW args 0 ≤ bc len .wide) :
    RelCT isa (Both (HeadP Ex base bytes len args sp 10 (cwc len .wide) 0)) (wideCoefficient true)
      (Both (Run Ex base bytes len args sp)) := by
  rw [wideCoefficientP_eq]
  refine VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.copy fun _ X => coCopyP_wide X) ?_
  refine VG.RelCT.seq (preparePre_relCT fits) ?_
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

theorem coCopyP_half (X : HeadP Ex base bytes len args sp 10 (cwc len .half) 0 s) :
    WP isa (copy (.slot .wide 10) (.slot .half 0) (one .half)) s (PrepP Ex base bytes len args sp .half 0) := by
  obtain ⟨R, P, W, H⟩ := X
  have bl := R.1.bytes_lt
  refine WP.mono (toHalf_val (j := 10) (d := 0) (by decide) (by decide) (by decide) R) fun u ⟨R₁, O, V, K, B⟩ =>
    ⟨R₁, ?_, W.keep K, H.keepO O (by simp only [lo, numBase]; omega_arith)⟩
  rw [V]
  exact P.keepO K (by decide) B (by omega_arith)

theorem narrowCoefficientP_relCT (hc : CoChecks) (h14 : RHChecks 14) (h17 : RHChecks 17)
    (fits : 8 * preW args 0 ≤ bc len .half) :
    RelCT isa (Both (HeadP Ex base bytes len args sp 10 (cwc len .half) 0)) (narrowCoefficient true)
      (Both (Run Ex base bytes len args sp)) := by
  unfold narrowCoefficient
  refine VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.copyP fun _ X => coCopyP_half X) ?_
  refine VG.RelCT.seq (preparePre_relCT fits) ?_
  refine VG.RelCT.seq (reduceHalf_relCT h14 (by decide) (by decide) (ks := [3, 4]) (by decide) (by decide)
    (by decide)) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 8) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m854 (ks' := [8, 3, 4]) (by decide) (by decide) (by decide)) ?_
  refine VG.RelCT.seq (reduceHalf_relCT h17 (by decide) (by decide) (ks := [8, 3, 4]) (by decide) (by decide)
    (by decide)) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.copyMp
    fun _ W => toHalf_wst (by decide) (by decide) (by decide) (by decide) (by decide) W) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.subH fun _ W => subModH_wst W) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 6) (a := 7) (b := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc.m678 (ks' := []) (by decide) (by decide) (by decide)) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.saveH fun _ W => saveResult7_run W

/-- After the test of the coefficient: a run, what the test read, and the state it started from. -/
theorem coefficientP_relCT_W {W : Nat} (fitsW : 8 * preW args 0 ≤ bc len .wide)
    (fitsH : W ≤ bc len .half → 8 * preW args 0 ≤ bc len .half)
    (hc : CoChecks) (h14 : RHChecks 14) (h17 : RHChecks 17) :
    RelCT isa (Both (PowP Ex base bytes len args sp 10 0 W)) (coefficient true)
      (Both (Run Ex base bytes len args sp)) := by
  unfold coefficient
  refine VG.RelCT.seq (PublicRt.relCT_both (F := TestP Ex base bytes len args sp 10 0 W)
    (VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.1.1.agree h.2.1.1) hc.test)
    fun x X => WP.mono (powerTestP_run X.1.1 X.2.1) fun u ⟨R, e, m, K⟩ => ⟨x, X, R, e, m, K⟩) ?_
  refine VG.RelCT.ite (fun _ _ h => by
    obtain ⟨_, _, _, e₁, _⟩ := h.1
    obtain ⟨_, _, _, e₂, _⟩ := h.2
    exact e₁.trans e₂.symm) ?_ ?_
  · by_cases hW : W ≤ bc len .half
    · have narrow : ∀ {u}, TestP Ex base bytes len args sp 10 0 W u → HeadP Ex base bytes len args sp 10 (cwc len .half) 0 u :=
        fun {u} T => T.head _ (by
          obtain ⟨v, ⟨_, _, N⟩, _, _, m, _⟩ := T
          rw [m]; exact (N hW).1)
      exact (narrowCoefficientP_relCT hc h14 h17 (fitsH hW)).mono
        (fun _ _ h => ⟨narrow h.1.1, narrow h.1.2⟩) fun _ _ h => h
    · intro s₁ s₂ t₁ t₂ s₁' s₂' h
      obtain ⟨⟨⟨_, _, _, e₁, _⟩, _⟩, b⟩ := h
      have : decide (W < bc len .half + 1) = true := Option.some.inj (e₁.symm.trans b)
      exact absurd (of_decide_eq_true this) (by omega_arith)
  · exact (wideCoefficientP_relCT hc fitsW).mono
      (fun _ _ h => ⟨h.1.1.head _ rfl, h.1.2.head _ rfl⟩) fun _ _ h => h


end

/-! ## `sized true` -/

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}
open VG.Proof.Bignum.X86.Crt (componentValue)

/-- Both factors' cached values of the components `m₀` holds, and argument 18 apart. -/
structure PreAll (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (m₀ : Mem) (s : State) : Prop where
  p0 : PreR2 s base bytes len args 0 (safeM (componentValue m₀ args 6))
  p1 : PreR2 s base bytes len args 1 (safeM (componentValue m₀ args 8))
  o0 : PreOut s args len 0
  o1 : PreOut s args len 1
  w : ArgWr s

theorem PreAll.keepBody {m₀ : Mem} (h : RIn base bytes len args s) (A : PreAll base bytes len args m₀ s)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs)
    (F : Frame (rtBody base (byteAddr (args 0)) bytes len (s.gpr .esp)) s.mem t.mem) :
    PreAll base bytes len args m₀ t :=
  ⟨A.p0.keepBody h A.o0 K sp F, A.p1.keepBody h A.o1 K sp F, A.o0.keep K sp, A.o1.keep K sp, A.w.keep K sp⟩

theorem PreAll.get {m₀ : Mem} (A : PreAll base bytes len args m₀ s) {j : Nat} (hj : j < 2) :
    PreR2 s base bytes len args j (safeM (componentValue m₀ args (6 + 2 * j))) ∧ PreOut s args len j := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
  exacts [⟨A.p0, A.o0⟩, ⟨A.p1, A.o1⟩]

/-- The factors' steps with `pre` after `j` of them. -/
def StP (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (j : Nat) (t : State) : Prop :=
  Run (CrtExtra base bytes len args) base bytes len args sp t ∧ ∃ m₀ s₀, RIn base bytes len args s₀ ∧
    Comps base len args m₀ s₀.mem ∧ FacInv base bytes len args m₀ s₀ j t ∧ PreAll base bytes len args m₀ s₀

theorem powP_of {i j k W : Nat} {m₀ : Mem} {s₀ : State} (R : Run (CrtExtra base bytes len args) base bytes len args sp t)
    (h₀ : RIn base bytes len args s₀) (I : FacInv base bytes len args m₀ s₀ j t)
    (P : PreR2 s₀ base bytes len args i (safeM (componentValue m₀ args k))) (O : PreOut s₀ args len i)
    (Aw : ArgWr s₀) (H : PreHdr t base args i)
    (hf : val32 t.mem base (lo len (.slot .wide 10)) (cwc len .wide) = componentValue m₀ args k)
    (hW : w32 t.mem base lenOff = W) (hk : W = (args (k + 1)).toNat)
    (hfit : W ≤ bc len .half → 8 * preW args i ≤ bc len .half) :
    PowP (CrtExtra base bytes len args) base bytes len args sp 10 i W t := by
  refine ⟨⟨R, by rw [hf]; exact P.keepBody h₀ O I.keeps (by decide) I.frame, Aw.keep I.keeps, H⟩, hW,
    fun hle => ⟨?_, hfit hle⟩⟩
  have bhw := bc_le_wide len .half
  have cwh := bc_eq_cwc len .half
  have cww := bc_eq_cwc len .wide
  refine val32_low (b := cwc len .wide - cwc len .half)
    (by rw [show cwc len .half + (cwc len .wide - cwc len .half) = cwc len .wide by omega_arith]) ?_
  rw [hf]
  exact fits_half (i := k) (by rw [← hk]; exact hle)

theorem stepP_relCT {j : Nat} (hj : j < 2) (hc : SizedChecks) (hlo : 64 ≤ len)
    (hl : (args (7 + 2 * j)).toNat < len) :
    RelCT isa (Both (StP base bytes len args sp j)) (factorStep true)
      (Both fun u => StP base bytes len args sp (j + 1) u ∧ u.zf = some (decide (j + 1 = 2))) := by
  have lb := len_le_bc len
  have fitW : 8 * preW args j ≤ bc len .wide := fitG_of (i := j) (c := .wide) hlo (by omega_using [hl, lb])
  have e6 : (if j = 1 then 8 else 6) = 6 + 2 * j := by rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have e7 : (if j = 1 then 9 else 7) = 7 + 2 * j := by rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;> rfl
  have conv : ∀ {t}, StP base bytes len args sp j t →
      PowP (CrtExtra base bytes len args) base bytes len args sp 10 j (args (7 + 2 * j)).toNat t := by
    intro t ⟨R, m₀, s₀, h₀, c, I, A⟩
    have G := A.get hj
    have Q := preStep_of hj h₀ I A.p0 A.o0 A.p1 A.o1
    refine powP_of R h₀ I G.1 G.2 A.w Q.1.2 (k := 6 + 2 * j) ?_ ?_ (by rw [show 6 + 2 * j + 1 = 7 + 2 * j by omega_using []]) ?_
    · rw [I.f₁, e6]
    · rw [I.l₁, e7]
    · exact fun hle => fitG_of (i := j) (c := .half) hlo hle
  have tr : RelCT isa (Both (StP base bytes len args sp j)) (factorStep true) fun _ _ => True := by
    unfold factorStep
    refine VG.RelCT.seq ((powerP_relCT (Ex := CrtExtra base bytes len args) (base := base) (bytes := bytes)
      (len := len) (args := args) (sp := sp) fitW hc.p rhChecks.1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).mono (fun _ _ h => ⟨_, conv h.1, conv h.2⟩) fun _ _ h => h)
      (VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) hc.swaps)
  have step : ∀ {t}, StP base bytes len args sp j t → WP isa (factorStep true) t
      (fun u => StP base bytes len args sp (j + 1) u ∧ u.zf = some (decide (j + 1 = 2))) := by
    intro t ⟨R, m₀, s₀, h₀, c, I, A⟩
    have Q := preStep_of hj h₀ I A.p0 A.o0 A.p1 A.o1
    refine WP.mono (facStep_ok c I.inp.crt.dpLen I.inp.crt.dqLen hj I (pc := some j) Q.1 Q.2) fun u ⟨I', Z⟩ => ?_
    have K := Keeps.of_common I.keeps I'.keeps
    exact ⟨⟨⟨I'.inp, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, m₀, s₀, h₀, c, I', A⟩, Z⟩
  exact (tr.wp (F₁ := fun (u : State) => StP base bytes len args sp (j + 1) u ∧ u.zf = some (decide (j + 1 = 2)))
    (F₂ := fun (u : State) => StP base bytes len args sp (j + 1) u ∧ u.zf = some (decide (j + 1 = 2)))
    fun _ _ h => ⟨step h.1, step h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The factors' loop with `pre`, from runs with `n` factors left. -/
theorem loopP_relCT (hc : SizedChecks) (hlo : 64 ≤ len) (h7 : (args 7).toNat < len) (h9 : (args 9).toNat < len)
    (n : Nat) :
    RelCT isa (Both fun t => 1 ≤ n ∧ n ≤ 2 ∧ StP base bytes len args sp (2 - n) t) (.loop (factorStep true) .ne)
      (Both (StP base bytes len args sp 2)) := by
  refine VG.RelCT.loop (M := isa) (fun n => Both fun t => 1 ≤ n ∧ n ≤ 2 ∧ StP base bytes len args sp (2 - n) t)
    (fun n => ?_) n
  by_cases hn : 1 ≤ n ∧ n ≤ 2
  swap
  · exact VG.RelCT.of_false fun _ _ h => hn ⟨h.1.1, h.1.2.1⟩
  obtain hl : (args (7 + 2 * (2 - n))).toNat < len := by
    rcases (by omega_arith : n = 1 ∨ n = 2) with rfl | rfl
    exacts [h9, h7]
  refine ((stepP_relCT (j := 2 - n) (by omega_arith) hc hlo hl).mono (fun _ _ h => ⟨h.1.2.2, h.2.2.2⟩) ?_)
  rintro s₁ s₂ ⟨⟨S₁, Z₁⟩, ⟨S₂, Z₂⟩⟩
  refine ⟨?_, fun x => ?_, fun e => ?_⟩
  · show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [Z₁, Z₂]
  · have n1 : 2 - n + 1 = 2 := by
      by_contra hn
      have : s₁.zf.map (!·) = some false := x
      rw [Z₁, decide_eq_false hn] at this; cases this
    rw [n1] at S₁ S₂
    exact ⟨S₁, S₂⟩
  · have e' : 2 - n + 1 ≠ 2 := fun h => by
      have : s₁.zf.map (!·) = some true := e
      rw [Z₁, h] at this; cases this
    refine ⟨1, by omega_arith, ⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, ?_⟩⟩
    · rw [show 2 - 1 = 2 - n + 1 by omega_arith]; exact S₁
    · rw [show 2 - 1 = 2 - n + 1 by omega_arith]; exact S₂


theorem frontPCheck : ACheck (Prog.chain [importComponents, validatePre] (.block [])) := by
  dsimp only [ACheck]; taint_decide

theorem frontP_run (R : Run (CrtExtra base bytes len args) base bytes len args sp s)
    (A : PreAll base bytes len args s.mem s) :
    WP isa (Prog.chain [importComponents, validatePre] (.block [])) s fun u =>
      Run (CrtExtra base bytes len args) base bytes len args sp u ∧
        ∃ m₀, Comps base len args m₀ u.mem ∧ PreAll base bytes len args m₀ u :=
  frontPre_ok R.1 fun u hu F c _ K => WP.block_nil ⟨⟨hu, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, _, c,
    A.keepBody R.1 K (by decide) F⟩

theorem sizedP_relCT' (sp : BitVec 32) (hlo : 64 ≤ len) (h7 : (args 7).toNat < len) (h9 : (args 9).toNat < len) :
    RelCT isa (Both fun s => Run (CrtExtra base bytes len args) base bytes len args sp s ∧
      PreAll base bytes len args s.mem s) (CrtRt.sized true) fun _ _ => True := by
  have hc := sizedChecks
  have lb := len_le_bc len
  have fitW : 8 * preW args 0 ≤ bc len .wide := fitG_of (i := 0) (c := .wide) hlo (by show (args 7).toNat ≤ _; omega_using [h7, lb])
  have conv2 : ∀ {t}, StP base bytes len args sp 2 t →
      PowP (CrtExtra base bytes len args) base bytes len args sp 10 0 (args 7).toNat t := by
    intro t ⟨R, m₀, s₀, h₀, c, I, A⟩
    exact powP_of R h₀ I A.p0 A.o0 A.w ⟨I.l₁, by rw [I.left]⟩ (k := 6) I.f₁ I.l₁ rfl
      fun hle => fitG_of (i := 0) (c := .half) hlo hle
  show RelCT isa _ (Prog.chain [importComponents, validatePre] (.seq (.block factorsInit)
    (.seq (.loop (factorStep true) .ne) (.seq (coefficient true) (.seq recombine exportResult))))) _
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ frontPCheck
    fun _ X => frontP_run X.1 X.2) ?_)
  refine VG.RelCT.seq (taint_both (F := fun u => 1 ≤ 2 ∧ 2 ≤ 2 ∧ StP base bytes len args sp (2 - 2) u)
    (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.init
    fun t ⟨R, m₀, c, A⟩ => WP.mono (factorsInit_ok R.1 c) fun u I =>
      ⟨by decide, by decide, ⟨I.inp, R.2.1.keep I.keeps, (I.keeps.1 _ (by decide)).trans R.2.2⟩, m₀, t, R.1, c,
        show FacInv base bytes len args m₀ t (2 - 2) u from I, A⟩) ?_
  refine VG.RelCT.seq (loopP_relCT hc hlo h7 h9 2) ?_
  refine VG.RelCT.seq ((coefficientP_relCT_W (W := (args 7).toNat) fitW
    (fun hle => fitG_of (i := 0) (c := .half) hlo hle) hc.co rhChecks.2.1 rhChecks.2.2).mono
    (fun _ _ h => ⟨conv2 h.1, conv2 h.2⟩) fun _ _ h => h) ?_
  exact VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) hc.back

theorem sizedP_relCT (sp : BitVec 32) :
    RelCT isa (Both fun s => Run (CrtExtra base bytes len args) base bytes len args sp s ∧
      PreAll base bytes len args s.mem s) (CrtRt.sized true) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' H
  have h := H.1.1.1
  exact sizedP_relCT' sp h.lower h.crt.pShort h.crt.qShort s₁ s₂ t₁ t₂ s₁' s₂' H


/-- Factor `i`'s cached value holds in `sized`'s narrowed runs too. -/
theorem PreR2.narrow {i p : Nat} (P : PreR2 s base bytes len args i p) :
    PreR2 (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) base bytes len args i p := by
  obtain ⟨r, hr, hc⟩ := P.arg.stack.read
  obtain ⟨r', hr', hc'⟩ := P.read
  exact ⟨⟨⟨⟨r, List.mem_append_left _ hr, hc⟩, P.arg.stack.apart⟩, P.arg.value⟩, P.hi, P.pos, P.lt, P.lt7, P.pos7,
    ⟨r', List.mem_append_left _ hr', hc'⟩, P.fit, P.apart, P.val, P.top, P.apartSp⟩

theorem PreOut.narrow {i : Nat} (O : PreOut s args len i) {R W : List Region} :
    PreOut (s.withRegions R W) args len i :=
  ⟨O.arg, O.val⟩

/-- What the runs of `sized true` from the states themselves need: `SizedAt`'s, `p q = n`, and both
factors' cached values. -/
def SizedAtP (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  SizedAt base bytes len args sp s ∧
    componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2 ∧
    PreR2 s base bytes len args 0 (safeM (componentValue s.mem args 6)) ∧
    PreR2 s base bytes len args 1 (safeM (componentValue s.mem args 8)) ∧
    PreOut s args len 0 ∧ PreOut s args len 1

theorem sizedNarrowP_relCT (sp : BitVec 32) :
    RelCT isa (Both (SizedAtP base bytes len args sp)) (CrtRt.sized true) fun _ _ => True := by
  refine relCT_narrow (Pn := Both fun s => Run (CrtExtra base bytes len args) base bytes len args sp s ∧
      PreAll base bytes len args s.mem s) (fun s => s.rd ++ s.wr)
    (fun _ => narrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_) (sizedP_relCT sp)
  have cov : ∀ {s : State}, SizedAt base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.crt.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, SizedAtP base bytes len args sp s →
      ∃ F, WP isa (CrtRt.sized true) (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F :=
    fun S => ⟨_, sizedPre_ok (narrow_in S.1) S.1.2.2.1 S.2.1 S.2.2.1.narrow S.2.2.2.2.1.narrow S.2.2.2.1.narrow
      S.2.2.2.2.2.narrow⟩
  have pre : ∀ {s : State}, SizedAtP base bytes len args sp s →
      PreAll base bytes len args s.mem (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
    intro s S
    refine ⟨S.2.2.1.narrow, S.2.2.2.1.narrow, S.2.2.2.2.1.narrow, S.2.2.2.2.2.narrow, fun r hr => ?_⟩
    simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact S.2.2.2.2.1.arg
    · exact S.2.2.1.arg.stack.apart
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁.1)), cov S₁.1,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂.1)), cov S₂.1, wp S₁, wp S₂,
    ⟨narrow_run S₁.1, pre S₁⟩, ⟨narrow_run S₂.1, pre S₂⟩⟩

end

end VG.Proof.Bignum.X86.CrtRt
