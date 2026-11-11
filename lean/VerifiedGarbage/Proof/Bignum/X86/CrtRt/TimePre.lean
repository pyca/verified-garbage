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
(`τP`, `agreeP`), from what each run keeps of `pre` (`PreC`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both)

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
    addr_eq (by simp only [preArg]; omega)
  rw [sa] at h18
  intro a ha hr
  simp only [Region.Contains] at ha
  by_cases h : (a - (s.gpr .esp).setWidth 64).toNat < 76
  · exact h76 a (by simp only [Region.Contains]; omega) hr
  · refine h18 a ?_ hr
    simp only [Region.Contains]
    rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
    have := (a - (s.gpr .esp).setWidth 64).isLt
    omega

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
    · rw [show (k - 4) / 4 = preArg by simp only [preArg]; omega]
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

/-- What a run of `preparePre c i` needs: a run, factor `i`'s cached value of the modulus in slot 0, and
argument 18 apart from what it writes. -/
def PrepP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (c : Ctx) (i : Nat) (s : State) : Prop :=
  Run Ex base bytes len args sp s ∧ PreR2 s base bytes len args i (safeM (sv s.mem base len c 0)) ∧ ArgWr s

theorem preparePre_wst {c : Ctx} {i : Nat} (X : PrepP Ex base bytes len args sp c i s)
    (fits : 8 * preW args i ≤ bc len c) :
    WP isa (preparePre c i) s (WSt Ex base bytes len args sp c [3, 4] 0) := by
  obtain ⟨R, P, -⟩ := X
  refine WP.mono (preparePre_ok R.1 P fits) fun u ⟨C, one, R2, _, K⟩ =>
    ⟨_, C, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
  have hM := safeM_gt (sv s.mem base len c 0)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · rw [one]; exact hM
  · rw [R2]; exact Nat.mod_lt _ (by omega_arith)

/-- The taint check of `preparePre`. -/
abbrev PCheck (p : Prog isa) : Prop := (VG.Taint.check sseTaint τP p (VG.Taint.hintOf sseTaint τP p)).isSome = true

theorem prepPChecks : PCheck (preparePre .half 0) ∧ PCheck (preparePre .half 1) ∧ PCheck (preparePre .wide 0) ∧
    PCheck (preparePre .wide 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [PCheck] <;> taint_decide

theorem preparePre_relCT {c : Ctx} {i : Nat} (hi : i ≤ 1) (fits : 8 * preW args i ≤ bc len c) :
    RelCT isa (Both (PrepP Ex base bytes len args sp c i)) (preparePre c i)
      (Both (WSt Ex base bytes len args sp c [3, 4] 0)) := by
  have hc : PCheck (preparePre c i) := by
    have H := prepPChecks
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases c
    exacts [H.2.2.1, H.1, H.2.2.2, H.2.1]
  exact PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τP (fun _ _ h =>
      agreeP h.1.1.1 h.2.1.1 h.1.2.1 h.2.2.1 (argsOkP_of h.1.1.2.1 h.1.2.1 h.1.2.2)
        (argsOkP_of h.2.1.2.1 h.2.2.1 h.2.2.2) (h.1.1.2.2.trans h.2.1.2.2.symm)) hc)
    fun _ X => preparePre_wst X fits

end

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

/-- The cached value holds after a stage that changes only the working space. -/
theorem PreR2.keepO {i p : Nat} (P : PreR2 s base bytes len args i p) {regs : List Reg} (K : Keeps regs s t)
    (spn : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) (fit : bytes ≤ 2 ^ 64) :
    PreR2 t base bytes len args i p := by
  have F := VG.Proof.Bignum.outside_frame O (by omega)
  simp only [BitVec.add_zero] at F
  exact P.keep K spn F (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).1)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).2)

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
factor in the wide slot `f` (its `k` low words), and argument 18 apart from what is written. -/
def HeadP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (f k i : Nat) (s : State) : Prop :=
  Run Ex base bytes len args sp s ∧
    PreR2 s base bytes len args i (safeM (val32 s.mem base (lo len (.slot .wide f)) k)) ∧ ArgWr s

theorem narrowHeadP_run {f e i : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (X : HeadP Ex base bytes len args sp f (cwc len .half) i s) :
    WP isa (Prog.chain (narrowHead f e) (.block [])) s (PrepP Ex base bytes len args sp .half i) := by
  obtain ⟨R, P, W⟩ := X
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
      WP.block_nil ⟨R₂, ?_, W.keep (K₁.trans K₂)⟩))
  have M : sv u₂.mem base len .half 0 = val32 s.mem base (lo len (.slot .wide f)) (cwc len .half) := by
    simp only [sv] at V₁ ⊢
    rw [h0, VG.Proof.Mont.Outside.val32 O₂ (d := numBase) (k := cwc len .half) (.inl (by omega_arith))
      (by omega_arith), ← h0, V₁]
  rw [M]
  exact (P.keepO K₁ (by decide) B₁ (by omega_arith)).keepO K₂ (by decide) B₂ (by omega_arith)

theorem wideHeadP_run {f e i : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (X : HeadP Ex base bytes len args sp f (cwc len .wide) i s) :
    WP isa (Prog.chain (wideHead f e) (.block [])) s (PrepP Ex base bytes len args sp .wide i) := by
  obtain ⟨R, P, W⟩ := X
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
  refine WP.block_nil ⟨R₃, ?_, ((W.keep K₁).keep K₂).keep K₃⟩
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

theorem narrowPowerP_eq (f e o i : Nat) : narrowPower f e o (some i) = Prog.chain (narrowHead f e)
    (.seq (preparePre .half i) (.seq (reduceHalf 15) (.seq (windowPower .half) (saveResult .half o)))) := rfl

theorem widePowerP_eq (f e o i : Nat) : widePower f e o (some i) = Prog.chain (wideHead f e)
    (.seq (preparePre .wide i) (.seq (windowPower .wide) (saveResult .wide o))) := rfl

theorem narrowPowerP_relCT {f e o i : Nat} (hi : i ≤ 1) (fits : 8 * preW args i ≤ bc len .half)
    (hc : PowChecks f e o) (hr : RHChecks 15) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (HeadP Ex base bytes len args sp f (cwc len .half) i)) (narrowPower f e o (some i))
      (Both (Run Ex base bytes len args sp)) := by
  rw [narrowPowerP_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.head
    fun _ X => narrowHeadP_run hf9 hf he9 he X) ?_)
  refine VG.RelCT.seq (preparePre_relCT hi fits) ?_
  refine VG.RelCT.seq (reduceHalf_relCT hr (by decide) (by decide) (ks := [3, 4]) (by decide) (by decide)
    (by decide)) ?_
  refine VG.RelCT.seq (windowPower_relCT (winChecks .half)) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.saveH fun _ W => saveResult_run (by omega_arith) (by omega_arith) W

theorem widePowerP_relCT {f e o i : Nat} (hi : i ≤ 1) (fits : 8 * preW args i ≤ bc len .wide)
    (hc : PowChecks f e o) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15) (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (HeadP Ex base bytes len args sp f (cwc len .wide) i)) (widePower f e o (some i))
      (Both (Run Ex base bytes len args sp)) := by
  rw [widePowerP_eq]
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ X₁ X₂ => X₁.1.agree X₂.1) _ hc.wide
    fun _ X => wideHeadP_run hf9 hf he9 he X) ?_)
  refine VG.RelCT.seq (preparePre_relCT hi fits) ?_
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
  obtain ⟨v, ⟨⟨_, P, A⟩, _⟩, R, _, m, K⟩ := T
  refine ⟨R, ?_, A.keep K⟩
  rw [hk, m]
  exact P.keepM K (by decide) m

theorem powerP_relCT_W {f e o i W : Nat} (hi : i ≤ 1) (fitsW : 8 * preW args i ≤ bc len .wide)
    (fitsH : W ≤ bc len .half → 8 * preW args i ≤ bc len .half)
    (hc : PowChecks f e o) (hr : RHChecks 15) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (Both (PowP Ex base bytes len args sp f i W)) (power f e o (some i))
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
      exact (narrowPowerP_relCT hi (fitsH hW) hc hr hf9 hf he9 he ho16 ho).mono
        (fun _ _ h => ⟨narrow h.1.1, narrow h.1.2⟩) fun _ _ h => h
    · intro s₁ s₂ t₁ t₂ s₁' s₂' h
      obtain ⟨⟨⟨_, _, _, e₁, _⟩, _⟩, b⟩ := h
      have : decide (W < bc len .half + 1) = true := Option.some.inj (e₁.symm.trans b)
      exact absurd (of_decide_eq_true this) (by omega_arith)
  · exact (widePowerP_relCT hi fitsW hc hf9 hf he9 he ho16 ho).mono
      (fun _ _ h => ⟨h.1.1.head _ rfl, h.1.2.head _ rfl⟩) fun _ _ h => h

/-- A factor's power with `pre`, from runs whose factors' lengths agree. -/
theorem powerP_relCT {f e o i : Nat} (hi : i ≤ 1) (fitsW : 8 * preW args i ≤ bc len .wide)
    (hc : PowChecks f e o) (hr : RHChecks 15) (hf9 : 9 ≤ f) (hf : f ≤ 15) (he9 : 9 ≤ e) (he : e ≤ 15)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) :
    RelCT isa (fun s₁ s₂ => ∃ W, Both (PowP Ex base bytes len args sp f i W) s₁ s₂)
      (power f e o (some i)) (Both (Run Ex base bytes len args sp)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨W, h⟩
  exact powerP_relCT_W hi fitsW (fun hW => ((h.1.2.2 hW).2)) hc hr hf9 hf he9 he ho16 ho _ _ _ _ _ _ h

end

end VG.Proof.Bignum.X86.CrtRt
