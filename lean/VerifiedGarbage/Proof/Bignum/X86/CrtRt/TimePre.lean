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

end VG.Proof.Bignum.X86.CrtRt
