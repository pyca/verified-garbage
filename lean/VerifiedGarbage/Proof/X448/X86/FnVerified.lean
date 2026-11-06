module

public import VerifiedGarbage.Proof.X448.Field16Contract
public import VerifiedGarbage.Proof.X448.X86.FnContract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.X448.X86.FnLit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.X86.FnContract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.X448.X86.FnLit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# X448 on x86 (32-bit): the field functions' `Verified`

Correctness under `binX86` and `a24X86` (`FnContract.lean`), constant time
by taint tracking (every branch is on the row pointer and every address is
`ws`, an offset, the row pointer or `esp` plus a constant: only the
arguments, which are public, and `esp` need be), satisfiability, and the
shared contracts of `Proof/X448/Field16Contract.lean`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem slot_of_fits {o : BitVec 32} (h : Proof.X448.Field16.Fits o) : Slot o.toNat := h

/-- A difference, as `Spec` states it. -/
theorem toFe_sub_inv {a b c : Nat} (h : toFe c = toFe a - toFe b) : (c + b) % Spec.X448.P = a % Spec.X448.P := by
  have e := congrArg Fin.val h
  simp only [toFe_val, Fin.sub_def] at e
  have hx : a % Spec.X448.P < Spec.X448.P := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne Spec.X448.P))
  have hy : b % Spec.X448.P < Spec.X448.P := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne Spec.X448.P))
  rw [Nat.add_mod, e]
  generalize a % Spec.X448.P = x at *
  generalize b % Spec.X448.P = y at *
  rcases Nat.lt_or_ge (Spec.X448.P - y + x) Spec.X448.P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, show Spec.X448.P - y + x + y = x + Spec.X448.P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · rw [show (Spec.X448.P - y + x) % Spec.X448.P = Spec.X448.P - y + x - Spec.X448.P by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)],
      show Spec.X448.P - y + x - Spec.X448.P + y = x by omega, Nat.mod_eq_of_lt hx]

/-- What a field function changes preserves the calling convention. -/
theorem FnOut.abi {c : Prog isa} (hc : NoSp c) (h0 : stackUse c = 0) {s s' : State} {tr : List Leak}
    (ex : Exec isa c s tr s') (hwr : ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r)
    {base : Addr} {o : Nat} (h : FnOut base o s s') : abiPreserved s s' := by
  refine ⟨fun r hr => h.keeps.1 r (by revert r hr; decide), ?_⟩
  have hf := VG.X86.Exec.frameSp ex hc (by omega)
  rw [h0] at hf
  refine Mem.readW_congr fun k hk => hf _ fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact fun hc' => hwr r hr _ (by simp only [Region.Contains]; rw [Offset.add_sub_cancel_left]; simp only [BitVec.toNat_ofNat]; omega) hc'
  · rw [List.mem_singleton.mp hr]; simp only [Region.Contains]; omega

theorem fnPre_ret {len : Nat} {s : State} (h : fnPre len s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
  intro r hr; rw [h.2.2.1, List.mem_singleton] at hr; subst hr; exact h.2.2.2.2.1

theorem mulFn_correct (s : State) (hs : (binX86 fun o a b => o % Spec.X448.P = a * b % Spec.X448.P).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧
      (binX86 fun o a b => o % Spec.X448.P = a * b % Spec.X448.P).post s s' := by
  obtain ⟨hp, ho, ha, hb, la, lb⟩ := hs
  have he := FnEntry.of_pre (n := 4) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := mulFn_ok he (b := (arg s 3).toNat) (by simp) (slot_of_fits hb) la lb
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), hk.bounded, ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_mul rfl).symm)

theorem addFn_correct (s : State) (hs : (binX86 fun o a b => o % Spec.X448.P = (a + b) % Spec.X448.P).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧
      (binX86 fun o a b => o % Spec.X448.P = (a + b) % Spec.X448.P).post s s' := by
  obtain ⟨hp, ho, ha, hb, la, lb⟩ := hs
  have he := FnEntry.of_pre (n := 4) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := addFn_ok he (b := (arg s 3).toNat) (by simp) (slot_of_fits hb) la lb
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), hk.bounded, ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_add rfl).symm)

theorem subFn_correct (s : State) (hs : (binX86 fun o a b => (o + b) % Spec.X448.P = a % Spec.X448.P).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧
      (binX86 fun o a b => (o + b) % Spec.X448.P = a % Spec.X448.P).post s s' := by
  obtain ⟨hp, ho, ha, hb, la, lb⟩ := hs
  have he := FnEntry.of_pre (n := 4) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := subFn_ok he (b := (arg s 3).toNat) (by simp) (slot_of_fits hb) la lb
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), hk.bounded, ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq, valAt_eq]
  exact toFe_sub_inv hv

theorem mulA24Fn_correct (s : State) (hs : a24X86.pre s) :
    ∃ t s', Exec isa mulA24Fn s t s' ∧ abiPreserved s s' ∧ a24X86.post s s' := by
  obtain ⟨hp, ho, ha, la⟩ := hs
  have he := FnEntry.of_pre (n := 3) (by decide) hp ho ha
  obtain ⟨t, s', ex, hk, hv⟩ := mulA24Fn_ok he la
  refine ⟨t, s', ex, hk.abi (NoSp.of_all (by lit_decide)) (by lit_decide) ex (fnPre_ret hp), hk.bounded, ?_, hk.mem.keeps⟩
  rw [valAt_eq, valAt_eq]
  exact toFe_eq_iff.mp (hv.trans (toFe_a24 rfl).symm)

/-! ## Constant time -/

/-- The analysis starts with `esp` and the `len` bytes of arguments public. -/
def fnτ (len : Nat) : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 4 + len }

theorem fn_wf {len : Nat} {s : State} (h : fnPre len s) : VG.X86.Taint.Wf (fnτ len) s := by
  obtain ⟨hsp, _, hwr, hdis, hret, _⟩ := h
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [fnτ]; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  rw [hwr]
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact VG.X86.Taint.frame_disjoint (n := len) hsp hret hdis.symm

/-- Two states of the precondition whose `esp` and arguments agree agree on
what `fnτ` says is public. -/
theorem fn_agree {len : Nat} {s₁ s₂ : State} (h₁ : fnPre len s₁) (h₂ : fnPre len s₂)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : ∀ i, 4 * i < len → arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree (fnτ len) s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, fn_wf h₁, fn_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fnτ, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [fnτ] at hk
    rw [show VG.X86.Taint.depth (fnτ len).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 4 + len) (by have := h₁.1; omega) h4 hk,
      VG.X86.Taint.argByte_eq (n := 4 + len) (by have := h₂.1; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega))

theorem mulFn_check : ∃ h, (taint.check (fnτ 16) mulFn h).isSome = true := ⟨_, by taint_decide⟩

theorem mulFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 16) s₁ s₂) :
    ConstantTime isa pre pub mulFn :=
  let ⟨_, hc⟩ := mulFn_check
  VG.Taint.constantTime (A := taint) (fnτ 16) h hc

theorem addFn_check : ∃ h, (taint.check (fnτ 16) addFn h).isSome = true := ⟨_, by taint_decide⟩

theorem addFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 16) s₁ s₂) :
    ConstantTime isa pre pub addFn :=
  let ⟨_, hc⟩ := addFn_check
  VG.Taint.constantTime (A := taint) (fnτ 16) h hc

theorem subFn_check : ∃ h, (taint.check (fnτ 16) subFn h).isSome = true := ⟨_, by taint_decide⟩

theorem subFn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 16) s₁ s₂) :
    ConstantTime isa pre pub subFn :=
  let ⟨_, hc⟩ := subFn_check
  VG.Taint.constantTime (A := taint) (fnτ 16) h hc

theorem mulA24Fn_check : ∃ h, (taint.check (fnτ 12) mulA24Fn h).isSome = true := ⟨_, by taint_decide⟩

theorem mulA24Fn_ct {pre : State → Prop} {pub : State → State → Prop}
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree (fnτ 12) s₁ s₂) :
    ConstantTime isa pre pub mulA24Fn :=
  let ⟨_, hc⟩ := mulA24Fn_check
  VG.Taint.constantTime (A := taint) (fnτ 12) h hc

theorem bin_agree {r : Nat → Nat → Nat → Prop} (s₁ s₂ : State) (h₁ : (binX86 r).pre s₁)
    (h₂ : (binX86 r).pre s₂) (hp : (binX86 r).pub s₁ s₂) : VG.X86.Taint.Agree (fnτ 16) s₁ s₂ := by
  obtain ⟨e, a0, a1, a2, a3⟩ := hp
  refine fn_agree h₁.1 h₂.1 e fun i hi => ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3]

theorem a24_agree (s₁ s₂ : State) (h₁ : a24X86.pre s₁) (h₂ : a24X86.pre s₂) (hp : a24X86.pub s₁ s₂) :
    VG.X86.Taint.Agree (fnτ 12) s₁ s₂ := by
  obtain ⟨e, a0, a1, a2⟩ := hp
  refine fn_agree h₁.1 h₂.1 e fun i hi => ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  exacts [a0, a1, a2]



end VG.Proof.X448.X86
