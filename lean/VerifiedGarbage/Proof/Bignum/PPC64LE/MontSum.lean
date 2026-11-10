module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Framework.TaintRel
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
meta import VerifiedGarbage.Proof.Framework.TaintRel
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-!
# Montgomery multiplication on PPC64LE: the kernel's summary for constant time

The callers' analyses use the kernel's relational summary (`kernelSum`,
`Proof/Framework/TaintRel.lean`) in place of analysing its code at every
call: from states that agree on at least `kernelPre`, the call of the kernel
leaks the same trace and leaves `kernelPost` public, and also what was public
of the registers it never writes (`kernelKeep`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum.PPC64LE

/-- The registers both of `a` and `b` say are public. -/
def regUnion (a b : T) : T := ⟨a.bits ||| b.bits⟩

theorem mem_regUnion {a b : T} {r : Reg} : r ∈ regUnion a b ↔ r ∈ a ∨ r ∈ b := by
  rw [RegSet.mem_iff, RegSet.mem_iff, RegSet.mem_iff]
  show (a.bits ||| b.bits).testBit _ = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true]

/-- What the kernel needs public: `2 w` and the bases. -/
def kernelPre : T := ofRegs [.r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- What the kernel's analysis from `kernelPre` leaves public. -/
def kernelPost : T := ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r15, .r16, .r17]

/-- The registers no instruction of the kernel writes, and the call does not. -/
def kernelKeep : T := ofRegs [.r2, .r5, .r10, .r21, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The call of the kernel, its code and its summary. -/
def kernelCall : Prog isa := .call kernelName kernel

def kernelSum : VG.Taint.RSum isa taint.T where
  code := kernelCall
  pre := kernelPre
  post τ := regUnion (τ.inter kernelKeep) kernelPost

theorem kernel_keep_all : (instrs kernelCall).all (fun i => match dstOf i with
    | some d => !kernelKeep.mem d
    | none => true) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem kernel_keep : ∀ i ∈ instrs kernelCall, ∀ r ∈ kernelKeep, dstOf i ≠ some r := fun i hi r hr e => by
  have := List.all_eq_true.mp kernel_keep_all i hi
  rw [e] at this
  have h2 : kernelKeep.mem r = false := by simpa using this
  exact Bool.false_ne_true (h2.symm.trans hr)

theorem kernel_check : ∃ hc, (taint.check kernelPre kernelCall hc).map (kernelPost.subset ·) = some true :=
  ⟨_, by taint_decide⟩

theorem kernelSum_ok : kernelSum.Ok taint := by
  intro τ hle s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
  obtain ⟨hc, hk⟩ := kernel_check
  cases hQ : taint.check kernelPre kernelCall hc with
  | none => rw [hQ] at hk; cases hk
  | some Q =>
  rw [hQ] at hk
  have hPQ : kernelPost.subset Q = true := Option.some.inj hk
  obtain ⟨ht, hQa⟩ := VG.Taint.check_sound hQ (taint.le_sound hle ha) e₁ e₂
  refine ⟨ht, hQa.1, fun r hr => ?_⟩
  rcases mem_regUnion.mp hr with hr | hr
  · replace hr := (RegSet.mem_inter (R := Reg) (a := (τ : RegSet Reg))).mp hr
    have hd := fun i hi => kernel_keep i hi r hr.2
    have hl : r ∉ linkRegs := by
      have := hr.2
      simp only [kernelKeep, mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [Exec.gpr hd e₁ (.inr hl), Exec.gpr hd e₂ (.inr hl)]
    exact ha.2 r hr.1
  · exact hQa.2 r (RegSet.mem_of_subset hPQ hr)


/-- The summaries the callers' analyses use. -/
def montSums : List (VG.Taint.RSum isa taint.T) := [kernelSum]

theorem montSums_ok : VG.Taint.RAllOk taint montSums := ⟨kernelSum_ok, trivial⟩

end VG.Proof.Bignum.PPC64LE
