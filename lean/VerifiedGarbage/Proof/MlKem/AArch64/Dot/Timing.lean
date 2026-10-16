module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Advance
public import VerifiedGarbage.Proof.Framework.AArch64.TaintSplit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG VG.AArch64 VG.Impl.MlKem.AArch64

abbrev symbols : List String := ["VG_MLKEM_GAMMA"]
abbrev publicRegs : List Reg := [.x28]
abbrev loopT : VG.AArch64.Taint.T := Taint.ofRegs [.x0,.x3,.x9,.x10,.x11,.x12,.x28]
abbrev fullT : VG.AArch64.Taint.T := Taint.ofRegs [.x0,.x1,.x2,.x3,.x9,.x10,.x11,.x12,.x28]

theorem term_check (fg : Nat × Nat) :
    (taintS symbols).checkBlock fullT (Dot.dotTerm fg) = some fullT := by
  unfold Dot.dotTerm ptrTo
  split <;> split <;> rfl

theorem term_entry (fg : Nat × Nat) :
    (taintS symbols).checkBlock loopT (Dot.dotTerm fg) = some fullT := by
  unfold Dot.dotTerm ptrTo
  split <;> split <;> rfl

theorem terms_check (terms : List (Nat × Nat)) :
    (taintS symbols).checkBlock fullT (terms.flatMap Dot.dotTerm) = some fullT := by
  induction terms with
  | nil => rfl
  | cons fg terms ih =>
    rw [List.flatMap_cons]
    rw [VG.AArch64.checkBlock_append (taintS symbols) fullT (Dot.dotTerm fg) (terms.flatMap Dot.dotTerm)]
    rw [term_check]
    exact ih

theorem terms_entry (terms : List (Nat × Nat)) :
    (taintS symbols).checkBlock loopT (terms.flatMap Dot.dotTerm) =
      some (if terms.isEmpty then loopT else fullT) := by
  cases terms with
  | nil => rfl
  | cons fg terms =>
    rw [List.flatMap_cons]
    rw [VG.AArch64.checkBlock_append (taintS symbols) loopT (Dot.dotTerm fg) (terms.flatMap Dot.dotTerm)]
    rw [term_entry]
    exact terms_check terms

def tail : List Instr := [.ldrq .v18 .x3 0] ++ finish ++ store ++ bump

theorem body_check (terms : List (Nat × Nat)) :
    (taintS symbols).checkBlock loopT (body terms) =
      some (if terms.isEmpty then loopT else fullT) := by
  have hb : body terms = clear ++ terms.flatMap Dot.dotTerm ++ tail := by
    simp only [body,compute,tail,List.append_assoc]
  rw [hb]
  rw [VG.AArch64.checkBlock_append (taintS symbols) loopT
    (clear ++ terms.flatMap Dot.dotTerm) tail]
  rw [VG.AArch64.checkBlock_append (taintS symbols) loopT clear (terms.flatMap Dot.dotTerm)]
  change ((taintS symbols).checkBlock loopT (terms.flatMap Dot.dotTerm)).bind
    (fun τ => (taintS symbols).checkBlock τ tail) = _
  rw [terms_entry]
  cases terms.isEmpty <;> rfl

def hint : VG.Taint.Hint VG.AArch64.Taint.T :=
  .seq loopT (.block []) (.loop loopT (.block []))

theorem check (out : Nat) (terms : List (Nat × Nat)) :
    ((taintS symbols).check (VG.AArch64.Taint.ofRegs publicRegs) (Dot.dot out terms) hint).isSome = true := by
  have hs : (taintS symbols).checkBlock (VG.AArch64.Taint.ofRegs publicRegs)
      (ptrTo .x0 .x28 out ++ vconsts ++
        [.adrSym .x3 "VG_MLKEM_GAMMA",.movz .x .x11 32 0,.movz .x .x12 0 0]) = some loopT := by
    unfold ptrTo
    split <;> rfl
  rw [dot_partition]
  change (((taintS symbols).checkBlock (VG.AArch64.Taint.ofRegs publicRegs) _).bind
    (fun τ => if (taintS symbols).le loopT τ then
      (if (taintS symbols).le loopT loopT then
        ((taintS symbols).checkBlock loopT (body terms)).bind (fun σ =>
          if (taintS symbols).le loopT σ && (taintS symbols).condPub σ (.nonzero .x .x11)
          then some σ else none) else none)
      else none)).isSome = true
  rw [hs]
  change (((taintS symbols).checkBlock loopT (body terms)).bind (fun σ =>
    if (taintS symbols).le loopT σ && (taintS symbols).condPub σ (.nonzero .x .x11)
    then some σ else none)).isSome = true
  rw [body_check]
  cases terms.isEmpty <;> rfl

theorem dot_ct (out : Nat) (terms : List (Nat × Nat)) :
    ConstantTime isa (fun _ => True)
      (VG.AArch64.Taint.AgreeS symbols (VG.AArch64.Taint.ofRegs publicRegs))
      (Dot.dot out terms) :=
  VG.Taint.constantTime (A:=taintS symbols) _ (fun _ _ _ _ h => h) (check out terms)

end VG.Proof.MlKem.AArch64.Dot
