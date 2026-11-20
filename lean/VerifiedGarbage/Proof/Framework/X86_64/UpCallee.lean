module

public import VerifiedGarbage.Proof.Framework.X86_64.CalleeSide

/-!
# What the cleanup at the level `sse` of a caller needs of an implementation it calls (x86-64)

`upCallee d n` is what `X86_64.Scrub.verifiedScrubbedAllUp`
(`Proof/Framework/X86_64/ScrubUpFill.lean`) needs of the code `d` of an
implementation that a function generic over it calls, which the
implementation proves where it is defined. It is in a module of its own so
that the structures of variants that state it import only this.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64

/-- At most `n` bytes of stack, instructions below the level `evex`,
vectors' upper halves that agree at its end if they did at its start, and no
indirect call. Only the kernel evaluates it. -/
noncomputable def upCallee (d : Prog isa) (n : Nat) : Bool :=
  decide (d.x86_64Depth ≤ n) && d.allInstrs (fun i => decide (i.vecLevel ≤ 1)) && UpperLock.up d true &&
    (UpperLock.inames d).isEmpty

/-- `List.foldl UpperLock.stepI`, each step forced: what the kernel
evaluates in place of `UpperLock.up`'s fold, which it would otherwise build as
a chain as long as the block before evaluating it. -/
def stepsK : List Instr → Bool → Bool
  | [], a => a
  | i :: is, a => match UpperLock.stepI a i with
    | true => stepsK is true
    | false => stepsK is false

theorem stepsK_eq : ∀ (is : List Instr) (a : Bool), stepsK is a = is.foldl UpperLock.stepI a
  | [], _ => rfl
  | i :: is, a => by
    simp only [stepsK, List.foldl_cons]
    cases h : UpperLock.stepI a i <;> exact stepsK_eq is _

/-- `UpperLock.up`, with `stepsK` for its blocks. -/
def upK : Prog isa → Bool → Bool
  | .block is, a => stepsK is a
  | .seq x y, a => upK y (upK x a)
  | .ite _ t e, a => upK t a && upK e a
  | .loop b _, a => upK b a
  | .call _ b, a => upK b a
  | .frame _ b _, a => upK b a
  | .icall _ _ b n, a => upK b a && upK n a

theorem upK_eq : ∀ (c : Prog isa) (a : Bool), upK c a = UpperLock.up c a
  | .block is, a => stepsK_eq is a
  | .seq x y, a => by simp only [upK, UpperLock.up, upK_eq x, upK_eq y]
  | .ite _ t e, a => by simp only [upK, UpperLock.up, upK_eq t, upK_eq e]
  | .loop b _, a => upK_eq b a
  | .call _ b, a => upK_eq b a
  | .frame _ b _, a => upK_eq b a
  | .icall _ _ b n, a => by simp only [upK, UpperLock.up, upK_eq b, upK_eq n]

/-- `upCallee`, as the kernel evaluates it (`upK`). -/
theorem upCallee_eq (d : Prog isa) (n : Nat) :
    upCallee d n = (decide (d.x86_64Depth ≤ n) && d.allInstrs (fun i => decide (i.vecLevel ≤ 1)) && upK d true &&
      (UpperLock.inames d).isEmpty) := by
  rw [upK_eq]; rfl

end VG.X86_64.Scrub
