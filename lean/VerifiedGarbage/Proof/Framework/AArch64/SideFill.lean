module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The cleanup of code that is the same for every implementation it calls (AArch64)

A function generic over one implementation of a function it calls (the
permutation of a Keccak backend) is the same code for each, but for the calls
of it. Built with that function's body empty (`.block []`, a *hole*), it is
closed; the code for an implementation is that code with its holes filled
(`Code.fillCalls name body`, which, unlike `Code.fillHoles`, fills the holes
in the bodies of the functions the code calls too), an equation the kernel
checks with the implementation a variable (`kernel_rfl`).

What the cleanup of the function needs of its code, that no instruction
writes PSTATE.DIT and nothing is called indirectly (`ScrubAll.sideAll`), and
how deeply its frames nest, are then evaluated once, of the closed code, and
hold for every implementation of which they hold (`verifiedScrubbedOfFill`):
the function as emitted is `scrubOf W rb c`, a definition in `Impl/` that
states no registers.

No function a caller calls has an empty body, so a hole is never a call of
another function.
-/

@[expose] public section

namespace VG

/-- `c` with each call whose body is empty (a hole) made a call of `n`, with
body `b`, in the bodies of the functions `c` calls too. -/
def Code.fillCalls {M : ISA} (n : String) (b : Prog M) : Prog M → Prog M
  | .block is => .block is
  | .seq x y => .seq (fillCalls n b x) (fillCalls n b y)
  | .ite cd t e => .ite cd (fillCalls n b t) (fillCalls n b e)
  | .loop x cd => .loop (fillCalls n b x) cd
  | .call m body => match body with
    | .block [] => .call n b
    | _ => .call m (fillCalls n b body)
  | .frame i x j => .frame i (fillCalls n b x) j
  | .icall i m x y => .icall i m x y

theorem Code.aarch64Depth_fillCalls_le (n : String) (b e : Prog AArch64.isa) :
    (Code.fillCalls n b e).aarch64Depth ≤ e.aarch64Depth + b.aarch64Depth := by
  induction e with
  | block is => exact Nat.zero_le _
  | seq x y ihx ihy =>
    simp only [Code.fillCalls, Code.aarch64Depth]
    omega_using [ihx, ihy]
  | ite cd t e iht ihe =>
    simp only [Code.fillCalls, Code.aarch64Depth]
    omega_using [iht, ihe]
  | loop x cd ih => simpa only [Code.fillCalls, Code.aarch64Depth] using ih
  | call m body ih =>
    cases body with
    | block is =>
      cases is with
      | nil => exact Nat.le_add_left _ _
      | cons i is => exact Nat.le_add_right _ _
    | _ => simpa only [Code.fillCalls, Code.aarch64Depth] using ih
  | frame i x j ih =>
    simp only [Code.fillCalls, Code.aarch64Depth]
    omega_using [ih]
  | icall i m x y => simp only [Code.fillCalls]; exact Nat.le_add_right _ _

namespace AArch64.ScrubAll

open VG.Impl.Residue.AArch64

/-- `sideAll` of code with its holes filled, from the code's and the
filling's. -/
theorem sideAll_fillCalls {p : Instr → Bool} {n : String} {b e : Prog isa} (hb : sideAll p b = true)
    (he : sideAll p e = true) : sideAll p (Code.fillCalls n b e) = true := by
  induction e with
  | block is => exact he
  | seq x y ihx ihy =>
    simp only [Code.fillCalls, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨ihx he.1, ihy he.2⟩
  | ite cd t e iht ihe =>
    simp only [Code.fillCalls, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1, ihe he.2⟩
  | loop x cd ih => simp only [Code.fillCalls, sideAll] at he ⊢; exact ih he
  | call m body ih =>
    cases body with
    | block is =>
      cases is with
      | nil => exact hb
      | cons i is => exact he
    | _ => simp only [Code.fillCalls, sideAll] at he ⊢; exact ih he
  | frame i x j ih =>
    simp only [Code.fillCalls, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, ih he.1.2⟩, he.2⟩
  | icall i m x y => simp only [sideAll, Bool.false_eq_true] at he

/-- No instruction of an implementation that proves `calleeSide` writes
PSTATE.DIT, and it calls nothing indirectly. -/
theorem sideAll_noDit_of_calleeSide {c : Prog isa} {cl : Clear} (h : calleeSide c cl = true) :
    sideAll (fun i => !i.writesDit) c = true :=
  sideAll_mono (fun _ hi => by
    simp only [sideI, Bool.and_eq_true] at hi
    exact hi.1.1) h

/-- `c`, which is the closed code `e` with its holes filled by the function
`b` it calls, with its cleanup over `W` bytes of stack and the registers it
may write cleared (`scrubOf`), meets `c`'s contract in constant time and
returns without secret residue: from `sideAll` and the depth of `e`, which the
kernel evaluates once, and `sideAll` of `b`, which has no frames. -/
theorem verifiedScrubbedOfFill {c e b : Prog isa} {n : String} {k : Contract isa} {W rb : Nat}
    (hv : Verified target c k) (hok : ScrubAllOk k W rb) (hc : c = Code.fillCalls n b e)
    (hb : sideAll (fun i => !i.writesDit) b = true) (hbd : b.aarch64Depth = 0)
    (he : sideAll (fun i => !i.writesDit) e = true) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hd : 16 * e.aarch64Depth ≤ W) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOf W rb c) k rb := by
  refine verifiedScrubbedOf hv hok hW ?_ (hc ▸ sideAll_fillCalls hb he) hrb
  have := Code.aarch64Depth_fillCalls_le n b e
  rw [hc]
  omega_using [hbd, hd, this]

end AArch64.ScrubAll

end VG
