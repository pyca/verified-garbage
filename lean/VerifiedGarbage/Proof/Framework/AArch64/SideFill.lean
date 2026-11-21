module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAllW
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
writes PSTATE.DIT and nothing is called indirectly (`Scrub.sideAll`), and
how deeply its frames nest, are then evaluated once, of the closed code, and
hold for every implementation of which they hold (`verifiedScrubbedOfFill`):
the function as emitted is `scrubOf W rb c`, a definition in `Impl/` that
states no registers.

No function a caller calls has an empty body, so a hole is never a call of
another function.

Code generic over an implementation in two ways (the Keccak permutation it
calls, and the absorb loop of that backend, which a backend may give whole)
has two kinds of holes, each replaced by code (`Code.fill2`): the depth of
the closed code is then evaluated with the depth of what fills each
(`Code.aarch64Depth2`), and `side_depth_of_fill2` gives `sideAll` and the
depth of the code for every implementation.

Code without frames has no stack to zero: its cleanup only clears registers
(`scrubOf 0`, `verifiedScrubbedOf0`), and what it states it writes of a buffer
still holds (`written_scrubOf0`).
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

/-- `c` with each call whose body is empty (a hole) replaced by the code `a`,
and each call whose body is two empty blocks (a hole of a second kind) by
`b`, in the bodies of the functions `c` calls too. -/
def Code.fill2 {M : ISA} (a b : Prog M) : Prog M → Prog M
  | .block is => .block is
  | .seq x y => .seq (fill2 a b x) (fill2 a b y)
  | .ite cd t e => .ite cd (fill2 a b t) (fill2 a b e)
  | .loop x cd => .loop (fill2 a b x) cd
  | .call m body => match body with
    | .block [] => a
    | .seq (.block []) (.block []) => b
    | _ => .call m (fill2 a b body)
  | .frame i x j => .frame i (fill2 a b x) j
  | .icall i m x y => .icall i m x y

/-- `Code.aarch64Depth` of code with holes, those of the first kind standing
for code of depth `da` and those of the second for code of depth `db`. -/
def Code.aarch64Depth2 (da db : Nat) : Prog AArch64.isa → Nat
  | .block _ => 0
  | .seq x y => max (aarch64Depth2 da db x) (aarch64Depth2 da db y)
  | .ite _ t e => max (aarch64Depth2 da db t) (aarch64Depth2 da db e)
  | .loop x _ => aarch64Depth2 da db x
  | .call _ body => match body with
    | .block [] => da
    | .seq (.block []) (.block []) => db
    | _ => aarch64Depth2 da db body
  | .frame i x _ => aarch64Depth2 da db x + i.frameUnits
  | .icall _ _ x y => max x.aarch64Depth y.aarch64Depth

theorem Code.aarch64Depth_fill2_le {a b : Prog AArch64.isa} {da db : Nat} (ha : a.aarch64Depth ≤ da)
    (hb : b.aarch64Depth ≤ db) (e : Prog AArch64.isa) :
    (Code.fill2 a b e).aarch64Depth ≤ Code.aarch64Depth2 da db e := by
  induction e with
  | block is => exact Nat.le_refl _
  | seq x y ihx ihy =>
    simp only [Code.fill2, Code.aarch64Depth, Code.aarch64Depth2]
    omega_using [ihx, ihy]
  | ite cd t e iht ihe =>
    simp only [Code.fill2, Code.aarch64Depth, Code.aarch64Depth2]
    omega_using [iht, ihe]
  | loop x cd ih => simpa only [Code.fill2, Code.aarch64Depth, Code.aarch64Depth2] using ih
  | call m body ih =>
    unfold Code.fill2 Code.aarch64Depth2
    split
    · exact ha
    · exact hb
    · simpa only [Code.aarch64Depth] using ih
  | frame i x j ih =>
    simp only [Code.fill2, Code.aarch64Depth, Code.aarch64Depth2]
    omega_using [ih]
  | icall i m x y => exact Nat.le_refl _

namespace AArch64.Scrub

open VG.Impl.Scrub.AArch64

/-- `sideAll` of code with its two kinds of holes filled, from the code's and
the fillings'. -/
theorem sideAll_fill2 {p : Instr → Bool} {a b e : Prog isa} (ha : sideAll p a = true)
    (hb : sideAll p b = true) (he : sideAll p e = true) : sideAll p (Code.fill2 a b e) = true := by
  induction e with
  | block is => exact he
  | seq x y ihx ihy =>
    simp only [Code.fill2, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨ihx he.1, ihy he.2⟩
  | ite cd t e iht ihe =>
    simp only [Code.fill2, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1, ihe he.2⟩
  | loop x cd ih => simp only [Code.fill2, sideAll] at he ⊢; exact ih he
  | call m body ih =>
    unfold Code.fill2
    split
    · exact ha
    · exact hb
    · simp only [sideAll] at he ⊢; exact ih he
  | frame i x j ih =>
    simp only [Code.fill2, sideAll, Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, ih he.1.2⟩, he.2⟩
  | icall i m x y => simp only [sideAll, Bool.false_eq_true] at he

/-- What `verifiedScrubbedOf` needs of code `c` that is the closed code `e`
with its two kinds of holes filled by `a` and `b`: from `sideAll` and the
depth of `e`, which the kernel evaluates once, and those of `a` and `b`. -/
theorem side_depth_of_fill2 {c e a b : Prog isa} {da db d : Nat} (hc : c = Code.fill2 a b e)
    (ha : sideAll (fun i => !i.writesDit) a = true) (hda : a.aarch64Depth ≤ da)
    (hb : sideAll (fun i => !i.writesDit) b = true) (hdb : b.aarch64Depth ≤ db)
    (he : sideAll (fun i => !i.writesDit) e = true) (hd : Code.aarch64Depth2 da db e ≤ d) :
    sideAll (fun i => !i.writesDit) c = true ∧ c.aarch64Depth ≤ d := by
  subst hc
  exact ⟨sideAll_fill2 ha hb he, Nat.le_trans (Code.aarch64Depth_fill2_le hda hdb e) hd⟩

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

/-- `c` with its cleanup over `W` bytes of stack and every register the
calling convention does not preserve cleared (`Clear.all`) meets `c`'s
contract in constant time and returns without secret residue, if no
instruction of it, or of what it calls, writes PSTATE.DIT and it calls
nothing indirectly: `verifiedScrubbedOf` for a function that states it clears
them all, so that code which calls it as emitted is the same for every
implementation. -/
theorem verifiedScrubbedClearAll {c : Prog isa} {k : Contract isa} {W rb : Nat} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hs : sideAll (fun i => !i.writesDit) c = true) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubAll W rb Clear.all c) k rb :=
  ⟨Verified.scrubAll clearAll_wf hv hW hrb hok,
    noResidue_scrubAll clearAll_wf (clearAll_keeps _) hv hW hok.sp hd
      (Code.all_of_allInstrs (allInstrs_of_sideAll hs))
      (fun _ _ _ n hn => by rw [inames_of_noIcall (noIcall_of_sideAll hs)] at hn; cases hn) hrb⟩

/-- `c`, which has no frames, with the registers it may write cleared
(`scrubOf 0`: no stack to zero) meets `c`'s contract in constant time and
returns without secret residue, if no instruction of it, or of what it
calls, writes PSTATE.DIT and it calls nothing indirectly: `verifiedScrubbedOf`
for code without frames. -/
theorem verifiedScrubbedOf0 {c : Prog isa} {k : Contract isa} {rb : Nat} (hv : Verified target c k)
    (hok : ScrubAllOk k 0 rb) (hd : c.aarch64Depth = 0)
    (hs : sideAll (fun i => !i.writesDit) c = true) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOf 0 rb c) k rb :=
  ⟨Verified.scrubAll0 (Clear.of_wf _) hv hrb hok,
    noResidue_scrubAll0 (Clear.of_wf _) (Clear.of_keeps _) hv hd
      (Code.all_of_allInstrs (allInstrs_of_sideAll hs)) hrb⟩

/-- What code without frames states it writes of a buffer
(`Registration.written`) holds of it with its registers cleared
(`scrubOf 0`), which writes no memory after it. -/
theorem written_scrubOf0 {sig : Sig} {w : List (String × Nat)} {c : Prog isa} {rb : Nat}
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) {P : State → Prop}
    (h : ∀ s t s', P s → Exec isa c s t s' → Sig.writtenWithin abi sig w s s') :
    ∀ s t s', P s → Exec isa (scrubOf 0 rb c) s t s' → Sig.writtenWithin abi sig w s s' := by
  intro s t s' hs he
  obtain ⟨t', u, hc, hm⟩ := scrubAll0_mem (Clear.of_wf _) hrb he
  exact writtenWithin_of_mem hm (h s t' u hs hc)

end AArch64.Scrub

end VG
