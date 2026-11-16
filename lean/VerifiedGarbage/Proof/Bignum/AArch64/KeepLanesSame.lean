module

public import VerifiedGarbage.Proof.Bignum.AArch64.KeepLanes

/-!
# `KeepLanes.keeps`, for long code that seldom moves a register

`keepsK` rebuilds the list of facts after every instruction, so that the next
filter reads a list: twelve cells for each of the 16,000 instructions of an
RSA function, though all but a few hundred of them drop no fact. `keepsS`
asks first whether the instruction changes the facts at all (`unchanged`),
and where it does not goes on with the list it has. That list is then the
same term for the next instruction, and the kernel, which remembers the
value of a term by the term, finds again what it evaluated for the same
instruction from the same facts. `keepsS` is `keeps` (`keepsS_eq`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

namespace KeepLanes

open VG VG.AArch64

/-- Whether `step A i` is `A`: `i` is neither an `ins` nor a `umov` that `step` follows, and
keeps every location of `A`. -/
def unchanged (A : Facts) (i : Instr) : Bool :=
  match insView i with
  | some _ => false
  | none =>
    match umovView i with
    | some _ => false
    | none => A.all fun p => keepP i p.2

theorem step_of_unchanged {A : Facts} {i : Instr} (h : unchanged A i = true) : step A i = A := by
  unfold unchanged at h
  unfold step
  split at h
  · cases h
  · rename_i h₁
    split at h
    · cases h
    · rename_i h₂
      simp only [h₁, h₂]
      exact List.filter_eq_self.mpr (by simpa only [List.all_eq_true] using h)

/-- `foldK`, which rebuilds the facts only after an instruction that changes them. -/
def foldS (A : Facts) : List Instr → Facts
  | [] => A
  | i :: is => cond (unchanged A i) (foldS A is) (forceL (step A i) fun B => foldS B is)

theorem foldS_eq (A : Facts) (is : List Instr) : foldS A is = is.foldl step A := by
  induction is generalizing A with
  | nil => rfl
  | cons i is ih =>
    rw [foldS, List.foldl_cons]
    cases h : unchanged A i
    · rw [Bool.cond_false, forceL_eq, ih]
    · rw [Bool.cond_true, ih, step_of_unchanged h]

/-- `checkK`, with `foldS`. A block starts from its facts as an evaluated list: the kernel then
finds again a block it has analysed from the same facts, however it came by them. -/
def checkS : Facts → Prog isa → Option Facts
  | A, .block is => forceL A fun A => some (foldS A is)
  | A, .seq a b => (checkS A a).bind (checkS · b)
  | A, .ite _ t e => (checkS A t).bind fun B => (checkS A e).map fun C => B.filter (· ∈ C)
  | A, .loop body _ => loopInv (fun I => checkS I body) (A.length + 1) A
  | _, _ => none

theorem checkS_eq (A : Facts) (c : Prog isa) : checkS A c = check A c := by
  induction c generalizing A <;> simp only [checkS, check, foldS_eq, forceL_eq, *]

/-- `keeps`, evaluated with `checkS`. -/
def keepsS (T : List Reg) (c : Prog isa) : Bool :=
  match checkS (T.map fun r => (r, .g r)) c with
  | some B => T.all fun r => B.contains (r, .g r)
  | none => false

theorem keepsS_eq (T : List Reg) (c : Prog isa) : keepsS T c = keeps T c := by
  unfold keepsS keeps
  rw [checkS_eq]
  rfl

end KeepLanes

open VG VG.AArch64 KeepLanes
open VG.Proof.MlKem.AArch64 (Keep)

/-- `WP.keepLanes`, with the registers' check evaluated as `KeepLanes.keepsS`. -/
theorem WP.keepLanesS {c : Prog isa} {s : State} {Q : State → Prop} (rs T : List Reg) (h : WP isa c s Q)
    (hc : writesOnly (rs ++ T) c = true) (hT : keepsS T c = true) (hn : c.noCalls = true)
    (hv : c.allInstrs keepsV = true) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' :=
  WP.keepLanes rs T h hc (by rw [keepsK_eq, ← keepsS_eq]; exact hT) hn hv

end VG.Proof.Bignum.AArch64
