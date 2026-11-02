module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ECDSA verification on x86-64: checks of every instruction, on the code without its displacements

The verifiers' ABI facts (`InlineOk`, and no instruction writing `rsp` or
loading MXCSR) do not read displacements and immediates, so they hold of the
code exactly when they hold of it with them erased (`Code.erase`). The
kernel evaluates them on the erased code's literal of shared blocks
(`materialize_shared`, which the constant-time check already has), where the
field arithmetic is the same few blocks again and again, each evaluated once.
-/

@[expose] public section

namespace VG.X86_64

theorem erase_band_congr {a b c d : Bool} (h₁ : a = b) (h₂ : c = d) : (a && c) = (b && d) := by
  rw [h₁, h₂]

theorem Code.allInstrs_erase {p : Instr → Bool} (hp : ∀ i, p i.erase = p i) (c : Prog isa) :
    (Code.erase c).allInstrs p = c.allInstrs p := by
  induction c with
  | icall => rfl
  | block is =>
    show List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) (KList.map Instr.erase is) =
      List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) is
    rw [KList.map_eq]
    induction is with
    | nil => rfl
    | cons i is ih => exact erase_band_congr (hp i) ih
  | seq a b iha ihb => exact erase_band_congr iha ihb
  | ite _ t e iht ihe => exact erase_band_congr iht ihe
  | loop b _ ih => exact ih
  | call _ b ih => exact ih
  | frame i b j ih => exact congrArg (fun x => p i && x && p j) ih

theorem Code.noCalls_erase (c : Prog isa) : (Code.erase c).noCalls = c.noCalls := by
  induction c with
  | icall => rfl
  | block => rfl
  | seq a b iha ihb => exact erase_band_congr iha ihb
  | ite _ t e iht ihe => exact erase_band_congr iht ihe
  | loop b _ ih => exact ih
  | call => rfl
  | frame => rfl

theorem Instr.clobbers_erase (i : Instr) (r : Reg) : Taint.clobbers i.erase r = Taint.clobbers i r := by
  cases i <;> rfl

theorem Instr.rspFree_erase (i : Instr) : i.erase.rspFree = i.rspFree := by
  cases i <;> try rfl
  all_goals rename_i s; cases s <;> rfl

theorem Instr.loadsMxcsr_erase (i : Instr) : loadsMxcsr i.erase = loadsMxcsr i := by
  cases i <;> rfl

theorem Code.InlineOk_erase (c : Prog isa) : (Code.erase c).InlineOk = c.InlineOk := by
  induction c with
  | icall => rfl
  | block is =>
    show KList.all (KList.map Instr.erase is) _ = KList.all is _
    rw [KList.map_eq, KList.all_eq, KList.all_eq, List.all_map]
    exact congrArg is.all (funext fun i => congrArg (!·) (Instr.clobbers_erase i .rsp))
  | seq a b iha ihb => exact erase_band_congr iha ihb
  | ite _ t e iht ihe => exact erase_band_congr iht ihe
  | loop b _ ih => exact ih
  | call _ b =>
    exact erase_band_congr (Code.noCalls_erase b) (Code.allInstrs_erase Instr.rspFree_erase b)
  | frame => rfl

/-- A check of every instruction of `c` that does not read displacements,
from that of `Code.erase c`. -/
theorem Code.allInstrs_of_erase {p : Instr → Bool} (hp : ∀ i, p i.erase = p i) {c : Prog isa}
    (h : (Code.erase c).allInstrs p = true) : c.allInstrs p = true := by
  rwa [Code.allInstrs_erase hp] at h

/-- `rsp_mxcsr`'s check of `c`, from that of `Code.erase c`. -/
theorem Code.rspMxcsr_of_erase {c : Prog isa}
    (h : (Code.erase c).allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true) :
    c.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i) = true := by
  rwa [Code.allInstrs_erase fun i => by rw [Instr.clobbers_erase, Instr.loadsMxcsr_erase]] at h

/-- `InlineOk c`, from that of `Code.erase c`. -/
theorem Code.inlineOk_of_erase {c : Prog isa} (h : (Code.erase c).InlineOk = true) : c.InlineOk = true := by
  rwa [Code.InlineOk_erase] at h

end VG.X86_64
