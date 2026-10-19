module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Sound
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# ML-KEM on x86-64: the NTT on registers, pass A of `u16`s

Pass A of `u16`s (`passA16`) loads each block of sixteen coefficients with
one load, where pass A of `u32`s packs two; from the input's terms as words
(`initA16`) it leaves the registers and `S` that pass A of `u32`s leaves, but
for `ymm3`, which pass B does not read and `toBA` forgets (`stA16_toBA`). So
every check of pass B to an accumulator holds after either pass A.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

/-- The regions of pass A of `u16`s: `S` and the input's 256 words. -/
def rsA16 : List Rg := [(.rsi, oS, 256, true), (.rdi, 0, 256, false)]

/-- The input, sixteen words at a time: word `p` is coefficient `p`. -/
def inTerms16 : List Y := (List.range 16).map fun c => (List.range 16).map fun e => .lv 0 (16 * c + e)

def initA16 : St :=
  ⟨(List.range 16).map (fun r => if r = 15 then List.replicate 16 (.c qN) else List.replicate 16 .junk),
   [junks 16, inTerms16]⟩

/-- The state after pass A of `u16`s. -/
def stA16 : Option St := initA16.run fwdRules rsA16 passA16

materialize_value stA16

/-- Lists equal element by element, by `f`. -/
def lbeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && lbeq f as bs
  | _, _ => false

theorem lbeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, lbeq f l l' = true → l = l'
  | [], [] => fun _ => rfl
  | a :: as, b :: bs => fun h => by
    simp only [lbeq, Bool.and_eq_true] at h
    rw [hf a b h.1, lbeq_eq hf h.2]
  | [], _ :: _ => fun h => by cases h
  | _ :: _, [] => fun h => by cases h

/-- Equal states, which the kernel evaluates directly. -/
def St.beq (a b : St) : Bool := lbeq (lbeq E.beq) a.regs b.regs && lbeq (lbeq (lbeq E.beq)) a.mem b.mem

theorem St.beq_eq {a b : St} (h : St.beq a b = true) : a = b := by
  simp only [St.beq, Bool.and_eq_true] at h
  have e1 := lbeq_eq (fun _ _ => lbeq_eq fun _ _ => E.beq_eq) h.1
  have e2 := lbeq_eq (fun _ _ => lbeq_eq fun _ _ => lbeq_eq fun _ _ => E.beq_eq) h.2
  cases a; cases b; simp only at e1 e2; rw [e1, e2]

/-- Pass B starts from the same state after either pass A. -/
theorem stA16_toBA : ∃ σ₁₆ σ, stA16 = some σ₁₆ ∧ stA = some σ ∧ toBA σ₁₆ = toBA σ := by
  rw [stA16.lit_eq, stA.lit_eq]
  exact ⟨_, _, rfl, rfl, St.beq_eq (by lit_decide)⟩

end VG.Proof.MlKem.X86_64.NttR
