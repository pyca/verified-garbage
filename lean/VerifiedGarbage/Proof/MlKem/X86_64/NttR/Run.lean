module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeAccY

/-!
# ML-KEM on x86-64: the NTT on registers, the run of its terms

The regions of the two passes (`rsA`: `S` and the input; `rsB d`: `S` and the
output at `d`), the terms where pass A starts (`initA`: `q` in `ymm15`, the
input's coefficients in the low words of their `u32`s, zero in the high
ones), and the check, by the kernel, that the terms of the output after pass
B are the reduced words of `NTT` (`outOk`).

The kernel checks the run in parts, each the state after it as a literal
(`materialize_value`) in a module of its own: pass A (`stA`, `RunA.lean`),
and for each output register the halves of pass B (`stRdi0`, `stRdi1`, …,
`RunRdi0.lean`, …), each starting from the literal of the part before. Each
part costs the kernel a fraction of the whole run's memory, and the parts of
the two registers build in parallel.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

def rsA : List Rg := [(.rsi, oS, 256, true), (.rdi, 0, 512, false)]

def rsB (d : Reg) : List Rg := [(.rsi, oS, 256, true), (d, 0, 512, true)]

/-- `n` chunks of sixteen words not followed. -/
def junks (n : Nat) : List Y := List.replicate n (List.replicate 16 .junk)

/-- The input, sixteen words at a time: coefficient `p` in the low word of
its `u32`, zero in the high one. -/
def inTerms : List Y :=
  (List.range 32).map fun c => (List.range 16).map fun e =>
    if (16 * c + e) % 2 = 0 then .lv 0 ((16 * c + e) / 2) else .c 0

def initA : St :=
  ⟨(List.range 16).map (fun r => if r = 15 then List.replicate 16 (.c qN) else List.replicate 16 .junk),
   [junks 16, inTerms]⟩

/-- The registers and `S` after pass A, the output not yet written, and
`ymm3` forgotten (pass A of `u32`s packs through it, that of `u16`s does not). -/
def toB (σ : St) : St := ⟨(σ.set .xmm3 (List.replicate 16 .junk)).regs, [σ.mem.getD 0 [], junks 32]⟩

/-- The output's words are the reduced coefficients, in the low words of their `u32`s. -/
def outOk (σ : St) : Bool :=
  (List.range 512).all fun i =>
    E.beq (Y.get ((σ.mem.getD 1 []).getD (i / 16) []) (i % 16)) (if i % 2 = 0 then .out (i / 2) else .c 0)

/-- The run of pass A and of pass B `pb` storing to `d`, and whether it
leaves `NTT` in the output. -/
def check (pb : List Instr) (d : Reg) : Bool :=
  match initA.run fwdRules rsA passA with
  | some σ =>
    match (toB σ).run fwdRules (rsB d) pb with
    | some σ' => outOk σ'
    | none => false
  | none => false

/-! ## To an accumulator -/

/-- The regions of pass B storing to the accumulator at `d` (256 words). -/
def rsBA (d : Reg) : List Rg := [(.rsi, oS, 256, true), (d, 0, 256, true)]

/-- The registers and `S` after pass A, the accumulator not yet written, and
`ymm3` forgotten (pass A of `u32`s packs through it, that of `u16`s does not). -/
def toBA (σ : St) : St := ⟨(σ.set .xmm3 (List.replicate 16 .junk)).regs, [σ.mem.getD 0 [], junks 16]⟩

/-- The accumulator's words are the reduced coefficients, coefficient
`accIdx w` in word `w`. -/
def outAccOk (σ : St) : Bool :=
  (List.range 256).all fun w => E.beq (Y.get ((σ.mem.getD 1 []).getD (w / 16) []) (w % 16)) (.out (accIdx w))

/-- The run of pass A and of pass B `pb` storing to the accumulator at `d`,
and whether it leaves `NTT` there. -/
def checkAcc (pb : List Instr) (d : Reg) : Bool :=
  match initA.run fwdRules rsA passA with
  | some σ =>
    match (toBA σ).run fwdRules (rsBA d) pb with
    | some σ' => outAccOk σ'
    | none => false
  | none => false

/-! ## The run in parts -/

theorem St.run_append (R : Rules) (rs : List Rg) (σ : St) (a b : List Instr) :
    σ.run R rs (a ++ b) = (σ.run R rs a).bind fun σ' => σ'.run R rs b := by
  induction a generalizing σ with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, St.run]
    cases σ.step R rs i with
    | none => rfl
    | some σ' => exact ih σ'

/-- The state after pass A. -/
def stA : Option St := initA.run fwdRules rsA passA

/-- The state after half 0 of pass B, from that after pass A. -/
def stB0 (d : Reg) (p₀ : List Instr) : Option St := stA.bind fun σ => (toB σ).run fwdRules (rsB d) p₀

def stRdi0 : Option St := stB0 .rdi passBRdi0
def stRdi1 : Option St := stRdi0.bind fun σ => σ.run fwdRules (rsB .rdi) passBRdi1
def stR100 : Option St := stB0 .r10 passBR100
def stR101 : Option St := stR100.bind fun σ => σ.run fwdRules (rsB .r10) passBR101

/-- The state after half 0 of pass B to the accumulator at `d`. -/
def stAccB0 (d : Reg) (p₀ : List Instr) : Option St := stA.bind fun σ => (toBA σ).run fwdRules (rsBA d) p₀

def stAccR100 : Option St := stAccB0 .r10 passBAccR100
def stAccR101 : Option St := stAccR100.bind fun σ => σ.run fwdRules (rsBA .r10) passBAccR101

/-- `check` from the state after the halves of pass B. -/
theorem check_of {p₀ p₁ : List Instr} {d : Reg}
    (ho : ((stB0 d p₀).bind fun σ => σ.run fwdRules (rsB d) p₁).any outOk = true) :
    check (p₀ ++ p₁) d = true := by
  unfold check
  rw [stB0, stA] at ho
  split
  · rename_i σA hA
    rw [hA, Option.bind_some] at ho
    split
    · rename_i σ' h'
      rw [St.run_append] at h'
      rw [h', Option.any_some] at ho
      exact ho
    · rename_i h'
      rw [St.run_append] at h'
      rw [h', Option.any_none] at ho
      exact ho
  · rename_i hA
    rw [hA, Option.bind_none, Option.bind_none, Option.any_none] at ho
    exact ho

/-- `checkAcc` from the state after the halves of pass B. -/
theorem checkAcc_of {p₀ p₁ : List Instr} {d : Reg}
    (ho : ((stAccB0 d p₀).bind fun σ => σ.run fwdRules (rsBA d) p₁).any outAccOk = true) :
    checkAcc (p₀ ++ p₁) d = true := by
  unfold checkAcc
  rw [stAccB0, stA] at ho
  split
  · rename_i σA hA
    rw [hA, Option.bind_some] at ho
    split
    · rename_i σ' h'
      rw [St.run_append] at h'
      rw [h', Option.any_some] at ho
      exact ho
    · rename_i h'
      rw [St.run_append] at h'
      rw [h', Option.any_none] at ho
      exact ho
  · rename_i hA
    rw [hA, Option.bind_none, Option.bind_none, Option.any_none] at ho
    exact ho

end VG.Proof.MlKem.X86_64.NttR
