module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Step
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the NTT on registers, the run of its terms

The regions of the two passes (`rsA`: `S` and the input; `rsB d`: `S` and the
output at `d`), the terms where pass A starts (`initA`: `q` in `ymm15`, the
input's coefficients in the low words of their `u32`s, zero in the high
ones), and the check, by the kernel, that the terms of the output after pass
B are the reduced words of `NTT` (`outOk`).
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

/-- The registers and `S` after pass A, the output not yet written. -/
def toB (σ : St) : St := ⟨σ.regs, [σ.mem.getD 0 [], junks 32]⟩

/-- The output's words are the reduced coefficients, in the low words of their `u32`s. -/
def outOk (σ : St) : Bool :=
  (List.range 512).all fun i =>
    E.beq (Y.get ((σ.mem.getD 1 []).getD (i / 16) []) (i % 16)) (if i % 2 = 0 then .out (i / 2) else .c 0)

/-- The run of pass A and of pass B `pb` storing to `d`, and whether it
leaves `NTT` in the output. -/
def check (pb : List Instr) (d : Reg) : Bool :=
  match initA.run rsA passA with
  | some σ =>
    match (toB σ).run (rsB d) pb with
    | some σ' => outOk σ'
    | none => false
  | none => false

theorem check_rdi : check passBsRdi .rdi = true := by lit_decide
theorem check_r10 : check passBsR10 .r10 = true := by lit_decide

end VG.Proof.MlKem.X86_64.NttR
