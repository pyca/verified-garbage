import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Public values through SSE registers, in the x86-64 taint analysis

A function that needs every general-purpose register saves the callee-saved
ones in SSE registers (`movq xmm, r64`) and restores them (`movq r64, xmm`):
the analysis keeps a public register public through that round trip, and
forgets it if anything else writes the vector registers in between.
-/

namespace VG.Test.X86_64TaintXmm

open VG VG.X86_64

/-- Saves `rbx` in `xmm8`, overwrites it with a secret, restores it and
loads through it. -/
def roundTrip : Prog isa :=
  .block [.xop (.movq .xmm8 .rbx), .mov .rbx (.mem { base := .rdi }), .movqR .rbx .xmm8,
    .mov .rax (.mem { base := .rbx })]

theorem roundTrip_ct :
    ConstantTime isa (fun _ => True) (X86_64.Taint.Agree (Taint.ofRegs [.rbx, .rdi])) roundTrip :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rbx, .rdi]) (fun _ _ _ _ h => h) (by taint_decide)

/-- The taint after `is`, from `rbx` public. -/
def after (is : List Instr) : Option X86_64.Taint.T :=
  is.foldl (fun τ i => τ.bind (X86_64.Taint.step · i)) (some (Taint.ofRegs [.rbx]))

-- The round trip keeps `rbx` public.
example : (after [.xop (.movq .xmm8 .rbx), .movImm64 .rbx 0, .movqR .rbx .xmm8]).map
    (X86_64.Taint.pub · .rbx) = some true := by decide

-- A vector instruction in between makes every SSE register secret.
example : (after [.xop (.movq .xmm8 .rbx), .xop (.bin .pand .xmm0 .xmm1), .movqR .rbx .xmm8]).map
    (X86_64.Taint.pub · .rbx) = some false := by decide

-- So does saving a secret register in the same SSE register.
example : (after [.xop (.movq .xmm8 .rbx), .xop (.movq .xmm8 .rcx), .movqR .rbx .xmm8]).map
    (X86_64.Taint.pub · .rbx) = some false := by decide

end VG.Test.X86_64TaintXmm
