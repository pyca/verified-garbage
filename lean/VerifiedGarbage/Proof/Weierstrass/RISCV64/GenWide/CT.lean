module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT

/-!
# Arithmetic modulo a wide modulus on RISC-V: constant time

`fn k core` (`Impl/Weierstrass/RISCV64/GenWide.lean`) is constant time if the
taint analysis finds the rest of it so from the pointers' and offsets'
registers after the zero-extension (`fn_ct`), as P-384's
(`Proof/Weierstrass/RISCV64/P384Field/Verified.lean`). Each modulus's proof
runs the analysis on its code.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.Ed25519.RISCV64 (mulAgreeLo mulZext_rel)

/-- What the taint analysis checks of `fn k core`: all but the zero-extension. -/
abbrev fnBody (k : Nat) (core : List Instr) : Prog isa :=
  .seq (.block ptrs) (.ite (.zero .t0) (.block core)
    (.seq (.block ([.addi .t1 .t2 0] ++ unpack k .t4 (SA k) 0 ++ unpack k .t5 (SB k) 0 ++
        [.addi .t4 .a3 (SA k), .addi .t5 .a3 (SB k), .addi .t2 .a3 (SO k)])) <|
      .seq (.block core) (.block (pack k .t1 (SO k) 0))))

theorem fn_ct {k : Nat} {core : List Instr} {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂)
    (h : RelCT isa (VG.RISCV64.Taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3])) (fnBody k core) fun _ _ => True) :
    ConstantTime isa Pre Pub (fn k core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold fn
  refine RelCT.seq (mulZext_rel.mono (fun _ _ ⟨h₁, h₂, hp⟩ => hpub _ _ h₁ h₂ hp) fun _ _ h => h) ?_
  exact h.mono (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (by simpa using h)⟩) fun _ _ h => h

end VG.Proof.Weierstrass.RISCV64.GenWide
