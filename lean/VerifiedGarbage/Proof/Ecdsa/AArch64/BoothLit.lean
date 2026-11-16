module

public import VerifiedGarbage.Impl.P256.Booth
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Impl.P256.Booth
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
meta import VerifiedGarbage.Proof.EcKey.AArch64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! The comb that signing and public keys share is checked once, and their
literals read it.

The comb's forwarded field programs (`CombArithmetic.program`) are the
optimizer's output, which `Forward.CombMixed` and `Forward.CombOut` already
have as literals: the comb's literal is its code with those, by rewriting,
rather than the kernel running the optimizer again. `materialize_code` reads
a literal only of what has one under its own name (`mixed.lit`, and
`CombArithmetic.program.lit` for the function `combJP` is given), so those
are stated here, from the optimizer's. -/

@[expose] public section

namespace VG.Impl.P256.Booth
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

private theorem program_eq (k : CombArithmetic.Kind) :
    CombArithmetic.program CombArithmetic.K.M (CombArithmetic.operations k) =
      .block (VG.Proof.Weierstrass.AArch64.Forward.CombArithmetic.optimized k) := by
  rw [CombArithmetic.program,
    ite_eq_left ⟨rfl, List.mem_map.mpr ⟨k, by cases k <;> decide, rfl⟩⟩]
  rfl

/-- The comb's mixed addition is its field program's code. -/
theorem program_mixed : CombArithmetic.program CombArithmetic.K.M
    (maddJ CombArithmetic.K.S CombArithmetic.K.A CombArithmetic.K.E CombArithmetic.K.D) = .block mixed :=
  program_eq .mixed

theorem mixed_lit : mixed = VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit :=
  VG.Proof.Weierstrass.AArch64.Forward.CombMixed.optimized_lit

/-- The comb's mixed addition's literal, the optimizer's (`Forward.CombMixed`):
the literals of the code with it read it, rather than run the optimizer. -/
noncomputable abbrev mixed.lit : List Instr :=
  VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit
theorem mixed.lit_eq : mixed = mixed.lit := mixed_lit

/-- The comb's field programs with the optimizer's literals: the forwarded
programs of the comb's two schedules, which a literal of the comb reads
(`combJP` runs `program` on its conversion), rather than run the optimizer. -/
noncomputable def _root_.VG.Impl.P256.CombArithmetic.program.lit (M : VG.Impl.Mont.Mod)
    (ops : List FOp) : Prog isa :=
  if M = CombArithmetic.K.M ∧ ops = CombArithmetic.operations .mixed then
    .block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit
  else if M = CombArithmetic.K.M ∧ ops = CombArithmetic.operations .out then
    .block VG.Proof.Weierstrass.AArch64.Forward.CombOut.rightCode.lit
  else fprogB M ops

theorem _root_.VG.Impl.P256.CombArithmetic.program.lit_eq :
    CombArithmetic.program = CombArithmetic.program.lit := by
  funext M ops
  unfold CombArithmetic.program.lit
  split
  · next h =>
    obtain ⟨rfl, rfl⟩ := h
    exact (program_eq .mixed).trans
      (congrArg _ VG.Proof.Weierstrass.AArch64.Forward.CombMixed.optimized_lit)
  · next h1 =>
    split
    · next h =>
      obtain ⟨rfl, rfl⟩ := h
      exact (program_eq .out).trans
        (congrArg _ VG.Proof.Weierstrass.AArch64.Forward.CombOut.optimized_lit)
    · next h2 =>
      rw [CombArithmetic.program, ite_eq_right]
      rintro ⟨rfl, hm⟩
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hm
      cases k
      · exact absurd ⟨rfl, rfl⟩ h1
      · exact absurd ⟨rfl, rfl⟩ h2

-- The comb, which signing and public keys both contain, is evaluated once.
materialize_code comb
materialize_code sign
materialize_code publicKey

end VG.Impl.P256.Booth
