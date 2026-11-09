module

public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLit
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! The precomputed variant satisfies the same reviewed ABI contract, with 8 bytes of stack for
its call of `vg_gf25519_r64_invert`: correct and constant time as its code with the inversion
inlined (`Verified.of_inline`); callers get its correctness and constant time for states that
keep their buffers off those 8 bytes (`scalarBase_precomputed_ok`, `scalarBaseLocal.clear`). -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64
open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem scalarBase_precomputed_okI [X25519.X86_64.DivstepInv] (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa (scalarBase_precomputed fld).inline s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct_of_engine _ (scalarBasePrecomputedEngine_ok (fld := fld)) hs
  rw [← scalarBaseWith_inline] at he
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; fld_lit_decide) he h.1, h.2⟩

omit [EdArith fld] in
/-- The output is apart from the call's return address. -/
theorem scalarBase_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : scalarBaseLocal.pre s)
    (hcl : Clear (hole (s.gpr .rsp)) s) (hp : scalarBaseLocal.post s b) :
    scalarBaseLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hw, -⟩ := hs
  have hb := Clear.wr_bytes hcl (p := s.gpr .rdi) (n := 32) (by rw [hw]; simp) (by decide)
  exact (bytes_patch hb).trans hp

/-- The code's correctness, for callers. -/
theorem scalarBase_precomputed_ok [X25519.X86_64.DivstepInv] :
    ∀ s, scalarBaseLocal.clear.pre s → ∃ t s', Exec isa (scalarBase_precomputed fld) s t s' ∧
      abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  ok_of_inline (by fld_lit_decide) scalarBase_precomputed_okI scalarBase_patch

/-- The code's constant time, for callers. -/
theorem scalarBase_precomputed_ctC [X25519.X86_64.DivstepInv] :
    ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub (scalarBase_precomputed fld) :=
  ct_of_inline (by fld_lit_decide)
    (fun s h => let ⟨t, s', e, _⟩ := scalarBase_precomputed_okI s h; ⟨t, s', e⟩) (fun _ _ h => h.1)
    scalarBase_precomputed_ct

theorem combConsts_eq : combConsts = [(combSym, combWords)] := rfl

/-- The memory of the contract's witness: the tables at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the tables). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 combWords

theorem combSatMem_held : ∀ i < combWordCount,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  unfold combSatMem
  intro i hi
  exact constMem_held _ _ (by rw [combWords_length]; simp only [combWordCount]; omega) i
    (by rw [combWords_length]; exact hi)

/-- A state satisfying the precondition. -/
def baseSatStateT : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := combSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 40448⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]
  syms _ := 0x100000

end VG.Proof.Ed25519.X86_64
