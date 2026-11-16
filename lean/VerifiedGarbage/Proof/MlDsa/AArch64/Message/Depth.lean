module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
public import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on AArch64: how deep frames nest

Untrusted: everything here is checked by Lean. Frames nest at most once
(`DLe`, from the structure of the code, `dle_tac`) in the SHA-3 sponge
functions, with any implementation of the Keccak permutation (`keccak_dle`),
so that calls of them use the 16 bytes of stack below the stack pointer.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64

/-- Frames nest at most `d` deep in `c` and the functions it calls, and none of
them touches PSTATE.DIT (`nd`, whence calls of `c` from any mode:
`ConstantTime.withDit`) (a structure, so that unification never unfolds it
into a computation of the depth). -/
structure DLe (d : Nat) (c : Prog isa) : Prop where
  le : c.aarch64Depth ≤ d
  nd : c.all (fun i => !i.touchesDit) = true

section
variable {d : Nat}

theorem DLe.block (is : List Instr) (h : (Code.block is : Prog isa).all (fun i => !i.touchesDit) = true) :
    DLe d (.block is) := ⟨Nat.zero_le _, h⟩

theorem DLe.seq {a b : Prog isa} (ha : DLe d a) (hb : DLe d b) : DLe d (.seq a b) :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩, by simp only [Code.all, ha.2, hb.2, Bool.and_self]⟩

theorem DLe.ite {c : isa.Cond} {a b : Prog isa} (ha : DLe d a) (hb : DLe d b) : DLe d (.ite c a b) :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩, by simp only [Code.all, ha.2, hb.2, Bool.and_self]⟩

theorem DLe.loop {c : isa.Cond} {a : Prog isa} (ha : DLe d a) : DLe d (.loop a c) := ⟨ha.1, ha.2⟩

theorem DLe.call {c : Prog isa} (n : String) (h : DLe d c) : DLe d (.call n c) := ⟨h.1, h.2⟩

theorem DLe.seqR {f : Nat → Prog isa} (h : ∀ k, DLe d (f k)) :
    ∀ a n, DLe d (Impl.MlDsa.AArch64.Call.seqR f a n)
  | _, 0 => DLe.block _ rfl
  | a, n + 1 => DLe.seq (h a) (DLe.seqR h (a + 1) n)

theorem DLe.of_fd {c : Prog isa} (h : 16 * c.aarch64Depth ≤ 16) (hnd : c.all (fun i => !i.touchesDit) = true) :
    DLe 1 c := ⟨by omega_using [h], hnd⟩

/-- A callee's: its frames and its no-DIT fact (`CalleeOk.fd`, `CalleeOk.nd`). -/
theorem DLe.of_callee {S : Nat} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k) :
    DLe (S / 16) c := ⟨by have := C.fd; omega_using [this], C.nd⟩

end

theorem ptrTo_noDit (d b : Reg) (off : Nat) :
    (Impl.MlKem.AArch64.ptrTo d b off).all (fun i => !i.touchesDit) = true := by
  unfold Impl.MlKem.AArch64.ptrTo; split <;> rfl

theorem keccakArgs_noDit (sc : Reg) (st wk rate : Nat) (first : Bool) (wr : Reg) :
    (Impl.MlKem.AArch64.keccakArgs sc st wk rate first wr).all (fun i => !i.touchesDit) = true := by
  simp only [Impl.MlKem.AArch64.keccakArgs, List.all_append, List.all_cons, ptrTo_noDit, Bool.and_true]
  cases first <;> rfl

theorem copySeed4_noDit (j : Nat) :
    (Impl.MlDsa.AArch64.KeyGen.copySeed4 j).all (fun i => !i.touchesDit) = true := by
  simp only [Impl.MlDsa.AArch64.KeyGen.copySeed4, List.all_append, lea_noDit, Bool.true_and]; rfl

theorem montDotBody_noDit (n : Nat) :
    (Impl.MlDsa.AArch64.Optimized.MontDot.body n).all (fun i => !i.touchesDit) = true := by
  have hp : ∀ j, (Impl.MlDsa.AArch64.Optimized.MontDot.product j).all (fun i => !i.touchesDit) = true :=
    fun j => by unfold Impl.MlDsa.AArch64.Optimized.MontDot.product; split <;> rfl
  simp only [Impl.MlDsa.AArch64.Optimized.MontDot.body, List.all_append, List.all_flatMap, Bool.and_eq_true]
  exact ⟨⟨⟨List.all_eq_true.mpr fun j _ => hp j, by decide⟩, by decide⟩, by decide⟩

/-- `DLe` of code from its structure, given that of the functions it calls. -/
tactic_template "dle_tac" : tactic =>
  `(tactic| repeat' (first
                     | (with_reducible assumption)
                     | (apply DLe.call; assumption)
                     | apply DLe.seq
                     | apply DLe.ite
                     | apply DLe.loop
                     | (apply DLe.seqR; intro)
                     | (apply DLe.block; first
                         | lit_decide
                         | (simp only [Code.all, List.all_append, glue_noDit, lea_noDit, movV_noDit, ptrTo_noDit,
                             keccakArgs_noDit, copySeed4_noDit, montDotBody_noDit, Bool.and_true, Bool.true_and]; done)
                         | (simp only [Code.all, List.all_append, glue_noDit, lea_noDit, movV_noDit, ptrTo_noDit,
                             keccakArgs_noDit, copySeed4_noDit, montDotBody_noDit, Bool.and_true, Bool.true_and]; rfl)
                         | rfl)
                     | (dsimp only [Impl.MlDsa.AArch64.Sign.rejCallAt,
                         Impl.MlDsa.AArch64.Sign.maskAt, Impl.MlDsa.AArch64.Sign.maskCallAt, Impl.MlDsa.AArch64.Sign.masks]; split)))

end VG.Proof.MlDsa.AArch64.Message

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

section
variable (v : Proof.Sha3.AArch64.Permutation)

theorem keccak_dle :
    DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith v.callee) ∧ DLe 1 (Impl.Sha3.AArch64.Stream.padWith v.callee) ∧
      DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith v.callee) :=
  ⟨⟨by rw [v.absorb_depth], v.absorb_noDit⟩, ⟨by rw [v.pad_depth], v.pad_noDit⟩,
    ⟨by rw [v.squeeze_depth], v.squeeze_noDit⟩⟩

end

end VG.Proof.MlDsa.AArch64.Message
