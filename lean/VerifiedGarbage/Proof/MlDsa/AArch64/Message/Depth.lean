module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst

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

/-- Frames nest at most `d` deep in `c` and the functions it calls (a
structure, so that unification never unfolds it into a computation of the
depth). -/
structure DLe (d : Nat) (c : Prog isa) : Prop where
  le : c.aarch64Depth ≤ d

section
variable {d : Nat}

theorem DLe.block (is : List Instr) : DLe d (.block is) := ⟨Nat.zero_le _⟩

theorem DLe.seq {a b : Prog isa} (ha : DLe d a) (hb : DLe d b) : DLe d (.seq a b) := ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩⟩

theorem DLe.ite {c : isa.Cond} {a b : Prog isa} (ha : DLe d a) (hb : DLe d b) : DLe d (.ite c a b) :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩⟩

theorem DLe.loop {c : isa.Cond} {a : Prog isa} (ha : DLe d a) : DLe d (.loop a c) := ⟨ha.1⟩

theorem DLe.call {c : Prog isa} (n : String) (h : DLe d c) : DLe d (.call n c) := ⟨h.1⟩

theorem DLe.seqR {f : Nat → Prog isa} (h : ∀ k, DLe d (f k)) :
    ∀ a n, DLe d (Impl.MlDsa.AArch64.Call.seqR f a n)
  | _, 0 => DLe.block _
  | a, n + 1 => DLe.seq (h a) (DLe.seqR h (a + 1) n)

theorem DLe.of_fd {c : Prog isa} (h : 16 * c.aarch64Depth ≤ 16) : DLe 1 c := ⟨by omega⟩

end

/-- `DLe` of code from its structure, given that of the functions it calls. -/
tactic_template "dle_tac" : tactic =>
  `(tactic| repeat' (first
                     | (with_reducible assumption)
                     | (apply DLe.call; assumption)
                     | apply DLe.seq
                     | apply DLe.ite
                     | apply DLe.loop
                     | (apply DLe.seqR; intro)
                     | apply DLe.block
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
  ⟨⟨by rw [v.absorb_depth]⟩, ⟨by rw [v.pad_depth]⟩, ⟨by rw [v.squeeze_depth]⟩⟩

end

end VG.Proof.MlDsa.AArch64.Message
