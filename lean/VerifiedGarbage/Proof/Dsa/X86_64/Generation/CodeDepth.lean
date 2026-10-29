module
public import VerifiedGarbage.Proof.Framework.X86_64.Depth

public import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Compositional bounds for stack use below the persistent search frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64

def generationDepth (c : Prog isa) : Prop := c.x86_64Depth ≤ 128

theorem generationDepth.seq {a b : Prog isa} (ha : generationDepth a) (hb : generationDepth b) :
    generationDepth (.seq a b) := Nat.max_le.mpr ⟨ha, hb⟩

theorem generationDepth.ite {a b : Prog isa} (ha : generationDepth a) (hb : generationDepth b) (cc : Cond) :
    generationDepth (.ite cc a b) := Nat.max_le.mpr ⟨ha, hb⟩

theorem generationDepth.loop {b : Prog isa} (hb : generationDepth b) (cc : Cond) :
    generationDepth (.loop b cc) := hb

theorem generationDepth.block (is : List Instr) : generationDepth (.block is) := by
  change 0 ≤ 128
  decide

/-- What code around the probable-prime calls may use below the frame: a
call's return address and the 184 bytes of the test's stack. -/
def callerDepth (c : Prog isa) : Prop := c.x86_64Depth ≤ 192

theorem callerDepth.of {c : Prog isa} (h : generationDepth c) : callerDepth c :=
  Nat.le_trans h (by decide)

theorem callerDepth.seq {a b : Prog isa} (ha : callerDepth a) (hb : callerDepth b) :
    callerDepth (.seq a b) := Nat.max_le.mpr ⟨ha, hb⟩

theorem callerDepth.ite {a b : Prog isa} (ha : callerDepth a) (hb : callerDepth b) (cc : Cond) :
    callerDepth (.ite cc a b) := Nat.max_le.mpr ⟨ha, hb⟩

theorem generation_depth_seqs (l : List (Prog isa)) :
    (Impl.Bignum.X86_64.seqs l).x86_64Depth = l.foldr (fun c n => max c.x86_64Depth n) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => simp only [Impl.Bignum.X86_64.seqs, List.foldr_cons, List.foldr_nil, Nat.max_zero]
    | cons b l => simp only [Impl.Bignum.X86_64.seqs, Code.x86_64Depth, List.foldr_cons] at ih ⊢; rw [ih]

end VG.Proof.Dsa.X86_64.Generation
