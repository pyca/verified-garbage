module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Original h tape and per-chunk plans for the native generator loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure GeneratorSearchPlan where
  core : GeneratorPlan
  saved : Nat → BitVec 64
  tape : List Byte
  tapePtr : Addr
  tapeFits : tape.length < 2 ^ 64
  tapeSeparate : ∀ r ∈ core.changed, (⟨tapePtr, tape.length⟩ : Region).Disjoint r
  q : Nat
  exponentValue : Spec.Dsa.decodeBE core.eb = (Spec.Dsa.decodeBE core.pb - 1) / q

def GeneratorSearchPlan.chunk (p : GeneratorSearchPlan) (used : Nat)
    (room : used + p.core.len ≤ p.tape.length) : GeneratorPlan :=
  { p.core with
    hp := off p.tapePtr used
    hb := (p.tape.drop used).take p.core.len
    hLength := by simp only [List.length_take, List.length_drop]; omega
    hSeparate := by
      intro r hr
      exact fun a ha hb => p.tapeSeparate r hr a (Offset.sub_base p.tapePtr room a ha) hb }

def GeneratorSearchPlan.remaining (p : GeneratorSearchPlan) (used : Nat) : Option Nat :=
  Spec.Dsa.generator (Spec.Dsa.decodeBE p.core.pb) p.q
    ((Spec.Dsa.generationChunks p.core.len (p.tape.drop used)).map Spec.Dsa.decodeBE)

theorem GeneratorSearchPlan.remaining_done (p : GeneratorSearchPlan) {used : Nat}
    (h : p.tape.length - used < p.core.len) : p.remaining used = none := by
  unfold remaining
  rw [VG.Proof.Dsa.Generation.generationChunks_done (by simpa only [List.length_drop] using h)]
  rfl

theorem GeneratorSearchPlan.remaining_step (p : GeneratorSearchPlan) {used : Nat}
    (room : used + p.core.len ≤ p.tape.length) :
    p.remaining used = if (p.chunk used room).accepts then some (p.chunk used room).value
      else p.remaining (used + p.core.len) := by
  have hw : 0 < p.core.len := by rcases p.core.width with hh | hh | hh <;> omega
  rw [remaining, VG.Proof.Dsa.Generation.generator_chunks_step hw (by
    simp only [List.length_drop]; omega)]
  simp only [GeneratorPlan.accepts, GeneratorPlan.value, chunk, p.exponentValue,
    remaining, List.drop_drop]

end VG.Proof.Dsa.X86_64.Generation
