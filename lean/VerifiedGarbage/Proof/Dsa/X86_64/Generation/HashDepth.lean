module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
import VerifiedGarbage.Proof.Framework.Omega

/-! # Seed hashing fits the reserved stack below the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

structure HashDepth (H : Stream) : Prop where
  init : H.initC.x86_64Depth ≤ 120
  update : H.updC.x86_64Depth ≤ 120
  finish : H.finC.x86_64Depth ≤ 120

theorem hashLabel_depth {H : Stream} (h : HashDepth H) (o : Nat) :
    generationDepth (Impl.RsaOaep.X86_64.hashLabel H o) := by
  simp only [generationDepth, Impl.RsaOaep.X86_64.hashLabel, Impl.Mgf1.X86_64.seqs,
    Code.x86_64Depth, Nat.max_le]
  exact ⟨by decide, Nat.add_le_add_right h.init 8, by decide,
    Nat.add_le_add_right h.update 8, by decide, Nat.add_le_add_right h.finish 8⟩

theorem seedAdd_depth (n : Nat) : generationDepth (seedAdd n) := by
  induction n with
  | zero => exact generationDepth.block _
  | succ n ih => exact (generationDepth.block _).seq ih

theorem seedHash_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256) :
    generationDepth (seedHash H1 H256) :=
  (generationDepth.block _).seq ((hashLabel_depth h1 _).ite (hashLabel_depth h256 _) _)

theorem pHashOne_depth {H : Stream} (h : HashDepth H) (len count j : Nat) :
    generationDepth (pHashOne H len count j) :=
  ((generationDepth.block _).seq ((seedAdd_depth len).seq (hashLabel_depth h _))).seq
    ((generationDepth.block _).seq (by unfold generationDepth; decide +kernel))

theorem pHashPrefix_depth {H : Stream} (h : HashDepth H) (len count k : Nat) :
    generationDepth (pHashPrefix H len count k) := by
  induction k with
  | zero => exact generationDepth.block _
  | succ k ih => exact ih.seq (pHashOne_depth h len count k)

theorem pHashes_depth {H : Stream} (h : HashDepth H) (len count : Nat) :
    generationDepth (pHashes H len count) := pHashPrefix_depth h len count (count + 1)

end VG.Proof.Dsa.X86_64.Generation
