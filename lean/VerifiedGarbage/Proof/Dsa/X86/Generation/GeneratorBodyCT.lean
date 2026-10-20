module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCandidateCT
public import Aesop.BuiltinRules
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorArguments
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCandidateCT

/-! # Restore a generator candidate using only the two live public frame words -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

structure GeneratorBodyAt (G : PrimeConfig) (p : GeneratorCandidatePublic) (s : State) : Prop where
  layout : GeneratorLayout G p.frame.base (p.frame.words 5)
  prepared : PrimePrepared G s
  frame : FrameAt [5, 21] p.frame s
  input : p.frame.words 21 = p.input
  base : (p.frame.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic).setWidth 64 = G.base
  value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.input.setWidth 64) G.len) = p.value
  exponent : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
    ((generatorExponentPointer (p.frame.words 5)).setWidth 64) G.len) = p.exponent
  fit : p.input.toNat + G.len ≤ 2 ^ 32
  read : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr) (off (p.input.setWidth 64) d) 4
  apart : Region.Disjoint ⟨p.input.setWidth 64, G.len⟩ ⟨G.base, G.size⟩
  exponentRead : ∀ d, d + 4 ≤ G.len → InRegions (s.rd ++ s.wr)
    (off ((generatorExponentPointer (p.frame.words 5)).setWidth 64) d) 4
  outputWrite : ∀ d k, d + k ≤ G.len → InRegions s.wr
    (off ((generatorOutputPointer (p.frame.words 5)).setWidth 64) d) k

theorem generatorBodyArgs_ct (G : PrimeConfig) : RelCT isa (Two (GeneratorBodyAt G))
    (.block (workspaceBase ++ ([.mov .esi (.mem (frameSlot 21))] : List Instr))) (Two (GeneratorCandidateAt G)) := by
  refine two_piece [.esp] (fun p s t hs ht => frameAt_pins _ p.frame s t hs.frame ht.frame) (by taint_decide) ?_
  intro p s R
  refine WP.mono (generatorArguments_ok R.frame.1 (observedWords_rep p.frame.base s)) fun t ⟨di, si, mem, K⟩ => ?_
  have parent : observedWords p.frame.base s 5 = p.frame.words 5 := R.frame.2 5 (by simp)
  have input : observedWords p.frame.base s 21 = p.input := (R.frame.2 21 (by simp)).trans R.input
  rw [parent] at di
  rw [input] at si
  have ready := (R.prepared.frame (by rw [mem]; exact Frame.refl [] s.mem) (by simp) K (by decide)).restore
    (by rw [di, R.base])
  refine ⟨R.layout, ⟨observedWords p.frame.base s, ready, R.frame.1.keeps K (by decide), ?_, parent, ?_, ?_⟩,
    si, ?_, ?_, R.fit, ?_, R.apart⟩
  · rw [mem]; exact observedWords_rep p.frame.base s
  · intro d hd; rw [K.2.1, K.2.2]; exact R.exponentRead d hd
  · intro d k hd; rw [K.2.2]; exact R.outputWrite d k hd
  · rw [mem]; exact R.value
  · rw [mem]; exact R.exponent
  · intro d hd; rw [K.2.1, K.2.2]; exact R.read d hd

theorem generatorBody_ct (G : PrimeConfig) : RelCT isa (Two (GeneratorBodyAt G))
    (generatorBody G.len) (fun _ _ => True) :=
  RelCT.seq (generatorBodyArgs_ct G) (generatorCandidate_ct G)
end VG.Proof.Dsa.X86.Generation
