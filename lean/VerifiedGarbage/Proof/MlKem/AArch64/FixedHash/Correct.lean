module
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.AbsorbLoop
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Init
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Compiled
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Fusion
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Transport
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.Framework.Contract
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt absorb pad)

theorem compiled_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate sfx : Nat} {ins outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (hi : ∀p∈ins,PieceOk sc st wk s₀ false p)
 (hio : ∀p∈ins,p.off+p.len≤65536)
 (valid : Valid rate ins 0 0 (schedule rate ins).1 (schedule rate ins).2)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate) :
 WP isa (compiled v.callee sc st wk rate sfx ins outs) s₀ fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::outs.map (preg s₀)) s₀ t ∧
 t.gpr .x30=s₀.gpr .x30 ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx)
   (ins.map (pbytes s₀)).flatten)) 0 outs := by
 dsimp only [compiled]
 refine WP.seq (WP.mono (zeroSave_ok hs hl) fun a ⟨ka,za,la⟩=>?_)
 refine WP.seq (WP.mono (compile_ok v hs ha hb valid a [] hi hio ka
   (by rw [Proof.Sha3.rep_nil]; exact za) (by simp)) fun b ⟨kb,mb,pb,fb⟩=>?_)
 simp only [List.nil_append,remaining_zero] at mb pb
 exact finish_ok v hs ha hb hl ho hp hn ht kb mb pb (by rw [link_frame hs fb,la])

/-- Original hash interface, with only the specialization's encoding and schedule checks added. -/
theorem code_ok (v : Proof.Sha3.AArch64.Permutation)
 {s₀ : State} {sc : Reg} {st wk rate sfx : Nat} {ins outs : List Piece}
 (hs : HSetup sc st wk rate s₀) (ha : st%8=0) (hb : st+rate≤4096)
 (hl : (wk+600)%8=0 ∧ wk+600<32768)
 (hi : ∀p∈ins,PieceOk sc st wk s₀ false p)
 (hio : ∀p∈ins,p.off+p.len≤65536)
 (valid : Valid rate ins 0 0 (schedule rate ins).1 (schedule rate ins).2)
 (ho : ∀p∈outs,PieceOk sc st wk s₀ true p)
 (hp : outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)))
 (hn : ∀p∈outs,p.off+p.len≤65536 ∧ p.len%8=0)
 (ht : (outs.map Piece.len).sum≤rate)
 (same : Fusion.Same (compiled v.callee sc st wk rate sfx ins outs)
   (Impl.MlKem.AArch64.FixedHash.code v.callee sc st wk rate sfx ins outs)) :
 WP isa (Impl.MlKem.AArch64.FixedHash.code v.callee sc st wk rate sfx ins outs) s₀ fun t=>
 Kept (STr sc st s₀::WKr sc wk s₀::below s₀.sp 16::outs.map (preg s₀)) s₀ t ∧
 Outs s₀ t.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx)
   (ins.map (pbytes s₀)).flatten)) 0 outs := by
 apply same.wp.mp
 refine WP.mono (compiled_ok v hs ha hb hl hi hio valid ho hp hn ht) fun t ⟨hk,_,out⟩=>⟨hk.mono ?_,out⟩
 intro r hr
 simp only [List.mem_cons] at hr ⊢
 rcases hr with h|h|h
 · exact Or.inl h
 · exact Or.inr (Or.inl h)
 · exact Or.inr (Or.inr (Or.inr h))
end VG.Proof.MlKem.AArch64.FixedHash
