module

public import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming

/-! # Exponentiation and output copies preserve the public layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    RelCT isa (fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t)
      (.seq (Generate.deriveCompute L.pLen L.qLen) (Generate.writeKey L.pLen L.qLen))
      (VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)) := by
  have W := L.lengths
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t) ?_ ?_
  · intro s t tr ur sf tf ⟨Pair, S, T⟩ E F
    obtain ⟨Trace, Pair'⟩ := deriveCompute_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, X, Nat.le_refl _⟩)
      _ _ _ _ _ _ Pair E F
    have Es := (wp_result (deriveCompute_ok Pair.1.moduli (Pair.1.buffers _ G) (Pair.1.buffers _ X) rfl rfl) E).2.2.2
    have Et := (wp_result (deriveCompute_ok Pair.2.moduli (Pair.2.buffers _ G) (Pair.2.buffers _ X) rfl rfl) F).2.2.2
    exact ⟨Trace, Pair', S.keep Es, T.keep Et⟩
  · apply (writeKey_relCT L.base L.size L.pLen L.qLen out L.saved ho (by omega) A).mono ?_ (fun _ _ h => h)
    intro s t ⟨Pair, S, T⟩
    exact ⟨S.writeReady Pair.1 Params X A, T.writeReady Pair.2 Params X A,
      Pair.pointer (.inl ⟨_, P, Nat.le_refl _⟩), Pair.pointer (.inl ⟨_, X, Nat.le_refl _⟩)⟩

end VG.Proof.Dsa.X86
