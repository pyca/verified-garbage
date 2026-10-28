module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveComputeTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! Private comb computation followed by the shared output copies. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def DomainReady (L : CallLayout) (s : State) : Prop :=
  let g := operandValue s L.base (.input .g) L.pLen
  (1<g ∧ g<L.p) ∧ (L.p-1)%L.q=0 ∧ g^L.q%L.p=1

theorem deriveBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : (.input .p,L.pLen)∈L.inputs) (Q : (.input .q,L.qLen)∈L.inputs)
    (G : (.input .g,L.pLen)∈L.inputs) (X : (.input .nonce,L.qLen)∈L.inputs)
    (Params : (.input .p,2*L.pLen+L.qLen)∈L.inputs)
    (ho : out.toNat+(3*L.pLen+2*L.qLen)≤2^32)
    (A : Region.Disjoint ⟨L.base,L.size⟩ ⟨out.setWidth 64,3*L.pLen+2*L.qLen⟩)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t)
      (.seq (deriveCompute L.pLen L.qLen) (Generate.writeKey L.pLen L.qLen))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have W := L.lengths
  refine RelCT.seq (R := fun s t => CallPair L s t ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t) ?_ ?_
  · intro s t tr ur sf tf ⟨Pair,S,T,Cs,Ct,Ds,Dt⟩ E F
    have H := deriveCompute_relCT L (.inl ⟨_,P,Nat.le_refl _⟩) (.inl ⟨_,Q,Nat.le_refl _⟩)
      G X fits _ _ _ _ _ _ ⟨Pair,Cs,Ct⟩ E F
    have Es := (wp_result (deriveCompute_ok Pair.1.moduli (Pair.1.buffers _ G)
      (Pair.1.buffers _ X) rfl rfl Ds fits Cs) E).2.2.2
    have Et := (wp_result (deriveCompute_ok Pair.2.moduli (Pair.2.buffers _ G)
      (Pair.2.buffers _ X) rfl rfl Dt fits Ct) F).2.2.2
    exact ⟨H.1,H.2,S.keep Es,T.keep Et⟩
  · apply (writeKey_relCT L.base L.size L.pLen L.qLen out L.saved ho (by omega) A).mono ?_ (fun _ _ h => h)
    intro s t ⟨Pair,S,T⟩
    exact ⟨S.writeReady Pair.1 Params X A,T.writeReady Pair.2 Params X A,
      Pair.pointer (.inl ⟨_,P,Nat.le_refl _⟩),Pair.pointer (.inl ⟨_,X,Nat.le_refl _⟩)⟩

end VG.Proof.Dsa.X86.Comb
