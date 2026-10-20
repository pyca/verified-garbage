module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

/-- A readonly table's caller obligations, independent of polynomial values. -/
structure TableReady (s : State) (symbol : String) (H : List Nat) (f w : Addr) : Prop where
  table : ∀ i<64, s.mem.readW (s.syms symbol+BitVec.ofNat 64 (8*i)) 64=hw4 H i
  readable : Covers [⟨s.syms symbol,512⟩] (s.rd++s.wr)
  output : (polyRegion f).Disjoint ⟨s.syms symbol,512⟩
  scratch : (polyRegion w).Disjoint ⟨s.syms symbol,512⟩

theorem transform_call {op : Poly → Poly} {symbol : String} {H : List Nat} {c : Prog isa}
    (hv : ∀ s, (contract op symbol H).pre s → ∃ tr t, Exec isa c s tr t ∧
      abiPreserved s t ∧ (contract op symbol H).post s t)
    (hn : c.noCalls=true) {s : State} {f w : Addr} (h0 : s.gpr .x0=f) (h1 : s.gpr .x1=w)
    (hd : (polyRegion f).Disjoint (polyRegion w)) (hr : Reduced s.mem f)
    (hw : Covers [polyRegion f,polyRegion w] s.wr) (ht : TableReady s symbol H f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [polyRegion f,polyRegion w] s s' → PolyIs s'.mem f (op (polyAt s.mem f)) → Q s') :
    WP isa c s Q := by
  refine WP.inline (k:=contract op symbol H) hv (rd:=[⟨s.syms symbol,512⟩])
    (wr:=[polyRegion f,polyRegion w]) ?_ (ht.readable.append_left hw.right) hw ?_ hn
  · refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
    · simp only [fP,sP,State.withRegions_wr,State.withRegions_gpr,h0,h1]
    · simpa only [fP,sP,State.withRegions_gpr,h0,h1] using hd
    · simpa only [fP,State.withRegions_mem,State.callEntry_mem,State.withRegions_gpr,h0] using hr
    · exact ht.table
    · exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simp only [fP,State.withRegions_gpr,h0]
      change (polyRegion f).Disjoint ⟨s.syms symbol,512⟩
      exact ht.output
    · simp only [sP,State.withRegions_gpr,h1]
      change (polyRegion w).Disjoint ⟨s.syms symbol,512⟩
      exact ht.scratch
  · intro s' hrd hwr habi hf _ hpost
    change PolyIs s'.mem (s.gpr .x0) (op (polyAt s.mem (s.gpr .x0))) at hpost
    rw [h0] at hpost
    exact hQ s' ⟨fun r hr _ => habi.1 r hr,habi.2.1,hrd,hwr,hf,habi.2.2⟩ hpost

theorem fwd_call {s : State} {f w : Addr} (h0 : s.gpr .x0=f) (h1 : s.gpr .x1=w)
    (hd : (polyRegion f).Disjoint (polyRegion w)) (hr : Reduced s.mem f)
    (hw : Covers [polyRegion f,polyRegion w] s.wr)
    (ht : TableReady s "VG_MLKEM_NTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.tableHalves f w)
    {Q : State → Prop} (hQ : ∀ s', Kept [polyRegion f,polyRegion w] s s' →
      PolyIs s'.mem f (ntt (polyAt s.mem f)) → Q s') :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.fwd s Q :=
  transform_call fwd_correct (by decide +kernel) h0 h1 hd hr hw ht hQ

theorem inv_call {s : State} {f w : Addr} (h0 : s.gpr .x0=f) (h1 : s.gpr .x1=w)
    (hd : (polyRegion f).Disjoint (polyRegion w)) (hr : Reduced s.mem f)
    (hw : Covers [polyRegion f,polyRegion w] s.wr)
    (ht : TableReady s "VG_MLKEM_INTT16_ZETAS" Impl.MlKem.AArch64.Ntt16.invTableHalves f w)
    {Q : State → Prop} (hQ : ∀ s', Kept [polyRegion f,polyRegion w] s s' →
      PolyIs s'.mem f (nttInv (polyAt s.mem f)) → Q s') :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.inv s Q :=
  transform_call inv_correct (by decide +kernel) h0 h1 hd hr hw ht hQ

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
