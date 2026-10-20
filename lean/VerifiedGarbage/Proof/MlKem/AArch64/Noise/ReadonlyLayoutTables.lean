module
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem allWrites_tables_far {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
 {B : Addr} (hc : Covers [⟨B,L.scl⟩] s.wr) (ht : Optimized.TransformTables s) :
 ∀r∈allWrites L kg B,
   (Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r ∧
   (Region.mk (s.syms "VG_MLKEM_INTT16_ZETAS") 512).Disjoint r := by
 have lim := layout_limits wf kg
 have cw {o l : Nat} (ho : o+l≤L.scl) := coversScratch hc ho
 have far {symbol H} (h : Optimized.TransformTable s symbol H) :
   ∀r∈allWrites L kg B,(Region.mk (s.syms symbol) 512).Disjoint r := by
   apply allWrites_apart
   · exact h.apart (cw (by omega))
   · exact h.apart (cw lim.2.2.1)
   · intro j hj; exact h.apart (cw (outOff_fits wf room kg hj))
 exact fun r hr=>⟨far ht.forward r hr,far ht.inverse r hr⟩

theorem readonly_noiseAll_tables {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
 {B : Addr} (hB : s.gpr .x28=B) (hc : Covers [⟨B,L.scl⟩] s.wr)
 (ht : Optimized.TransformTables s) :
 WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWithW L kg) s fun t=>
 Kept (allWrites L kg B) s t ∧ ∀j<2*L.k,PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg j))
   (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j)) := by
 have lim := layout_limits wf kg
 have cw {o l : Nat} (ho : o+l≤L.scl) := coversScratch hc ho
 apply readonly_noiseAll_layout wf room kg hB hc
 · intro j hj
   exact ht.forward.ready (coversTwo (cw (outOff_fits wf room kg hj)) (cw lim.2.2.1))
 · apply allWrites_apart
   · exact ht.forward.apart (cw (by omega))
   · exact ht.forward.apart (cw lim.2.2.1)
   · intro j hj; exact ht.forward.apart (cw (outOff_fits wf room kg hj))
end VG.Proof.MlKem.AArch64.Noise
