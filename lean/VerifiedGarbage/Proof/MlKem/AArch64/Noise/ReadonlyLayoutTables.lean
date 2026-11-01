module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutPair

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/AllWith.lean`, which only this module imported.
section

/-! # Accumulating all paired noise outputs -/
section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)
open VG.Spec.MlKem

theorem all_loop_okWith {s : State} {L : KemLay} (nttAt : Nat→Nat→Prog isa) (kg : Bool) (hk : 0<L.k)
    (rs : List Region) (out : Nat → Addr) (value : Nat → Poly) (writes : Nat → List Region)
    (hsub : ∀i<L.k, ∀r∈writes i, r∈rs)
    (hfar : ∀i<L.k, ∀j<2*i, ∀r∈writes i, (polyRegion (out j)).Disjoint r)
    (hstep : ∀i<L.k, ∀t, Kept rs s t → t.syms=s.syms →
      WP isa (Impl.MlKem.AArch64.Noise.noisePairWith nttAt L kg (2*i)) t fun u =>
        Kept (writes i) t u ∧ PolyIsW (cw true) u.mem (out (2*i)) (value (2*i)) ∧
        PolyIsW (cw true) u.mem (out (2*i+1)) (value (2*i+1))) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith nttAt L kg) s fun t =>
      Kept rs s t ∧ ∀j<2*L.k, PolyIsW (cw true) t.mem (out j) (value j) := by
  apply WP.mono (Q:=fun t : State=> (Kept rs s t ∧ t.syms=s.syms) ∧ ∀j<2*L.k, PolyIsW (cw true) t.mem (out j) (value j)) ?_ (fun _ h=>⟨h.1.1,h.2⟩)
  apply WPs.seqs (map_range_ne_nil hk _)
  apply WPs.range (I := fun i t => (Kept rs s t ∧ t.syms=s.syms) ∧ ∀j<2*i, PolyIsW (cw true) t.mem (out j) (value j))
  · intro i hi t ⟨⟨kt,st⟩,old⟩
    refine WP.mono_syms (hstep i hi t kt st) fun u ⟨ku,a,b⟩ ut => ?_
    refine ⟨⟨kt.trans (ku.mono (hsub i hi)),ut.trans st⟩,fun j hj => ?_⟩
    by_cases hj0 : j<2*i
    · exact Proof.MlKem.polyIsW_frame_poly ku.frame (hfar i hi j hj0) (old j hj0)
    · rcases (show j=2*i ∨ j=2*i+1 by omega) with rfl | rfl
      · exact a
      · exact b
  · exact ⟨⟨Kept.refl rs s,rfl⟩,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Noise
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/ReadonlyLayoutAll.lean`, which only this module imported.
section

/-! # Complete paired sampling of all secrets and retained errors -/
section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem readonly_noiseAll_layout {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} (hB : s.gpr .x28=B) (hc : Covers [⟨B,L.scl⟩] s.wr)
    (ht : ∀j<2*L.k,NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg j)) (B+BitVec.ofNat 64 (nttOff kg)))
    (hfar : ∀r∈allWrites L kg B,(NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith Ntt16.Readonly.nttAtWithW L kg) s fun t =>
      Kept (allWrites L kg B) s t ∧
      ∀j<2*L.k, PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg j))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j)) := by
  refine all_loop_okWith Ntt16.Readonly.nttAtWithW kg (by have := wf.facts; omega) (allWrites L kg B)
    (fun j => B+BitVec.ofNat 64 (outOff L kg j))
    (fun j => sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j))
    (fun i => writes L kg B (2*i)) ?_ ?_ ?_
  · intro i hi r hr
    exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hr⟩
  · intro i hi j hj
    exact writes_old_far wf room kg B (by omega) hj
  · intro i hi t kt ts
    have table (j : Nat) (hj : j<2*L.k) := (ht j hj).frame ts kt.rd kt.wr kt.frame hfar
    have far : ∀r∈writes L kg B (2*i),(NttR.fastRegion t).Disjoint r := by
      intro r hr; simp only [NttR.fastRegion, NttR.sRegion, ts]; exact hfar r (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hr⟩)
    refine WP.mono (readonly_noisePair_layout (B := B) wf room kg (by omega : 2*i+1<2*L.k)
      (by rw [kt.cs .x28 (by decide) (by decide)]; exact hB)
      (by rw [kt.wr]; exact hc) (table _ (by omega)) (table _ (by omega)) far) fun u ⟨ku,pu,qu⟩ => ?_
    have he := Proof.MlKem.bytesAt_frame kt.frame (allWrites_seed_far wf room kg B) (by decide)
    exact ⟨ku,by simpa only [sampled,he] using pu,by simpa only [sampled,he] using qu⟩
 
end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem allWrites_tables_far {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
 {B : Addr} (hc : Covers [⟨B,L.scl⟩] s.wr) (ht : Optimized.TransformTables s) :
 ∀r∈allWrites L kg B,
   (Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r ∧
   (NttR.fastInvRegion s).Disjoint r ∧ (NttR.fastRegion s).Disjoint r := by
 have lim := layout_limits wf kg
 have cw {o l : Nat} (ho : o+l≤L.scl) := coversScratch hc ho
 have far {symbol H} (h : Optimized.TransformTable s symbol H) :
   ∀r∈allWrites L kg B,(Region.mk (s.syms symbol) 512).Disjoint r := by
   apply allWrites_apart
   · exact h.apart (cw (by omega))
   · exact h.apart (cw lim.2.2.1)
   · intro j hj; exact h.apart (cw (outOff_fits wf room kg hj))
 have farF : ∀r∈allWrites L kg B,(NttR.fastRegion s).Disjoint r := by
   apply allWrites_apart
   · exact ht.fast.apart (cw (by omega))
   · exact ht.fast.apart (cw lim.2.2.1)
   · intro j hj; exact ht.fast.apart (cw (outOff_fits wf room kg hj))
 have farI : ∀r∈allWrites L kg B,(NttR.fastInvRegion s).Disjoint r := by
   apply allWrites_apart
   · exact ht.inverse.apart (cw (by omega))
   · exact ht.inverse.apart (cw lim.2.2.1)
   · intro j hj; exact ht.inverse.apart (cw (outOff_fits wf room kg hj))
 exact fun r hr=>⟨far ht.forward r hr,farI r hr,farF r hr⟩

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
   exact ht.fast.ready (coversTwo (cw (outOff_fits wf room kg hj)) (cw lim.2.2.1))
 · apply allWrites_apart
   · exact ht.fast.apart (cw (by omega))
   · exact ht.fast.apart (cw lim.2.2.1)
   · intro j hj; exact ht.fast.apart (cw (outOff_fits wf room kg hj))
end VG.Proof.MlKem.AArch64.Noise
