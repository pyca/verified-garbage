module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.AllWith
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyLayoutPair
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At

/-! # Complete paired sampling of all secrets and retained errors -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem readonly_noiseAll_layout {w16 : Bool} {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} (hB : s.gpr .x28=B) (hc : Covers [⟨B,L.scl⟩] s.wr)
    (ht : ∀j<2*L.k,Ntt16.Readonly.TableReady s "VG_MLKEM_NTT16_ZETAS" Ntt16.tableHalves
      (B+BitVec.ofNat 64 (outOff L kg j)) (B+BitVec.ofNat 64 (nttOff kg)))
    (hfar : ∀r∈allWrites L kg B,(Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAllWith (Ntt16.Readonly.nttAtR w16) L kg w16) s fun t =>
      Kept (allWrites L kg B) s t ∧
      ∀j<2*L.k, PolyIsW (cw w16) t.mem (B+BitVec.ofNat 64 (outOff L kg j))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j)) := by
  refine all_loop_okWith (Ntt16.Readonly.nttAtR w16) kg (by have := wf.facts; omega) (allWrites L kg B)
    (fun j => B+BitVec.ofNat 64 (outOff L kg j))
    (fun j => sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j))
    (fun i => writes L kg B (2*i)) ?_ ?_ ?_
  · intro i hi r hr
    exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hr⟩
  · intro i hi j hj
    exact writes_old_far wf room kg B (by omega) hj
  · intro i hi t kt ts
    have table (j : Nat) (hj : j<2*L.k) := (ht j hj).frame ts kt.rd kt.wr kt.frame hfar
    have far : ∀r∈writes L kg B (2*i),(Region.mk (t.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r := by
      intro r hr; rw [ts]; exact hfar r (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hr⟩)
    refine WP.mono (readonly_noisePair_layout (B := B) wf room kg (by omega : 2*i+1<2*L.k)
      (by rw [kt.cs .x28 (by decide) (by decide)]; exact hB)
      (by rw [kt.wr]; exact hc) (table _ (by omega)) (table _ (by omega)) far) fun u ⟨ku,pu,qu⟩ => ?_
    have he := Proof.MlKem.bytesAt_frame kt.frame (allWrites_seed_far wf room kg B) (by decide)
    exact ⟨ku,by simpa only [sampled,he] using pu,by simpa only [sampled,he] using qu⟩
 
end VG.Proof.MlKem.AArch64.Noise
