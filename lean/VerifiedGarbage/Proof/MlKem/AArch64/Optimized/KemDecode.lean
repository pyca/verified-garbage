module
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps

import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc

/-! # Decode a key vector into the consumed first matrix row -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

structure DecodeInv (P : KemLay) (L : Layout) (s₀ : State) (mD : Mem)
    (T Y : Nat → Poly) (v : BitVec 64) (n : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24=v
  decoded : ∀ j<n, PolyIs s.mem (sA L s₀ (aOff P 0 j)) (T j)
  y : ∀ j<P.k, PolyIs s.mem (sA L s₀ (yOff P j)) (Y j)
  frame : Frame [R (kA s₀) L.sc AH (1024*n)] mD s.mem

theorem decode_step {s₀ s : State} (hp : Pre P L s₀) {kE eo : Nat}
    (hkE : kE<4) (hread : L.slot kE<L.nrd) (hfit : eo+384*P.k≤L.len (L.slot kE))
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64} {j : Nat} (hj : j<P.k)
    (ht : ∀ i<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*i)) 384)=T i)
    (h : DecodeInv P L s₀ mD T Y v j s) :
    WP isa (dec12At (slotReg kE) (eo+384*j) (aOff P 0 j)) s (DecodeInv P L s₀ mD T Y v (j+1)) := by
  have hw := hp.wf
  have h0 : 0<P.k := hw.facts.1
  have hs : L.slot kE ≠ L.sc := by have := hp.scw; omega
  have hmul := mul_succ_le (a := 384) hj
  refine WP.mono (dec12_ok hp (k := kE) (o := eo+384*j) hkE (by omega)
    (po_a hw h0 hj) (.inl hs) h.kb) fun t ⟨kt,ft,pt,xt⟩ => ?_
  rw [h.kb.ro_bytes hread (by omega),ht j hj] at pt
  refine ⟨kt,xt.trans h.x24,?_,?_,?_⟩
  · intro i hi
    rcases (by omega : i<j ∨ i=j) with hi | rfl
    · exact polyIs_frame ft (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact papart hp (po_a hw h0 (by omega)) (po_a hw h0 hj) (.inl (by lom))) (h.decoded i hi)
    · exact pt
  · intro i hi
    exact polyIs_frame ft (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact papart hp (po_y hw hi) (po_a hw h0 hj) (.inr (by
        have := Nat.mul_le_mul_right P.k hw.facts.1
        lom))) (h.y i hi)
  · exact (h.frame.sub (fun r hh => by
      rw [List.mem_singleton.mp hh]
      exact ⟨_,List.mem_singleton_self _,R.sub2 (by omega) (by omega)⟩)).trans
      (ft.sub (fun r hh => by
        rw [List.mem_singleton.mp hh]
        exact ⟨_,List.mem_singleton_self _,R.sub2 (by simp [aOff]) (by simp [aOff]; omega)⟩))

theorem decode_all {s₀ s : State} (hp : Pre P L s₀) {kE eo : Nat}
    (hkE : kE<4) (hread : L.slot kE<L.nrd) (hfit : eo+384*P.k≤L.len (L.slot kE))
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64}
    (ht : ∀ i<P.k, decode12 (bytesAt s₀.mem (kA s₀ (L.slot kE)+BitVec.ofNat 64 (eo+384*i)) 384)=T i)
    (h : DecodeInv P L s₀ mD T Y v 0 s) :
    WPs ((List.range P.k).map fun j => dec12At (slotReg kE) (eo+384*j) (aOff P 0 j)) s
      (DecodeInv P L s₀ mD T Y v P.k) :=
  WPs.range (fun _ hj _ h => decode_step hp hkE hread hfit hj ht h) h

end VG.Proof.MlKem.AArch64.Kem
