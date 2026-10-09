import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackSpec

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.HighPack
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep)

structure PackConstants (s : State) : Prop where
  zero : s.v .v28=0
  idx29 : s.v .v29=ofVDwords 0x0908060504020100 0xffffffff0e0d0c0a
  idx24 : s.v .v24=ofVDwords 0xffff0504ffff0100 0xffff0d0cffff0908
  idx25 : s.v .v25=ofVDwords 0xffff0706ffff0302 0xffff0f0effff0b0a

structure PackReady (g : Nat) (s : State) : Prop extends HighConstants g s, PackConstants s

def packedVector (width : Nat) (s : State) : BitVec 128 :=
  if width=4 then packed4 s else packed6 s

structure TailPost (g : Nat) (s t : State) : Prop where
  keep : Keep [.x9] s t
  vec : ∀ r, r∉[.v4,.v5,.v6] → t.v r=s.v r
  ready : PackReady g t
  frame : Frame [⟨s.gpr .x1,2*packWidth g⟩] s.mem t.mem
  bytes : ∀ i<2*packWidth g, t.mem (s.gpr .x1+BitVec.ofNat 64 i)=
    vbyte (packedVector (packWidth g) s) i

/-- The tail's exact register and memory effects, shared by both parameter choices. -/
theorem tailPost_of_store {g : Nat} (hg : IsG g) {s t : State} (hc : PackReady g s)
    (hk : Keep [.x9] s t) (hv : ∀ r, r∉[.v4,.v5,.v6] → t.v r=s.v r)
    (hm : t.mem=storePacked (packWidth g) s.mem (s.gpr .x1) (packedVector (packWidth g) s)) :
    TailPost g s t := by
  have hw : packWidth g=4 ∨ packWidth g=6 := by rcases hg with rfl | rfl <;> decide
  refine ⟨hk,hv,?_,?_,?_⟩
  · refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_,?_,?_⟩⟩
    · rw [hv .v17 (by decide)]; exact hc.add
    · rw [hv .v18 (by decide)]; exact hc.mul
    · rw [hv .v19 (by decide)]; exact hc.round
    · rw [hv .v20 (by decide)]; exact hc.modulus
    · rw [hv .v28 (by decide)]; exact hc.zero
    · rw [hv .v29 (by decide)]; exact hc.idx29
    · rw [hv .v24 (by decide)]; exact hc.idx24
    · rw [hv .v25 (by decide)]; exact hc.idx25
  · rw [hm]; exact storePacked_frame _ _ _ hw
  · intro i hi; rw [hm]; exact storePacked_byte _ _ _ hw hi

theorem packTail_ok {g : Nat} (hg : IsG g) {s : State} (hc : PackReady g s)
    (hw8 : InRegions s.wr (s.gpr .x1) 8)
    (hw4 : packWidth g=6 → InRegions s.wr (s.gpr .x1+8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, TailPost g s t → WP isa (.block rest) t Q) :
    WP isa (.block (packTail (packWidth g) ++ rest)) s Q := by
  have hw : packWidth g=4 ∨ packWidth g=6 := by rcases hg with rfl | rfl <;> decide
  rcases hw with hw | hw
  · rw [hw]
    refine packTail4_ok hw8 fun t ht hv hm => k t (tailPost_of_store hg hc ht hv ?_)
    simpa only [hw,storePacked,packedVector,ite_true] using hm
  · rw [hw]
    refine packTail6_ok hw8 (hw4 hw) fun t ht hv hm => k t (tailPost_of_store hg hc ht hv ?_)
    simpa only [hw,storePacked,packedVector,show ¬(6:Nat)=4 by decide,ite_false] using hm


/-- Initialize the arithmetic and packing tables together, with exact frames. -/
theorem setup_ready (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (constants g ++ packSetup)) s fun t =>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] s t ∧
      PackReady g t := by
  rw [WP.block_append_iff]
  refine WP.mono (constants_ready s hg) fun a ha => ?_
  refine WP.mono (packSetup_ok a) fun t ht => ?_
  refine ⟨ha.1.trans ht.1,⟨?_,?_,?_,?_⟩,⟨ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩⟩
  · rw [ht.1.vec .v17 (by decide)]; exact ha.2.add
  · rw [ht.1.vec .v18 (by decide)]; exact ha.2.mul
  · rw [ht.1.vec .v19 (by decide)]; exact ha.2.round
  · rw [ht.1.vec .v20 (by decide)]; exact ha.2.modulus

/-- Arithmetic temporaries never overlap the setup vectors. -/
theorem PackReady.afterLoads {g : Nat} {s t : State} (h : PackReady g s)
    (k : VG.Proof.MlKem.AArch64.VChg [.v0,.v1,.v2,.v3,.v7] s t) : PackReady g t := by
  refine ⟨h.toHighConstants.chg k (by decide) (by decide) (by decide) (by decide),⟨?_,?_,?_,?_⟩⟩
  · rw [k.get .v28]; exact h.zero
  · rw [k.get .v29]; exact h.idx29
  · rw [k.get .v24]; exact h.idx24
  · rw [k.get .v25]; exact h.idx25

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
