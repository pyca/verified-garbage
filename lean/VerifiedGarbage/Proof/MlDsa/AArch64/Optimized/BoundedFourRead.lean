import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCompact

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices)

def TableAt (m : Mem) (base : Addr) : Prop := ∀mask<16,
 m.read (base+BitVec.ofNat 64 (64*mask)) 16=shuffleWord mask ∧
 m.readW (base+BitVec.ofNat 64 (64*mask)+32) 64=BitVec.ofNat 64 (acceptedIndices mask).length

theorem TableAt.frame {m m' : Mem} {base : Addr} {rs : List Region} (h : TableAt m base)
    (hf : Frame rs m m') (hd : ∀r∈rs,(⟨base,1024⟩ : Region).Disjoint r) : TableAt m' base := by
  intro mask hm
  constructor
  · rw [hf.read (Offset.contains_base base (by omega : 64*mask+16≤1024) (by omega)) hd (by decide)]
    exact (h mask hm).1
  · have ha : base+BitVec.ofNat 64 (64*mask)+32=base+BitVec.ofNat 64 (64*mask+32) := by
      rw [BitVec.add_assoc,BitVec.ofNat_add]
      rfl
    rw [ha,hf.readW (Offset.contains_base base (by omega : 64*mask+32+8≤1024) (by omega)) hd (by decide),←ha]
    exact (h mask hm).2

private theorem maskShift : ∀m<16,(BitVec.ofNat 64 m<<<6)=BitVec.ofNat 64 (64*m) := by decide

theorem tableAddress_ok {s : State} {p : Addr} {mask : Nat} (hm : mask<16)
    (h12 : s.gpr .x12=p) (h6 : s.gpr .x6=BitVec.ofNat 64 mask) :
    WP isa (.block [.lsl .x .x6 .x6 6,.add .x .x13 .x12 .x6]) s fun t=>
      ((t.gpr .x13=p+BitVec.ofNat 64 (64*mask) ∧ t.mem=s.mem) ∧
        Keep [.x6,.x13] s t) ∧ t.v=s.v := by
  apply WP.keepV (by decide)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [h12,h6,maskShift mask hm]

theorem tableRead_ok {s : State} {p : Addr} {mask : Nat} (hm : mask<16)
    (ht : TableAt s.mem p) (ha : s.gpr .x13=p+BitVec.ofNat 64 (64*mask))
    (hr : InRegions (s.rd++s.wr) (s.gpr .x13) 16)
    (hc : InRegions (s.rd++s.wr) (s.gpr .x13+32) 8) :
    WP isa (.block [.ldrq .v6 .x13 0,.ldr .x .x6 .x13 32]) s fun t=>
      Keep [.x6] s t ∧ t.mem=s.mem ∧ t.v .v6=shuffleWord mask ∧
      t.gpr .x6=BitVec.ofNat 64 (acceptedIndices mask).length ∧
      (∀r,r≠.v6→t.v r=s.v r) := by
  refine wp_ldrq (by decide) (by simp) hr fun a hv=>?_
  have hr' : InRegions (a.rd++a.wr) (a.gpr .x13+32) 8 := by
    rw [hv.rd,hv.wr,hv.gpr]; exact hc
  have hh : WP isa (.block [.ldr .x .x6 .x13 32]) a fun t=>
      (Only [.x6] a t ∧ t.gpr .x6=a.mem.readW (a.gpr .x13+32) 64) ∧ t.v=a.v :=
    WP.keepV (by decide) (wp_ldrx (by decide) rfl hr' fun t hk hc=>wp_nil ⟨hk,hc⟩)
  refine WP.mono hh fun t ⟨⟨hk,hc⟩,hvec⟩=>?_
  refine ⟨(hv.chg.keep.trans hk.keep).mono (by decide),hk.mem.trans hv.mem,?_,?_,?_⟩
  · rw [hvec,hv.v,ha]; exact (ht mask hm).1
  · rw [hc,hv.mem,hv.gpr,ha]; exact (ht mask hm).2
  · intro r hr
    rw [hvec,hv.other r hr]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
