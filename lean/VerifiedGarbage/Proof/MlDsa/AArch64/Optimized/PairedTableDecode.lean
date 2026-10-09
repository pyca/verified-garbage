import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

theorem Words.layer1 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g)) 16) e=BitVec.ofNat 32 (z (255-16*u-4*g-e)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+0+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (255-16*u-4*g-e))) := by
  exact h.row (by decide) he (by omega) (layer1_values hu hg he)

theorem Words.layer2 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g)) 16) e=BitVec.ofNat 32 (z (127-8*u-2*g-e/2)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+128+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (127-8*u-2*g-e/2))) := by
  exact h.row (by decide) he (by omega) (layer2_values hu hg he)

theorem Words.layer4 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g)) 16) e=BitVec.ofNat 32 (z (63-4*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+256+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (63-4*u-g))) := by
  exact h.row (by decide) he (by omega) (layer4_values hu hg he)

theorem Words.layer8 {m : Mem} {p : Addr} (h : Words m p)
    {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g)) 16) e=BitVec.ofNat 32 (z (31-2*u-g)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+384+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z (31-2*u-g))) := by
  exact h.row (by decide) he (by omega) (layer8_values hu hg he)

theorem Words.layer16 {m : Mem} {p : Addr} (h : Words m p)
    {u e : Nat} (hu : u<8) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+448)) 16) e=BitVec.ofNat 32 (z (15-u)) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+464)) 16) e=BitVec.ofNat 32 (bar (z (15-u))) := by
  exact h.row (g := 0) (off := 448) (by decide) he (by omega) (layer16_values hu he)

theorem Words.tail {m : Mem} {p : Addr} (h : Words m p)
    {j e : Nat} (hj : j<8) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (3840+32*j)) 16) e=BitVec.ofNat 32 (tailRoot j) ∧
    vword (m.read (p+BitVec.ofNat 64 (3840+32*j+16)) 16) e=BitVec.ofNat 32 (bar (tailRoot j)) := by
  have hv := tail_values hj he
  have h0 : 3840+32*j=4*(960+8*j) := by omega
  have h1 : 3840+32*j+16=4*(960+8*j+4) := by omega
  constructor
  · rw [h0,h.vector (by omega) he,hv.1]
  · rw [h1,h.vector (by omega) he,show 960+8*j+4+e=960+8*j+e+4 by omega,hv.2]

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable
