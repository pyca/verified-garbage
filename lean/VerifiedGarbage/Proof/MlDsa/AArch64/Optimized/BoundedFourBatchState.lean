import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchGeometry

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64 (Keep)

theorem Layout.frame {s t : State} {table p q : Addr} {X : List Byte} (h : Layout s table p q X)
    {regs : List Reg} {rs : List Region} (hk : Keep regs s t) (hf : Frame rs s.mem t.mem)
    (ha : ∀r∈rs,(⟨q,X.length+2⟩ : Region).Disjoint r) : Layout t table p q X := by
  rcases h with ⟨hs,he,hx,ho,ht,hr,htr,hw⟩
  refine ⟨hs,he,?_,ho,ht,by simpa only [hk.rd,hk.wr] using hr,
    by simpa only [hk.rd,hk.wr] using htr,by simpa only [hk.wr] using hw⟩
  intro i hi
  rw [hf.bytes ha (by change X.length+2≤2^64; omega) (by change i<X.length+2; omega)]
  exact hx i hi

theorem ScalarLayout.frame {s t : State} {p q : Addr} {X : List Byte} (h : ScalarLayout s p q X)
    {regs : List Reg} {rs : List Region} (hk : Keep regs s t) (hf : Frame rs s.mem t.mem)
    (ha : ∀r∈rs,(⟨q,X.length+2⟩ : Region).Disjoint r) : ScalarLayout t p q X := by
  rcases h with ⟨hs,hx,ho,hr,hw⟩
  refine ⟨hs,?_,ho,by simpa only [hk.rd,hk.wr] using hr,by simpa only [hk.wr] using hw⟩
  intro i hi
  rw [hf.bytes ha (by change X.length+2≤2^64; omega) (by change i<X.length+2; omega)]
  exact hx i hi

structure BatchLayout (σ : State) (b p : Addr) (off : Nat) (X : Nat→List Byte) : Prop where
 length : ∀i<4,(X i).length=272
 vector : ∀i<4,Layout σ (b+6000) (outputAt p i) (inputAt b i off) (X i)
 scalar : ∀i<4,ScalarLayout σ (outputAt p i) (inputAt b i off) (X i)
 streamsApart : ∀i<4,∀r∈batchWrites b p,(⟨inputAt b i off,(X i).length+2⟩ : Region).Disjoint r
 tableApart : ∀r∈batchWrites b p,(⟨b+6000,1024⟩ : Region).Disjoint r
 outputCount : ∀i<4,∀j<4,(polyR (outputAt p i)).Disjoint ⟨countAt b j,8⟩
 countRead : ∀i<4,InRegions (σ.rd++σ.wr) (countAt b i) 8
 countWrite : ∀i<4,InRegions σ.wr (countAt b i) 8

structure BatchFields (m : Mem) (b p : Addr) (L : Nat→List Zq) : Prop where
 bound : ∀i<4,(L i).length≤256
 stored : ∀i<4,Stored m (outputAt p i) (L i)
 count : ∀i<4,m.readW (countAt b i) 64=BitVec.ofNat 64 (256-(L i).length)

structure BatchInv (σ s : State) (b p : Addr) (L : Nat→List Zq) : Prop where
 keep : Keep (.x0::parserRegs) σ s
 frame : Frame (batchWrites b p) σ.mem s.mem
 base : s.gpr .x19=b
 output : s.gpr .x21=p
 table : TableAt s.mem (b+6000)
 fields : BatchFields s.mem b p L

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
