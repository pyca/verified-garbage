module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.PairTail
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
import VerifiedGarbage.Proof.Framework.Offset

/-! # Complete paired-noise operation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def outOff (L : KemLay) (kg : Bool) (n : Nat) : Nat :=
 if n<L.k then (if kg then KG.sOff L n else KEM.yOff L n) else Impl.MlKem.AArch64.Noise.noiseOff L (n-L.k)
def transformed (L : KemLay) (kg : Bool) (n : Nat) : Bool := kg || n<L.k

theorem TailSetup.regions {s t : State} {p f g w : Addr} (h : TailSetup s p f g w)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) : TailSetup t p f g w := by
  rcases h with ⟨a,b,c,d,e,f,g,j,k,l,m,n,o,q,r,v⟩
  exact ⟨by simpa only [hr,hw] using a,by simpa only [hw] using b,
    by simpa only [hw] using c,by simpa only [hw] using d,by simpa only [hr,hw] using e,
    by simpa only [hr,hw] using f,by simpa only [hr,hw] using g,
    by simpa only [hw] using j,by simpa only [hw] using k,l,m,n,o,q,r,v⟩

theorem noisePair_ok {s : State} {L : KemLay} (kg : Bool) {n : Nat} {p a f g w : Addr}
    (hn : n+1<256)
    (h0 : outOff L kg n <65536) (h1 : outOff L kg (n+1)<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SS else KEM.SS)=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SG else KEM.RB)=a)
    (hf : s.gpr .x28+BitVec.ofNat 64 (outOff L kg n)=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 (outOff L kg (n+1))=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.NS else KEM.NS)=w)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hsv : ∀j<6, InRegions s.wr (p+BitVec.ofNat 64 (1800+8*j)) 8)
    (has : (Region.mk a 32).Disjoint (savedR p))
    (hap : (Region.mk a 32).Disjoint (pairR p))
    (hs : TailSetup s p f g w) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePair L kg n) s fun t =>
      Kept (pairWrites p f g w) s t ∧
      Proof.MlKem.PolyIs t.mem f (sampled s.mem a n (transformed L kg n)) ∧
      Proof.MlKem.PolyIs t.mem g (sampled s.mem a (n+1) (transformed L kg (n+1))) := by
  change WP isa (.seq (.block (Impl.MlKem.AArch64.Noise.noiseInit L kg n))
    (seqs [Impl.MlKem.AArch64.Noise.squeezePair,
      outCode (outOff L kg n) (if kg then KG.NS else KEM.NS) 400 (transformed L kg n),
      outCode (outOff L kg (n+1)) (if kg then KG.NS else KEM.NS) 528 (transformed L kg (n+1)),
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))])) s _
  refine WP.seq (WP.mono (init_ok (by cases kg <;> decide) hn
    (by cases kg <;> decide) (by cases kg <;> decide) hp ha hin hwr hsv has hap
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku,fu,sv,h19,h20,h21,pair⟩ => ?_)
  have pu : Partial (pairWrites p f g w) s u :=
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,ku.vcs,
      fu.mono (by simp [pairWrites])⟩
  exact pair_tail_ok (transformed L kg n) (transformed L kg (n+1)) hn h0 h1
    (by cases kg <;> decide) pu sv h19 h20 h21
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hg)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    (hs.regions ku.rd ku.wr) pair

end VG.Proof.MlKem.AArch64.Noise
