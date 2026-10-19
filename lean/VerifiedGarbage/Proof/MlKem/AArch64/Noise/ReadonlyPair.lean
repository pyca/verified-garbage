module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyPairTail
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Pair
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Complete paired-noise operation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Spec.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem readonly_noisePair_ok {w16 : Bool} {s : State} {L : KemLay} (kg : Bool) {n : Nat} {p a f g w : Addr}
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
    (hs : TailSetup s p f g w)
    (ht0 : Ntt16.Readonly.TableReady s "VG_MLKEM_NTT16_ZETAS" Ntt16.tableHalves f w)
    (ht1 : Ntt16.Readonly.TableReady s "VG_MLKEM_NTT16_ZETAS" Ntt16.tableHalves g w)
    (hfar : ∀r∈pairWrites p f g w,(Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith (Ntt16.Readonly.nttAtR w16) L kg n w16) s fun t =>
      Kept (pairWrites p f g w) s t ∧
      PolyIsW (cw w16) t.mem f (sampled s.mem a n (transformed L kg n)) ∧
      PolyIsW (cw w16) t.mem g (sampled s.mem a (n+1) (transformed L kg (n+1))) := by
  change WP isa (.seq (.block (Impl.MlKem.AArch64.Noise.noiseInit L kg n))
    (seqs [Impl.MlKem.AArch64.Noise.squeezePair,
      outCodeWith (Ntt16.Readonly.nttAtR w16) (outOff L kg n) (if kg then KG.NS else KEM.NS) 400 (transformed L kg n) w16,
      outCodeWith (Ntt16.Readonly.nttAtR w16) (outOff L kg (n+1)) (if kg then KG.NS else KEM.NS) 528 (transformed L kg (n+1)) w16,
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))])) s _
  refine WP.seq (WP.mono_syms (init_ok (by cases kg <;> decide) hn
    (by cases kg <;> decide) (by cases kg <;> decide) hp ha hin hwr hsv has hap
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku,fu,sv,h19,h20,h21,pair⟩ us => ?_)
  have pu : Partial (pairWrites p f g w) s u :=
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,ku.vcs,
      fu.mono (by simp [pairWrites])⟩
  have t0 := ht0.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  have t1 := ht1.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  exact readonly_pair_tail_ok (transformed L kg n) (transformed L kg (n+1)) hn h0 h1
    (by cases kg <;> decide) pu sv h19 h20 h21
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hg)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    (hs.regions ku.rd ku.wr) pair t0 t1 (by simpa only [us] using hfar)

end VG.Proof.MlKem.AArch64.Noise
