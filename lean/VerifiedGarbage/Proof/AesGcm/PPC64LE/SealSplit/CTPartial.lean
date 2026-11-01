module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Partial
import VerifiedGarbage.Proof.AesGcm.PPC64LE.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Partial

-- separate module: the source's final partial block uses the shared constant-time byte-copy loop.
/-! # Constant time of split-seal text processing -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
open VG VG.PPC64LE


theorem partial_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs publicRegs)
    Impl.AesGcm.PPC64LE.SealSplit.partialCopy h).isSome=true := ⟨_,by taint_decide⟩


theorem partial_si {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64} {s : State}
    (hs : SI c st w sp R A D N S count s) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.partialCopy s (SI c st w sp R A D N S count) := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata,lay⟩ := hs
  have cfg : PartialCopy.Config s N.toNat count := by
    refine ⟨by rw [← hn]; exact lay.bound,N.isLt,lay.countReg,?_,?_,?_⟩
    · rw [lay.source]; exact lay.reads
    · rw [he.fr .r27 (by decide),hd]; exact hdata.wr
    · rw [lay.source,he.fr .r27 (by decide),← hn]; exact lay.data
  refine WP.mono (PartialCopy.ok s _ _ cfg) fun t ht => ?_
  obtain ⟨heT,layT⟩ := partial_env_layout he lay ht
  exact ⟨V,hc,hst,hw,hR,ha,hd,hn,heT,hdata.of_eq ht.keep.2.1 ht.keep.2.2,layT⟩


theorem whole_bi [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64} {s : State}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) (hs : SI c st w sp R A D N S count s) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.whole s (SealFusedCT.BI c st w sp R A D N) := by
  obtain ⟨V,hc,hst,hw,hR,ha,hd,hn,he,hdata,lay⟩ := hs
  have hds : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat := by
    rw [hc,hst,hw,hd,hn]; exact hdata
  refine WP.mono (WP.with_rdwr (SealSplit.whole_ok (L.v hc hst hw) he hds lay hR hv)) fun t ⟨ho,rd,wr,_⟩ => ?_
  exact ⟨V,hc,hst,hw,hR,ha,hd,hn,ho.env,hdata.of_eq rd wr⟩


theorem partial_finish_ct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {c st w sp : Addr} {R count : Nat} {A D N S : BitVec 64}
    (L : Lay c st w) (hv : R=10 ∨ R=12 ∨ R=14) :
    CT (SI c st w sp R A D N S count)
      (.seq Impl.AesGcm.PPC64LE.SealSplit.partialCopy
        (.seq Impl.AesGcm.PPC64LE.SealSplit.whole
          (.seq (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) Impl.AesGcm.PPC64LE.cryptTail)
            (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0))))) := by
  obtain ⟨_,hp⟩ := partial_taint
  exact CT.seq (CT.taint publicRegs (fun _ _ => si_agree) hp) (fun _ => partial_si)
    (CT.seq (whole_ct L hv) (fun _ => whole_bi L hv)
      (CT.seq (SealFusedCT.tail_ct L hv) (fun _ => SealFusedCT.tail_gi L hv) (SealFusedCT.absorb_fin_ct L hv)))

end VG.Proof.AesGcm.PPC64LE.SealSplit.CTBlocks
