module
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open Optimized
variable {P : KemLay} {L : Layout}

theorem transform_enc_far {s₀ s : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) (hk : KB P L s₀ s) (ht : TransformTables s) :
    ∀r∈encW P L s₀ kC co,
      (Region.mk (s.syms "VG_MLKEM_NTT16_ZETAS") 512).Disjoint r ∧
      (Region.mk (s.syms "VG_MLKEM_INTT16_ZETAS") 512).Disjoint r ∧ (NttR.fastRegion s).Disjoint r := by
  have hw := hp.wf
  have cover {o n : Nat} (h : o+n≤SV P+48) : Covers [R (kA s₀) L.sc o n] s.wr :=
    cov_w hp hk ⟨hp.scw,hp.scb⟩ (hp.fs h)
  have far {r : Region} (hc : Covers [r] s.wr) :=
    And.intro (ht.forward.apart hc) (And.intro (ht.inverse.apart hc) (ht.fast.apart hc))
  intro r hr
  simp only [encW,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · exact far (cover (by lom))
  · exact far (cover (by lom))
  · exact far (cover (by lom))
  · simpa only [hk.sp] using And.intro ht.forwardStack (And.intro ht.inverseStack ht.fastStack)
  · exact far (cov_w hp hk ⟨A.wC,hp.slots _ A.hkC⟩ A.fC)

theorem transform_enc_frame {s₀ s t : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) (hk : KB P L s₀ s) (hk' : KB P L s₀ t)
    (ht : TransformTables s) (hs : t.syms=s.syms)
    (hf : Frame (encW P L s₀ kC co) s.mem t.mem) : TransformTables t :=
  ht.frameFar hs (hk'.rd.trans hk.rd.symm) (hk'.wr.trans hk.wr.symm)
    (hk'.sp.trans hk.sp.symm) hf (transform_enc_far hp A hk ht)
end VG.Proof.MlKem.AArch64.Kem
