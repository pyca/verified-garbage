import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskDecode

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrw wp_lsr)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (parseBoth)

/-- The width branch depends only on the saved public gamma parameter. -/
theorem dispatch_ok {σ s : State} {d : Nat} (hp : Pre σ) (hd : d=18 ∨ d=20)
    (hg : (σ.gpr .x1).setWidth 32=BitVec.ofNat 32 (2^(d-1))) (hs : SpongePost σ s) :
    WP isa (.seq (.block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18])
      (.ite (.zero .x .x9) (parseBoth 18) (parseBoth 20))) s (fun t => Decoded σ t d) := by
  obtain ⟨he,hleft,hright⟩ := hs
  apply WP.seq
  refine wp_ldrw (a := σ.gpr .x4+7904) ⟨by decide,by decide⟩ (by rw [he.base]; rfl)
    (by rw [he.rd,he.wr]
        exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ (by decide) (by decide)⟩)
    fun a ha ea => wp_lsr (by decide) fun t ht et => WP.block_nil_iff.mpr ?_
  have hk := (ha.trans ht).mono (rs' := [.x27,.x9]) (by simp)
  have hm : t.mem=s.mem := ht.mem.trans ha.mem
  have he' : Env σ t := he.lowStep (RegKeep.only hk)
    (rs := [.x27,.x9]) (W := []) (by rw [hm]; exact Frame.refl _ _)
    (by decide) (by simp)
  have hs' : SpongePost σ t := ⟨he',by simpa only [hm] using hleft,by simpa only [hm] using hright⟩
  have hx : t.gpr .x9 = (BitVec.ofNat 32 (2^(d-1))).setWidth 64 >>> 18 := by
    rw [et,ea,he.gamma,hg]
  rcases hd with rfl | rfl
  · refine WP.ite (M := isa) true ?_ (fun _ => decode_ok hp (.inl rfl) hs') (fun h => nomatch h)
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hx]
    rfl
  · refine WP.ite (M := isa) false ?_ (fun h => nomatch h) (fun _ => decode_ok hp (.inr rfl) hs')
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hx]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
