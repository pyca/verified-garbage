import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskDispatch

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (rawWith pro zero absorb)

/-- Exact two-seed expansion, including both polynomial outputs, all writes,
and restoration of the public AArch64 calling convention. -/
def Post (σ t : State) (d : Nat) : Prop :=
  abiPreserved σ t ∧ Frame (writes σ) σ.mem t.mem ∧
  Spec.MlDsa.PolyIs t.mem (σ.gpr .x2) (maskPoly σ.mem (σ.gpr .x0) d) ∧
  Spec.MlDsa.PolyIs t.mem (σ.gpr .x3) (maskPoly σ.mem (σ.gpr .x0+66) d) ∧
  t.rd=σ.rd ∧ t.wr=σ.wr

theorem finish_ok {σ s : State} {d : Nat} (hp : Pre σ) (hd : Decoded σ s d) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.ResidentMask.epi) s (fun t => Post σ t d) := by
  obtain ⟨he,hl,hr⟩ := hd
  have access (off : Nat) (hb : off+8≤8192) :
      InRegions (s.rd++s.wr) (σ.gpr .x4+BitVec.ofNat 64 off) 8 := by
    rw [he.rd,he.wr]
    exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ hb (by omega)⟩
  refine WP.mono (epi_ok σ s (σ.gpr .x4) he.base he.sp he.lr he.saved
    (fun i hi => access _ (by omega)) (fun i hi => access _ (by omega))) ?_
  intro t ⟨hab,hm,hrd,hwr⟩
  exact ⟨hab,hm ▸ he.frame,hm ▸ hl,hm ▸ hr,hrd.trans he.rd,hwr.trans he.wr⟩

def beforeDispatch (core : Prog isa) : Prog isa :=
  .seq (.block (pro ++ zero ++ absorb 0 ++
    ([Impl.MlKem.AArch64.mov .x23 .x19,.addImm .x .x24 .x19 840,
      .addImm .x .x25 .x19 1520] : List Instr)))
    (Impl.MlDsa.AArch64.Optimized.Resident.maskPairWith core .x23 .x24 .x25)

theorem beforeDispatch_ok (core : Resident.Core) (σ : State) (hp : Pre σ) :
    WP isa (beforeDispatch core.code) σ (SpongePost σ) := by
  unfold beforeDispatch
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (maskInit_ok σ hp) ?_
  intro a ⟨ha,hpair⟩
  refine WP.mono (spongeArgs_ok a) ?_
  intro b ⟨hb,h23,h24,h25⟩
  have he : Env σ b := ha.lowStep (RegKeep.only hb)
    (W := []) (by rw [hb.mem]; exact Frame.refl _ _) (by decide) (by simp)
  exact (sponge_ok core hp he (by simpa only [hb.mem] using hpair)
    (h23.trans ha.base) (by rw [h24,ha.base]) (by rw [h25,ha.base]))

theorem rawWith_ok (core : Resident.Core) (σ : State) {d : Nat}
    (hp : Pre σ) (hd : d=18 ∨ d=20)
    (hg : (σ.gpr .x1).setWidth 32=BitVec.ofNat 32 (2^(d-1))) :
    WP isa (rawWith core.code) σ (fun t => Post σ t d) := by
  unfold rawWith
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (beforeDispatch_ok core σ hp)) ?_
  intro a ha
  apply WP.seq
  refine WP.mono ha ?_
  intro s hs
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (dispatch_ok hp hd hg hs)) ?_
  intro t ht
  exact WP.seq (WP.mono ht fun _ h => finish_ok hp h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
