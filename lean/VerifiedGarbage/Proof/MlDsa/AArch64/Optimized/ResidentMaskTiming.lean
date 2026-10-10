import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskAccess
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ## From `ResidentMaskDecode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def maskPoly (m : Mem) (a : Addr) (d : Nat) : Spec.MlDsa.Poly :=
  Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack (Spec.MlDsa.H (Spec.Sha3.bytesAt m a 66) (32*d))
    (2^(d-1)-1) (2^(d-1)))

def Decoded (σ t : State) (d : Nat) : Prop := Env σ t ∧
  Spec.MlDsa.PolyIs t.mem (σ.gpr .x2) (maskPoly σ.mem (σ.gpr .x0) d) ∧
  Spec.MlDsa.PolyIs t.mem (σ.gpr .x3) (maskPoly σ.mem (σ.gpr .x0+66) d)

theorem decode_ok {σ s : State} {d : Nat} (hp : Pre σ) (hd : d=18 ∨ d=20)
    (hs : SpongePost σ s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentMask.parseBoth d) s fun t => Decoded σ t d := by
  obtain ⟨he,hleft,hright⟩ := hs
  refine WP.mono (parseBoth_ok s hd (pairAccess_ok hp he hd)) ?_
  intro t ht
  have hk : RegKeep [.x0,.x4,.x9,.x11] s t := by
    refine ⟨?_,ht.rd,ht.wr,ht.sp⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact ht.gpr r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hf : Frame [⟨σ.gpr .x2,1024⟩,⟨σ.gpr .x3,1024⟩] s.mem t.mem := by
    simpa only [he.out1,he.out2] using ht.frame
  have ho : ∀ r∈[Region.mk (σ.gpr .x2) 1024,⟨σ.gpr .x3,1024⟩],
      (Region.mk (σ.gpr .x4) 8192).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.out1Sep.symm
    · exact hp.out2Sep.symm
  refine ⟨he.step hk hf (by decide) ?_ ?_ ?_,?_,?_⟩
  · intro r hr; exact ⟨r,List.mem_cons_of_mem _ hr,fun _ hx => hx⟩
  · intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by decide))
  · intro r hr
    exact (ho r hr).sub_left (Offset.sub_base _ (by decide))
  · have hv := ht.left.poly hd
    rw [he.out1,he.base] at hv
    rw [seedState_eq] at hleft
    rw [stream_mask_bytes hd (VG.Proof.Sha3.bytesAt_length _ _ _) hleft] at hv
    exact hv
  · have hv := ht.right.poly hd
    rw [he.out2,he.base] at hv
    rw [seedState_eq] at hright
    rw [stream_mask_bytes hd (VG.Proof.Sha3.bytesAt_length _ _ _) hright] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentMaskDispatch.lean` -/

section

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

end

/-! ## From `ResidentMaskCorrect.lean` -/

section

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

end

/-! ## From `ResidentMaskTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_ldrw wp_lsr)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (parseBoth epi rawWith)

def publicRegs : VG.AArch64.Taint.T := Taint.ofRegs [.x0,.x2,.x3,.x4]
def publicInputs (s t : State) : Prop := VG.AArch64.Taint.Agree publicRegs s t ∧
  (s.gpr .x1).setWidth 32=(t.gpr .x1).setWidth 32
def gammaCode : Prog isa := .block [.ldr .w .x27 .x19 7904,.lsr .x .x9 .x27 18]
def afterGamma : Prog isa := .seq (.ite (.zero .x .x9) (parseBoth 18) (parseBoth 20)) (.block epi)
def gammaValue (σ : State) : BitVec 64 := (σ.gpr .x1).setWidth 32 |>.setWidth 64 |>.ushiftRight 18

theorem gamma_ok {σ s : State} (hp : Pre σ) (he : Env σ s) :
    WP isa gammaCode s fun t => Env σ t ∧ t.gpr .x9=gammaValue σ := by
  refine wp_ldrw (a := σ.gpr .x4+7904) ⟨by decide,by decide⟩ (by rw [he.base]; rfl)
    (by rw [he.rd,he.wr]
        exact ⟨_,List.mem_append_right _ hp.scratch,Offset.contains_base _ (by decide) (by decide)⟩)
    fun a ha ea => wp_lsr (by decide) fun t ht et => WP.block_nil_iff.mpr ?_
  have hk := (ha.trans ht).mono (rs' := [.x27,.x9]) (by simp)
  refine ⟨he.lowStep (RegKeep.only hk) (W := [])
    (by rw [ht.mem,ha.mem]; exact Frame.refl _ _) (by decide) (by simp),?_⟩
  rw [et,ea,he.gamma]; rfl

private theorem afterGamma_ct :
    RelCT isa (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x21,.x22,.x9])) afterGamma (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x19,.x21,.x22,.x9]) (fun _ _ h => h) (by taint_decide)

/-- A public gamma value may make a memory round trip; the seeds and all
SHAKE lanes remain secret. The correctness invariant recovers only gamma. -/
theorem rawWith_ct (core : Resident.Core)
    (hc : RelCT isa (VG.AArch64.Taint.Agree publicRegs) (beforeDispatch core.code) (fun _ _ => True)) :
    ConstantTime isa Pre publicInputs (rawWith core.code) := by
  intro σ τ tr1 tr2 u v hp hq hpub e1 e2
  have front : RelCT isa (fun s t => s=σ ∧ t=τ) (beforeDispatch core.code)
      (fun s t => Env σ s ∧ Env τ t) := by
    apply RelCT.mono (RelCT.wp (F₁ := SpongePost σ) (F₂ := SpongePost τ) (RelCT.mono hc (fun s t h => by rcases h with ⟨rfl,rfl⟩; exact hpub.1)
      (fun _ _ _ => True.intro)) ?_) (fun _ _ h => h) (fun _ _ h => ⟨h.2.1.1,h.2.2.1⟩)
    intro s t h
    rw [h.1,h.2]
    exact ⟨beforeDispatch_ok core σ hp,beforeDispatch_ok core τ hq⟩
  have gamma : RelCT isa (fun s t => Env σ s ∧ Env τ t) gammaCode
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x21,.x22,.x9])) := by
    have check : RelCT isa (fun s t => Env σ s ∧ Env τ t) gammaCode (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x19]) (fun s t h => by
        refine ⟨h.1.sp.trans (hpub.1.1.trans h.2.sp.symm),?_⟩
        intro r hr; simp only [Taint.mem_ofRegs,List.mem_singleton] at hr; subst r
        exact h.1.base.trans ((hpub.1.2 .x4 (by simp [publicRegs])).trans h.2.base.symm)) (by taint_decide)
    apply RelCT.mono (RelCT.wp check (fun _ _ h => ⟨gamma_ok hp h.1,gamma_ok hq h.2⟩))
      (fun _ _ h => h) ?_
    intro s t ⟨_,⟨hs,h9s⟩,⟨ht,h9t⟩⟩
    refine ⟨hs.sp.trans (hpub.1.1.trans ht.sp.symm),?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.base.trans ((hpub.1.2 .x4 (by simp [publicRegs])).trans ht.base.symm)
    · exact hs.out1.trans ((hpub.1.2 .x2 (by simp [publicRegs])).trans ht.out1.symm)
    · exact hs.out2.trans ((hpub.1.2 .x3 (by simp [publicRegs])).trans ht.out2.symm)
    · rw [h9s,h9t,gammaValue,gammaValue,hpub.2]
  have all := RelCT.assoc (RelCT.seq front (RelCT.seq gamma afterGamma_ct))
  exact (all _ _ _ _ _ _ ⟨rfl,rfl⟩ e1 e2).1

private theorem original_front_ct :
    RelCT isa (VG.AArch64.Taint.Agree publicRegs)
      (beforeDispatch Resident.originalCore.code) (fun _ _ => True) :=
  RelCT.taint (A := taint) publicRegs (fun _ _ h => h) (by taint_decide)

private theorem n2_front_ct :
    RelCT isa (VG.AArch64.Taint.Agree publicRegs)
      (beforeDispatch Resident.n2Core.code) (fun _ _ => True) :=
  RelCT.taint (A := taint) publicRegs (fun _ _ h => h) (by taint_decide)

theorem raw_ct : ConstantTime isa Pre publicInputs
    Impl.MlDsa.AArch64.Optimized.ResidentMask.raw :=
  rawWith_ct Resident.originalCore original_front_ct

theorem raw_n2_ct : ConstantTime isa Pre publicInputs
    (rawWith Resident.n2Core.code) := rawWith_ct Resident.n2Core n2_front_ct

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
