import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbArgs

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (pro zero absorb)

theorem Env.lowStep {σ s t : State} {rs : List Reg} {W : List Region} (h : Env σ s)
    (hk : RegKeep rs s t) (hf : Frame W s.mem t.mem)
    (hregs : ∀ r∈[Reg.x19,.x20,.x21,.x22,.x30],r∉rs)
    (hsub : ∀ r∈W, r.Sub ⟨σ.gpr .x4,7904⟩) : Env σ t := by
  refine h.step hk hf hregs ?_ ?_ ?_
  · intro r hr
    exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],fun x hx =>
      (Region.sub_prefix (by decide : 7904≤8192)) x (hsub r hr x hx)⟩
  · intro r hr
    have hh : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 7968) 144).Disjoint ⟨σ.gpr .x4,7904⟩ := by
      simpa only [BitVec.add_zero] using Offset.disjoint (σ.gpr .x4) (d := 7968) (n := 144) (e := 0) (k := 7904)
        (Or.inr (by decide)) (by decide) (by decide)
    exact hh.sub_right (hsub r hr)
  · intro r hr
    have hh : (Region.mk (σ.gpr .x4+BitVec.ofNat 64 7904) 4).Disjoint ⟨σ.gpr .x4,7904⟩ := by
      simpa only [BitVec.add_zero] using Offset.disjoint (σ.gpr .x4) (d := 7904) (n := 4) (e := 0) (k := 7904)
        (Or.inr (by decide)) (by decide) (by decide)
    exact hh.sub_right (hsub r hr)

theorem Env.seedBytes {σ s : State} (hp : Pre σ) (h : Env σ s) {p : Nat} (hpn : p<2) :
    Spec.Sha3.bytesAt s.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) 66 =
      Spec.Sha3.bytesAt σ.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) 66 := by
  apply List.ext_getElem
  · rw [VG.Proof.MlKem.bytesAt_length,VG.Proof.MlKem.bytesAt_length]
  · intro i hi _
    rw [VG.Proof.MlKem.bytesAt_length] at hi
    rw [VG.Proof.MlKem.bytesAt_getElem,VG.Proof.MlKem.bytesAt_getElem,Offset.add_add]
    exact h.frame.bytes (R := ⟨σ.gpr .x0,132⟩) (i := 66*p+i) hp.seedSep (by change 132≤2^64; decide) (by change 66*p+i<132; omega)

theorem Env.seedState {σ s : State} (hp : Pre σ) (h : Env σ s) {p : Nat} (hpn : p<2) :
    seedState s.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p))=
      seedState σ.mem (σ.gpr .x0+BitVec.ofNat 64 (66*p)) := by
  rw [seedState_eq,seedState_eq,h.seedBytes hp hpn]

/-- Build the paired padded seed state while preserving the captured ABI and
both polynomial destination pointers. -/
theorem maskInit_ok (σ : State) (hp : Pre σ) :
    WP isa (.block (pro ++ zero ++ absorb 0)) σ fun t => Env σ t ∧
      PairAt t.mem (σ.gpr .x4) (seedState σ.mem (σ.gpr .x0)) (seedState σ.mem (σ.gpr .x0+66)) := by
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_env σ hp) ?_
  intro a ha
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok ha.base (fun i hi => by
    rw [ha.wr]; exact ⟨_,hp.scratch,Offset.contains_base _ (by omega) (by omega)⟩)) ?_
  intro b ⟨hb,hfb,hzb⟩
  have eb : Env σ b := ha.lowStep hb hfb (by simp) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Region.sub_prefix (by decide))
  refine WP.mono (absorb0_ok b (by rw [eb.rd,eb.wr,eb.seed]; exact hp.seed)
    (by rw [eb.wr,eb.base]; exact hp.scratch)
    (by rw [eb.seed,eb.base]
        exact (hp.seedSep ⟨σ.gpr .x4,8192⟩ (by simp [writes])).sub_right (Region.sub_prefix (by decide)))
    (by simpa only [eb.base] using hzb)) ?_
  intro t ⟨ht,hft,hpt⟩
  have hf : Frame [pairR (σ.gpr .x4)] b.mem t.mem := by simpa only [eb.base] using hft
  refine ⟨eb.lowStep ht hf (by simp) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Region.sub_prefix (by decide)),?_⟩
  rw [eb.base,eb.seed] at hpt
  have hleft : seedState b.mem (σ.gpr .x0)=seedState σ.mem (σ.gpr .x0) := by
    simpa only [Nat.mul_zero,BitVec.add_zero] using eb.seedState hp (p := 0) (by decide)
  have hright : seedState b.mem (σ.gpr .x0+66)=seedState σ.mem (σ.gpr .x0+66) :=
    eb.seedState hp (p := 1) (by decide)
  simpa only [hleft,hright] using hpt

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
