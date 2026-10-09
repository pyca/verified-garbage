import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParsePair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def writes (σ : State) : List Region :=
  [⟨σ.gpr .x4,8192⟩,⟨σ.gpr .x2,1024⟩,⟨σ.gpr .x3,1024⟩]

structure Pre (σ : State) : Prop where
  scratch : (Region.mk (σ.gpr .x4) 8192)∈σ.wr
  out1 : (Region.mk (σ.gpr .x2) 1024)∈σ.wr
  out2 : (Region.mk (σ.gpr .x3) 1024)∈σ.wr
  seed : (Region.mk (σ.gpr .x0) 132)∈σ.rd++σ.wr
  seedSep : ∀ r∈writes σ, (Region.mk (σ.gpr .x0) 132).Disjoint r
  out1Sep : (Region.mk (σ.gpr .x2) 1024).Disjoint ⟨σ.gpr .x4,8192⟩
  out2Sep : (Region.mk (σ.gpr .x3) 1024).Disjoint ⟨σ.gpr .x4,8192⟩
  outputs : (Region.mk (σ.gpr .x2) 1024).Disjoint ⟨σ.gpr .x3,1024⟩
  gamma : (σ.gpr .x1).setWidth 32=131072#32 ∨ (σ.gpr .x1).setWidth 32=524288#32

structure Env (σ s : State) : Prop where
  base : s.gpr .x19=σ.gpr .x4
  seed : s.gpr .x20=σ.gpr .x0
  out1 : s.gpr .x21=σ.gpr .x2
  out2 : s.gpr .x22=σ.gpr .x3
  lr : s.gpr .x30=σ.gpr .x30
  sp : s.sp=σ.sp
  rd : s.rd=σ.rd
  wr : s.wr=σ.wr
  saved : Saved σ (σ.gpr .x4) s.mem
  gamma : s.mem.readW (σ.gpr .x4+7904) 32=(σ.gpr .x1).setWidth 32
  frame : Frame (writes σ) σ.mem s.mem

theorem Env.step {σ s t : State} {rs : List Reg} {W : List Region} (h : Env σ s)
    (hk : RegKeep rs s t) (hf : Frame W s.mem t.mem)
    (hregs : ∀ r∈[Reg.x19,.x20,.x21,.x22,.x30],r∉rs)
    (hsub : ∀ r∈W, ∃ r'∈writes σ, r.Sub r')
    (hsave : ∀ r∈W, (Region.mk (σ.gpr .x4+7968) 144).Disjoint r)
    (hgamma : ∀ r∈W, (Region.mk (σ.gpr .x4+7904) 4).Disjoint r) : Env σ t := by
  refine ⟨(hk.gpr _ (hregs _ (by simp))).trans h.base,
    (hk.gpr _ (hregs _ (by simp))).trans h.seed,
    (hk.gpr _ (hregs _ (by simp))).trans h.out1,
    (hk.gpr _ (hregs _ (by simp))).trans h.out2,
    (hk.gpr _ (hregs _ (by simp))).trans h.lr,
    hk.sp.trans h.sp,hk.rd.trans h.rd,hk.wr.trans h.wr,h.saved.keep hf hsave,?_,h.frame.trans (hf.sub hsub)⟩
  rw [hf.readW (Region.contains_self _ _) hgamma (by decide)]
  exact h.gamma

theorem pro_env (σ : State) (hp : Pre σ) : WP isa (.block Impl.MlDsa.AArch64.Optimized.ResidentMask.pro) σ (Env σ) := by
  refine WP.mono (pro_ok σ hp.scratch) ?_
  intro s h
  refine ⟨h.base,h.seed,h.out1,h.out2,h.keep.gpr .x30 (by decide),h.keep.sp,
    h.keep.rd,h.keep.wr,h.saved,h.gamma,h.frame.sub ?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],Offset.sub_base _ (by decide)⟩
  · exact ⟨⟨σ.gpr .x4,8192⟩,by simp [writes],Offset.sub_base _ (by decide)⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
