module
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc


/-! # Encryption after the consumed matrix may be reused for decoded keys -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

structure VInv (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem) (v : BitVec 64)
    (rv mv : List Byte) (nY nU : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (sA L s₀ MB) 32 = mv
  y : ∀ j < nY, PolyIs s.mem (sA L s₀ (yOff P j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * i)) (32 * P.du) =
    compressEncode P.du (KPke.encU P.params (aM P L s₀ mB) rv i)
  fr : Frame (encW P L s₀ kC co) mE s.mem

/-- A region apart from what `VInv` describes. -/
def VFar (P : KemLay) (L : Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (kA s₀) L.sc RB 32).Disjoint r ∧ (R (kA s₀) L.sc MB 32).Disjoint r ∧
    (R (kA s₀) L.sc (YH P) (1024 * nY)).Disjoint r ∧
    (R (kA s₀) (L.slot kC) co (32 * P.du * nU)).Disjoint r ∧ ∃ r' ∈ encW P L s₀ kC co, Region.Sub r r'

theorem VInv.frame {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VInv P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, VFar P L s₀ kC co nY nU r) : VInv P L s₀ kC co mE mB v rv mv nY nU s' := by
  have hw := hp.wf
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by omega) (by have := mul_succ_le (a := 32 * P.du) hi; omega))) (by kom)]
    exact h.u i hi


theorem Far.vfar {s₀ : State} {kC co nY nU : Nat} {r : Region}
    (h : Far P L s₀ kC co nY nU r) : VFar P L s₀ kC co nY nU r :=
  ⟨h.1,h.2.1,h.2.2.2⟩

theorem VInv.frame_far {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VInv P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24=s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀r∈W, Far P L s₀ kC co nY nU r) : VInv P L s₀ kC co mE mB v rv mv nY nU s' :=
  h.frame hp hk hx hf (fun r hr => (hW r hr).vfar)


theorem EInv.vinv {s₀ s : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} (h : EInv P L s₀ kC co mE mB v rv mv nY nU s) :
    VInv P L s₀ kC co mE mB v rv mv nY nU s :=
  ⟨h.kb,h.x24,h.r,h.m,h.y,h.u,h.fr⟩

end VG.Proof.MlKem.AArch64.Kem
