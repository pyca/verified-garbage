import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedResponseProduct

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Spec.Sha3 (bytesAt)

/-- Signed response storage remains explicit until accepted output. -/
def SignedFam (s : State) (b m : Nat) (f : Nat → Poly) (lo hi : Int) : Prop :=
  ∀j<m,SignedPl s (b+j) (f j) lo hi

theorem SignedFam.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s u : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (hP : PPostB S s u ws) (hc : famChk rbs wbs ws b m=true)
    (h : SignedFam s b m f lo hi) : SignedFam u b m f lo hi :=
  fun j hj => keepSignedPoly L hP (famChk_one hc hj) (h j hj)

theorem SignedFam.snoc {s : State} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (h : SignedFam s b m f lo hi) (ht : SignedPl s (b+m) (f m) lo hi) :
    SignedFam s b (m+1) f lo hi := by
  intro j hj
  rcases (by omega : j<m ∨ j=m) with hj | rfl
  · exact h j hj
  · exact ht

structure PositiveKB (p : Params) (S : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : PositiveIL p S σ t s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p)=CTv p σ (p.ℓ*t)
  c : PosPl s 0 (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t)))
  sampled : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ*t))).isSome

theorem PositiveKB.step {p : Params} {S : Nat} {σ s u : State} {t : Nat}
    (h : PositiveKB p S σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : kbChk p ws=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveKB p S σ t u := by
  simp only [kbChk,Bool.and_eq_true] at hc
  exact ⟨h.l.step hP hy hc.1.1 hw,(h.l.st.lay.keepBytes hP hc.1.2).trans h.ct,
    h.c.keep h.l.st.lay hP hc.2,h.sampled⟩

structure PositiveIZb (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : PositiveKB p S σ t s
  z : SignedFam s (yBase p) r (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1)
  y : Fam s (yBase p+r) (p.ℓ-r) fun j => Yv p σ (p.ℓ*t) (r+j)
  w : Fam s (wBase p) p.k (Wv p σ (p.ℓ*t))
  ones : s.mem.readW (pa s (sc oONES)) 64=0

def PositiveIZ (p : Params) (S : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  PositiveIZb p S σ t r s ∧
    s.gpr .x24=bit (∀j<r,normRq [Zv p σ (p.ℓ*t) j]<p.γ₁-p.β)

theorem PositiveIZb.step {p : Params} {S : Nat} {σ s u : State} {t r : Nat}
    (h : PositiveIZb p S σ t r s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : zfam p ws r=true)
    (hys : famChk (sgR p) (sgW p) ws (yBase p+r) (p.ℓ-r)=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIZb p S σ t r u := by
  simp only [zfam,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP hy h1 hw,h.z.keep L hP h2,h.y.keep L hP hys,h.w.keep L hP h3,
    (L.keepW hP h4).trans h.ones⟩

end VG.Proof.MlDsa.AArch64.Sign
