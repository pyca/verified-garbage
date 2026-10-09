import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedResponseState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowCheck
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLow

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

abbrev NatPl (s : State) (j : Nat) (f : Vector Nat n) : Prop := NatPolyIs s.mem (pa s (pS j)) f
def NatFam (s : State) (b m : Nat) (f : Nat → Vector Nat n) : Prop := ∀j<m,NatPl s (b+j) (f j)

theorem keepNatPoly {S : Nat} {rbs wbs : List (Reg × Nat)} {s u : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {p : Ptr} {f : Vector Nat n}
    (hP : PPostB S s u ws) (hc : keepB rbs wbs ws p 1024=true)
    (h : NatPolyIs s.mem (pa s p) f) : NatPolyIs u.mem (pa u p) f := by
  rw [← h]
  apply Vector.ext
  intro i hi
  simp only [natPolyAt,Vector.getElem_ofFn]
  rw [hP.pa (L.keepBs hc),VG.Proof.MlDsa.Arith.coeffAt_frame hP.frame (L.fdisj hc) hi]

theorem NatFam.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s u : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {b m : Nat} {f : Nat → Vector Nat n}
    (hP : PPostB S s u ws) (hc : famChk rbs wbs ws b m=true) (h : NatFam s b m f) : NatFam u b m f :=
  fun j hj=>keepNatPoly L hP (famChk_one hc hj) (h j hj)

theorem NatFam.snoc {s : State} {b m : Nat} {f : Nat → Vector Nat n}
    (h : NatFam s b m f) (ht : NatPl s (b+m) (f m)) : NatFam s b (m+1) f := by
  intro j hj
  rcases (show j<m∨j=m by omega) with hj|rfl
  · exact h j hj
  · exact ht

abbrev WHighv (p : Params) (σ : State) (κ i : Nat) : Vector Nat n :=
  (W'v p σ κ i).map fun c=>(highBits p.γ₂ c).toNat

structure PositiveIRb (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : PositiveKB p S σ t s
  z : SignedFam s (yBase p) p.ℓ (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1)
  high : NatFam s (wBase p) i (WHighv p σ (p.ℓ*t))
  low : SignedFam s 5 i (R0v p σ (p.ℓ*t)) (-(p.γ₂:Int)) p.γ₂
  w : Fam s (wBase p+i) (p.k-i) fun j=>Wv p σ (p.ℓ*t) (i+j)
  ones : s.mem.readW (pa s (sc oONES)) 64=0

def PositiveIR (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  PositiveIRb p S σ t i s ∧
    s.gpr .x24=bit (ZOk p σ (p.ℓ*t) ∧ ∀j<i,normRq [R0v p σ (p.ℓ*t) j]<p.γ₂-p.β)

def positiveRfam (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  kbChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) ws (wBase p) i && famChk (sgR p) (sgW p) ws 5 i &&
  keepB (sgR p) (sgW p) ws (sc oONES) 8

theorem PositiveIRb.step {p : Params} {S : Nat} {σ s u : State} {t i : Nat}
    (h : PositiveIRb p S σ t i s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : positiveRfam p ws i=true)
    (hw : famChk (sgR p) (sgW p) ws (wBase p+i) (p.k-i)=true)
    (hwr : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIRb p S σ t i u := by
  simp only [positiveRfam,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hb,hz⟩,hh⟩,hl⟩,ho⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP hy hb hwr,h.z.keep L hP hz,h.high.keep L hP hh,h.low.keep L hP hl,
    h.w.keep L hP hw,(L.keepW hP ho).trans h.ones⟩

theorem positiveIR_of_IZ {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveIZ p S σ t p.ℓ s) : PositiveIR p S σ t 0 s := by
  refine ⟨⟨h.1.b,h.1.z,by intro j hj; omega,by intro j hj; omega,?_,h.1.ones⟩,?_⟩
  · simpa using h.1.w
  · rw [h.2]
    apply bit_congr
    simp [ZOk]

end VG.Proof.MlDsa.AArch64.Sign
