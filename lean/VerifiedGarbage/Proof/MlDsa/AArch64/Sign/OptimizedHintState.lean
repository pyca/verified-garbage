import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintFinish

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

/-- Completed hint rows replace signed low coefficients in place. -/
structure PositiveIHb (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : PositiveKB p S σ t s
  z : SignedFam s (yBase p) p.ℓ (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1)
  high : NatFam s (wBase p) p.k (WHighv p σ (p.ℓ*t))
  low : SignedFam s (5+i) (p.k-i) (fun j=>R0v p σ (p.ℓ*t) (i+j)) (-(p.γ₂:Int)) p.γ₂
  h : HFam s 5 i (Hv p σ (p.ℓ*t))
  ones : s.mem.readW (pa s (sc oONES)) 64=BitVec.ofNat 64 (onesSum (Hv p σ (p.ℓ*t)) i)

def PositiveIH (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  PositiveIHb p S σ t i s ∧
    s.gpr .x24=bit ((ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t)) ∧
      ∀j<i,normRq [CT0v p σ (p.ℓ*t) j]<p.γ₂)

theorem positiveIH_of_IR {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveIR p S σ t p.k s) : PositiveIH p S σ t 0 s := by
  refine ⟨⟨h.1.b,h.1.z,h.1.high,?_,by intro j hj; omega,?_⟩,?_⟩
  · simpa using h.1.low
  · simpa [onesSum] using h.1.ones
  · rw [h.2]
    apply bit_congr
    simp [R0Ok]


def positiveHfam (p : Params) (ws : List (VG.Impl.MlDsa.AArch64.Call.Ptr × Nat)) (i : Nat) : Bool :=
  kbChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) ws (wBase p) p.k &&
  famChk (sgR p) (sgW p) ws (5+i) (p.k-i) &&
  famChk (sgR p) (sgW p) ws 5 i && keepB (sgR p) (sgW p) ws (sc oONES) 8

theorem PositiveIHb.step {p : Params} {S : Nat} {σ s u : State} {t i : Nat}
    (h : PositiveIHb p S σ t i s) {ws : List (VG.Impl.MlDsa.AArch64.Call.Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : positiveHfam p ws i=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIHb p S σ t i u := by
  simp only [positiveHfam,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hb,hz⟩,hh⟩,hl⟩,hf⟩,ho⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP hy hb hw,h.z.keep L hP hz,h.high.keep L hP hh,
    h.low.keep L hP hl,HFam.keep L hP hf h.h,(L.keepW hP ho).trans h.ones⟩

theorem SignedFam.shift {s : State} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (h : SignedFam s b m f lo hi) (hm : 0<m) :
    SignedFam s (b+1) (m-1) (fun j=>f (j+1)) lo hi := by
  intro j hj
  have ht := h (j+1) (by omega)
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

end VG.Proof.MlDsa.AArch64.Sign
