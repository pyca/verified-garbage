module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa (Params Poly IPoly)
open VG.Proof.MlDsa (Reduced PolyIs polyAt poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

theorem copySeed4_generic {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : inB (rbs++wbs) (sc oSA) 32 = true)
    (hdst : inB wbs (sc (oSA4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oSA) 32 (sc (oSA4+34*j)) 32 = true) :
    WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  unfold copySeed4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oSA4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oSA,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oSA),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oSA4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oSA4+34*j))) (sb := .x28) (db := .x10) (so := oSA) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oSA),32⟩ : Region).Disjoint ⟨pa s (sc (oSA4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

theorem copySeed4_ok {S : Nat} {p : Params} (hF : PFacts p) {s : State} (L : Lay S kgR (kgW p) s)
    {j : Nat} (hj : j < 4) : WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  exact copySeed4_generic L (by layd) (by layd) (by layd)

structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : KSamp p σ e 0 s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oSA4+34*k))) 34 =
    seedA (rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ)

end VG.Proof.MlDsa.AArch64.KeyGen

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem slot_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs [.x28]) (seedSlot4 p e j) (.seq (Taint.ofRegs [.x28,.x10]) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 copySeed4 lea
  rw [VG.Proof.MlDsa.KeyGen.ifp (by dsimp only [oSA4]; omega_using [hj] : oSA4+34*j < 4096)]
  with_unfolding_all rfl

end VG.Proof.MlDsa.AArch64.KeyGen
