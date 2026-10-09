import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (n coeffAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (W St lRegs sign_bit)

structure FirstPost (X : List Byte) (a : Addr) (τ : Nat) (s u : State) : Prop where
  keep : Keep lRegs s u
  frame : Frame [polyR a] s.mem u.mem
  parser : Parser a (St X τ 128).1 (St X τ 128).2 (W X >>> ((St X τ 128).2-(256-τ))) u

theorem first_ok {X : List Byte} (hX : X.length=136) {a b : Addr} {τ : Nat} {s : State}
    (h25 : s.gpr .x25+BitVec.ofNat 64 840=b) (h26 : s.gpr .x26=a)
    (h27 : (s.gpr .x27).toNat=τ) (hτ : τ≤64)
    (hinw : InRegions (s.rd++s.wr) b 8)
    (hin : ∀ j<136,InRegions (s.rd++s.wr) (b+BitVec.ofNat 64 j) 1)
    (hbuf : ∀ j<136,s.mem (b+BitVec.ofNat 64 j)=X.getD j 0)
    (hw : ∀ j<256,InRegions s.wr (coeffAddr a j) 4)
    (hsep : (⟨b,136⟩ : Region).Disjoint (polyR a))
    (hz : ∀ j<256,coeffAt s.mem a j=0) :
    WP isa Impl.MlDsa.AArch64.Optimized.Ball.first s (FirstPost X a τ s) := by
  refine WP.seq (WP.mono (setup_ok h25 h26 h27 (by omega) hinw (fun j hj => hbuf j (by omega)) hz)
    fun t ⟨kt,mt,t2,t5,tp⟩ => ?_)
  have len : (X.drop 8).length=128 := by rw [List.length_drop,hX]
  have addr (j : Nat) : b+8+BitVec.ofNat 64 j=b+BitVec.ofNat 64 (8+j) := by
    rw [BitVec.add_assoc,BitVec.ofNat_add]; rfl
  refine WP.mono (chunk_ok (L := X.drop 8) (b := b+8) (τ := τ) (h := signs X)
    (by rw [len]; decide) (by rw [len]; decide) (by omega) tp t2 (by rw [len]; exact t5)
    (fun j hj => ?_) (fun j hj => ?_) (by rw [kt.wr]; exact hw) ?_
    (fun j hj hjn => sign_bit (by omega) hj hjn hτ)) fun u hu => ?_
  · rw [mt,addr,hbuf _ (by rw [len] at hj; omega)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]
  · rw [kt.rd,kt.wr,addr]; exact hin _ (by rw [len] at hj; omega)
  · exact hsep.sub_left (Offset.sub_base b (d := 8) (by rw [len]))
  · refine ⟨(kt.trans hu.keep).mono (by decide),?_,?_⟩
    · rw [← mt]; exact hu.frame
    · simpa only [len,Fold,St] using hu.parser
end VG.Proof.MlDsa.AArch64.Optimized.Ball
