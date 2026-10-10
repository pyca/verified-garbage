import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunk
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop

/-! ## From `BallSetup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored W)
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok q_eq)
open VG.Impl.MlDsa.AArch64.Sample (bSetup movQ)
open VG.Impl.MlKem.AArch64 (mov)
open VG.Spec.MlDsa (n coeffAt)

/-- Initialize the first128-byte chunk after loading the eight sign bytes. -/
theorem setup_ok {X : List Byte} {a b : Addr} {τ : Nat} {s : State}
    (h25 : s.gpr .x25+BitVec.ofNat 64 840=b) (h26 : s.gpr .x26=a)
    (h27 : (s.gpr .x27).toNat=τ) (hτ : τ≤256)
    (hin : InRegions (s.rd++s.wr) b 8)
    (hbuf : ∀ j<8,s.mem (b+BitVec.ofNat 64 j)=X.getD j 0)
    (hz : ∀ j<256,coeffAt s.mem a j=0) :
    WP isa (.block (bSetup ++ ([.movz .x .x5 128 0] : List Instr))) s fun u =>
      Keep [.x2,.x5,.x9,.x10,.x11,.x12,.x15] s u ∧ u.mem=s.mem ∧
      u.gpr .x2=b+8 ∧ (u.gpr .x5).toNat=128 ∧
      Parser a (Vector.replicate n 0) (256-τ) (W X) u := by
  unfold bSetup movQ
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrx (a := b) (by decide) h25 hin fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ =>
    wp_sub fun s₃ o₃ e₃ => wp_mov fun s₄ o₄ e₄ => wp_addImm (by decide) fun s₅ o₅ e₅ =>
    wp_movz fun s₆ o₆ e₆ => movQ_ok fun s₇ o₇ e₇ => wp_subImm (by decide) fun s₈ o₈ e₈ =>
    wp_movz fun s₉ o₉ e₉ => wp_movz fun u hu eu => wp_nil ?_
  have k₉ := ((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).trans o₉.keep)
  have ku : Keep [.x2,.x5,.x9,.x10,.x11,.x12,.x15] s u := (k₉.trans hu.keep).mono (by decide)
  have mu : u.mem=s.mem := by
    rw [hu.mem,o₉.mem,o₈.mem,o₇.mem,o₆.mem,o₅.mem,o₄.mem,o₃.mem,o₂.mem,o₁.mem]
  refine ⟨ku,mu,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hu.get .x2,o₉.get .x2,o₈.get .x2,o₇.get .x2,o₆.get .x2,e₅,o₄.get .x25,o₃.get .x25,
      o₂.get .x25,o₁.get .x25,← h25,BitVec.add_assoc]
    rfl
  · rw [eu]; rfl
  · rw [ku.get .x26,h26]
  · rw [hu.get .x9,o₉.get .x9,o₈.get .x9,o₇.get .x9,o₆.get .x9,o₅.get .x9,o₄.get .x9,o₃.get .x9,
      o₂.get .x9,e₁]
    exact readW_leNat _ _ _ hbuf
  · rw [hu.get .x10,o₉.get .x10,o₈.get .x10,o₇.get .x10,o₆.get .x10,o₅.get .x10,o₄.get .x10,e₃,
      BitVec.toNat_sub,e₂,o₂.get .x27,o₁.get .x27,h27]
    simp; omega
  · rw [hu.get .x11,o₉.get .x11,o₈.get .x11,o₇.get .x11,o₆.get .x11,o₅.get .x11,e₄,
      o₃.get .x27,o₂.get .x27,o₁.get .x27,h27]
    omega
  · rw [hu.get .x12,o₉.get .x12,e₈,toNat_sub_n (by rw [e₇,q_eq]; decide),e₇,q_eq]; rfl
  · rw [hu.get .x15,e₉]; rfl
  · rw [mu]; intro j hj
    rw [hz j hj,getElem!_pos _ j (by exact hj),Vector.getElem_replicate]; rfl
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallFirst.lean` -/

section

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

end
