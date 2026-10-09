import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourScalarLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def fallbackSetup : List Instr := [.movz .x .x16 10 0,.movz .x .x17 5 0,.mul .x .x8 .x4 .x5]

theorem fallbackSetup_ok {s : State} {η r n : Nat} {table : Addr} (hc : Consts η table s)
    (h4 : (s.gpr .x4).toNat=r) (h5 : s.gpr .x5=BitVec.ofNat 64 n) :
    WP isa (.block fallbackSetup) s fun t=>
      Only [.x8,.x16,.x17] s t ∧ ScalarConsts η t ∧ t.gpr .x8=BitVec.ofNat 64 (r*n) := by
  unfold fallbackSetup
  refine wp_movz fun a ha h16=>wp_movz fun b hb h17=>?_
  refine WP.mono (scalarGuard_ok (r := r) (n := n) (by rw [hb.get .x4,ha.get .x4]; exact h4)
    (by rw [hb.get .x5,ha.get .x5]; exact h5)) fun t ⟨ht,h8⟩=>?_
  refine ⟨((ha.trans hb).trans ht).mono (by decide),?_,h8⟩
  constructor
  · rw [ht.get .x9,hb.get .x9,ha.get .x9]; exact hc.scalarQ
  · rw [ht.get .x10,hb.get .x10,ha.get .x10]; exact hc.scalarEta
  · rw [ht.get .x11,hb.get .x11,ha.get .x11]; exact hc.mask
  · rw [ht.get .x15,hb.get .x15,ha.get .x15]; exact hc.scalarBound
  · rw [ht.get .x16,hb.get .x16,h16]; rfl
  · rw [ht.get .x17,h17]; rfl

theorem fallbackSetup_inv {σ s : State} {η done : Nat} {table p q : Addr}
    {L : List Zq} {X : List Byte} (hi : LoopInv σ η table p q L X done s) :
    WP isa (.block fallbackSetup) s fun t=>ScalarInv σ η p q L X done t := by
  have h4 : (s.gpr .x4).toNat=256-(parsed η L X done).length := by
    rw [hi.remaining,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (fallbackSetup_ok hi.consts h4 hi.bytes) fun t ⟨ht,hc,h8⟩=>?_
  refine ⟨hi.bound,hc,(hi.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_,?_,?_,h8⟩
  · rw [ht.mem]; exact hi.frame
  · rw [ht.mem]; exact hi.stored
  · rw [ht.get .x2]; exact hi.input
  · rw [ht.get .x3]; exact hi.output
  · rw [ht.get .x4]; exact h4
  · rw [ht.get .x5]; exact hi.bytes

def fallback (η : Nat) : Prog isa := .seq (.block fallbackSetup)
 (.ite (.zero .x .x8) (.block []) (.loop (scalarLoopBody η) (.nonzero .x .x8)))

theorem fallback_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hy : ScalarLayout σ p q X) (hi : LoopInv σ η table p q L X done s) :
    WP isa (fallback η) s (ScalarDone σ η p q L X) := by
  exact WP.seq (WP.mono (fallbackSetup_inv hi) fun _ ht=>scalarPhase_ok hη hl hy ht)

theorem parsedPhase_ok {σ s : State} {η done : Nat} (hη : η=2∨η=4)
    {table p q : Addr} {L : List Zq} {X : List Byte} (hl : L.length≤256)
    (hv : Layout σ table p q X) (hs : ScalarLayout σ p q X)
    (hi : LoopInv σ η table p q L X done s) :
    WP isa (.seq (.ite (.zero .x .x8) (.block [])
      (.loop (.block (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.vectorBody true η)) (.nonzero .x .x8)))
      (fallback η)) s fun t=>Keep parserRegs σ t ∧ Frame [polyR p] σ.mem t.mem ∧
        Stored t.mem p (rbFold η L X) ∧ (t.gpr .x4).toNat=256-(rbFold η L X).length := by
  refine WP.seq (WP.mono (vectorPhase_ok hη hv hi) fun u ⟨d,hu,_⟩=>?_) 
  refine WP.mono (fallback_ok hη hl hs hu) fun t ⟨d,ht,he⟩=>?_
  have heq:=parsed_complete he
  exact ⟨ht.keep,ht.frame,by rw [←heq]; exact ht.stored,by rw [←heq]; exact ht.remaining⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
