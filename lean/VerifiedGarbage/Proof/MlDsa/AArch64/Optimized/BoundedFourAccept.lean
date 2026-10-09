import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

/-- Each acceptance bit occupies a distinct bit in the scalar table index. -/
theorem acceptVector_ok (η : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hb : ∀e<4,vword (s.v .v22) e=BitVec.ofNat 32 (VG.Proof.MlDsa.Sample.rbB η))
    (hw : ∀e<4,vword (s.v .v24) e=BitVec.ofNat 32 (2^e))
    (k : ∀t,VChg [.v2] s t →
      (∀e<4,vword (t.v .v2) e=acceptWord η (vword (s.v .v1) e)*BitVec.ofNat 32 (2^e)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (([.vop (.sub .s4 .v2 .v1 .v22),
      .vop (.shift .ushr .s4 .v2 .v2 31),.vop (.mul .v2 .v2 .v24)] : List Instr)++rest)) s Q := by
  refine wp_vop (d := .v2) rfl fun a ha => wp_vop (d := .v2) rfl fun b hbb =>
    wp_vop (d := .v2) rfl fun t ht => ?_
  refine k t (((ha.chg.trans hbb.chg).trans ht.chg).mono ?_) ?_
  · intro r hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hbb.get .v24 (by decide),
      ha.get .v24 (by decide),hw e he,hbb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.v,VG.AArch64.vword_map2 _ _ _ he,hb e he]
    rfl

/-- Horizontal scalar reduction of the four weighted acceptance bits. -/
def maskReduce (x : BitVec 128) : BitVec 64 :=
  let a:=x.extractLsb' 0 64+x.extractLsb' 64 64
  (a+(a>>>32)) &&& 15

def acceptanceVector (a b c d : Bool) : BitVec 128 :=
  ofVWords (BitVec.ofNat 32 a.toNat) (BitVec.ofNat 32 (2*b.toNat))
    (BitVec.ofNat 32 (4*c.toNat)) (BitVec.ofNat 32 (8*d.toNat))

theorem maskReduce_eq (a b c d : Bool) :
    maskReduce (acceptanceVector a b c d)=BitVec.ofNat 64 (maskOf a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem acceptanceVector_words (a b c d : Bool) :
    ∀e<4,vword (acceptanceVector a b c d) e=
      BitVec.ofNat 32 (([a,b,c,d][e]!).toNat)*BitVec.ofNat 32 (2^e) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem vector_eq_of_words {x y : BitVec 128}
    (h : ∀e<4,vword x e=vword y e) : x=y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hh:=congrArg (fun b : BitVec 32=>b.getLsbD (k%32)) (h (k/32) (by omega))
  have hb : k%32<32:=Nat.mod_lt _ (by decide)
  have hd : 32*(k/32)+k%32=k:=by omega
  simpa only [vword,BitVec.getLsbD_extractLsb',hb,decide_true,Bool.true_and,hd] using hh

theorem acceptWord_decide {η : Nat} (hη : η=2∨η=4) : ∀b<16,
    acceptWord η (BitVec.ofNat 32 b)=
      BitVec.ofNat 32 (decide (b<VG.Proof.MlDsa.Sample.rbB η)).toNat := by
  rcases hη with rfl|rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
