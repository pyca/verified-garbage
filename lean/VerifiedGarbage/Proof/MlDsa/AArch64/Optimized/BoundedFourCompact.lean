import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (acceptedIndices)
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def tableBytes (x indices : BitVec 128) : BitVec 128 :=
 ofVBytes (fun i => let n:=(vbyte indices i).toNat; if n<16 then vbyte x n else 0)

theorem word_eq_of_bytes (x y : BitVec 128) (i j : Nat)
    (h : ∀r<4,vbyte x (4*i+r)=vbyte y (4*j+r)) : vword x i=vword y j := by
  apply BitVec.eq_of_getLsbD_eq
  intro a ha
  have hh := congrArg (fun z : BitVec 8 => z.getLsbD (a%8)) (h (a/8) (by omega))
  have hm : a%8<8 := Nat.mod_lt _ (by decide)
  simp only [vbyte,BitVec.getLsbD_extractLsb',hm,decide_true,Bool.true_and] at hh
  simp only [vword,BitVec.getLsbD_extractLsb',ha,decide_true,Bool.true_and]
  have hx : 8*(4*i+a/8)+a%8=32*i+a := by omega
  have hy : 8*(4*j+a/8)+a%8=32*j+a := by omega
  simpa only [hx,hy] using hh

theorem compact_word (x : BitVec 128) {mask i : Nat} (hm : mask<16)
    (hi : i<(acceptedIndices mask).length) :
    vword (tableBytes x (shuffleWord mask)) i=vword x (acceptedIndices mask)[i]! := by
  have hn := indices_length mask
  have hid := index_bound mask hm i hi
  apply word_eq_of_bytes
  intro j hj
  rw [tableBytes,vbyte_ofVBytes _ (by omega),shuffle_byte mask hm i hi j hj]
  have hidx : (BitVec.ofNat 8 (4*(acceptedIndices mask)[i]!+j)).toNat=
      4*(acceptedIndices mask)[i]!+j := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [hidx,ite_eq_left (by omega)]

/-- TBL preserves the accepted coefficients in their original scalar order. -/
theorem compact_ok {s : State} {rest : List Instr} {Q : State → Prop} {mask : Nat}
    (hm : mask<16) (h6 : s.v .v6=shuffleWord mask)
    (k : ∀t,VChg [.v1] s t →
      (∀i<(acceptedIndices mask).length,
        vword (t.v .v1) i=vword (s.v .v1) (acceptedIndices mask)[i]!) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.vop (.tbl .v1 .v1 .v6)::rest)) s Q := by
  refine wp_vop (d := .v1) rfl fun t ht => k t ht.chg ?_
  intro i hi
  rw [ht.v,h6]
  exact compact_word _ hm hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
