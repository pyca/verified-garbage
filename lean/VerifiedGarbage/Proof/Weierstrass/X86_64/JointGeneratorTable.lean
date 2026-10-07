import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombLay
import VerifiedGarbage.Proof.Weierstrass.CombW

/-! The existing width-seven comb table supplies the joint generator row directly. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def combGeneratorRow (n : Nat) {C : Curve} {J : Nat} {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hm : UnitMod C.p (2^(64*n))) (hC : Law C) (hT : CombOkW C 7 J tbl start) (hJ : 0<J) :
    JointGeneratorRow n C (G C) where
  x a := (combAt tbl 0 (a-1)).1*2^(64*n)%C.p
  y a := (combAt tbl 0 (a-1)).2*2^(64*n)%C.p
  canonical _ _ _ _ := ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p)),
    Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))⟩
  point a ha hb _ := by
    rw [toM_mont hm,toM_mont hm]
    have hp := hT.entry 0 hJ (a-1) (by omega)
    simp only [Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.sub_add_cancel ha] at hp
    rw [hp]
    exact InvJ.affine hC _ _

theorem wordsVal_addr (mem : Mem) (base : Addr) (d o n : Nat) :
    wordsVal mem (off base d) o n=wordsVal mem base (d+o) n := by
  apply wordsVal_congr₂
  intro i _
  simp only [Mont.word,off,Offset.add_add,Nat.add_assoc]

theorem combGenerator_coordinates {n : Nat} {C : Curve} {J a : Nat} {tbl : List (List (Nat×Nat))}
    {start : Nat×Nat}
    (hp : C.p<2^(64*n)) (hT : CombOkW C 7 J tbl start) (hJ : 0<J)
    {s : State} {T : Addr} (ht : TblMem s T (tcombWords n (2^(64*n)) C.p tbl))
    (ha : 1≤a) (hb : a≤63) :
    wordsVal s.mem (off T (16*n*(a-1))) 0 n=(combAt tbl 0 (a-1)).1*2^(64*n)%C.p ∧
    wordsVal s.mem (off T (16*n*(a-1))) (8*n) n=(combAt tbl 0 (a-1)).2*2^(64*n)%C.p := by
  have he := tbl_entry (n:=n) (R:=2^(64*n)) (p:=C.p) (H:=64) (J:=J)
    ht hT.len hT.lenH (j:=0) (m:=a-1) hJ (by omega)
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  simpa only [Nat.zero_mul,BitVec.add_zero] using he

theorem jointGenerator_of_table {c : Joint.Cfg} {C : Curve} {J size : Nat}
    {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hC : Law C) (hp : C.p<2^(64*c.K.M.n))
    (hT : CombOkW C 7 J tbl start) (hJ : 0<J)
    {s : State} {T base : Addr} (ht : TblMem s T (tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl))
    (hout : ∀ i<(tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length,∀ b<8,
      size≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms c.tsym=T) :
    JointGenerator c C base T size (combGeneratorRow c.K.M.n hm hC hT hJ) s := by
  have hlen : (tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length=J*(64*(2*c.K.M.n)) :=
    tcombWords_length (n:=c.K.M.n) (R:=2^(64*c.K.M.n)) (p:=C.p) hT.len hT.lenH
  have hlen' : 128*c.K.M.n≤(tcombWords c.K.M.n (2^(64*c.K.M.n)) C.p tbl).length := by
    rw [hlen]
    have := Nat.le_mul_of_pos_left (64*(2*c.K.M.n)) hJ
    omega
  intro a ha hb _
  have coords := combGenerator_coordinates hp hT hJ ht ha hb
  have hk : 16*c.K.M.n*(a-1)=16*(c.K.M.n*(a-1)) := Nat.mul_assoc ..
  have hka : c.K.M.n*(a-1)≤c.K.M.n*62 := Nat.mul_le_mul_left _ (by omega)
  refine ⟨hsym,?_,?_,coords.1,coords.2⟩
  · intro i hi
    simp only [off,Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by omega)⟩
  · intro i hi b hb'
    have ho := hout (2*(c.K.M.n*(a-1))+2*i+b/8) (by omega) (b%8) (by omega)
    simp only [off,Offset.add_add] at ho ⊢
    have he : 16*c.K.M.n*(a-1)+16*i+b=8*(2*(c.K.M.n*(a-1))+2*i+b/8)+b%8 := by omega
    rw [he]
    exact ho

end VG.Proof.Weierstrass.X86_64
