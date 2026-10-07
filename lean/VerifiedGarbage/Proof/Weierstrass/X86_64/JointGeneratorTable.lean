import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombLay
import VerifiedGarbage.Proof.Weierstrass.CombW

/-! The existing width-seven comb table supplies the joint generator row directly. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def combGeneratorRow {C : Curve} {J : Nat} {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hm : UnitMod C.p (2^256)) (hC : Law C) (hT : CombOkW C 7 J tbl start) (hJ : 0<J) :
    JointGeneratorRow C (G C) where
  x a := (combAt tbl 0 (a-1)).1*2^256%C.p
  y a := (combAt tbl 0 (a-1)).2*2^256%C.p
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

theorem combGenerator_coordinates {C : Curve} {J a : Nat} {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hp : C.p<2^256) (hT : CombOkW C 7 J tbl start) (hJ : 0<J)
    {s : State} {T : Addr} (ht : TblMem s T (tcombWords 4 (2^256) C.p tbl))
    (ha : 1≤a) (hb : a≤63) :
    wordsVal s.mem (off T (64*(a-1))) 0 4=(combAt tbl 0 (a-1)).1*2^256%C.p ∧
    wordsVal s.mem (off T (64*(a-1))) 32 4=(combAt tbl 0 (a-1)).2*2^256%C.p := by
  have he := tbl_entry (n:=4) (R:=2^256) (p:=C.p) (H:=64) (J:=J)
    ht hT.len hT.lenH (j:=0) (m:=a-1) hJ (by omega)
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne C.p))) hp)
  rw [wordsVal_addr,wordsVal_addr,Nat.add_zero]
  simpa only [Nat.zero_mul,BitVec.add_zero,Nat.reduceMul] using he

theorem jointGenerator_of_table {c : Joint.Cfg} {C : Curve} {J size : Nat}
    {tbl : List (List (Nat×Nat))} {start : Nat×Nat}
    (hm : UnitMod C.p (2^256)) (hC : Law C) (hp : C.p<2^256)
    (hT : CombOkW C 7 J tbl start) (hJ : 0<J)
    {s : State} {T base : Addr} (ht : TblMem s T (tcombWords 4 (2^256) C.p tbl))
    (hout : ∀ i<(tcombWords 4 (2^256) C.p tbl).length,∀ b<8,
      size≤ofs base (T+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 b))
    (hsym : s.syms c.tsym=T) :
    JointGenerator c C base T size (combGeneratorRow hm hC hT hJ) s := by
  have hlen : (tcombWords 4 (2^256) C.p tbl).length=J*(64*(2*4)) :=
    tcombWords_length (n:=4) (R:=2^256) (p:=C.p) hT.len hT.lenH
  have hlen' : 512≤(tcombWords 4 (2^256) C.p tbl).length := by rw [hlen]; omega
  intro a ha hb _
  have coords := combGenerator_coordinates hp hT hJ ht ha hb
  refine ⟨hsym,?_,?_,coords.1,coords.2⟩
  · intro i hi
    simp only [off,Offset.add_add]
    obtain ⟨r,hr,hreg⟩ := ht.rd
    exact ⟨r,hr,Region.contains_off hreg (by omega)⟩
  · intro i hi b hb'
    have ho := hout (8*(a-1)+2*i+b/8) (by omega) (b%8) (by omega)
    simp only [off,Offset.add_add] at ho ⊢
    have he : 64*(a-1)+16*i+b=8*(8*(a-1)+2*i+b/8)+b%8 := by omega
    rw [he]
    exact ho

end VG.Proof.Weierstrass.X86_64
