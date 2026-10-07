import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519 VG.Proof.Ed25519.AArch64

def fastRaw7 (x : BitVec 64) : BitVec 64 :=
  if x &&& 1=0 then 0 else (x &&& 127)-(((x &&& 127) &&& 64) <<< 1)

theorem fastMask7 (x : BitVec 64) : x &&& 127=BitVec.ofNat 64 (x.toNat%128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& (2^7-1) = (x.toNat%128)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem fastRaw7_eq {x : BitVec 64} {k j : Nat}
    (hx : x.toNat%128=FastNaf7.residual k j%128) : fastRaw7 x=BitVec.ofInt 64 (FastNaf7.digit k j) := by
  have H : ∀ r : Fin 128,
      (if r.val%2=0 then (0 : BitVec 64) else BitVec.ofNat 64 r.val-
        ((BitVec.ofNat 64 r.val &&& 64) <<< 1)) =
      BitVec.ofInt 64 (if r.val%2=0 then 0 else if r.val<64 then (r.val:Int) else (r.val:Int)-128) := by decide
  have he : x &&& 1=0 ↔ x.toNat%2=0 := by
    rw [←BitVec.toNat_inj]
    change x.toNat &&& 1=0 ↔ x.toNat%2=0
    rw [Nat.and_one_is_mod]
  simp only [fastRaw7,he,fastMask7,hx,FastNaf7.digit_mod128]
  have hp : x.toNat%2=FastNaf7.residual k j%128%2 := by omega
  rw [hp]
  change (if FastNaf7.residual k j%128%2=0 then (0:BitVec 64) else
    (x &&& (127:BitVec 64))-(BitVec.ofNat 64 (FastNaf7.residual k j%128) &&& 64) <<< 1)=_
  rw [fastMask7,hx]
  exact H ⟨FastNaf7.residual k j%128,Nat.mod_lt _ (by decide)⟩

theorem fastChoice_eq {w : Nat} (hw : FastNaf.Width w) (x : BitVec 64) (k j : Nat)
    (hx : x.toNat%128=FastNaf.residual w k j%128)
    (ho : FastNaf.residual w k j%2≠0) :
    (x &&& BitVec.ofNat 64 (2^w-1))-(((x &&& BitVec.ofNat 64 (2^w-1)) &&&
      BitVec.ofNat 64 (2^(w-1))) <<< 1)=BitVec.ofInt 64 (FastNaf.digit w k j) := by
  have he : x &&& 1≠0 := by
    intro h
    have hv := congrArg BitVec.toNat h
    change x.toNat &&& 1=0 at hv
    rw [Nat.and_one_is_mod] at hv
    omega
  rcases hw with rfl | rfl
  · have h := nafRaw_eq (x:=x) (k:=k) (j:=j) (by simpa only [FastNaf.residual,ite_false,show ¬(5=7) from by decide] using (show x.toNat%32=FastNaf.residual 5 k j%32 from by omega))
    simp only [nafRaw,he,ite_false] at h
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.natCast_eq_ofNat,Nat.reducePow,Nat.reduceSub,ite_false,FastNaf.digit,show ¬(5=7) from by decide] using h
  · have h := fastRaw7_eq (x:=x) (k:=k) (j:=j) (by simpa only [FastNaf.residual,ite_true] using hx)
    simp only [fastRaw7,he,ite_false] at h
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.natCast_eq_ofNat,Nat.reducePow,Nat.reduceSub,FastNaf.digit,ite_true] using h

theorem fastChoose_ok (s : State) {w : Nat} (hw : FastNaf.Width w) (k j : Nat)
    (hm : s.gpr .x10=BitVec.ofNat 64 (2^w-1)) (hs : s.gpr .x11=BitVec.ofNat 64 (2^(w-1)))
    (hv : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=FastNaf.residual w k j)
    (ho : FastNaf.residual w k j%2≠0) :
    WP isa (.block Impl.Weierstrass.AArch64.FastNaf.choose) s fun t =>
      t.gpr .x2=BitVec.ofInt 64 (FastNaf.digit w k j) ∧ Keeps [.x2,.x3] s t := by
  have he := fastChoice_eq hw (s.gpr .x5) k j (by dsimp only [nafVal5] at hv; omega) ho
  apply WP.of_runBlock
  simp only [Impl.Weierstrass.AArch64.FastNaf.choose,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,hm,hs,
    show 1<Size.x.bits from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨he,?_,rfl,rfl,rfl,rfl⟩
  intro r hr
  have hh : r≠.x2 ∧ r≠.x3 := by simpa using hr
  simp only [RegUpd.gpr_write,hh.1,hh.2,ite_false]

theorem fastSubtract_ok (s : State) (w k j : Nat) (h12 : s.gpr .x12=0)
    (h2 : s.gpr .x2=BitVec.ofInt 64 (FastNaf.digit w k j))
    (hv : nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)=FastNaf.residual w k j)
    (hb : FastNaf.residual w k j≤2^256) :
    WP isa (.block (Naf.subtractShift.take 7)) s fun t =>
      nafVal5 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x8) (t.gpr .x9)=2*FastNaf.residual w k (j+1) ∧
      Keeps [.x3,.x5,.x6,.x7,.x8,.x9] s t := by
  have hs := fastSub5_next (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9) w k j hv hb
  apply WP.of_runBlock
  simp only [Naf.subtractShift,List.take_succ_cons,List.take_zero,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,h12,h2,
    show 63<Size.x.bits from by decide,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,rfl,rfl,rfl,rfl⟩
  · exact hs
  · intro r hr
    have hh : r≠.x3 ∧ r≠.x5 ∧ r≠.x6 ∧ r≠.x7 ∧ r≠.x8 ∧ r≠.x9 := by simpa using hr
    simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2,ite_false]

theorem fastShift_ok (s : State) (w : Nat) (hw : w=1 ∨ w=5 ∨ w=7) :
    WP isa (.block (Impl.Weierstrass.AArch64.FastNaf.shift w)) s fun t =>
      nafVal5 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x8) (t.gpr .x9)=
      nafVal5 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) (s.gpr .x9)/2^w ∧
      Keeps [.x5,.x6,.x7,.x8,.x9] s t := by
  have hw64 : w<Size.x.bits := by rcases hw with rfl | rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [Impl.Weierstrass.AArch64.FastNaf.shift,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,hw64,
    Option.some.injEq,exists_eq_left']
  refine ⟨fastShift_value w hw ..,?_,rfl,rfl,rfl,rfl⟩
  intro r hr
  have hh : r≠.x5 ∧ r≠.x6 ∧ r≠.x7 ∧ r≠.x8 ∧ r≠.x9 := by simpa using hr
  simp only [RegUpd.gpr_write,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,ite_false]

end VG.Proof.Weierstrass.AArch64
