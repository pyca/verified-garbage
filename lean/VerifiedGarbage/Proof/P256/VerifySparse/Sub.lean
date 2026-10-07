import VerifiedGarbage.Proof.P256.VerifySparse.Arithmetic

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Proof.Ed25519

private def addPrime : List Instr :=
  [.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17,
   .adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
   .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2]

private theorem maskWords_ok (s : State) :
    WP isa (.block [.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17]) s fun t =>
      t.gpr .x1=s.gpr .x17>>>32 ∧ t.gpr .x2=(s.gpr .x17<<<32)-s.gpr .x17 ∧ Keeps [.x1,.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,Size.bits,
    show 32<64 by decide,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

private theorem adc_ok (s : State) :
    WP isa (.block [.adc .x .x11 .x11 .x2]) s fun t =>
      t.gpr .x11=Word64.addCarry (s.gpr .x11) (s.gpr .x2) s.c ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write_self,
    BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

private theorem adds_ok (s : State) :
    WP isa (.block [.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
      .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2]) s fun t =>
      regsVal t (low 4)=(regsVal s (low 4)+four (s.gpr .x17) (s.gpr .x1) (s.gpr .x7) (s.gpr .x2))%2^256 ∧
      Keeps [.x8,.x9,.x10,.x11] s t := by
  rw [show ([.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
      .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2] : List Instr)=
    [.adds .x .x8 .x8 .x17]++([.adcs .x .x9 .x9 .x1]++
    ([.adcs .x .x10 .x10 .x7]++[.adc .x .x11 .x11 .x2])) from rfl,WP.block_append_iff]
  refine WP.mono (addc_ok s .x8 .x8 .x17 true (c:=false) rfl) fun s1 ⟨e1,c1,k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addc_ok s1 .x9 .x9 .x1 false (c:=s1.c) rfl) fun s2 ⟨e2,c2,k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addc_ok s2 .x10 .x10 .x7 false (c:=s2.c) rfl) fun s3 ⟨e3,c3,k3⟩ => ?_
  refine WP.mono (adc_ok s3) fun t ⟨e4,k4⟩ => ?_
  rw [k1.gpr _ (by decide),k1.gpr _ (by decide),c1] at e2 c2
  rw [k2.gpr _ (by decide),k1.gpr _ (by decide),k2.gpr _ (by decide),k1.gpr _ (by decide),c2] at e3 c3
  rw [k3.gpr _ (by decide),k2.gpr _ (by decide),k1.gpr _ (by decide),
    k3.gpr _ (by decide),k2.gpr _ (by decide),k1.gpr _ (by decide),c3] at e4
  refine ⟨?_,(((k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))).trans
    (k3.mono (by sub_regs))).trans (k4.mono (by sub_regs))⟩
  have et1 : t.gpr .x8=s1.gpr .x8 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide),k2.gpr _ (by decide)]
  have et2 : t.gpr .x9=s2.gpr .x9 := by rw [k4.gpr _ (by decide),k3.gpr _ (by decide)]
  have et3 : t.gpr .x10=s3.gpr .x10 := k4.gpr _ (by decide)
  change four (t.gpr .x8) (t.gpr .x9) (t.gpr .x10) (t.gpr .x11)=_
  rw [et1,et2,et3,e1,e2,e3,e4]
  exact addFour_value _ _ _ _ _ _ _ _

private theorem addPrime_ok (s : State) (b : Bool) (hz : s.gpr .x7=0)
    (hm : s.gpr .x17=if b then -1 else 0) :
    WP isa (.block addPrime) s fun t =>
      regsVal t (low 4)=(regsVal s (low 4)+(if b then p else 0))%2^256 ∧
      Keeps [.x1,.x2,.x8,.x9,.x10,.x11] s t := by
  change WP isa (.block (([.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,.sub .x .x2 .x2 .x17] : List Instr)++
    [.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,.adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2])) s _
  rw [WP.block_append_iff]
  refine WP.mono (maskWords_ok s) fun s1 ⟨e1,e2,k1⟩ => ?_
  refine WP.mono (adds_ok s1) fun t ⟨et,k2⟩ => ?_
  refine ⟨?_,(k1.mono (by sub_regs)).trans (k2.mono (by sub_regs))⟩
  have er : regsVal s1 (low 4)=regsVal s (low 4) := regsVal_congr fun q hq =>
    k1.gpr q ((by decide : ∀q∈low 4,q∉[Reg.x1,.x2]) q hq)
  rw [er,k1.gpr .x17 (by decide),k1.gpr .x7 (by decide),hz,e1,e2,hm,(masked_words b).2.2] at et
  exact et


/-- Canonical P-256 subtraction, with the ordinary field-operation frame. -/
theorem sub_ok {s : State} {base : Addr} {size o a b : Nat} (hs : Scr s base size)
    (ho : o+32≤size) (ha : a+32≤size) (hb : b+32≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hA : wordsVal s.mem base a 4<p) (hB : wordsVal s.mem base b 4<p) :
    WP isa (.block (Impl.P256.VerifySparse.sub o a b)) s fun t =>
      OpKeep Impl.P256.VerifySparse.M base o s t ∧
      wordsVal t.mem base o 4=(wordsVal s.mem base a 4+p-wordsVal s.mem base b 4)%p := by
  have hf : Fresh (low 4) := by unfold Fresh; decide
  have hl : (low 4).length=4 := rfl
  rw [Impl.P256.VerifySparse.sub,show zero7::loads (low 4) a=[zero7]++loads (low 4) a from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s0 ⟨z0,k0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok (low 4) (hs.of_keeps k0 (by decide)) (a:=a) ha ha8 hf)
    fun s1 ⟨e1,k1,_⟩ => ?_
  have hs1 := (hs.of_keeps k0 (by decide)).of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have cw := chainSubs_ok hs1 (b:=b) (t:=.x8) (ts:=[.x9,.x10,.x11]) hb hb8 hf
  refine WP.mono cw fun s2 ⟨e2,k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have z2 : s2.gpr .x7=0 := by rw [k2.gpr _ (by decide),k1.gpr _ (by decide),z0]
  rw [show ([.sbc .x .x17 .x7 .x7,.lsr .x .x1 .x17 32,.lsl .x .x2 .x17 32,
      .sub .x .x2 .x2 .x17,.adds .x .x8 .x8 .x17,.adcs .x .x9 .x9 .x1,
      .adcs .x .x10 .x10 .x7,.adc .x .x11 .x11 .x2] : List Instr)=
      [.sbc .x .x17 .x7 .x7]++addPrime from rfl,List.append_assoc,WP.block_append_iff]
  refine WP.mono (sbcMask_ok s2 z2) fun s3 ⟨x3,k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addPrime_ok s3 (!s2.c) (by rw [k3.gpr _ (by decide),z2]) x3)
    fun s4 ⟨e4,k4⟩ => ?_
  have hs4 := (hs2.of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (stores_ok (low 4) hs4 (o:=o) ho ho8 hf.1) fun t ⟨et,kt,ot⟩ => ?_
  rw [hl] at et ot
  have keep : Keeps (clob 4) s s4 :=
    (((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide))).trans
      ((k3.mono (by decide)).trans (k4.mono (by decide)))
  have er : regsVal s3 (low 4)=regsVal s2 (low 4) :=
    regsVal_congr fun q hq => k3.gpr q (by
      have ne : ∀ r∈low 4,r≠.x17 := by decide
      simpa only [List.mem_singleton] using ne q hq)
  rw [er] at e4
  change regsVal s2 (low 4)+wordsVal s1.mem base b 4=regsVal s1 (low 4)+2^256*(!s2.c).toNat at e2
  rw [e1,k1.mem,k0.mem] at e2
  change regsVal s2 (low 4)+wordsVal s.mem base b 4=wordsVal s.mem base a 4+2^256*(!s2.c).toNat at e2
  refine ⟨⟨fun r hr => (kt.gpr r (by simp)).trans (keep.gpr r hr),
    kt.rd.trans keep.rd,kt.wr.trans keep.wr,kt.sp.trans keep.sp,fun x hx _ => ?_⟩,?_⟩
  · exact (ot x hx).trans (congrFun keep.mem x)
  · rw [et,e4]
    have rr := regsVal_lt s2 (low 4)
    rw [hl] at rr
    have pp : p<2^256 := by decide
    cases hc : s2.c <;> simp only [hc,Bool.not_false,Bool.not_true,Bool.toNat_true,
      Bool.toNat_false,Nat.mul_one,Nat.mul_zero,Nat.add_zero,Bool.false_eq_true,ite_true,ite_false] at e2 ⊢
    · have ne : wordsVal s.mem base a 4<wordsVal s.mem base b 4 := by omega
      have small : wordsVal s.mem base a 4+p-wordsVal s.mem base b 4<p := by omega
      have eq : regsVal s2 (low 4)+p=2^256+(wordsVal s.mem base a 4+p-wordsVal s.mem base b 4) := by omega
      rw [eq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt small]
    · have ge : wordsVal s.mem base b 4≤wordsVal s.mem base a 4 := by omega
      rw [Nat.mod_eq_of_lt rr,show wordsVal s.mem base a 4+p-wordsVal s.mem base b 4=
        (wordsVal s.mem base a 4-wordsVal s.mem base b 4)+p by omega,Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega

end VG.Proof.P256.VerifySparse
