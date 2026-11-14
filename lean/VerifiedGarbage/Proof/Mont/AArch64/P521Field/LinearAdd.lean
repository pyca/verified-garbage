module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearBorrow
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.HoistMarked
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointSchedule
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointCarry
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointMemory

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearCanonicalPrefix (z : Reg) : List Instr := [
  .movz .x .x0 512 0,
  .subs .x .x4 .x13 .x0,
  .subImm .x .x4 z 1,
  .cselc .x .x4 .x4 z .hs,
  .logic .and .x .x4 .x4 .x0]

theorem linear_top_carry (v : BitVec 64) : carryOut v (~~~(512 : BitVec 64)) true=decide (512≤v.toNat) := by
  simp only [carryOut,Bool.toNat_true,
    show (~~~(512 : BitVec 64)).toNat=18446744073709551103 from by decide]
  exact decide_eq_decide.mpr (by omega_arith)

theorem linear_canonical_prefix_ok (s : State) (z : Reg) (hz : z∈[Reg.x1,.x2]) (hv : s.gpr z=0) :
    WP isa (.block (linearCanonicalPrefix z)) s fun t =>
      t.c=decide (512≤(s.gpr .x13).toNat) ∧
      t.gpr .x4=(if decide (512≤(s.gpr .x13).toNat) then 512 else 0) ∧
      t.gpr .x0=512 ∧ Keeps [.x0,.x4] s t := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl <;>
    apply WP.of_runBlock <;>
    simp only [linearCanonicalPrefix,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
      BitVec.setWidth_eq,Nat.mul_zero,Nat.zero_lt_succ,Nat.reduceLT,CondCode.holds,
      show BitVec.setWidth 64 (512 : BitVec 16) <<< 0=(512 : BitVec 64) from rfl,
      ite_true,ite_false,reduceCtorEq,hv,Option.some.injEq,exists_eq_left']
  all_goals
    refine ⟨?_,?_,?_,⟨?_,?_,?_,?_,?_⟩⟩
    · exact linear_top_carry _
    · change ((if carryOut (s.gpr .x13) (~~~(512 : BitVec 64)) true then (0 : BitVec 64)-1 else 0) &&& 512)=_
      rw [linear_top_carry]
      split <;> rfl
    · trivial
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [RegUpd.gpr_write,RegUpd.gpr_addWithCarry,hr.1,hr.2,ite_false]
    · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
    · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
    · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
    · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

theorem linear_mersenne_split {lo hi n : Nat}
    (hl : lo<2^512) (hn : n<2*(2^521-1)) (he : lo+2^512*hi=n+1) :
    (n+1)%(2^521)+2^521*(decide (512≤hi)).toNat=n+1 := by
  by_cases hc : 512≤hi
  · simp only [hc,decide_true,Bool.toNat_true,Nat.mul_one]
    omega_arith
  · simp only [hc,decide_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    have hv : n+1<2^521 := by omega_arith
    exact Nat.mod_eq_of_lt hv

theorem linear_canonical_math {F R n w : Nat} {c d : Bool}
    (hF : 0<F) (hn : n<2*(F-1)) (hw : w<R)
    (ev : (n+1)%F+F*c.toNat=n+1)
    (ew : w+F*c.toNat+(!c).toNat=n+1+R*(!d).toNat) :
    w=n%(F-1) ∧ w<F-1 := by
  have hv : (n+1)%F<(F-1)+1 := by
    rw [Nat.sub_add_cancel hF]
    exact Nat.mod_lt _ hF
  have ev' : (n+1)%F+((F-1)+1)*c.toNat=n+1 := by
    simpa only [Nat.sub_add_cancel hF] using ev
  have ew' : w+(!c).toNat=(n+1)%F+R*(!d).toNat := by omega_using [ev,ew]
  exact P521Linear.canonical_correction hn hv hw ev' ew'

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearCanonicalPrepared (z : Reg) : List Instr :=
  linearCanonicalPrefix z++linearBorrow z linearRegs8++([.sbc .x .x13 .x13 .x4] : List Instr)

theorem linear_canonical_prepared_ok {s : State} {z : Reg} {n : Nat}
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0)
    (hn : n<2*(2^521-1)) (hv : regsVal s linearRegs9=n+1) :
    WP isa (.block (linearCanonicalPrepared z)) s fun t =>
      regsVal t linearRegs9=n%(2^521-1) ∧ regsVal t linearRegs9<2^521-1 ∧
      t.gpr .x0=512 ∧ Keeps (.x0::.x4::linearRegs9) s t := by
  rw [linearCanonicalPrepared,List.append_assoc,WP.block_append_iff]
  refine WP.mono (linear_canonical_prefix_ok s z hz hzv) fun u ⟨cu,mu,z0,ku⟩ => ?_
  have hzu : u.gpr z=0 := (ku.gpr z (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide)).trans hzv
  rw [WP.block_append_iff]
  refine WP.mono (linear_borrow_ok z linearRegs8 u (by decide) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide) hzu) fun v ⟨ev,kv⟩ => ?_
  refine WP.mono (sbc_word_ok v .x13 .x4) fun t ⟨et,_,kt⟩ => ?_
  have v13 : v.gpr .x13=u.gpr .x13 := kv.gpr .x13 (by decide)
  have v4 : v.gpr .x4=u.gpr .x4 := kv.gpr .x4 (by decide)
  have u13 : u.gpr .x13=s.gpr .x13 := ku.gpr .x13 (by decide)
  have tu8 : regsVal t linearRegs8=regsVal v linearRegs8 := regsVal_congr fun r h =>
    kt.gpr r ((by decide : ∀r∈linearRegs8,r∉[Reg.x13]) r h)
  have us8 : regsVal u linearRegs8=regsVal s linearRegs8 := regsVal_congr fun r h =>
    ku.gpr r ((by decide : ∀r∈linearRegs8,r∉[Reg.x0,.x4]) r h)
  have es := sub_borrow (v.gpr .x13) (v.gpr .x4) v.c
  rw [←et,v13,v4,u13] at es
  have mval : (u.gpr .x4).toNat=512*u.c.toNat := by
    rw [mu,cu]
    generalize decide (512≤(s.gpr .x13).toNat)=q
    cases q <;> rfl
  have eReg (w : State) : regsVal w linearRegs9=regsVal w linearRegs8+2^512*(w.gpr .x13).toNat := by
    rw [linearRegs9,regsVal_append]
    simp only [show linearRegs8.length=8 from by decide,Nat.reduceMul,regsVal,Nat.mul_zero,Nat.add_zero]
  have eSplit : (n+1)%(2^521)+2^521*u.c.toNat=n+1 := by
    rw [cu]
    have hl : regsVal s linearRegs8<2^512 := by
      simpa only [show linearRegs8.length=8 from by decide,Nat.reduceMul] using regsVal_lt s linearRegs8
    exact linear_mersenne_split (lo:=regsVal s linearRegs8) (hi:=(s.gpr .x13).toNat) (n:=n) hl hn (by
      have er := eReg s
      rw [hv] at er
      exact er.symm)
  have eWide : regsVal t linearRegs9+2^521*u.c.toNat+(!u.c).toNat=
      n+1+2^576*(!carryOut (v.gpr .x13) (~~~v.gpr .x4) v.c).toNat := by
    rw [eReg,tu8]
    have eps := congrArg (fun a : Nat => 2^512*a) es
    simp only [Nat.mul_add,←Nat.mul_assoc] at eps
    have epw : 2^512*2^64=2^576 := by lit_decide
    rw [epw] at eps
    have hvm := congrArg (fun a : Nat => 2^512*a) mval
    have eMask : 2^512*512=2^521 := by lit_decide
    simp only [←Nat.mul_assoc] at hvm
    rw [eMask] at hvm
    rw [hvm] at eps
    rw [v13,v4,u13]
    have hv' := hv
    rw [eReg] at hv'
    rw [us8] at ev
    simp only [show linearRegs8.length=8 from by decide,Nat.reduceMul] at ev
    omega_using [eps,ev,hv']
  have hlt : regsVal t linearRegs9<2^576 := by
    simpa only [show linearRegs9.length=9 from by decide,Nat.reduceMul] using regsVal_lt t linearRegs9
  have hresult : regsVal t linearRegs9=n%(2^521-1) ∧ regsVal t linearRegs9<2^521-1 := by
    have hpos : 0<(2:Nat)^521 := by lit_decide
    generalize hF : (2:Nat)^521=F at hn eSplit eWide hpos ⊢
    generalize hR : (2:Nat)^576=R at hlt eWide
    exact linear_canonical_math hpos hn hlt eSplit eWide
  refine ⟨hresult.1,hresult.2,?_,?_⟩
  · exact (kt.gpr .x0 (by decide)).trans ((kv.gpr .x0 (by decide)).trans z0)
  · exact (ku.mono (by simp)).trans ((kv.mono (by
      intro r h
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h)))).trans
      (kt.mono (by simp [linearRegs9])))

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

def linearMask : Instr := .logic .and .x .x4 .x4 .x0

def linearCanonicalTail (z : Reg) : List Instr :=
  linearBorrow z (linearRegs8.drop 1)++([.sbc .x .x13 .x13 .x4] : List Instr)

def linearCanonicalCode (z : Reg) : List Instr :=
  (linearCanonicalPrefix z).take 4++([.sbcs .x .x5 .x5 z,linearMask] : List Instr)++linearCanonicalTail z

theorem linear_canonical_schedule (z : Reg) (hz : z∈[Reg.x1,.x2]) :
    ∀s,runBlock isa (linearCanonicalCode z) s=runBlock isa (linearCanonicalPrepared z) s := by
  have hcheck : hoistMarked (fun i => i == linearMask) .x28
      ([.sbcs .x .x5 .x5 z,linearMask] : List Instr)=some ([linearMask],[.sbcs .x .x5 .x5 z]) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide
  have hm := hoistMarked_run hcheck
  have he := append_run_eq hm (fun s => rfl : ∀s,
    runBlock isa (linearCanonicalTail z) s=runBlock isa (linearCanonicalTail z) s)
  have hf := append_run_eq (fun s => rfl : ∀s,
    runBlock isa ((linearCanonicalPrefix z).take 4) s=runBlock isa ((linearCanonicalPrefix z).take 4) s) he
  have hbody : (linearCanonicalPrefix z).take 4++(([linearMask]++[.sbcs .x .x5 .x5 z])++linearCanonicalTail z)=
      linearCanonicalPrepared z := rfl
  intro s
  have hs := hf s
  rw [hbody] at hs
  simpa only [linearCanonicalCode,List.append_assoc] using hs

theorem linear_canonical_ok {s : State} {z : Reg} {n : Nat}
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0)
    (hn : n<2*(2^521-1)) (hv : regsVal s linearRegs9=n+1) :
    WP isa (.block (linearCanonicalCode z)) s fun t =>
      regsVal t linearRegs9=n%(2^521-1) ∧ regsVal t linearRegs9<2^521-1 ∧
      t.gpr .x0=512 ∧ VG.Proof.Ed25519.AArch64.Keeps (.x0::.x4::linearRegs9) s t := by
  obtain ⟨t,ht,hq⟩ := VG.AArch64.Interleave.runBlock_of_WP (linear_canonical_prepared_ok hz hzv hn hv)
  exact WP.of_runBlock ⟨t,(linear_canonical_schedule z hz s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def linearSetCarry : List Instr := [.subs .x .x0 .x0 .x0]

theorem linear_set_carry_ok (s : State) :
    WP isa (.block linearSetCarry) s fun t =>
      t.gpr .x0=0 ∧ t.c=true ∧ Keeps [.x0] s t := by
  have hself (v : BitVec 64) : carryOut v (~~~v) true=true := by
    simp only [carryOut,BitVec.toNat_not,Bool.toNat_true,decide_eq_true_eq]
    have h := v.isLt
    omega_arith
  apply WP.of_runBlock
  simp only [linearSetCarry,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,BitVec.setWidth_eq,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,?_,?_,?_,?_⟩⟩
  · exact point_self_sub _
  · exact hself _
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry,hr,ite_false]
  · simp only [RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)
open VG.Proof.Ed25519.AArch64

def linearAddClob : List Reg := [.x0,.x3,.x4]++linearRegs9

def linearAddNormalized (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) (z : Reg) : List Instr :=
  loadsR ra linearRegs9 a++linearSetCarry++linearSum rb b++linearCanonicalCode z++storesR ro linearRegs9 o

theorem linear_add_normalized_ok {s : State} {pa pb po : Addr} {ra rb ro z : Reg} {size cap room a b o : Nat}
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ho : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉linearAddClob) (hrb : rb∉linearAddClob) (hro : ro∉linearAddClob)
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0)
    (hva : wordsVal s.mem pa a 9<2^521-1) (hvb : wordsVal s.mem pb b 9<2^521-1) :
    WP isa (.block (linearAddNormalized ra a rb b ro o z)) s fun t =>
      wordsVal t.mem po o 9=(wordsVal s.mem pa a 9+wordsVal s.mem pb b 9)%(2^521-1) ∧
      wordsVal t.mem po o 9<2^521-1 ∧ t.gpr .x0=512 ∧
      KeepRegs linearAddClob s t ∧ Outside po o 72 s.mem t.mem := by
  have incl9 : ∀r∈linearRegs9,r∈linearAddClob := by decide
  have incl0 : ∀r∈([Reg.x0] : List Reg),r∈linearAddClob := by decide
  have inclsum : ∀r∈(.x3::.x4::linearRegs9),r∈linearAddClob := by decide
  have inclcanon : ∀r∈(.x0::.x4::linearRegs9),r∈linearAddClob := by decide
  rw [linearAddNormalized,List.append_assoc,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadsR_ok linearRegs9 ha (by simpa only [show linearRegs9.length=9 from by decide] using hA)
    ha8 (by decide) (fun h => hra (incl9 _ h))) fun u ⟨au,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (linear_set_carry_ok u) fun v ⟨_,cv,kv⟩ => ?_
  have kuv : Keeps linearAddClob s v := (ku.mono incl9).trans (kv.mono incl0)
  have hbv := hb.of_keeps kuv hrb
  have av : regsVal v linearRegs9=wordsVal s.mem pa a 9 :=
    (regsVal_congr fun r h => kv.gpr r ((by decide : ∀r∈linearRegs9,r∉[Reg.x0]) r h)).trans (by simpa only [show linearRegs9.length=9 from by decide] using au)
  have sumBound : regsVal v linearRegs9+wordsVal v.mem pb b 9+v.c.toNat<2^576 := by
    rw [av,kuv.mem,cv]
    simp only [Bool.toNat_true]
    omega_using [hva,hvb]
  rw [WP.block_append_iff]
  refine WP.mono (linear_sum_ok hbv hB hb8 (fun h => hrb ((by decide : ∀r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13],r∈linearAddClob) _ h)) sumBound)
    fun w ⟨aw,kw⟩ => ?_
  have kw' : Keeps linearAddClob v w := kw.mono inclsum
  have allw := kuv.trans kw'
  have hzNot : z∉linearAddClob := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide
  have hzw : w.gpr z=0 := (allw.gpr z hzNot).trans hzv
  rw [av,kuv.mem,cv] at aw
  simp only [Bool.toNat_true] at aw
  have hn : wordsVal s.mem pa a 9+wordsVal s.mem pb b 9<2*(2^521-1) := by omega_using [hva,hvb]
  rw [WP.block_append_iff]
  refine WP.mono (linear_canonical_ok hz hzw hn aw) fun x ⟨ax,bx,zx,kx⟩ => ?_
  have allx := allw.trans (kx.mono inclcanon)
  have hox := ho.of_keepRegs (Keeps.regs allx) hro
  refine WP.mono (storesR_ok linearRegs9 hox (by simpa only [show linearRegs9.length=9 from by decide] using hO)
    ho8 (by decide)) fun t ⟨stored,kt,ot⟩ => ?_
  have hs0 : t.gpr .x0=x.gpr .x0 := kt.gpr .x0 (by simp)
  simp only [show linearRegs9.length=9 from by decide] at stored ot
  exact ⟨stored.trans ax,stored ▸ bx,hs0.trans zx,
    (Keeps.regs allx).trans (kt.mono (by simp)),by rw [allx.mem] at ot; exact ot⟩

end VG.Proof.Mont.AArch64.P521Field
