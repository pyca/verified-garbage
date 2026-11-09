module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearMask
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearBorrow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.HoistMarked
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.LinearAdd

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field

theorem linear_sub_correction_math {F R a b d w : Nat} {c co : Bool}
    (hF : 0<F) (hR : F≤R) (hmod : R%F=0)
    (ha : a<F-1) (hb : b<F-1) (hd : d<R) (hw : w<R)
    (ed : d+b=a+R*(!c).toNat) (ew : w+(!c).toNat=d+R*(!co).toNat) :
    w%F=(a+(F-1)-b)%(F-1) ∧ w%F<F-1 := by
  have hc := P521Linear.subtraction_correction (p:=F-1) (R:=R) ha hb
    (by simpa only [Nat.sub_add_cancel hF] using hR)
    (by simpa only [Nat.sub_add_cancel hF] using hmod) hd hw ed ew
  simpa only [Nat.sub_add_cancel hF] using hc

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def linearSubCorrect (z : Reg) : List Instr := linearBorrow z linearRegs9++linearMaskTop

theorem linear_sub_correct_ok {s : State} {z : Reg} {a b : Nat}
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0) (hm : s.gpr .x0=511)
    (ha : a<2^521-1) (hb : b<2^521-1)
    (hd : regsVal s linearRegs9+b=a+2^576*(!s.c).toNat) :
    WP isa (.block (linearSubCorrect z)) s fun t =>
      regsVal t linearRegs9=(a+(2^521-1)-b)%(2^521-1) ∧ regsVal t linearRegs9<2^521-1 ∧
      t.gpr .x0=511 ∧ Keeps linearRegs9 s t := by
  rw [linearSubCorrect,WP.block_append_iff]
  refine WP.mono (linear_borrow_ok z linearRegs9 s (by decide) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide) hzv) fun u ⟨eu,ku⟩ => ?_
  have hum : u.gpr .x0=511 := (ku.gpr .x0 (by decide)).trans hm
  have hslt : regsVal s linearRegs9<2^576 := by
    simpa only [show linearRegs9.length=9 from by decide,Nat.reduceMul] using regsVal_lt s linearRegs9
  have hult : regsVal u linearRegs9<2^576 := by
    simpa only [show linearRegs9.length=9 from by decide,Nat.reduceMul] using regsVal_lt u linearRegs9
  simp only [show linearRegs9.length=9 from by decide,Nat.reduceMul] at eu
  have math : regsVal u linearRegs9%(2^521)=(a+(2^521-1)-b)%(2^521-1) ∧
      regsVal u linearRegs9%(2^521)<2^521-1 := by
    have hF : 0<(2:Nat)^521 := by lit_decide
    have hR : (2:Nat)^521≤2^576 := by lit_decide
    have hmod : (2:Nat)^576%(2^521)=0 := by lit_decide
    generalize hfe : (2:Nat)^521=F at ha hb hF hR hmod ⊢
    generalize hre : (2:Nat)^576=R at hd hslt hult eu hR hmod
    exact linear_sub_correction_math hF hR hmod ha hb hslt hult hd eu
  refine WP.mono (linear_mask_top_ok u hum) fun t ⟨et,mt,kt⟩ => ?_
  exact ⟨et.trans math.1,et ▸ math.2,mt,ku.trans (kt.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def linearSetMask : List Instr := [.movz .x .x0 511 0]

theorem linear_set_mask_ok (s : State) :
    WP isa (.block linearSetMask) s fun t =>
      t.gpr .x0=511 ∧ t.c=s.c ∧ Keeps [.x0] s t := by
  apply WP.of_runBlock
  simp only [linearSetMask,runBlock_cons,runStep_some,runBlock_nil,reduceExec,
    RegUpd.gpr_write,RegUpd.c_write,BitVec.setWidth_eq,Size.bits,Nat.mul_zero,Nat.reduceLT,ite_true,
    Option.some.injEq,exists_eq_left']
  exact ⟨rfl,True.intro,⟨by intro r h; simp only [List.mem_singleton] at h; simp only [RegUpd.gpr_write,h,ite_false],
    by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def linearSubFresh (z : Reg) : List Instr := linearBorrow z linearRegs9++linearSetMask++linearMaskTop

theorem linear_sub_fresh_ok {s : State} {z : Reg} {a b : Nat}
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0)
    (ha : a<2^521-1) (hb : b<2^521-1)
    (hd : regsVal s linearRegs9+b=a+2^576*(!s.c).toNat) :
    WP isa (.block (linearSubFresh z)) s fun t =>
      regsVal t linearRegs9=(a+(2^521-1)-b)%(2^521-1) ∧ regsVal t linearRegs9<2^521-1 ∧
      t.gpr .x0=511 ∧ Keeps (.x0::linearRegs9) s t := by
  have hcheck : hoistMarked (fun i => i == .movz .x .x0 511 0) .x28 (linearSubFresh z)=
      some (linearSetMask,linearSubCorrect z) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide
  apply WP.hoistMarked hcheck
  rw [WP.block_append_iff]
  refine WP.mono (linear_set_mask_ok s) fun u ⟨mu,cu,ku⟩ => ?_
  have uz : u.gpr z=0 := (ku.gpr z (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide)).trans hzv
  have ud : regsVal u linearRegs9+b=a+2^576*(!u.c).toNat := by
    rw [cu,regsVal_congr (fun r h => ku.gpr r ((by decide : ∀r∈linearRegs9,r∉[Reg.x0]) r h))]
    exact hd
  refine WP.mono (linear_sub_correct_ok hz uz mu ha hb ud) fun t ⟨vt,bt,mt,kt⟩ => ?_
  exact ⟨vt,bt,mt,(ku.mono (by simp)).trans (kt.mono (fun _ h => List.mem_cons_of_mem _ h))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64

def linearSubFinish (reuse : Bool) (z : Reg) : List Instr :=
  if reuse then linearSubCorrect z else linearSubFresh z

theorem linear_sub_finish_ok {s : State} {z : Reg} {a b : Nat} (reuse : Bool)
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0) (hm : reuse=true → s.gpr .x0=511)
    (ha : a<2^521-1) (hb : b<2^521-1)
    (hd : regsVal s linearRegs9+b=a+2^576*(!s.c).toNat) :
    WP isa (.block (linearSubFinish reuse z)) s fun t =>
      regsVal t linearRegs9=(a+(2^521-1)-b)%(2^521-1) ∧ regsVal t linearRegs9<2^521-1 ∧
      t.gpr .x0=511 ∧ Keeps linearAddClob s t := by
  cases reuse
  · change WP isa (.block (linearSubFresh z)) s _
    exact WP.mono (linear_sub_fresh_ok hz hzv ha hb hd) fun t ⟨v,b,m,k⟩ =>
      ⟨v,b,m,k.mono (by decide)⟩
  · change WP isa (.block (linearSubCorrect z)) s _
    exact WP.mono (linear_sub_correct_ok hz hzv (hm rfl) ha hb hd) fun t ⟨v,b,m,k⟩ =>
      ⟨v,b,m,k.mono (by decide)⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR storesR)
open VG.Proof.Ed25519.AArch64

def linearSubNormalized (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) (z : Reg) (reuse : Bool) : List Instr :=
  loadsR ra linearRegs9 a++linearDifference rb b++linearSubFinish reuse z++storesR ro linearRegs9 o

theorem linear_sub_normalized_ok {s : State} {pa pb po : Addr} {ra rb ro z : Reg} {size cap room a b o : Nat}
    (reuse : Bool)
    (ha : Ptr s ra pa size) (hb : Ptr s rb pb cap) (ho : PtrW s ro po room)
    (hA : a+72≤size) (hB : b+72≤cap) (hO : o+72≤room)
    (ha8 : a%8=0) (hb8 : b%8=0) (ho8 : o%8=0)
    (hra : ra∉linearAddClob) (hrb : rb∉linearAddClob) (hro : ro∉linearAddClob)
    (hz : z∈[Reg.x1,.x2]) (hzv : s.gpr z=0) (hm : reuse=true → s.gpr .x0=511)
    (hva : wordsVal s.mem pa a 9<2^521-1) (hvb : wordsVal s.mem pb b 9<2^521-1) :
    WP isa (.block (linearSubNormalized ra a rb b ro o z reuse)) s fun t =>
      wordsVal t.mem po o 9=(wordsVal s.mem pa a 9+(2^521-1)-wordsVal s.mem pb b 9)%(2^521-1) ∧
      wordsVal t.mem po o 9<2^521-1 ∧ t.gpr .x0=511 ∧
      KeepRegs linearAddClob s t ∧ Outside po o 72 s.mem t.mem := by
  have incl9 : ∀r∈linearRegs9,r∈linearAddClob := by decide
  have incldiff : ∀r∈(.x3::.x4::linearRegs9),r∈linearAddClob := by decide
  rw [linearSubNormalized,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadsR_ok linearRegs9 ha (by simpa only [show linearRegs9.length=9 from by decide] using hA)
    ha8 (by decide) (fun h => hra (incl9 _ h))) fun u ⟨au,ku,_⟩ => ?_
  have hb' := hb.of_keeps ku (fun h => hrb (incl9 _ h))
  rw [WP.block_append_iff]
  refine WP.mono (linear_difference_ok hb' hB hb8 (fun h => hrb ((by decide : ∀r∈[Reg.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13],r∈linearAddClob) _ h)))
    fun v ⟨dv,kv⟩ => ?_
  simp only [show linearRegs9.length=9 from by decide] at au
  rw [au,ku.mem] at dv
  have allv : Keeps linearAddClob s v := (ku.mono incl9).trans (kv.mono incldiff)
  have hzNot : z∉linearAddClob := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> decide
  have hz' : v.gpr z=0 := (allv.gpr z hzNot).trans hzv
  have hm' : reuse=true → v.gpr .x0=511 := fun h =>
    (kv.gpr .x0 (by decide)).trans ((ku.gpr .x0 (by decide)).trans (hm h))
  rw [WP.block_append_iff]
  refine WP.mono (linear_sub_finish_ok reuse hz hz' hm' hva hvb dv) fun w ⟨vw,bw,mw,kw⟩ => ?_
  have allw := allv.trans kw
  have how := ho.of_keepRegs (Keeps.regs allw) hro
  refine WP.mono (storesR_ok linearRegs9 how (by simpa only [show linearRegs9.length=9 from by decide] using hO)
    ho8 (by decide)) fun t ⟨stored,kt,ot⟩ => ?_
  simp only [show linearRegs9.length=9 from by decide] at stored ot
  exact ⟨stored.trans vw,stored ▸ bw,(kt.gpr .x0 (by simp)).trans mw,
    (Keeps.regs allw).trans (kt.mono (by simp)),by rw [allw.mem] at ot; exact ot⟩

end VG.Proof.Mont.AArch64.P521Field
