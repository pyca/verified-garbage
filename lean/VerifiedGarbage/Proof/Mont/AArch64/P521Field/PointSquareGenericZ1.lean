module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointProduct
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointLowZ1
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.StreamValue
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointReduction

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Impl.Mont.AArch64.P521Square (aRegs)

def pointLowZ1Code : List Instr := pointCross0Z1Code ++ pointCross1Z1Code ++ pointCross2Z1Code ++
  pointCross3Z1Code ++ pointDoubleZ1Code ++ pointDiagCode

def pointProductZ1Code (rn : Reg) (off : Nat) : List Instr := pointLowZ1Code ++
  ([.ldr .x .x1 rn off] : List Instr) ++ pointSquareTopCode ++ [.mul .x .x2 .x2 .x2]

theorem point_product_z1_ok (s : State) (rn : Reg) (off : Nat) (ho : off%8=0 ∧ off<32768)
    (hr : InRegions (s.rd++s.wr) (s.gpr rn+BitVec.ofNat 64 off) 8)
    (hrn : rn∉pointLowClob) (hz : s.gpr .x1=0)
    (ht : (s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64).toNat<512) :
    WP isa (.block (pointProductZ1Code rn off)) s fun t =>
      regsVal t pointProductRegs =
        (regsVal s (aRegs.take 8)+13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64).toNat) *
        (regsVal s (aRegs.take 8)+13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64).toNat) ∧
      t.gpr .x6=0 ∧ Keeps pointFullProductClob s t := by
  rw [pointProductZ1Code,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (point_low_z1_ok s hz) fun u ⟨lo,kl⟩ => ?_
  have hr' : InRegions (u.rd++u.wr) (u.gpr rn+BitVec.ofNat 64 off) 8 := by
    rw [kl.rd,kl.wr,kl.gpr rn hrn]
    exact hr
  rw [WP.block_append_iff]
  refine WP.mono (point_load_top u rn off ho hr') fun v ⟨hv,kr⟩ => ?_
  have hv' : v.gpr .x1=s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64 := by
    rw [hv,kl.mem,kl.gpr rn hrn]
  have htv : (v.gpr .x1).toNat<512 := by rw [hv']; exact ht
  have lowv : regsVal v (aRegs.take 8)=regsVal s (aRegs.take 8) :=
    regsVal_congr (fun r hr => (kr.gpr r ((show ∀r∈aRegs.take 8,r∉[Reg.x1] from by decide) r hr)).trans
      (kl.gpr r ((show ∀r∈aRegs.take 8,r∉pointLowClob from by decide) r hr)))
  have lov : (v.gpr .x2*v.gpr .x2).toNat + 18446744073709551616*(v.gpr .x11).toNat + 340282366920938463463374607431768211456*(v.gpr .x12).toNat + 6277101735386680763835789423207666416102355444464034512896*(v.gpr .x13).toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*(v.gpr .x14).toNat + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576*(v.gpr .x15).toNat + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816*(v.gpr .x16).toNat + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656*(v.gpr .x17).toNat + 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(v.gpr .x19).toNat + 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136*(v.gpr .x20).toNat + 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776*(v.gpr .x21).toNat + 84162174424773976115855838126082058648805436845170781751972494449099714468753293153818664580441415219631727501698851483408310916002940861810045036330430093599283578738055113571066620126149163476340692027772502016*(v.gpr .x22).toNat + 1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856*(v.gpr .x23).toNat + 28638903918474961204418783933674838490721739172170652529441449702311064005352904159345284265824628375429359509218999720074396860757073376700445026041564579620512874307979212102266801261478978776245040008231745247475930553606737583615358787106474295296*(v.gpr .x24).toNat + 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336*(v.gpr .x25).toNat + 9745314011399999080353382387875188310876226857595007526867906457212948690766426102465615065882010259225304916231408668183459169865203094046577987296312653419531277699956473029870789655490053648352799593479218378873685597925394874945746363615468965612827738803104277547081828589991914110976*(v.gpr .x0).toNat =
      regsVal v (aRegs.take 8)*regsVal v (aRegs.take 8) := by
    rw [lowv]
    rw [kr.gpr .x2 (by decide)]
    rw [kr.gpr .x11 (by decide)]
    rw [kr.gpr .x12 (by decide)]
    rw [kr.gpr .x13 (by decide)]
    rw [kr.gpr .x14 (by decide)]
    rw [kr.gpr .x15 (by decide)]
    rw [kr.gpr .x16 (by decide)]
    rw [kr.gpr .x17 (by decide)]
    rw [kr.gpr .x19 (by decide)]
    rw [kr.gpr .x20 (by decide)]
    rw [kr.gpr .x21 (by decide)]
    rw [kr.gpr .x22 (by decide)]
    rw [kr.gpr .x23 (by decide)]
    rw [kr.gpr .x24 (by decide)]
    rw [kr.gpr .x25 (by decide)]
    rw [kr.gpr .x0 (by decide)]
    rw [kl.gpr .x2 (by decide)]
    exact lo
  refine WP.mono (point_product_finish v htv lov) fun t ⟨prod,hz,kp⟩ => ?_
  refine ⟨?_,hz,(kl.mono (by decide)).trans ((kr.mono (by decide)).trans (kp.mono (by decide)))⟩
  rw [prod,point_input_split,lowv,hv']

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (loadsR)
open VG.Impl.Mont.AArch64.P521Square (aRegs)

def pointLoadedProductZ1 (rn : Reg) (d : Nat) : List Instr :=
  loadsR rn (aRegs.take 8) d ++ pointProductZ1Code rn (d+64)

theorem point_loaded_product_z1_ok {s : State} {rn : Reg} {p : Addr} {size d : Nat}
    (hp : Ptr s rn p size) (hd : d+72≤size) (ha8 : d%8=0)
    (hrn : rn∉pointFullProductClob) (hz : s.gpr .x1=0)
    (ha : wordsVal s.mem p d 9<2^521) :
    WP isa (.block (pointLoadedProductZ1 rn d)) s fun t =>
      regsVal t pointProductRegs=wordsVal s.mem p d 9*wordsVal s.mem p d 9 ∧
      t.gpr .x6=0 ∧ VG.Proof.Ed25519.AArch64.Keeps pointFullProductClob s t := by
  have hr : rn∉aRegs.take 8 := fun h => hrn
    ((show ∀r∈aRegs.take 8,r∈pointFullProductClob from by decide) rn h)
  have hrLow : rn∉pointLowClob := fun h => hrn
    ((show ∀r∈pointLowClob,r∈pointFullProductClob from by decide) rn h)
  rw [pointLoadedProductZ1,WP.block_append_iff]
  refine WP.mono (loadsR_ok (aRegs.take 8) hp (by simpa only [aRegs,List.take,List.length_cons,List.length_nil] using Nat.le_trans (by omega_arith : d+64≤d+72) hd)
    ha8 (by decide) hr) fun u ⟨loaded,kl,_⟩ => ?_
  have zu : u.gpr .x1=0 := (kl.gpr .x1 (by decide)).trans hz
  have hu := hp.of_keeps kl hr
  have hread : InRegions (u.rd++u.wr) (u.gpr rn+BitVec.ofNat 64 (d+64)) 8 := by
    rw [hu.reg]
    exact hu.ld (d+64) (by omega_arith)
  have hone : wordsVal s.mem p (d+64) 1=(word s.mem p (d+64)).toNat := by
    simp only [wordsVal,Nat.mul_zero,Nat.add_zero]
  have he := wordsVal_split s.mem p d 8 1
  simp only [Nat.reduceAdd,Nat.reduceMul,hone] at he
  have hp512 : (2:Nat)^512=13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by decide +kernel
  have hp521 : (2:Nat)^521=6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152 := by decide +kernel
  rw [hp512] at he
  have ha' := ha
  rw [hp521] at ha'
  have htop : (u.mem.readW (u.gpr rn+BitVec.ofNat 64 (d+64)) 64).toNat<512 := by
    rw [kl.mem,hu.reg]
    change (word s.mem p (d+64)).toNat<512
    omega_using [he,ha']
  refine WP.mono (point_product_z1_ok u rn (d+64) ⟨by omega_arith,by have := hu.enc; omega_arith⟩
    hread hrLow zu htop) fun t ⟨prod,hz,kp⟩ => ?_
  refine ⟨?_,hz,(kl.mono (by decide)).trans kp⟩
  simp only [show (aRegs.take 8).length=8 from by decide] at loaded
  rw [prod,loaded,kl.mem,hu.reg]
  rw [←he]

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 (storesR)
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def pointSquareNormalizedZ1 (rn : Reg) (d : Nat) (rt : Reg) (o : Nat) : List Instr :=
  pointLoadedProductZ1 rn d ++ (pointFoldCode++(pointCorrectCode++storesR rt pointFoldOutRegs o))

theorem point_square_normalized_z1_ok {s : State} {rn rt : Reg} {p q : Addr} {size cap d o : Nat}
    (hp : Ptr s rn p size) (hq : PtrW s rt q cap)
    (hd : d+72≤size) (ho : o+72≤cap) (hd8 : d%8=0) (ho8 : o%8=0)
    (hz : s.gpr .x1=0) (hrn : rn∉pointFullProductClob) (hrt : rt∉pointFullProductClob)
    (ha : wordsVal s.mem p d 9<fieldPrime) :
    WP isa (.block (pointSquareNormalizedZ1 rn d rt o)) s fun t =>
      wordsVal t.mem q o 9<fieldPrime ∧
      wordsVal t.mem q o 9=(wordsVal s.mem p d 9*wordsVal s.mem p d 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q o 72 s.mem t.mem := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have h := Nat.sub_le ((2:Nat)^521) 1
    exact h
  have ha' : wordsVal s.mem p d 9<2^521 := Nat.lt_of_lt_of_le ha fieldBound
  rw [pointSquareNormalizedZ1,WP.block_append_iff]
  refine WP.mono (point_loaded_product_z1_ok hp hd hd8 hrn hz ha') fun u ⟨prod,z6,kp⟩ => ?_
  have hu : regsVal u pointProductRegs<fieldPrime*fieldPrime := by
    rw [prod]
    exact Nat.mul_lt_mul'' ha ha
  rw [←List.append_assoc,WP.block_append_iff]
  refine WP.mono (point_reduce_ok z6 hu) fun v ⟨canon,val,z1,mask,kr⟩ => ?_
  have kv := kp.trans (kr.mono (by decide))
  have hqv := hq.of_keepRegs (Keeps.regs kv) hrt
  refine WP.mono (storesR_ok pointFoldOutRegs hqv (o:=o) (by simpa only
    [show pointFoldOutRegs.length=9 from rfl] using ho) ho8 (by decide))
    fun t ⟨stored,ks,frame⟩ => ?_
  change wordsVal t.mem q o 9=regsVal v pointFoldOutRegs at stored
  exact ⟨by rw [stored]; exact canon,by rw [stored,val,prod],
    (ks.gpr .x1 (by decide)).trans z1,(ks.gpr .x0 (by decide)).trans mask,
    (Keeps.regs kv).trans (ks.mono (by decide)),by rw [kv.mem] at frame; exact frame⟩

end VG.Proof.Mont.AArch64.P521Field
