module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointProductFinish
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block

/-! Product composition with the top input loaded at its measured late position. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Square (aRegs)
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

def pointLowCode : List Instr := pointCross0Code ++ pointCross1Code ++ pointCross2Code ++
  pointCross3Code ++ pointDoubleCode ++ pointDiagCode

def pointProductCode (rn : Reg) (off : Nat) : List Instr := pointLowCode ++
  ([.ldr .x .x1 rn off] : List Instr) ++ pointSquareTopCode ++ [.mul .x .x2 .x2 .x2]

def pointFullProductClob : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25]

theorem point_input_split (s : State) : regsVal s pointInputRegs =
    regsVal s (aRegs.take 8) + 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(s.gpr .x1).toNat := by
  simp only [pointInputRegs,aRegs,List.take,regsVal]
  omega_arith

theorem point_load_top (s : State) (rn : Reg) (off : Nat) (ho : off%8=0 ∧ off<32768)
    (hr : InRegions (s.rd++s.wr) (s.gpr rn+BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldr .x .x1 rn off]) s fun t =>
      t.gpr .x1=s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec_ldr_x ho hr,
    RegUpd.gpr_write_self,BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩⟩
  reg_keeps

theorem point_product_ok (s : State) (rn : Reg) (off : Nat) (ho : off%8=0 ∧ off<32768)
    (hr : InRegions (s.rd++s.wr) (s.gpr rn+BitVec.ofNat 64 off) 8)
    (hrn : rn∉pointLowClob)
    (ht : (s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64).toNat<512) :
    WP isa (.block (pointProductCode rn off)) s fun t =>
      regsVal t pointProductRegs =
        (regsVal s (aRegs.take 8)+13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64).toNat) *
        (regsVal s (aRegs.take 8)+13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096*(s.mem.readW (s.gpr rn+BitVec.ofNat 64 off) 64).toNat) ∧
      t.gpr .x6=0 ∧ Keeps pointFullProductClob s t := by
  rw [pointProductCode,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (point_low_ok s) fun u ⟨lo,kl⟩ => ?_
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
