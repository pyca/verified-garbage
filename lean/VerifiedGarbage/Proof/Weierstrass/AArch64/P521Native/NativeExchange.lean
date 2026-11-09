module

-- separate module: the consolidated stack/save/restore and API body replay costs 0.79s of local elaboration/kernel work versus 0.52s importing dependencies; the generic security registration reuses this whole-function functional proof.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeBodyCorrectness
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NativeEntry
import VerifiedGarbage.Proof.Framework.AArch64.Call

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native (config body)

 theorem native_body_api_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) {s : State}
    (pre : (VG.Spec.Ecdh.Instance.exchangeContract VG.Spec.EcKey.P521.inst abi 3456).pre s) :
    WP isa body (allocated 3456 s) fun t =>
      (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VG.Proof.Ecdh.AArch64.EPost config s t ∧
      t.rd=(allocated 3456 s).rd ∧ t.wr=(allocated 3456 s).wr ∧ t.sp=(allocated 3456 s).sp ∧
      t.gpr .x27=s.gpr .x27 ∧ t.gpr .x28=s.gpr .x28 ∧ t.v .v31=s.v .v31 := by
  have bodyPre := native_body_pre pre
  have orderBound : 17≤config.C.n := by decide +kernel
  refine WP.mono (native_body_raw_ok hc law ha order orderBound bodyPre) fun t raw => ?_
  have correct := native_body_correctness hc law ha order bodyPre.stack raw
  obtain ⟨ready,P,front,mid,xv,x,y,parseX,parseY,selected,hP,pne,kbound,offset,arith,window,
    original,b,xb,value,bytes,ret,saved,rd,wr,sp,g27,g28,v31⟩ := raw
  exact ⟨saved,correct,rd,wr,sp,g27,g28,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Ecdsa.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Weierstrass
open VG.Proof.Ecdh.AArch64 VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config body exchange outerBlock000 outerBlock172)

private theorem epost_keep {c : Cfg} {s t v : State} (h : EPost c s t)
    (mem : v.mem=t.mem) (reg : v.gpr .x0=t.gpr .x0) : EPost c s v := by
  unfold EPost at h ⊢
  rw [mem,reg]
  exact h

 theorem native_exchange_api_ok (hc : BaseCfgOk config) (law : Law config.C) (ha : AM3 config.C)
    (order : PrimeOrder config.C) {s : State} (pre : nativeContract.pre s) :
    WP isa exchange s fun t => EPost config s t ∧
      (∀r∈[Reg.x19,Reg.x20,Reg.x21,Reg.x22,Reg.x23,Reg.x24,Reg.x25,Reg.x26,Reg.x27,Reg.x28,Reg.x30],t.gpr r=s.gpr r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  have entry := native_pre_saved pre
  have stack := prepare_stack_pre entry
  change WP isa (.seq (.block outerBlock000) (.seq (.frame (.alloc 3456) body (.free 3456)) (.seq (.block outerBlock172) (.block [])))) s _
  apply WP.seq
  refine WP.mono (native_prologue_ok s) fun u hu => ?_
  subst u
  apply WP.seq
  apply WP.alloc (by decide) stack.room
  refine WP.mono (native_body_api_ok hc law ha order entry) fun t ⟨saved,api,rd,wr,sp,g27,g28,v31⟩ => ?_
  apply WP.seq
  refine WP.mono (native_epilogue_ok (freed 3456 t)) fun v hv => ?_
  obtain ⟨g26,keep,_⟩ := hv
  apply WP.block_nil
  have reg r (hr : r≠Reg.x26) : v.gpr r=t.gpr r := keep.gpr r (by simpa using hr)
  refine ⟨?_,?_,?_,?_,?_⟩
  · change EPost config s v
    change EPost config s t at api
    have mem : v.mem=t.mem := by simpa only [freed] using keep.mem
    exact epost_keep api mem (reg .x0 (by decide))
  · intro r hr
    by_cases eq26 : r=Reg.x26
    · subst r
      rw [g26]
      change (t.v .v31).extractLsb' 64 64=s.gpr .x26
      rw [v31,native_saved_high]
    · rw [reg r eq26]
      have cases : r∈Cfg.saved.map Prod.fst ∨ r=Reg.x27 ∨ r=Reg.x28 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false,Cfg.saved,List.map_cons,List.map_nil] at hr ⊢
        rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|bad|rfl|rfl|rfl <;> simp_all
      rcases cases with h|rfl|rfl
      · exact saved r h
      · exact g27
      · exact g28
  · have vr : v.rd=t.rd := by simpa only [freed] using keep.rd
    have tr : t.rd=s.rd := rd
    exact vr.trans tr
  · change v.wr=s.wr
    rw [keep.wr]
    change t.wr.tail=s.wr
    rw [wr]
    rfl
  · rw [keep.sp]
    change t.sp+3456#64=s.sp
    rw [sp]
    exact BitVec.sub_add_cancel _ _

end VG.Proof.Weierstrass.AArch64.P521Native
