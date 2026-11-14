module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeBody
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Framework.Block

/-! The complete ordinary multiplier, with admitted input/output aliases,
higher workspace offsets, canonical output and all ABI obligations. -/

-- separate module: function wrapper around the measured arithmetic kernel
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (saves_ok insCode lane fieldPrime)
open VG.Impl.Mont.AArch64.P521Square (slot)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off Outside.of_off)

theorem native_mul_fn_ok {s : State} {W o a b : Nat} (hp : NativePre s W o a b)
    (ha : wordsVal s.mem (s.gpr .x0) a 9<fieldPrime)
    (hb : wordsVal s.mem (s.gpr .x0) b 9<fieldPrime) :
    WP isa mulFn s fun t =>
      abiPreserved s t ∧
      (wordsVal t.mem (s.gpr .x0) o 9<fieldPrime ∧
        wordsVal t.mem (s.gpr .x0) o 9=
          wordsVal s.mem (s.gpr .x0) a 9*wordsVal s.mem (s.gpr .x0) b 9%fieldPrime) ∧
      (∀x,(ofs (s.gpr .x0) x<o ∨ o+72≤ofs (s.gpr .x0) x) →
        (ofs (s.gpr .x0) x<3952 ∨ 4016≤ofs (s.gpr .x0) x) → t.mem x=s.mem x) ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      (∀d,(∀i,i<12 → d≠(slot i).1) → t.v d=s.v d) := by
  let base := s.gpr .x0
  let pa := off base a
  let pb := off base b
  let po := off base o
  let pt := off base 3952
  rw [mulFn,nativeMul_body,WP.block_append_iff]
  refine WP.mono (saves_ok nativeSaved 0 (s:=s) (by decide)) fun u ⟨ku,lanes,_,vu⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (native_pointers_ok u) fun v ⟨go,ga,gb,gt,gw,kv,vv⟩ => ?_
  have memv : v.mem=s.mem := kv.mem.trans ku.mem
  have rdv : v.rd=s.rd := kv.rd.trans ku.rd
  have wrv : v.wr=s.wr := kv.wr.trans ku.wr
  have gpo : v.gpr .x0=po := by rw [go,ku.gpr,hp.argO]
  have gpa : v.gpr .x1=pa := by rw [ga,ku.gpr,hp.argA]
  have gpb : v.gpr .x2=pb := by rw [gb,ku.gpr,hp.argB]
  have gpt : v.gpr .x27=pt := by rw [gt,ku.gpr]
  have gws : v.gpr .x28=base := by rw [gw,ku.gpr]
  have ap := workspace_ptr hp.workspace hp.inputA gpa rdv wrv
  have bp := workspace_ptr hp.workspace hp.inputB gpb rdv wrv
  have tp := workspace_ptrW hp.workspace (by have h:=hp.scratch; omega_arith)
    (by decide : 0<64) gpt wrv
  have stable : StableInput v pa pt := by
    intro m hm d hd
    rw [memv] at hm ⊢
    exact stable_workspace_input hp m hm d hd
  have ha' : wordsVal v.mem pa 0 9<fieldPrime := by
    rw [memv,wordsVal_off,Nat.add_zero]; exact ha
  have hb' : wordsVal v.mem pb 0 9<fieldPrime := by
    rw [memv,wordsVal_off,Nat.add_zero]; exact hb
  rw [WP.block_append_iff]
  refine WP.mono (arithmetic_vectors ap bp tp stable ha' hb') fun w ⟨⟨bound,prod,om,kw⟩,vw⟩ => ?_
  have gpw : w.gpr .x0=po := (kw.gpr _ (by decide)).trans gpo
  have wrw : w.wr=s.wr := kw.wr.trans wrv
  have op := workspace_ptrW hp.workspace hp.output (by decide : 0<72) gpw wrw
  rw [WP.block_append_iff]
  refine WP.mono (stores_vectors op) fun y ⟨⟨stored,ky,oy⟩,vy⟩ => ?_
  refine WP.mono (native_exit_ok y) fun t ⟨reset,restored,kt,vt⟩ => ?_
  have out : wordsVal t.mem base o 9=regsVal w bRegs := by
    rw [kt.mem]
    have e := stored
    change wordsVal y.mem (off base o) 0 9=regsVal w bRegs at e
    rw [wordsVal_off,Nat.add_zero] at e
    exact e
  have prod' : regsVal w bRegs=wordsVal s.mem base a 9*wordsVal s.mem base b 9%fieldPrime := by
    rw [prod,memv,wordsVal_off,wordsVal_off,Nat.add_zero,Nat.add_zero]
  have vec : ∀d,(∀i,i<12 → d≠(slot i).1) → t.v d=s.v d := by
    intro d hd
    rw [vt,vy,vw,vv,vu d hd]
  have saved : ∀r∈nativeSaved,t.gpr r=s.gpr r := by
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
    have e := lanes i hi
    rw [Nat.zero_add] at e
    rw [restored i hi,vy,vw,vv]
    exact e
  have link : t.gpr .x30=s.gpr .x30 := by
    rw [kt.gpr _ (by decide),ky.gpr _ (by decide),kw.gpr _ (by decide),
      kv.gpr _ (by decide),ku.gpr]
  have sp : t.sp=s.sp := kt.sp.trans (ky.sp.trans (kw.sp.trans (kv.sp.trans ku.sp)))
  refine ⟨⟨?_,sp,?_⟩,⟨by rw [out]; exact bound,by rw [out,prod']⟩,?_,?_,?_,?_,vec⟩
  · intro r hr
    have hpres : preserved=nativeSaved++[.x30] := by decide
    rw [hpres,List.mem_append] at hr
    rcases hr with hr | hr
    · exact saved r hr
    · have h : r=.x30 := List.mem_singleton.mp hr
      rw [h]; exact link
  · intro d hd
    have h : ∀d∈preservedV,∀i,i<12 → d≠(slot i).1 := by decide
    rw [vec d (h d hd)]
  · intro x ho htmp
    have os := Outside.of_off om (by decide : 3952+64<2^64)
    have oo := Outside.of_off oy (by
      have hfit:=hp.workspace.enc; have hO:=hp.output; omega_arith)
    rw [kt.mem,oo x ho,os x htmp,memv]
  · rw [reset,ky.gpr _ (by decide),kw.gpr _ (by decide),gws]
  · rw [kt.rd,ky.rd,kw.rd,rdv]
  · rw [kt.wr,ky.wr,kw.wr,wrv]

end VG.Proof.Mont.AArch64.P521Field
