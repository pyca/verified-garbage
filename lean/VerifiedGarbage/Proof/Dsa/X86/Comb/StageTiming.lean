module

public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Impl.Dsa.X86.CombCore
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Core
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.CorePowerTiming
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.ToDual
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicVerified
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.SelectTable
import VerifiedGarbage.Proof.Dsa.X86.CorePowerLoad
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming

/-! ### `Dsa.X86.Comb.CorePowerTiming`, which only this module used -/

section

/-! ### `Dsa.X86.Comb.CallTiming`, which only this module used -/

section

/-! ### `Dsa.X86.WorkspaceCallTiming`, which only this module used -/

section

/-! Relational timing at the common cdecl workspace boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86

def WorkspacePair (base : Addr) (size : Nat) (P : Mem → Mem → Prop) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ Pow.Room (s.gpr .esp) base size ∧
    Pow.Room (t.gpr .esp) base size ∧ s.gpr .esp=t.gpr .esp ∧ P s.mem t.mem

theorem workspaceCall_entry {s : State} {base : Addr} {size : Nat}
    (S : Scr s base size) (room : Pow.Room (s.gpr .esp) base size) :
    Pow.Entry (pushed [Reg.eax,.edi] s).callEntry base size := by
  have low := room.1
  have bound := (s.gpr .esp).isLt
  have fit : 4*[Reg.eax,.edi].length+4≤(s.gpr .esp).toNat := by simp; omega_using [low]
  have sp : ((pushed [Reg.eax,.edi] s).callEntry.gpr .esp).toNat=(s.gpr .esp).toNat-12 :=
    callEntry_espNat fit
  refine ⟨?_,?_,?_,S.nowrap,?_⟩
  · rw [callEntry_argAddr0]
    refine ⟨below (s.gpr .esp) 8,List.mem_append_right _ (List.mem_cons_self ..),?_⟩
    change ((s.gpr .esp-BitVec.ofNat 32 8).setWidth 64-
      (s.gpr .esp-BitVec.ofNat 32 8).setWidth 64).toNat+4≤8
    rw [BitVec.sub_self]
    decide
  · rw [callEntry_arg fit (by decide) (by decide)]
    exact S.edi
  · exact List.mem_cons_of_mem _ S.wr
  · unfold StkOk
    rw [sp]
    have sep := room.2
    constructor <;> omega_arith

theorem workspaceCall_relCT {base : Addr} {size bytes : Nat} {P : Mem → Mem → Prop}
    {body : Prog isa} {name : String}
    (stable : ∀ {s t m n}, WorkspacePair base size P s t →
      Frame [below (s.gpr .esp) 12] s.mem m → Frame [below (t.gpr .esp) 12] t.mem n → P m n)
    (timing : RelCT isa (fun s t => Pow.Entry s base size ∧ Pow.Entry t base size ∧
      s.gpr .esp=t.gpr .esp ∧ P s.mem t.mem) body (fun _ _ => True)) :
    RelCT isa (WorkspacePair base size P)
      (.seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (bytes/8)))])
        (.frame (.push [.eax,.edi]) (.call name body) (.pop .eax 2))) (fun _ _ => True) := by
  refine RelCT.seq (R := WorkspacePair base size P) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T,RS,RT,SP,H⟩ E F
    have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (bytes/8)))]) s
        fun u => Keeps [.eax] s u ∧ u.mem=s.mem :=
      wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps,U.mem⟩
    obtain ⟨K,M⟩ := wp_result (W s) E
    obtain ⟨L,N⟩ := wp_result (W t) F
    refine ⟨?_,S.of_keeps K (by decide),T.of_keeps L (by decide),?_,?_,?_,?_⟩
    · cases E with
      | block E => cases F with
        | block F =>
          simp only [execBlock,isa,exec,readSrc,Option.map_some,addrs,srcAddrs,List.map_nil,
            List.nil_append,Option.some.injEq,Prod.mk.injEq] at E F
          exact E.2.symm.trans F.2
    · rw [K.1 .esp (by decide)]; exact RS
    · rw [L.1 .esp (by decide)]; exact RT
    · rw [K.1 .esp (by decide),L.1 .esp (by decide)]; exact SP
    · rw [M,N]; exact H
  · refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.2.2.2.2.1) ?_
    rintro _ _ tr ur sf tf ⟨s,t,H,rfl,rfl⟩ E F
    have H0 := H
    obtain ⟨S,T,RS,RT,SP,_⟩ := H
    cases E with
    | call C E R => cases F with
      | call D F Q =>
        rw [call_callEntry,Option.some.injEq] at C D
        subst C D
        have fitS : 4*[Reg.eax,.edi].length+4≤(s.gpr .esp).toNat := by have := RS.1; simp; omega_using [this]
        have fitT : 4*[Reg.eax,.edi].length+4≤(t.gpr .esp).toNat := by have := RT.1; simp; omega_using [this]
        have trace := (timing _ _ _ _ _ _ ⟨workspaceCall_entry S RS,workspaceCall_entry T RT,
          by rw [callEntry_esp',callEntry_esp',SP],
          stable H0 (callEntry_frame (rs := [Reg.eax,.edi]) (s := s) fitS (by decide)) (callEntry_frame (rs := [Reg.eax,.edi]) (s := t) fitT (by decide))⟩ E F).1
        have r := (ret_gpr R .esp).1
        have q := (ret_gpr Q .esp).1
        refine ⟨?_,trivial⟩
        simp only [r,q,State.callEntry_esp,pushed_esp,SP,trace]

end VG.Proof.Dsa.X86

end

end


/-! The public and secret exponent calls share a proved relational calling boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_readArg {s : State} {base : Addr} {size : Nat} (E : Pow.Entry s base size) :
    readSrc s (.mem (VG.Impl.Mont.X86.at_ .esp 4))=some (arg s 0) := by
  change s.load32 (argAddr s 0)=some (arg s 0)
  unfold State.load32
  rw [ite_eq_left E.arg]
  rfl

theorem entry_arg_eq {s t : State} {base : Addr} {size : Nat}
    (E : Pow.Entry s base size) (F : Pow.Entry t base size) : arg s 0=arg t 0 := by
  have H := congrArg (fun x : BitVec 64 => x.setWidth 32) (E.base_eq.trans F.base_eq.symm)
  simpa only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq] using H

def PublicValues (n e m g x : Nat) (base : Addr) (mem : Mem) : Prop :=
  wordsVal mem base (slot n 0) n=m ∧ wordsVal mem base (slot n 5) n=g ∧ val32 mem base (slot n 8) e=x

theorem publicBodyWide_relCT {n e size : Nat} (h : Supported n e) (base : Addr) (m g x : Nat)
    (fits : (layout n e).size≤size) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => Pow.Entry s base size ∧ Pow.Entry t base size ∧ s.gpr .esp=t.gpr .esp ∧
      PublicValues n e m g x base s.mem ∧ PublicValues n e m g x base t.mem)
      (body true n e) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨S,T,SP,A,B⟩ E F
  obtain ⟨u,Eu⟩ := publicNarrowRun h S fits A.1 hm odd E
  obtain ⟨v,Ev⟩ := publicNarrowRun h T fits B.1 hm odd F
  have Sn := (narrowResources S fits).1
  have Tn := (narrowResources T fits).1
  exact publicBody_relCT h base m g x hm odd _ _ _ _ _ _
    ⟨⟨Sn,A.1,A.2.1,A.2.2⟩,⟨Tn,B.1,B.2.1,B.2.2⟩,SP,entry_arg_eq Sn Tn,
      entry_readArg Sn,entry_readArg Tn⟩ Eu Ev

theorem privateCall_relCT {n e : Nat} (h : Supported n e) (base : Addr) (size : Nat) :
    RelCT isa (WorkspacePair base size (fun _ _ => True)) (call false n e) (fun _ _ => True) := by
  apply workspaceCall_relCT (fun _ _ _ => trivial)
  intro s t tr ur sf tf ⟨S,T,SP,_⟩ E F
  exact private_body_relCT h _ _ _ _ _ _ ⟨SP,entry_arg_eq S T,entry_readArg S,entry_readArg T⟩ E F

theorem publicCall_relCT {n e : Nat} (h : Supported n e) (base : Addr) (size m g x : Nat)
    (fits : (layout n e).size≤size) (hm : 1<m) (odd : m%2=1) :
    RelCT isa (WorkspacePair base size (fun a b => PublicValues n e m g x base a ∧ PublicValues n e m g x base b))
      (call true n e) (fun _ _ => True) := by
  apply workspaceCall_relCT (timing := publicBodyWide_relCT h base m g x fits hm odd)
  intro s t a b ⟨S,T,RS,RT,_,A,B⟩ Fa Fb
  have keep {s : State} {mem : Mem} (S : Scr s base size) (R : Pow.Room (s.gpr .esp) base size)
      (V : PublicValues n e m g x base s.mem) (F : Frame [below (s.gpr .esp) 12] s.mem mem) :
      PublicValues n e m g x base mem := by
    have bounds : slot n 0+8*n≤(layout n e).size ∧ slot n 5+8*n≤(layout n e).size ∧
        slot n 8+4*e≤(layout n e).size := by
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
    have vals := fun d k hd => Pow.frame_val32 R S.nowrap F (d := d) (k := k) hd
    refine ⟨?_,?_,(vals _ _ (by omega_using [fits, bounds])).trans V.2.2⟩
    · rw [wordsVal_eq_val32,vals _ _ (by omega_using [fits, bounds]),←wordsVal_eq_val32]; exact V.1
    · rw [wordsVal_eq_val32,vals _ _ (by omega_using [fits, bounds]),←wordsVal_eq_val32]; exact V.2.1
  exact ⟨keep S RS A Fa,keep T RT B Fb⟩

end VG.Proof.Dsa.X86.Comb

end

end


/-! Constant-time composition of byte staging, comb calls, and byte output. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def PowerAgree (prepare : Bool) (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer)
    (s t : State) : Prop :=
  VG.Proof.Dsa.X86.PowerAgree base size len bl modulus a b s t ∧
  (prepare=true → operandValue s base (.input modulus) len=operandValue t base (.input modulus) len ∧
    operandValue s base a len=operandValue t base a len ∧ operandValue s base b bl=operandValue t base b bl) ∧
  (prepare=false → canonical ((len+7)/8) ((bl+3)/4) (operandValue s base (.input modulus) len)
    (operandValue s base a len) base s.mem ∧
    canonical ((len+7)/8) ((bl+3)/4) (operandValue t base (.input modulus) len)
      (operandValue t base a len) base t.mem)

theorem corePower_relCT (prepare : Bool) (base : Addr) (size len bl output : Nat)
    (modulus : Field) (a b : Pointer) (sup : Supported ((len+7)/8) ((bl+3)/4))
    (hz : VG.Impl.Dsa.X86.Layout.saved≤size) (hu : usedBytes≤size)
    (h4 : 4≤len) (hmax : len≤384) (hw4 : len%4=0) (he : 8≤bl) (hel : bl≤len) (hew : bl%4=0)
    (fits : (layout ((len+7)/8) ((bl+3)/4)).size≤size) :
    RelCT isa (PowerAgree prepare base size len bl modulus a b)
      (power prepare len bl modulus a b output) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨⟨S,T,PM,PA,PB⟩,RS,RT,SP⟩,Pub,Priv⟩ E F
  have hn : (len+7)/8≤48 := by omega_using [hmax]
  have ctx : contextBytes ((len+7)/8)≤size :=
    Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn) (Nat.le_trans (by decide) hu)
  have table := table_layout sup
  cases E with | seq Es Es => cases Es with | seq Cs Os =>
  cases F with | seq Et Et => cases Et with | seq Ct Ot =>
  have Head := (powerHead_relCT base size len bl modulus a b hz h4 hmax hw4
    _ _ _ _ _ _ ⟨S,T,PM,PA,PB⟩ Es Et).1
  obtain ⟨Ms,Gs,Xs,Fs,Ks⟩ := wp_result (coreLoadPower_ok S.scr hz rfl h4 hmax hw4 he hel hew
    S.modulusReady S.leftReady S.rightReady rfl ctx) Es
  obtain ⟨Mt,Gt,Xt,Ft,Kt⟩ := wp_result (coreLoadPower_ok T.scr hz rfl h4 hmax hw4 he hel hew
    T.modulusReady T.leftReady T.rightReady rfl ctx) Et
  have Ss := S.scr.of_keeps Ks (by decide)
  have Ts := T.scr.of_keeps Kt (by decide)
  have RSw := RS
  rw [← Ks.1 .esp (by decide)] at RSw
  have RTw := RT
  rw [← Kt.1 .esp (by decide)] at RTw
  have SPw : _ = _ := (Ks.1 .esp (by decide)).trans (SP.trans (Kt.1 .esp (by decide)).symm)
  have preserve {u v : State} (O : Outside base 0 (contextBytes ((len+7)/8)) u.mem v.mem)
      {m g : Nat} (C : canonical ((len+7)/8) ((bl+3)/4) m g base u.mem) :
      canonical ((len+7)/8) ((bl+3)/4) m g base v.mem := by
    apply canonical_outs sup C (Outs.of_outside (rs := [(0,contextBytes ((len+7)/8))]) O (by simp))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact .inr (by simpa only [Nat.zero_add] using table.apart)
  have Ps := fun eq : prepare=false => preserve Fs (Priv eq).1
  have Pt := fun eq : prepare=false => preserve Ft (Priv eq).2
  simp only [operandValue] at Ps Pt
  rw [← Gs] at Ps
  rw [← Gt] at Pt
  have CallTrace := by
    cases prepare with
    | false => exact (privateCall_relCT sup base size _ _ _ _ _ _ ⟨Ss,Ts,RSw,RTw,SPw,trivial⟩ Cs Ct).1
    | true =>
      obtain ⟨M,G,X⟩ := Pub rfl
      exact (publicCall_relCT sup base size (operandValue s base (.input modulus) len)
        (operandValue s base a len) (operandValue s base b bl) fits S.large S.odd
        _ _ _ _ _ _ ⟨Ss,Ts,RSw,RTw,SPw,⟨Ms,Gs,Xs⟩,
          ⟨Mt.trans M.symm,Gt.trans G.symm,Xt.trans X.symm⟩⟩ Cs Ct).1
  obtain ⟨_,_,Kcs⟩ := wp_result (call_ok sup prepare Ss RSw fits hu Ms S.large S.odd Ps) Cs
  obtain ⟨_,_,Kct⟩ := wp_result (call_ok sup prepare Ts RTw fits hu Mt T.large T.odd Pt) Ct
  have DI : _ = _ := BitVec.eq_of_toNat_eq (Ss.edi_toNat.trans Ts.edi_toNat.symm)
  have Store := (coreStore_workspace_relCT len output _ _ _ _ _ _ (agree_regs (rs := [.edi]) (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    rw [Kcs.1 .edi (by decide),Kct.1 .edi (by decide)]
    exact DI)) Os Ot).1
  exact ⟨by simp only [Head,CallTrace,Store],trivial⟩

end VG.Proof.Dsa.X86.Comb

end

end

/-! Comb stages retain the common public caller layout. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem keepSchedule {L : CallLayout} {s t : State} (R : CallReady L s)
    (E : ScheduleFrame L.base L.size s t) : CallReady L t := by
  refine ⟨(E.keeps.1 .esp (by decide)).trans R.sp, E.moduli R.moduli, ?_, ?_, ?_⟩
  · intro input hi; exact E.buffer (R.buffers input hi) (L.stable input hi)
  · intro input hi; exact (E.pointer (L.stable input hi)).trans (R.pointers input hi)
  · exact (E.pointer (p := .input .digestPrefixLen) (by decide)).trans R.prefixLen

def StageAgree (prepare : Bool) (L : CallLayout) (a b : Pointer) (s t : State) : Prop :=
  CallPair L s t ∧
  (prepare=true → operandValue s L.base a L.pLen=operandValue t L.base a L.pLen ∧
    operandValue s L.base b L.qLen=operandValue t L.base b L.qLen) ∧
  (prepare=false → canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p
    (operandValue s L.base a L.pLen) L.base s.mem ∧
    canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p
      (operandValue t L.base a L.pLen) L.base t.mem)

theorem stagePower_relCT (prepare : Bool) (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.qLen)
    (ho : output∈Layout.wideValues)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (StageAgree prepare L a b) (power prepare L.pLen L.qLen .p a b output) (CallPair L) := by
  have W := L.lengths
  intro s t tr ur sf tf H E F
  have Pair := H.1
  have CT := corePower_relCT prepare L.base L.size L.pLen L.qLen output .p a b
    (supported_widths L.widths) L.saved L.extent (by omega_using [W]) (by omega_using [W]) L.aligned.1
    (by omega_using [W]) (by omega_using [W]) L.aligned.2 fits
  have M := Pair.1.moduli.pValue.trans Pair.2.moduli.pValue.symm
  have Trace := (CT _ _ _ _ _ _ ⟨⟨⟨Pair.1.arithmeticP A B (by omega_using [W]),
    Pair.2.arithmeticP A B (by omega_using [W]),Pair.pointer P,Pair.pointer A,Pair.pointer B⟩,
    Pair.1.moduli.room,Pair.2.moduli.room,Pair.1.sp.trans Pair.2.sp.symm⟩,
    fun eq => ⟨M,H.2.1 eq⟩,fun eq => by
      rw [Pair.1.moduli.pValue,Pair.2.moduli.pValue]; exact H.2.2 eq⟩ E F).1
  have S := wp_result (stagePower_ok prepare Pair.1.moduli
    (Pair.1.operand A (by omega_using [W]) (by omega_using [W])) (Pair.1.operand B (by omega_using [W]) (by omega_using [W])) ho fits
    (fun eq => (H.2.2 eq).1)) E
  have T := wp_result (stagePower_ok prepare Pair.2.moduli
    (Pair.2.operand A (by omega_using [W]) (by omega_using [W])) (Pair.2.operand B (by omega_using [W]) (by omega_using [W])) ho fits
    (fun eq => (H.2.2 eq).2)) F
  exact ⟨Trace,keepSchedule Pair.1 S.2.2.2.2.1,keepSchedule Pair.2 T.2.2.2.2.1⟩

end VG.Proof.Dsa.X86.Comb
