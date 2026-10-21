module

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

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
  have fit : 4*[Reg.eax,.edi].length+4≤(s.gpr .esp).toNat := by simp; omega
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
    constructor <;> omega

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
        have fitS : 4*[Reg.eax,.edi].length+4≤(s.gpr .esp).toNat := by have := RS.1; simp; omega
        have fitT : 4*[Reg.eax,.edi].length+4≤(t.gpr .esp).toNat := by have := RT.1; simp; omega
        have trace := (timing _ _ _ _ _ _ ⟨workspaceCall_entry S RS,workspaceCall_entry T RT,
          by rw [callEntry_esp',callEntry_esp',SP],
          stable H0 (callEntry_frame (rs := [Reg.eax,.edi]) (s := s) fitS (by decide)) (callEntry_frame (rs := [Reg.eax,.edi]) (s := t) fitT (by decide))⟩ E F).1
        have r := (ret_gpr R .esp).1
        have q := (ret_gpr Q .esp).1
        refine ⟨?_,trivial⟩
        simp only [r,q,State.callEntry_esp,pushed_esp,SP,trace]

end VG.Proof.Dsa.X86
