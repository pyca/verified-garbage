module

meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

meta import VerifiedGarbage.Impl.Mont.X86

meta import VerifiedGarbage.Proof.Framework.X86.Taint

import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! Loading a public workspace word once makes its value available to taint analysis. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def loadedWordTaint : VG.X86.Taint.T := {regs := .ofList [.edi,.eax],flags := false}

theorem publicWord_relCT (base : Addr) (size o : Nat) (hz : o+4≤size) :
    RelCT isa (fun (s t : State) => Scr s base size ∧ Scr t base size ∧ w32 s.mem base o=w32 t.mem base o) (.block [.mov .eax (.mem (sc o))]) (VG.X86.Taint.Agree loadedWordTaint) := by
  intro s t tr ur sf tf ⟨S,T,W⟩ E F
  have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
  have Trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.mov .eax (.mem (sc o))]) (VG.X86.Taint.Agree (workspaceTaint false)) :=
    erased_relCT _ (.block [.mov .eax (.mem (sc 0))]) (.block []) rfl rfl rfl (by taint_decide)
  have first {u : State} (U : Scr u base size) :
      WP isa (.block [.mov .eax (.mem (sc o))]) u fun v =>
        v.gpr .eax=u.mem.readW (off base o) 32 ∧ Keeps [.eax] u v :=
    wp_movS (readSrc_sc U hz) fun v V _ => WP.block_nil ⟨V.gpr,V.keeps⟩
  obtain ⟨V1,K1⟩ := wp_result (first S) E
  obtain ⟨V2,K2⟩ := wp_result (first T) F
  refine ⟨(Trace _ _ _ _ _ _ A E F).1,?_⟩
  apply agree_regs (rs := [.edi,.eax])
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · rw [K1.1 _ (by decide),K2.1 _ (by decide),DI]
  · rw [V1,V2]; exact BitVec.eq_of_toNat_eq W

end VG.Proof.Mont.X86.Dynamic
