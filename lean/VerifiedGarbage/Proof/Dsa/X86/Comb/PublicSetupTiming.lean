module

import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicSelectTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.Setup
import VerifiedGarbage.Proof.Mont.X86.CombDigitMath
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.Words
meta import VerifiedGarbage.Proof.Mont.X86.Words
public import Init.Prelude
meta import Init.Prelude
public import VerifiedGarbage.Impl.Dsa.X86.CombSetup
meta import VerifiedGarbage.Impl.Dsa.X86.CombSetup
public import VerifiedGarbage.Proof.Mont.Words
meta import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout

/-! The fast setup branch observes only the public modulus's high word. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def seedFlags : VG.X86.Taint.T := { regs := .ofList [.edi], flags := true }

def seedAfterLoad (n : Nat) : Prog isa :=
    (.ite .e (highPower (contextMod n) (slot n 2) (slot n 4) (n+1))
      (powerTwo (contextMod n) (slot n 2) (slot n 4) (65*n)))

theorem contextStart_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint (workspaceTaint false) (contextStart n)
      (VG.Taint.hintOf taint (workspaceTaint false) (contextStart n))).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> taint_decide

theorem seedAfterLoad_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint seedFlags (seedAfterLoad n)
      (VG.Taint.hintOf taint seedFlags (seedAfterLoad n))).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> taint_decide

theorem setupSquares_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint (workspaceTaint false) (setupSquares n)
      (VG.Taint.hintOf taint (workspaceTaint false) (setupSquares n))).map
      (taint.le (workspaceTaint false))=some true := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> taint_decide

structure PublicSetupInput (n e m : Nat) (base : Addr) (s : State) : Prop where
  scr : Scr s base (layout n e).size
  modulus : wordsVal s.mem base (slot n 0) n=m

theorem publicSetup_relCT {n e : Nat} (h : Supported n e) (base : Addr) (m : Nat)
    (hm : 1<m) (odd : m%2=1) :
    RelCT isa (fun s t => PublicSetupInput n e m base s ∧ PublicSetupInput n e m base t)
      (setup n) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have shape : 0<n ∧ contextBytes n≤(layout n e).size ∧ slot n 0+4*(2*n-1)+4≤(layout n e).size := by
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  obtain ⟨τ₀,C₀,L₀⟩ := Option.map_eq_some_iff.mp (contextStart_check h)
  obtain ⟨τ₁,C₁,L₁⟩ := Option.map_eq_some_iff.mp (seedAfterLoad_check h)
  obtain ⟨τ₂,C₂,L₂⟩ := Option.map_eq_some_iff.mp (setupSquares_check h)
  unfold setup seed
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint false)) ?_ (checkedProgramChange C₂ L₂)
  refine RelCT.seq (R := fun (s t : State) => Context n m base (layout n e).size s ∧ Context n m base (layout n e).size t) ?_ ?_
  · intro s t tr ur sf tf ⟨S,T⟩ Es Et
    have DI : s.gpr .edi=t.gpr .edi := BitVec.eq_of_toNat_eq (S.scr.edi_toNat.trans T.scr.edi_toNat.symm)
    have A := agree_regs (rs := [.edi]) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact DI)
    exact ⟨(checkedProgramChange C₀ L₀ _ _ _ _ _ _ A Es Et).1,
      (wp_result (contextStart_ok S.scr shape.1 shape.2.1 S.modulus hm odd) Es).1,
      (wp_result (contextStart_ok T.scr shape.1 shape.2.1 T.modulus hm odd) Et).1⟩
  · change RelCT isa _ (.seq (.block ([.mov .eax (.mem (sc (slot n 0+4*(2*n-1))))] ++
      [.shift .shr .eax 31,.alu .cmp .eax (.imm 1)])) _) _
    refine RelCT.seq (R := VG.X86.Taint.Agree seedFlags) ?_ (checkedProgramChange C₁ L₁)
    apply RelCT.block_append
    refine RelCT.seq (R := VG.X86.Taint.Agree loadedIndex) ?_
      (checkedProgramChange (hint := .block []) rfl rfl)
    apply (loadWord_relCT base (layout n e).size _ shape.2.2).mono
    · intro s t ⟨S,T⟩
      refine ⟨S.scr,T.scr,?_⟩
      rw [←VG.Proof.Mont.X86.Comb.val32_word (by omega : 2*n-1<2*n),
        ←VG.Proof.Mont.X86.Comb.val32_word (by omega : 2*n-1<2*n),
        ←wordsVal_eq_val32,←wordsVal_eq_val32,show wordsVal s.mem base (slot n 0) n=m from S.modulus.val,
        show wordsVal t.mem base (slot n 0) n=m from T.modulus.val]
    · exact fun _ _ h => h

end VG.Proof.Dsa.X86.Comb
