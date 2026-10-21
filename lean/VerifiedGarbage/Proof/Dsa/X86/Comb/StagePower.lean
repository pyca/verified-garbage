module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.CorePower
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame

/-! Integrate comb powers into the byte-oriented DSA schedule with their full footprint. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem supported_widths {pLen qLen : Nat} (H : Spec.Dsa.lengthsValid pLen qLen) :
    Supported ((pLen+7)/8) ((qLen+3)/4) := by
  unfold Spec.Dsa.lengthsValid at H
  rcases H with ⟨rfl,rfl⟩|⟨rfl,(rfl|rfl|rfl)⟩|⟨rfl,rfl⟩ <;> unfold Supported <;> decide

theorem stagePower_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (prepare : Bool) (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen+7)/8) a pLen)
    (Rb : OperandReady s base ((pLen+7)/8) b qLen)
    (ho : output∈Layout.wideValues)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (H : prepare=false → canonical ((pLen+7)/8) ((qLen+3)/4) p
      (operandValue s base a pLen) base s.mem) :
    WP isa (power prepare pLen qLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      Spec.Rsa.bytesAt t.mem (off base output) pLen = Spec.Dsa.encodeBE pLen
        (operandValue s base a pLen ^ operandValue s base b qLen % p) ∧
      (prepare=true → canonical ((pLen+7)/8) ((qLen+3)/4) p
        (operandValue s base a pLen) base t.mem) ∧
      flagW base (Layout.field .mask) t = flagW base (Layout.field .mask) s ∧
      ScheduleFrame base size s t ∧
      StackOuts base (s.gpr .esp) (callRanges prepare ((pLen+7)/8) output pLen) s.mem t.mem := by
  have L := M.lengths
  have Al := M.aligned
  have sup := supported_widths M.widths
  have W : 14944≤output ∧ output+384≤15712 := by
    simp only [Layout.wideValues,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl <;> decide
  have fit := M.wideFit ho
  have np : (pLen+7)/8≤48 := by omega
  have sep : output+pLen≤context ((pLen+7)/8) ∨ context ((pLen+7)/8)+272*((pLen+7)/8)≤output := by
    rcases sup with ⟨hn,_⟩|⟨hn,_⟩|⟨hn,_⟩|⟨hn,_⟩|⟨hn,_⟩ <;> rw [hn]
    · change output+pLen≤9216 ∨ 13568≤output; omega
    · change output+pLen≤16384 ∨ 25088≤output; omega
    · change output+pLen≤16384 ∨ 25088≤output; omega
    · change output+pLen≤16384 ∨ 25088≤output; omega
    · change output+pLen≤16384 ∨ 29440≤output; omega
  refine WP.mono (corePower_ok sup prepare M.scr M.saved M.room M.extent rfl
    (by omega) (by omega) Al.1 (by omega) (by omega) Al.2 M.pReady Ra Rb M.pValue
    M.pLarge M.pOdd (Nat.le_trans fit M.extent)
    (by have := VG.Proof.Dsa.X86.Layout.context_bound np; change _≤7048 at this; omega)
    sizeComb sep H) fun t ⟨V,C,O,K⟩ => ?_
  have bounds : ∀ r∈callRanges prepare ((pLen+7)/8) output pLen, r.1+r.2≤size := by
    intro r hr
    unfold callRanges at hr
    rcases List.mem_append.mp hr with hr|hr
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · simpa only [Nat.zero_add] using M.context np
      · exact Nat.le_trans fit M.extent
    · cases prepare with
      | false => simp at hr
      | true => simp only [ite_true,List.mem_singleton] at hr; subst r
                exact sizeComb
  have unchanged (d : Nat) (lo : 8192≤d) (hi : d+4≤8272) :
      ∀ r∈callRanges prepare ((pLen+7)/8) output pLen, d+4≤r.1 ∨ r.1+r.2≤d := by
    intro r hr
    unfold callRanges at hr
    rcases List.mem_append.mp hr with hr|hr
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · have B := VG.Proof.Dsa.X86.Layout.context_bound np
        change _≤7048 at B; simp only [Nat.zero_add]; omega
      · change 14944≤output ∧ output+384≤15712 at W
        exact .inl (by omega)
    · cases prepare with
      | false => simp at hr
      | true => simp only [ite_true,List.mem_singleton] at hr; subst r
                exact .inl (by unfold context; split <;> omega)
  have F := ScheduleFrame.of_ranges K O bounds (fun f _ => unchanged _
    (VG.Proof.Dsa.X86.Layout.field_bounds f).1 (by
      have B := (VG.Proof.Dsa.X86.Layout.field_bounds f).2
      change _≤8256 at B; omega)) (fun p hp => unchanged _
    (by have := (saved_bounds hp).1; omega) (saved_bounds hp).2)
  refine ⟨F.moduli M,V,C,?_,F,O⟩
  have Vmask := O.val32 (unchanged (Layout.field .mask) (by decide) (by decide)) (by decide : Layout.field .mask+4*1≤usedBytes)
  apply BitVec.eq_of_toNat_eq
  simpa only [flagW,val32,Nat.mul_zero,Nat.add_zero] using Vmask

theorem stagePrivate_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen+7)/8) a pLen)
    (Rb : OperandReady s base ((pLen+7)/8) b qLen)
    (ho : output∈Layout.wideValues)
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (C : canonical ((pLen+7)/8) ((qLen+3)/4) p (operandValue s base a pLen) base s.mem) :
    WP isa (power false pLen qLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output pLen
        (operandValue s base a pLen ^ operandValue s base b qLen % p) := by
  refine WP.mono (stagePower_ok false M Ra Rb ho sizeComb (fun _ => C)) fun t ⟨Mt,V,_,_,F,O⟩ => ?_
  have O' : StackOuts base (s.gpr .esp) [(0,contextBytes ((pLen+7)/8)),(output,pLen)] s.mem t.mem := by
    simpa only [callRanges,Bool.false_eq_true,ite_false,List.append_nil] using O
  exact ⟨Mt,⟨StageFrame.of_stackFrame F.keeps (by decide) O' (by have := M.lengths; omega),V⟩⟩

end VG.Proof.Dsa.X86.Comb
