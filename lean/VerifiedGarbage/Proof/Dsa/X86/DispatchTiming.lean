module

public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.PublicCompare

/-! # Public length comparisons and relational dispatch composition -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

structure CompareInvariant (base : Addr) (size : Nat) (R : State → State → Prop) : Prop where
  scr : ∀ s t, R s t → Scr s base size ∧ Scr t base size
  keep : ∀ s t sf tf, R s t → Keeps [.eax] s sf → Keeps [.eax] t tf →
    sf.mem = s.mem → tf.mem = t.mem → R sf tf

theorem publicCompare_relCT (base : Addr) (size value wanted : Nat) (f : Field)
    (R : State → State → Prop) (I : CompareInvariant base size R) (hz : Layout.saved ≤ size)
    (V : ∀ s t, R s t → (pointerValue base s (.input f)).toNat = value ∧
      (pointerValue base t (.input f)).toNat = value) (hb : wanted < 2 ^ 32) :
    RelCT isa R (.block [.mov .eax (.mem (sc (Layout.field f))), .alu .cmp .eax (.imm (BitVec.ofNat 32 wanted))])
      (fun s t => R s t ∧ s.zf = some (decide (value = wanted)) ∧ t.zf = some (decide (value = wanted))) := by
  have C : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.mov .eax (.mem (sc (Layout.field f))), .alu .cmp .eax (.imm (BitVec.ofNat 32 wanted))])
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change taint.checkBlock (workspaceTaint false) [.mov .eax (.mem (sc 0)), .alu .cmp .eax (.imm 0)] = _
    rfl
  intro s t tr ur sf tf H E F
  obtain ⟨S, T⟩ := I.scr s t H
  have A : VG.X86.Taint.Agree (workspaceTaint false) s t := by
    apply agree_regs (rs := [.edi])
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  obtain ⟨Z1, K1, O1⟩ := wp_result (publicCompare_ok f S hz (V s t H).1 hb) E
  obtain ⟨Z2, K2, O2⟩ := wp_result (publicCompare_ok f T hz (V s t H).2 hb) F
  exact ⟨(C _ _ _ _ _ _ A E F).1, I.keep s t sf tf H K1 K2 O1 O2, Z1, Z2⟩

theorem fixedChoice_relCT {R Q : State → State → Prop} {yes no : Prog isa} (b : Bool)
    (C : RelCT isa R (if b then yes else no) Q) :
    RelCT isa (fun s t => R s t ∧ s.zf = some b ∧ t.zf = some b) (.ite .e yes no) Q := by
  apply RelCT.ite
  · intro s t H
    change s.zf = t.zf
    exact H.2.1.trans H.2.2.symm
  · intro s t tr ur sf tf ⟨H, E⟩ F G
    have B : b = true := Option.some.inj (H.2.1.symm.trans E)
    subst b
    exact C _ _ _ _ _ _ H.1 F G
  · intro s t tr ur sf tf ⟨H, E⟩ F G
    have B : b = false := Option.some.inj (H.2.1.symm.trans E)
    subst b
    exact C _ _ _ _ _ _ H.1 F G

theorem digestDispatch_relCT (signing : Bool) (pLen qLen limit len : Nat) (base : Addr) (size : Nat)
    (R Q : State → State → Prop) (I : CompareInvariant base size R) (hz : Layout.saved ≤ size)
    (hl : len ≤ limit) (hb : limit < 2 ^ 32)
    (V : ∀ s t, R s t → (pointerValue base s (.input .digestPrefixLen)).toNat = len ∧
      (pointerValue base t (.input .digestPrefixLen)).toNat = len)
    (body : RelCT isa R (if signing then SignVerify.signBody pLen qLen len else SignVerify.verifyBody pLen qLen len) Q) :
    RelCT isa R (Entry.digestDispatch signing pLen qLen limit) Q := by
  induction limit with
  | zero =>
    have H : len = 0 := by omega
    simpa only [Entry.digestDispatch, H] using body
  | succ limit ih =>
    unfold Entry.digestDispatch
    refine RelCT.seq (publicCompare_relCT base size len (limit + 1) .digestPrefixLen R I hz V hb)
      (fixedChoice_relCT (decide (len = limit + 1)) ?_)
    by_cases H : len = limit + 1
    · simpa only [H, decide_true, ite_true] using body
    · simp only [H, decide_false]
      exact ih (by omega) (by omega)

theorem widthDispatch_relCT (signing : Bool) (widths : List (Nat × Nat)) (pLen qLen : Nat)
    (base : Addr) (size : Nat) (R Q : State → State → Prop)
    (I : CompareInvariant base size R) (hz : Layout.saved ≤ size)
    (member : (pLen, qLen) ∈ widths) (bound : ∀ w ∈ widths, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32)
    (P : ∀ s t, R s t → (pointerValue base s (.input .pLen)).toNat = pLen ∧
      (pointerValue base t (.input .pLen)).toNat = pLen)
    (Qlen : ∀ s t, R s t → (pointerValue base s (.input .qLen)).toNat = qLen ∧
      (pointerValue base t (.input .qLen)).toNat = qLen)
    (body : RelCT isa R (Entry.sized signing pLen qLen) Q) :
    RelCT isa R (Entry.widthDispatch signing widths) Q := by
  induction widths with
  | nil => simp only [List.not_mem_nil] at member
  | cons w rest ih =>
    obtain ⟨wp, wq⟩ := w
    have B := bound (wp, wq) List.mem_cons_self
    have Brest : ∀ w ∈ rest, w.1 < 2 ^ 32 ∧ w.2 < 2 ^ 32 :=
      fun w hw => bound w (List.mem_cons_of_mem _ hw)
    unfold Entry.widthDispatch
    refine RelCT.seq (publicCompare_relCT base size pLen wp .pLen R I hz P B.1)
      (fixedChoice_relCT (decide (pLen = wp)) ?_)
    by_cases Hp : pLen = wp
    · simp only [Hp, decide_true, ite_true]
      refine RelCT.seq (publicCompare_relCT base size qLen wq .qLen R I hz Qlen B.2)
        (fixedChoice_relCT (decide (qLen = wq)) ?_)
      by_cases Hq : qLen = wq
      · simpa only [Hp, Hq, decide_true, ite_true] using body
      · simp only [Hq, decide_false]
        exact ih (by simpa only [List.mem_cons, Prod.mk.injEq, Hq, and_false, false_or] using member) Brest
    · simp only [Hp, decide_false]
      exact ih (by simpa only [List.mem_cons, Prod.mk.injEq, Hp, false_and, false_or] using member) Brest

end VG.Proof.Dsa.X86
