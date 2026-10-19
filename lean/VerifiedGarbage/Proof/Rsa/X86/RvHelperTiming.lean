module

public import VerifiedGarbage.Proof.Rsa.X86.CvHelperTiming
public import VerifiedGarbage.Proof.Rsa.X86.MulModTiming
public import VerifiedGarbage.Proof.Mont.X86.PowerTiming
public import VerifiedGarbage.Impl.Rsa.X86.Recover

/-! # Secret-independent workspace operations in prime recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.Recover
open VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 (sc)

/-- Only the workspace address is public; data and temporary registers may differ. -/
def WorkspacePublic (c : Prog isa) : Prop := ∃ hint out,
  VG.Taint.check taint (workspaceTaint false) c hint = some out ∧
  taint.le (workspaceTaint false) out = true

theorem WorkspacePublic.seq {a b : Prog isa} (ha : WorkspacePublic a) (hb : WorkspacePublic b) :
    WorkspacePublic (.seq a b) := by
  obtain ⟨ah, ao, ac, al⟩ := ha
  obtain ⟨bh, bo, bc, bl⟩ := hb
  exact ⟨.seq (workspaceTaint false) ah bh, bo, exponent_check_seq taint ac al bc, bl⟩

theorem WorkspacePublic.seqs {cs : List (Prog isa)}
    (h : ∀ c ∈ cs, WorkspacePublic c) : WorkspacePublic (seqs cs) := by
  induction cs with
  | nil => exact ⟨.block [], workspaceTaint false, rfl, rfl⟩
  | cons c cs ih =>
    cases cs with
    | nil => exact h c (by simp)
    | cons d ds => exact (h c (by simp)).seq (ih (fun x hx => h x (by simp [hx])))

theorem WorkspacePublic.trace {c : Prog isa} (h : WorkspacePublic c) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) c (fun _ _ => True) := by
  obtain ⟨hint, out, checked, _⟩ := h
  apply VG.RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h) (hc := hint)
  rw [checked]
  rfl

theorem mmul_public (n o a b : Nat) : WorkspacePublic (mmul n o a b) := by
  have mul : WorkspacePublic (VG.Impl.Mont.X86.Dynamic.mul (montMod n) sInv
      (slot (width n) mAcc) (slot (width n) o) (slot (width n) a) (slot (width n) b)) :=
    ⟨mulHint false, rowTaint false, mul_check false _ _ _ _ _ _, by rfl⟩
  have clear : WorkspacePublic (clrTop n o) :=
    ⟨zerosHint false, zerosTaint false, zeros_check false _ _, by rfl⟩
  exact mul.seq clear

theorem copy_workspace (n o a : Nat) : WorkspacePublic (copy n o a) := by
  let reference : Prog isa := copy 1 0 1
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (copy n o a) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem sub3_workspace (n o a b : Nat) : WorkspacePublic (sub3 n o a b) := by
  let reference : Prog isa := sub3 1 0 1 2
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (sub3 n o a b) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem sel_workspace (n o a b sl : Nat) : WorkspacePublic (sel n o a b sl) := by
  let reference : Prog isa := sel 1 0 1 2 100
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (sel n o a b sl) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem eqS_workspace (n d a b t : Nat) : WorkspacePublic (eqS n d a b t) := by
  let reference : Prog isa := eqS 1 100 0 1 2
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (eqS n d a b t) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem bitOf_workspace (n d a : Nat) : WorkspacePublic (.block (bitOf n d a)) := by
  let reference : Prog isa := .block (bitOf 1 100 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (bitOf n d a)) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem setOne_workspace (n j : Nat) : WorkspacePublic (.block (setOne n j)) := by
  let reference : Prog isa := .block (setOne 1 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (setOne n j)) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem clrLow_workspace (n j : Nat) : WorkspacePublic (.block (clrLow n j)) := by
  let reference : Prog isa := .block (clrLow 1 0)
  let hint := VG.Taint.hintOf taint (workspaceTaint false) (Code.erase reference)
  let out := (VG.Taint.check taint (workspaceTaint false) reference hint).getD (workspaceTaint false)
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block (clrLow n j)) reference (workspaceTaint false) hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem shiftWord_private_taint (out : Nat) (last : Bool) :
    taint.checkBlock (workspaceTaint false) (VG.Impl.Mont.X86.Dynamic.shiftWord out last) = some (if last then zeroTaint false else workspaceTaint false) := by
  cases last <;>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  · change taint.checkBlock (workspaceTaint false)
      [.mov .eax (.mem (sc 0)), .alu .and .eax (.imm 0), .shift .ror .eax 0,
       .mov .edx (.mem (sc 0)), .shift .shr .edx 0, .alu .add .edx (.reg .eax), .store (sc 0) .edx] = _
    rfl
  · change taint.checkBlock (workspaceTaint false)
      [.mov .eax (.imm 0), .alu .and .eax (.imm 0), .shift .ror .eax 0,
       .mov .edx (.mem (sc 0)), .shift .shr .edx 0, .alu .add .edx (.reg .eax), .store (sc 0) .edx] = _
    rfl

theorem shiftExponent_private_taint (n out : Nat) :
    taint.checkBlock (workspaceTaint false) (VG.Impl.Mont.X86.Dynamic.shiftExponent n out) =
      some (if n = 0 then workspaceTaint false else zeroTaint false) := by
  induction n generalizing out with
  | zero => rfl
  | succ n ih =>
    rw [VG.Impl.Mont.X86.Dynamic.shiftExponent, exponent_check_append taint (workspaceTaint false), shiftWord_private_taint]
    cases n with
    | zero => rfl
    | succ n =>
      change taint.checkBlock (workspaceTaint false) (VG.Impl.Mont.X86.Dynamic.shiftExponent (n + 1) (out + 4)) = _
      exact ih (out + 4)

theorem half_workspace (n j : Nat) : WorkspacePublic (half n j) := by
  refine ⟨.block [], zeroTaint false, ?_, by rfl⟩
  unfold half
  simp only [VG.Taint.check, VG.Taint.checkChunks]
  rw [exponent_check_append taint (workspaceTaint false)]
  have store : taint.checkBlock (workspaceTaint false)
      [.store (VG.Impl.Mont.X86.sc (slot n j + 4 * n)) .ebx] = some (workspaceTaint false) := by
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change taint.checkBlock (workspaceTaint false) [.store (VG.Impl.Mont.X86.sc 0) .ebx] = _
    rfl
  rw [store]
  change taint.checkBlock (workspaceTaint false)
    (VG.Impl.Mont.X86.Dynamic.shiftExponent (n + 1) (slot n j)) = _
  rw [shiftExponent_private_taint, ite_eq_right (by omega)]
  rfl


theorem fixedBlock_workspace (code : List Instr)
    (checked : (taint.checkBlock (workspaceTaint false) code).isSome = true)
    (kept : ∀ out, taint.checkBlock (workspaceTaint false) code = some out →
      taint.le (workspaceTaint false) out = true) : WorkspacePublic (.block code) := by
  obtain ⟨out, ho⟩ := Option.isSome_iff_exists.mp checked
  exact ⟨.block [], out, ho, kept out ho⟩

theorem cntNext_workspace : WorkspacePublic (.block cntNext) := by
  let out := (VG.Taint.check taint (workspaceTaint false) (.block cntNext) (.block [])).getD (workspaceTaint false)
  exact ⟨.block [], out, by rfl, by decide +kernel⟩

theorem sqNext_workspace : WorkspacePublic (.block sqNext) := by
  let out := (VG.Taint.check taint (workspaceTaint false) (.block sqNext) (.block [])).getD (workspaceTaint false)
  exact ⟨.block [], out, by rfl, by decide +kernel⟩

theorem sqMasks_workspace : WorkspacePublic (.block sqMasks) := by
  let out := (VG.Taint.check taint (workspaceTaint false) (.block sqMasks) (.block [])).getD (workspaceTaint false)
  exact ⟨.block [], out, by rfl, by decide +kernel⟩

theorem zeroCarry_workspace : WorkspacePublic (.block [.mov .ebx (.imm 0)]) := by
  let out := (VG.Taint.check taint (workspaceTaint false) (.block [.mov .ebx (.imm 0)]) (.block [])).getD (workspaceTaint false)
  exact ⟨.block [], out, by rfl, by decide +kernel⟩

theorem halfBit_workspace (n : Nat) : WorkspacePublic (.block (halfBit n)) := by
  let reference : Prog isa := Code.erase (.block (halfBit 1))
  let out := (VG.Taint.check taint (workspaceTaint false) reference (.block [])).getD (workspaceTaint false)
  refine ⟨.block [], out, ?_, by decide +kernel⟩
  exact (check_of_erase_eq (.block (halfBit n)) reference (workspaceTaint false)
    (.block []) rfl rfl rfl).trans (by rfl)

theorem halfBody_workspace (n : Nat) : WorkspacePublic (halfBody n) := by
  unfold halfBody
  apply WorkspacePublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact copy_workspace .. | exact zeroCarry_workspace | exact half_workspace .. |
    exact halfBit_workspace .. | exact sel_workspace .. | exact cntNext_workspace

theorem shiftUpWord_private_taint (out : Nat) (lowest : Bool) :
    taint.checkBlock (workspaceTaint false) (VG.Impl.Mont.X86.Dynamic.shiftUpWord out lowest) =
      some (workspaceTaint false) := by
  cases lowest <;>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  · change taint.checkBlock (workspaceTaint false)
      [.mov .edx (.mem (sc 0)), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
       .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .mov .eax (.mem (sc 0)),
       .shift .shr .eax 28, .alu .add .edx (.reg .eax), .store (sc 0) .edx] = _
    rfl
  · change taint.checkBlock (workspaceTaint false)
      [.mov .edx (.mem (sc 0)), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
       .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .store (sc 0) .edx] = _
    rfl

theorem shiftUp_private_taint (k exp : Nat) :
    taint.checkBlock (workspaceTaint false) (VG.Impl.Mont.X86.Dynamic.shiftUp k exp) =
      some (workspaceTaint false) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [VG.Impl.Mont.X86.Dynamic.shiftUp, exponent_check_append taint (workspaceTaint false),
      shiftUpWord_private_taint]
    exact ih

theorem cntNext_taint : taint.checkBlock (workspaceTaint false) cntNext = some (workspaceTaint false) := rfl

theorem alignBody_workspace (n : Nat) : WorkspacePublic (alignBody n) := by
  refine ⟨.block [], workspaceTaint false, ?_, by rfl⟩
  unfold alignBody
  simp only [VG.Taint.check, VG.Taint.checkChunks]
  rw [exponent_check_append taint (workspaceTaint false), shiftUp_private_taint]
  change taint.checkBlock (workspaceTaint false) cntNext = _
  exact cntNext_taint

theorem windowTop_taint (n : Nat) :
    taint.checkBlock (workspaceTaint false) (windowTop n) = some (workspaceTaint false) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false)
    [.mov .eax (.mem (sc 0)), .shift .shr .eax 28, .store (sc 0) .eax] = _
  rfl

theorem windowTop_workspace (n : Nat) : WorkspacePublic (.block (windowTop n)) :=
  ⟨.block [], workspaceTaint false, windowTop_taint n, by rfl⟩

theorem shiftUp_workspace (k exp : Nat) :
    WorkspacePublic (.block (VG.Impl.Mont.X86.Dynamic.shiftUp k exp)) :=
  ⟨.block [], workspaceTaint false, shiftUp_private_taint k exp, by rfl⟩

theorem windowIs_workspace (j : Nat) : WorkspacePublic (.block (windowIs j)) := by
  refine ⟨.block [], workspaceTaint false, ?_, by rfl⟩
  exact (check_of_erase_eq (.block (windowIs j)) (.block (windowIs 0)) (workspaceTaint false)
    (.block []) rfl rfl rfl).trans rfl

theorem scan_workspace (n : Nat) : ∀ k, WorkspacePublic (scan n k)
  | 0 => copy_workspace ..
  | k + 1 => by
    rw [scan]
    exact (scan_workspace n k).seq ((windowIs_workspace _).seq (sel_workspace ..))

theorem powers_workspace (n : Nat) : ∀ k, WorkspacePublic (powers n k)
  | 0 => ⟨.block [], workspaceTaint false, rfl, rfl⟩
  | k + 1 => by
    rw [powers]
    exact (powers_workspace n k).seq (mmul_public ..)

theorem table_workspace (n : Nat) : WorkspacePublic (table n) := by
  unfold table
  exact (copy_workspace ..).seq ((copy_workspace ..).seq (powers_workspace n 14))

theorem windowBody_workspace (n : Nat) : WorkspacePublic (windowBody n) := by
  unfold windowBody square
  apply WorkspacePublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact mmul_public .. | exact windowTop_workspace .. | exact shiftUp_workspace .. |
    exact scan_workspace .. | exact cntNext_workspace

theorem sqBody_workspace (n : Nat) : WorkspacePublic (sqBody n) := by
  unfold sqBody eqAt
  apply WorkspacePublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact mmul_public .. | exact eqS_workspace .. | exact sqMasks_workspace |
    exact copy_workspace .. | exact sel_workspace .. | exact sqNext_workspace

theorem candNext_workspace : WorkspacePublic (.block candNext) := by
  let out := (VG.Taint.check taint (workspaceTaint false) (.block candNext) (.block [])).getD (workspaceTaint false)
  exact ⟨.block [], out, by rfl, by decide +kernel⟩

theorem setupR2_workspace (n : Nat) : WorkspacePublic (setupR2 n) :=
  (show WorkspacePublic (VG.Impl.Mont.X86.Dynamic.powerTwo (montMod n)
    (slot (width n) mAcc) (slot (width n) mR2) (128 * n)) from
      ⟨powerHint, counterEndTaint, powerTwo_check _ _ _ _, by rfl⟩).seq
    ⟨zerosHint false, zerosTaint false, zeros_check false _ _, by rfl⟩

theorem setupInverse_workspace (n : Nat) : WorkspacePublic
    (.block (VG.Impl.Mont.X86.Dynamic.setupInverse (slot (width n) mBase) sInv)) :=
  ⟨.block [], workspaceTaint false, setupInverse_taint false _ _, by rfl⟩

theorem mont_workspace (n : Nat) : WorkspacePublic (mont n) := by
  unfold mont
  apply WorkspacePublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact sub3_workspace .. | exact copy_workspace .. | exact setOne_workspace .. |
    exact setupInverse_workspace .. | exact setupR2_workspace .. | exact mmul_public ..

theorem finY_workspace (n : Nat) : WorkspacePublic (finY n) := by
  have mask : WorkspacePublic (.block [.mov .eax (.mem (sc sOk)), .store (sc sMask) .eax]) :=
    ⟨.block [], workspaceTaint false, rfl, rfl⟩
  exact mask.seq ((copy_workspace ..).seq (mmul_public ..))

theorem gcdSet_workspace (n : Nat) : WorkspacePublic (gcdSet n) := by
  unfold gcdSet
  apply WorkspacePublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact sub3_workspace .. | exact copy_workspace .. | exact setOne_workspace ..

theorem divSet_workspace (n : Nat) : WorkspacePublic (divSet n) := by
  have clear : WorkspacePublic (.block [.mov .eax (.imm 0),
      .store (sc (slot (width n) aDv + 4 * width n)) .eax]) := by
    let reference : Prog isa := .block [.mov .eax (.imm 0), .store (sc 0) .eax]
    refine ⟨.block [], zeroTaint false, ?_, rfl⟩
    exact (check_of_erase_eq _ reference (workspaceTaint false) (.block []) rfl rfl rfl).trans (by rfl)
  exact (copy_workspace ..).seq ((copy_workspace ..).seq clear)

theorem order_workspace (n : Nat) : WorkspacePublic (order n) := by
  have store : WorkspacePublic (.block [.store (sc sLt) .ebx]) := ⟨.block [], workspaceTaint false, rfl, rfl⟩
  exact (sub3_workspace ..).seq (store.seq ((sel_workspace ..).seq (sel_workspace ..)))

theorem factors_workspace (n : Nat) : WorkspacePublic (factors n) := by
  have inverse : WorkspacePublic (VG.Impl.Rsa.X86.Keys.inverse (width n)) := by
    obtain ⟨hint, checked⟩ := VG.Proof.Rsa.X86.Keys.inverse_check (width n) false
    exact ⟨hint, counterEndTaint, checked, by rfl⟩
  have divide : WorkspacePublic (VG.Impl.Rsa.X86.Div.code (width n)
      (slot (width n) aQ) (slot (width n) aRm) (slot (width n) aDv) (slot (width n) aDt)) := by
    let out : VG.X86.Taint.T := { regs := .ofList [.edi, .esi, .ebp, .edx], flags := true }
    refine ⟨VG.Proof.Rsa.X86.Div.divisionHint, out, ?_, by decide +kernel⟩
    exact (check_of_erase_eq (VG.Impl.Rsa.X86.Div.code (width n)
      (slot (width n) aQ) (slot (width n) aRm) (slot (width n) aDv) (slot (width n) aDt))
      (VG.Impl.Rsa.X86.Div.code 1 0 0 0 0) (workspaceTaint false)
      VG.Proof.Rsa.X86.Div.divisionHint rfl rfl rfl).trans (by rfl)
  exact (gcdSet_workspace n).seq (inverse.seq ((divSet_workspace n).seq (divide.seq (order_workspace n))))

end VG.Proof.Rsa.X86.Recover
