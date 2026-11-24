module

public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Impl.Rc2.X86.Block
public import VerifiedGarbage.Proof.Rc2.X86.Save
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

@[expose] public section

/-! # RC2 words in registers -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

/-- The four words are the low halves of their registers. -/
def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  ∀ i < 4, (s.gpr (wordReg i)).setWidth 16 = v.getD i 0

def roundWrites : List Reg := [.eax, .ebx, .ecx, .edx, .esi]

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by simp [Vector.getD, hi]

theorem Words.at_mod {s : State} {v : Spec.Rc2.State} (h : Words s v) (i : Nat) :
    (s.gpr (wordReg i)).setWidth 16 = v.getD (i % 4) 0 := by
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_inj : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j → i = j := by decide

theorem wordReg_round (i : Nat) : wordReg i ∈ roundWrites := by
  have fact : ∀ j < 4, wordReg j ∈ roundWrites := by decide
  simpa only [wordReg, Nat.mod_mod] using fact (i % 4) (Nat.mod_lt _ (by decide))

/-- One word changed, the others kept. -/
theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : Words s v) {i : Nat} (hi : i < 4) {x : BitVec 16}
    (hx : (s'.gpr (wordReg i)).setWidth 16 = x)
    (keep : ∀ j < 4, j ≠ i → s'.gpr (wordReg j) = s.gpr (wordReg j)) : Words s' (v.set! i x) := by
  intro j hj
  by_cases he : j = i
  · subst he
    rw [hx]; simp [Vector.getD, hj]
  · rw [keep j hj he, h j hj, vector_getD _ j hj, vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

/-! ## MIX's arithmetic, and its inverse -/

/-- What the rounds need of a state: the schedule at EDI, and the 8 bytes of
scratch `keyLookup` writes, at EBP + 48. -/
structure RoundEnv (s : State) : Prop where
  scratchFit : (s.gpr .ebp).toNat + 256 ≤ 2 ^ 32
  keyFit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32
  keyAll : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi)) 128
  laneWrite : InRegions s.wr (addr (s.gpr .ebp) 48) 8
  keySep : (Region.mk (addr32 (s.gpr .edi)) 128).Disjoint ⟨addr (s.gpr .ebp) 48, 8⟩

/-- The schedule at EDI. -/
def schedule (s : State) : Spec.Rc2.Schedule := Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))

structure RoundFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ roundWrites → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨addr (s₀.gpr .ebp) 48, 8⟩] s₀.mem s.mem

theorem RoundFrame.refl (s : State) : RoundFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem RoundFrame.trans {s₀ s₁ s₂ : State} (h₁ : RoundFrame s₀ s₁) (h₂ : RoundFrame s₁ s₂) :
    RoundFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame := h₂.mem
  rw [h₁.reg .ebp (by decide)] at frame
  exact h₁.mem.trans frame

theorem RoundFrame.env {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) : RoundEnv s' := by
  have hb := h.reg .ebp (by decide)
  have hd := h.reg .edi (by decide)
  constructor
  · rw [hb]; exact env.scratchFit
  · rw [hd]; exact env.keyFit
  · rw [h.rd, h.wr, hd]; exact env.keyAll
  · rw [h.wr, hb]; exact env.laneWrite
  · rw [hd, hb]; exact env.keySep

theorem RoundFrame.schedule {s s' : State} (h : RoundFrame s s') (env : RoundEnv s) :
    schedule s' = schedule s := by
  unfold Proof.Rc2.X86.schedule
  rw [h.reg .edi (by decide)]
  exact scheduleAt_frame h.mem _ (by simpa using env.keySep)

theorem RoundFrame.of_keep {s s' : State} {rs : List Reg} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ roundWrites) :
    RoundFrame s s' := by
  refine ⟨(h.weaken hs).reg, h.rd, h.wr, ?_⟩
  rw [h.mem]; exact Frame.refl _ _

theorem mixRegs_round (i : Nat) : ∀ r ∈ [wordReg i, Reg.esi], r ∈ roundWrites := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact wordReg_round i
  · decide

/-- The sum or difference, modulo 2¹⁶. -/
def addOrSub (sub : Bool) (x y : BitVec 16) : BitVec 16 := if sub then x - y else x + y

theorem addOrSub_low (sub : Bool) (x y : BitVec 32) :
    (if sub then x - y else x + y).setWidth 16 = addOrSub sub (x.setWidth 16) (y.setWidth 16) := by
  cases sub <;>
    simp [addOrSub, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]

theorem read32_lo (m : Mem) (a : Addr) : (m.readW a 32).setWidth 16 = m.readW a 16 := by
  have h := readW_extract m a (w := 32) (k := 0) (n := 2) (by decide)
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h
  exact (BitVec.setWidth_eq_extractLsb' (by decide)).trans h

theorem read32_hi (m : Mem) (a : Addr) : (m.readW a 32 >>> 16).setWidth 16 = m.readW (a + BitVec.ofNat 64 2) 16 := by
  have h := readW_extract m a (w := 32) (k := 2) (n := 2) (by decide)
  refine Eq.trans ?_ h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem loadKey_addr {s : State} (env : RoundEnv s) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi) + BitVec.ofNat 64 o) 4 := by
  exact CallLay.inRegions_sub env.keyAll ho (by decide)

/-- The schedule's last word, from the doubleword that ends with it. -/
theorem lastKey_ok (s : State) (env : RoundEnv s) :
    ∃ s', runBlock isa [.mov .esi (.mem (memOp .edi 124)), .shift .shr .esi 16] s = some s' ∧
      (s'.gpr .esi).setWidth 16 = (schedule s).getD 63 0 ∧ Keep [.esi] s s' := by
  have fit := env.keyFit
  have hload := exec_load s .esi .edi 124 (by omega_arith) (loadKey_addr env (o := 124) (by decide))
  refine ⟨_, by
    rw [runBlock_cons, hload, runStep_some, runBlock_cons]
    simp only [reduceExec, execShift, Nat.reduceLeDiff, and_self, ite_true, gpr_setReg, runStep_some, runBlock_nil]
    rfl, ?_, ?_⟩
  · rw [gpr_setReg_self, read32_hi, Offset.add_add, schedule, ← sword_eq _ _ (by decide)]
    rfl
  · refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hq
    rw [gpr_setReg_of_ne _ _ hq, gpr_setFlags, gpr_setReg_of_ne _ _ hq]

theorem keyAdjust_ok (sub : Bool) (s : State) (env : RoundEnv s) (r : Reg) (hr : r ≠ .esi) (j : Nat) (hj : j < 64) :
    ∃ s', runBlock isa (keyAdjust sub j r) s = some s' ∧
      (s'.gpr r).setWidth 16 = addOrSub sub ((s.gpr r).setWidth 16) ((schedule s).getD j 0) ∧
      Keep [r, .esi] s s' := by
  have fit := env.keyFit
  unfold keyAdjust
  by_cases h : j = 63
  · rw [ite_eq_left h]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := lastKey_ok s env
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := adjust_ok sub s₁ r
    refine ⟨s₂, ?_, ?_, (keep₁.weaken (by simp)).trans (keep₂.weaken (by simp))⟩
    · rw [Interleave.runBlock_append, run₁]; exact run₂
    · rw [out₂, addOrSub_low, out₁, keep₁.reg _ (by rw [List.mem_singleton]; exact hr), h]
  · rw [ite_eq_right h]
    have hin := loadKey_addr env (o := 2 * j) (by omega_arith)
    have ha := addr_add (x := s.gpr .edi) (k := 2 * j) (by omega_arith)
    have val : (s.mem.readW (addr32 (s.gpr .edi) + BitVec.ofNat 64 (2 * j)) 32).setWidth 16 =
        (schedule s).getD j 0 := by
      rw [read32_lo, schedule, ← sword_eq _ _ hj]; rfl
    cases sub <;> refine ⟨_, by
      simp only [adjustOp, Bool.false_eq_true, ite_false, ite_true, runBlock_cons, reduceExec, execAlu, readSrc, State.ea,
        memOp, State.load32, ← addr_eq_def, ha, hin, Option.bind_some, runStep_some, runBlock_nil]
      rfl, ?_, ?_⟩
    · rw [gpr_setReg_self, ← val]; exact addOrSub_low false _ _
    · refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
      have hq' : q ≠ r := by rintro rfl; exact hq (by simp)
      rw [gpr_setReg_of_ne _ _ hq', gpr_arithFlags]
    · rw [gpr_setReg_self, ← val]; exact addOrSub_low true _ _
    · refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
      have hq' : q ≠ r := by rintro rfl; exact hq (by simp)
      rw [gpr_setReg_of_ne _ _ hq', gpr_arithFlags]

theorem select_low (a b c : BitVec 32) :
    ((a &&& b) + (~~~a &&& c)).setWidth 16 =
      (a.setWidth 16 &&& b.setWidth 16) + (~~~(a.setWidth 16) &&& c.setWidth 16) := by
  rw [BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide), BitVec.setWidth_and, BitVec.setWidth_and,
    BitVec.setWidth_not (show 16 ≤ 32 by decide)]

/-- Word `i` plus or minus its key word and the choice between its neighbours,
modulo 2¹⁶, from the low halves of the registers. -/
theorem mixArithmetic_ok (sub : Bool) (s : State) (env : RoundEnv s) (i j : Nat) (hj : j < 64) :
    ∃ s', runBlock isa (mixArithmetic sub j i) s = some s' ∧
      (∀ a b c : BitVec 16, wordReg (i + 1) ≠ wordReg i → wordReg (i + 2) ≠ wordReg i → wordReg (i + 3) ≠ wordReg i →
        (s.gpr (wordReg (i + 3))).setWidth 16 = a → (s.gpr (wordReg (i + 2))).setWidth 16 = b →
        (s.gpr (wordReg (i + 1))).setWidth 16 = c →
        (s'.gpr (wordReg i)).setWidth 16 = addOrSub sub
          (addOrSub sub ((s.gpr (wordReg i)).setWidth 16) ((schedule s).getD j 0)) ((a &&& b) + (~~~a &&& c))) ∧
      Keep [wordReg i, .esi] s s' := by
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := keyAdjust_ok sub s env (wordReg i) (wordReg_separate i).1 j hj
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := mixSelect_ok s₁ i
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := adjust_ok sub s₂ (wordReg i)
  refine ⟨s₃, ?_, fun a b c h1 h2 h3 ha hb hc => ?_,
    (keep₁.trans (keep₂.weaken (by simp))).trans (keep₃.weaken (by simp))⟩
  · rw [mixArithmetic, Interleave.runBlock_append, Interleave.runBlock_append, run₁, Option.bind_some, run₂]
    exact run₃
  · have nbr (n : Nat) (hn : wordReg (i + n) ≠ wordReg i) : s₁.gpr (wordReg (i + n)) = s.gpr (wordReg (i + n)) :=
      keep₁.reg _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hn, (wordReg_separate _).1⟩)
    rw [out₃, addOrSub_low, keep₂.reg _ (by simp only [List.mem_singleton]; exact (wordReg_separate i).1), out₁, out₂,
      nbr 1 h1, nbr 2 h2, nbr 3 h3, select_low, ha, hb, hc]

def mixResult (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : BitVec 16 :=
  let x := v.getD i 0
  let a := v.getD ((i + 3) % 4) 0
  let b := v.getD ((i + 2) % 4) 0
  let c := v.getD ((i + 1) % 4) 0
  match d with
  | .encrypt => (x + k.getD j 0 + (a &&& b) + (~~~a &&& c)).rotateLeft (Spec.Rc2.rotation i)
  | .decrypt => x.rotateRight (Spec.Rc2.rotation i) - k.getD j 0 - (a &&& b) - (~~~a &&& c)

theorem neighbor_ne : ∀ i < 4, ∀ n < 4, 1 ≤ n → wordReg (i + n) ≠ wordReg i := by decide

def mixSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mix k j i v
  | .decrypt => Spec.Rc2.reverseMix k j i v

theorem mixSpec_eq (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j i : Nat)
    (v : Spec.Rc2.State) : mixSpec d k j i v = v.set! i (mixResult d k j i v) := by
  cases d <;> rfl

theorem mixCore_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v) (env : RoundEnv s)
    (i j : Nat) (hi : i < 4) (hj : j < 64) :
    ∃ s', runBlock isa (mixCore d j i) s = some s' ∧
      (s'.gpr (wordReg i)).setWidth 16 = mixResult d (schedule s) j i v ∧ Keep [wordReg i, .esi] s s' := by
  have ne := neighbor_ne i hi
  have bounds := rotation_bounds i
  have sep := (wordReg_separate i).1
  cases d
  · obtain ⟨s₁, run₁, out₁, keep₁⟩ := mixArithmetic_ok false s env i j hj
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := rotate16_ok s₁ (wordReg i) sep (Spec.Rc2.rotation i) bounds.1 bounds.2
    refine ⟨s₂, ?_, ?_, keep₁.trans keep₂⟩
    · rw [mixCore, Interleave.runBlock_append, run₁]; exact run₂
    · rw [out₂, out₁ _ _ _ (ne 1 (by decide) (by decide)) (ne 2 (by decide) (by decide)) (ne 3 (by decide) (by decide))
        (hv.at_mod _) (hv.at_mod _) (hv.at_mod _), hv i hi]
      simp only [addOrSub, Bool.false_eq_true, ite_false, mixResult, BitVec.add_assoc]
  · obtain ⟨s₁, run₁, out₁, keep₁⟩ := rotate16_ok s (wordReg i) sep (16 - Spec.Rc2.rotation i) (by omega_arith)
      (by omega_arith)
    have f₁ := RoundFrame.of_keep keep₁ (mixRegs_round i)
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := mixArithmetic_ok true s₁ (f₁.env env) i j hj
    refine ⟨s₂, ?_, ?_, keep₁.trans keep₂⟩
    · rw [mixCore, Interleave.runBlock_append, run₁]; exact run₂
    · have nbr (n : Nat) (hn : 1 ≤ n) (hn' : n < 4) :
          (s₁.gpr (wordReg (i + n))).setWidth 16 = v.getD ((i + n) % 4) 0 := by
        rw [keep₁.reg _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨ne n hn' hn, (wordReg_separate _).1⟩)]
        exact hv.at_mod _
      rw [out₂ _ _ _ (ne 1 (by decide) (by decide)) (ne 2 (by decide) (by decide)) (ne 3 (by decide) (by decide))
        (nbr 3 (by decide) (by decide)) (nbr 2 (by decide) (by decide)) (nbr 1 (by decide) (by decide)), out₁,
        hv i hi, f₁.schedule env, Word32.rotateLeft_reverse _ _ bounds.1 bounds.2]
      simp only [addOrSub, ite_true, mixResult, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

theorem mixStep_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v) (env : RoundEnv s)
    (i j : Nat) (hi : i < 4) (hj : j < 64) :
    WP isa (.block (mixCore d j i)) s (fun s' => Words s' (mixSpec d (schedule s) j i v) ∧ RoundFrame s s') := by
  obtain ⟨s', run, out, keep⟩ := mixCore_ok d s v hv env i j hi hj
  refine WP.of_runBlock ⟨s', run, ?_, RoundFrame.of_keep keep (mixRegs_round i)⟩
  rw [mixSpec_eq]
  refine hv.update hi out fun k hk hne => keep.reg _ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨fun h => hne (wordReg_inj k hk i hi h), (wordReg_separate k).1⟩

/-! ## MASH -/

def mashResult (d : Spec.Rc2.Direction) (x k : BitVec 16) : BitVec 16 :=
  match d with
  | .encrypt => x + k
  | .decrypt => x - k

theorem indexWord (x : BitVec 32) : (x.setWidth 6).toNat = (x.setWidth 16 &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 64 = x.toNat % 65536 &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

def mashSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mashSpec_eq (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (i : Nat)
    (v : Spec.Rc2.State) : mashSpec d k i v = v.set! i
      (mashResult d (v.getD i 0) (k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0)) := by
  cases d <;> rfl

theorem mash_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : Words s v) (env : RoundEnv s) (i : Nat) (hi : i < 4) :
    WP isa (.block (mash d i)) s (fun s' => Words s' (mashSpec d (schedule s) i v) ∧ RoundFrame s s') := by
  rw [mash, WP.block_append_iff]
  apply WP.mono (keyLookup_ok s (wordReg (i + 3)) env.keyFit env.keyAll env.laneWrite)
  intro s₁ ⟨h₁, g₁, rd₁, wr₁, m₁⟩
  have f₁ : RoundFrame s s₁ := ⟨fun r hr => g₁ r (by rintro rfl; exact hr (by decide)), rd₁, wr₁, m₁⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := adjust_ok (d == .decrypt) s₁ (wordReg i)
  refine WP.of_runBlock ⟨s₂, run₂, ?_, f₁.trans (RoundFrame.of_keep keep₂ (by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact wordReg_round i))⟩
  rw [mashSpec_eq]
  refine hv.update hi ?_ fun k hk hne => ?_
  · rw [out₂, addOrSub_low, g₁ _ (wordReg_separate i).1, hv i hi, h₁, indexWord, hv.at_mod]
    cases d <;> rfl
  · rw [keep₂.reg _ (by rw [List.mem_singleton]; exact fun h => hne (wordReg_inj k hk i hi h)),
      g₁ _ (wordReg_separate k).1]

/-! ## The sixteen rounds -/

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), Words s v → RoundEnv s →
      WP isa (.block (code i)) s (fun s' => Words s' (step (schedule s) i v) ∧ RoundFrame s s'))
    (s : State) (v : Spec.Rc2.State) (hv : Words s v) (env : RoundEnv s) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      Words s' (is.foldl (fun v i => step (schedule s) i v) v) ∧ RoundFrame s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, RoundFrame.refl s⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv env)
    intro s₁ h₁
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 (h₁.2.env env))
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.schedule env] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v) (j : Nat) (hj : j < 16) (env : RoundEnv s) :
    WP isa (.block ((List.range 4).flatMap (fun i => mixCore .encrypt (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.mixRound (schedule s) j v) ∧ RoundFrame s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound := List.mem_range.mp hi
  exact mixStep_ok .encrypt s v hv env i (4 * j + i) bound (by omega_arith)

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v) (j : Nat) (hj : j < 16)
    (env : RoundEnv s) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => mixCore .decrypt (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.reverseMixRound (schedule s) j v) ∧ RoundFrame s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega_arith
  exact mixStep_ok .decrypt s v hv env i (4 * j + i) bound (by omega_arith)

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v) (env : RoundEnv s) :
    WP isa (.block ((order d).flatMap (mash d))) s (fun s' =>
      Words s' (mashRoundSpec d (schedule s) v) ∧ RoundFrame s s') := by
  have he (k : Spec.Rc2.Schedule) : mashRoundSpec d k v =
      (order d).foldl (fun v i => mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply foldWords_ok (step := fun k i v => mashSpec d k i v) _ _ _ s v hv env
  intro i hi s v hv env
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega_arith
  exact mash_ok d s v hv env i bound

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16) (env : RoundEnv s) :
    WP isa (.block (round d j)) s (fun s' => Words s' (roundSpec d (schedule s) j v) ∧ RoundFrame s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : Words s₁ v₁ ∧ RoundFrame s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        Words s₂ (if j = 4 ∨ j = 10 then mashRoundSpec d (schedule s) v₁ else v₁) ∧ RoundFrame s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      apply WP.mono (mashRound_ok d s₁ v₁ h₁.1 (h₁.2.env env))
      intro s₂ h₂
      rw [h₁.2.schedule env] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (mixRound_ok s v hv j hj env)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (reverseMixRound_ok s v hv (15 - j) (by omega_arith) env)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v) (env : RoundEnv s) :
    WP isa (.block ((List.range 16).flatMap (round d))) s (fun s' =>
      Words s' ((List.range 16).foldl (fun v j => roundSpec d (schedule s) j v) v) ∧ RoundFrame s s') := by
  apply foldWords_ok (step := fun k j v => roundSpec d k j v) _ _ _ s v hv env
  intro j hj s v hv env
  exact round_ok d s v hv j (List.mem_range.mp hj) env

/-! ## The block -/

/-- The half-words of two doublewords loaded are the block's words. -/
theorem decode_half (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 = m.readW (p + BitVec.ofNat 64 (2 * i)) 16 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ (by omega_arith), getD_ofFn _ _ (by omega_arith), readW16, Offset.add_add]

theorem blockLoad_ok (s : State) (fit : (s.gpr .esi).toNat + 8 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .esi)) 8) :
    WP isa (.block blockLoad) s (fun s' =>
      Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))) ∧ RoundFrame s s') := by
  have h0 := CallLay.inRegions_sub (off := 0) (l := 4) readable (by decide) (by decide)
  have h4 := CallLay.inRegions_sub (off := 4) (l := 4) readable (by decide) (by decide)
  have a0 := addr_add (x := s.gpr .esi) (k := 0) (by omega_arith)
  have a4 := addr_add (x := s.gpr .esi) (k := 4) (by omega_arith)
  refine WP.of_runBlock ⟨_, by
    simp only [blockLoad, rr, memOp, State.ea, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
      State.load32, execShift, ← addr_eq_def, a0, a4, h0, h4, Option.map_some, gpr_setReg, gpr_setFlags, mem_setReg,
      rd_setReg, wr_setReg, reduceCtorEq, ite_true, ite_false, Nat.reduceLeDiff, and_self]
    rfl, ?_, ?_⟩
  · intro i hi
    rw [decode_half _ _ _ hi]
    rcases cases4 hi with rfl | rfl | rfl | rfl <;>
      simp only [wordReg, Nat.reduceMod, List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ,
        gpr_setReg, gpr_setFlags, reduceCtorEq, ite_true, ite_false, Nat.reduceMul]
    · exact read32_lo _ _
    · rw [read32_hi, Offset.add_add]
    · exact read32_lo _ _
    · rw [read32_hi, Offset.add_add]
  · refine ⟨fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
    simp only [roundWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_setFlags, hr, ite_false]

theorem joinWords_ok (s : State) (lo hi : Reg) (h : hi ≠ lo) :
    ∃ s', runBlock isa (joinWords lo hi) s = some s' ∧
      s'.gpr lo = (s.gpr hi).setWidth 16 ++ (s.gpr lo).setWidth 16 ∧ Keep [lo, hi] s s' := by
  have h' := h.symm
  refine ⟨_, by
    simp only [joinWords, runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, execShift, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags, gpr_setFlags, h', ite_true, ite_false, Nat.reduceLeDiff, and_self]
    rfl, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h, h', ite_true, ite_false]
    generalize s.gpr lo = x
    generalize s.gpr hi = y
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have m : (4294901760 : BitVec 32).getLsbD i = decide (16 ≤ i) := by
      have fact : ∀ i < 32, (4294901760 : BitVec 32).getLsbD i = decide (16 ≤ i) := by decide
      exact fact i hi
    rw [BitVec.getLsbD_or, Word32.maskWord, BitVec.getLsbD_and, m, BitVec.getLsbD_append]
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight, Nat.reduceMod, Nat.reduceSub, hi, decide_true,
      Bool.true_and]
    by_cases h16 : i < 16
    · simp only [h16, decide_true, Bool.true_and, show ¬ 16 ≤ i by omega_arith, decide_false, Bool.and_false, Bool.or_false,
        ite_true]
    · simp only [h16, show 16 ≤ i by omega_arith, show i - 16 < 16 by omega_arith, decide_true, decide_false, Bool.and_true,
        Bool.true_and, Bool.false_and, Bool.false_or, ite_false]
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]

theorem pack_halves (v : Spec.Rc2.State) : pack v = (v.getD 3 0 ++ v.getD 2 0) ++ (v.getD 1 0 ++ v.getD 0 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pack, BitVec.getLsbD_append]
  by_cases h₁ : i < 16
  · simp only [h₁, show i < 32 by omega_arith, ite_true]
  · by_cases h₂ : i < 32
    · simp only [h₁, h₂, show i - 16 < 16 by omega_arith, ite_true, ite_false]
    · simp only [h₁, h₂, show ¬ i - 16 < 16 by omega_arith, ite_false, Nat.sub_sub, Nat.reduceAdd]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .esi).toNat + 8 ≤ 2 ^ 32) (writable : InRegions s.wr (addr32 (s.gpr .esi)) 8) :
    WP isa (.block blockStore) s (fun s' =>
      Keep [.eax, .ebx, .ecx, .edx] {s with mem := s.mem.writeW (addr32 (s.gpr .esi)) (pack v)} s') := by
  simp only [blockStore, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := joinWords_ok s .eax .ebx (by decide)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := joinWords_ok s₁ .ecx .edx (by decide)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [keep₁.reg .ecx (by decide), keep₁.reg .edx (by decide)] at out₂
  have keep : Keep [.eax, .ebx, .ecx, .edx] s s₂ := (keep₁.weaken (by decide)).trans (keep₂.weaken (by decide))
  have a : s₂.gpr .eax = v.getD 1 0 ++ v.getD 0 0 := by
    rw [keep₂.reg .eax (by decide), out₁, ← hv 0 (by decide), ← hv 1 (by decide)]; rfl
  have c : s₂.gpr .ecx = v.getD 3 0 ++ v.getD 2 0 := by
    rw [out₂, ← hv 2 (by decide), ← hv 3 (by decide)]; rfl
  have p : s₂.gpr .esi = s.gpr .esi := keep.reg .esi (by decide)
  have w0 := CallLay.inRegions_sub (off := 0) (l := 4) writable (by decide) (by decide)
  have w4 := CallLay.inRegions_sub (off := 4) (l := 4) writable (by decide) (by decide)
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_store s₂ .eax .esi 0 (by rw [p]; omega_arith) (by rw [keep.wr, p]; exact w0), runStep_some,
      runBlock_cons, exec_store _ .ecx .esi 4 (by rw [p]; omega_arith) (by rw [keep.wr, p]; exact w4), runStep_some,
      runBlock_nil], ?_⟩
  refine ⟨keep.reg, ?_, keep.rd, keep.wr⟩
  change ((s₂.mem.writeW _ (s₂.gpr .eax)).writeW _ (s₂.gpr .ecx)) = s.mem.writeW _ (pack v)
  rw [a, c, p, keep.mem, pack_halves, Word32.write64_pair, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]

theorem argContainsCount (s : State) (count : Nat) (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (i : Nat) (hi : i < count) :
    (Region.mk (argAddr s 0) (4 * count)).Contains
      (addr32 (s.gpr .esp) + BitVec.ofNat 64 (4 + 4 * i)) 4 := by
  rw [argAddr_eq s 0 (by omega_arith)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem arguments_frame (count : Nat) {s s' : State} {rs : List Region}
    (frame : Frame rs s.mem s'.mem) (sp : s'.gpr .esp = s.gpr .esp)
    (fit : (s.gpr .esp).toNat + 4 + 4 * count ≤ 2 ^ 32)
    (sep : ∀ r ∈ rs, (Region.mk (argAddr s 0) (4 * count)).Disjoint r) :
    ∀ i < count, arg s' i = arg s i := by
  intro i hi
  unfold arg
  have e : argAddr s' i = argAddr s i := by unfold argAddr; rw [sp]
  rw [e, argAddr_eq s i (by omega_arith)]
  exact frame.readW (argContainsCount s count fit i hi) sep (by decide)

theorem pinBlock_ok (s : State)
    (key : InRegions (s.rd ++ s.wr) (argAddr s 0) 4) (data : InRegions (s.rd ++ s.wr) (argAddr s 1) 4) :
    ∃ s', runBlock isa [rr .ebp .eax, .mov .edi (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8))] s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .edi = arg s 0 ∧ s'.gpr .esi = arg s 1 ∧ Keep [.ebp, .edi, .esi] s s' := by
  simp only [argAddr, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at key data
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, rr, memOp, State.ea, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, State.load32, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, key, data]
    rfl, ?_⟩
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]; rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem blockScratchBase_ok (s : State) :
    ∃ s', runBlock isa [rr .eax .ebp] s = some s' ∧
      s'.gpr .eax = s.gpr .ebp ∧ Keep [.eax] s s' := by
  refine ⟨s.setReg .eax (s.gpr .ebp), rfl, rfl, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

end VG.Proof.Rc2.X86
