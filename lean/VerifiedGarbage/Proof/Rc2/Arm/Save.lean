import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.Arm.Rounds

section

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), Words s v → (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 →
      (∀ j < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 j)) 1) →
      WP isa (.block (code i)) s (fun s' =>
        Words s' (step (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) i v) ∧ Keep roundWrites s s'))
    (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ j < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 j)) 1) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      Words s' (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) i v) v) ∧
      Keep roundWrites s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv fit readable)
    intro s₁ h₁
    have ptr₁ := h₁.2.reg .r0 (by decide)
    have read₁ : ∀ j < 128,
        InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 j)) 1 := by
      rw [h₁.2.rd, h₁.2.wr, ptr₁]; exact readable
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 (by rw [ptr₁]; exact fit) read₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.mem, ptr₁] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) ∧
      Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv fit readable
  intro i hi s v hv fit readable
  have bound := List.mem_range.mp hi
  apply WP.mono (mix_ok s v hv i (4 * j + i) bound (by omega_arith) fit readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      Words s' (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) ∧
      Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv fit readable
  intro i hi s v hv fit readable
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega_arith
  apply WP.mono (reverseMix_ok s v hv i (4 * j + i) bound (by omega_arith) fit readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ((order d).flatMap (mash d))) s (fun s' =>
      Words s' (mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) v) ∧
      Keep roundWrites s s') := by
  have he (k : Spec.Rc2.Schedule) : mashRoundSpec d k v =
      (order d).foldl (fun v i => mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply foldWords_ok (step := fun k i v => mashSpec d k i v) _ _ _ s v hv fit readable
  intro i hi s v hv fit readable
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega_arith
  apply WP.mono (mash_ok d s v hv i bound fit readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (j : Nat) (hj : j < 16)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block (round d j)) s (fun s' =>
      Words s' (roundSpec d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) ∧
      Keep roundWrites s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : Words s₁ v₁ ∧ Keep roundWrites s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        Words s₂ (if j = 4 ∨ j = 10 then mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) v₁
          else v₁) ∧ Keep roundWrites s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      have ptr₁ := h₁.2.reg .r0 (by decide)
      have read₁ : ∀ k < 128,
          InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 k)) 1 := by
        rw [h₁.2.rd, h₁.2.wr, ptr₁]; exact readable
      apply WP.mono (mashRound_ok d s₁ v₁ h₁.1 (by rw [ptr₁]; exact fit) read₁)
      intro s₂ h₂
      rw [h₁.2.mem, ptr₁] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (mixRound_ok s v hv j hj fit readable)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [round, WP.block_append_iff]
    apply WP.mono (reverseMixRound_ok s v hv (15 - j) (by omega_arith) fit readable)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ k < 128, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 1) :
    WP isa (.block ((List.range 16).flatMap (round d))) s (fun s' =>
      Words s' ((List.range 16).foldl (fun v j => roundSpec d
        (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) j v) v) ∧ Keep roundWrites s s') := by
  apply foldWords_ok (step := fun k j v => roundSpec d k j v) _ _ _ s v hv fit readable
  intro j hj s v hv fit readable
  exact round_ok d s v hv j (List.mem_range.mp hj) fit readable

end VG.Proof.Rc2.Arm

end

section

section

/-! # Byte loads and stores for RC2 on ARMv7 -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm

theorem decode_word (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ (by omega_arith), getD_ofFn _ _ (by omega_arith)]

theorem loadWord_ok (s : State) (i : Nat) (hi : i < 4)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (loadWord i) s = some s' ∧
      s'.gpr (wordReg i) =
        ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).getD i 0).setWidth 32 ∧
      Keep [wordReg i, .r12] s s' := by
  have sep := wordReg_separate i
  have lo := readable (2 * i) (by omega_arith)
  have high := readable (2 * i + 1) (by omega_arith)
  have a := addr_add (a := s.gpr .r1) (k := 2 * i) (by omega_arith)
  have b := addr_add (a := s.gpr .r1) (k := 2 * i + 1) (by omega_arith)
  have loOff : 2 * i < 4096 := by omega_arith
  have hiOff : 2 * i + 1 < 4096 := by omega_arith
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLeDiff, and_self, loadWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.load8, loOff, hiOff, a, b, lo, high, 
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      Ne.symm sep.2.2.2.2.1, sep.1]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, sep.1, ite_false, ite_true]
    rw [decode_word _ _ i hi]
    exact Word32.joinBytes_shift _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem loadWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block (is.flatMap loadWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) =
        ((Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))).getD i 0).setWidth 32) ∧
      Keep (is.map wordReg ++ ([.r12] : List Reg)) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := loadWord_ok s i (hi i (by simp)) fit readable
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have ptr₁ := keep₁.reg .r1 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Ne.symm (wordReg_separate i).2.2.2.2.1, by decide⟩)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁
      (by rw [ptr₁]; exact fit) (by rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable))
    intro s₂ h₂
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, keep₁.mem, ptr₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨?_, (wordReg_separate i).1⟩
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h
        · subst r; simp
        · subst r; simp
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State) (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (readable : ∀ j < 8, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block blockLoad) s (fun s' =>
      Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))) ∧
      Keep roundWrites s s') := by
  apply WP.mono (loadWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s fit readable)
  intro s' h
  refine ⟨fun i hi => h.1 i (List.mem_range.mpr hi), h.2.weaken ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, _, he⟩ := List.mem_map.mp hr
    subst r; exact wordReg_mem_roundWrites i
  · simp only [List.mem_singleton] at hr
    subst r; decide

end VG.Proof.Rc2.Arm

end

/-! # Writing the four RC2 words as little-endian bytes -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.WriteBytes VG.Proof.Rc2.Word32

theorem storeWord_ok (s : State) (i : Nat) (hi : i < 4) (v : BitVec 16)
    (value : s.gpr (wordReg i) = v.setWidth 32)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa (storeWord i) s = some s' ∧
      Keep [.r12] {s with
        mem := (s.mem.writeW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (2 * i)) (v.setWidth 8)).writeW
          (State.addr (s.gpr .r1) + BitVec.ofNat 64 (2 * i + 1)) ((v >>> 8).setWidth 8)} s' := by
  have sep := wordReg_separate i
  have lo := writable (2 * i) (by omega_arith)
  have high := writable (2 * i + 1) (by omega_arith)
  have a := addr_add (a := s.gpr .r1) (k := 2 * i) (by omega_arith)
  have b := addr_add (a := s.gpr .r1) (k := 2 * i + 1) (by omega_arith)
  have loOff : 2 * i < 4096 := by omega_arith
  have hiOff : 2 * i + 1 < 4096 := by omega_arith
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, storeWord, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, State.store8, loOff, hiOff, a, b, lo, high, 
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      ]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    exact gpr_setReg_of_ne _ _ hr
  · rw [value]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]
    have byte : ((v.setWidth 32) >>> 8).setWidth 8 = (v >>> 8).setWidth 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj,
        show 8 + j < 32 by omega_arith, decide_true, Bool.true_and]
    rw [byte]
  · rfl
  · rfl

theorem storeWords_ok (n : Nat) (hn : n ≤ 4) (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block ((List.range n).flatMap storeWord)) s (fun s' =>
      Keep [.r12] {s with mem := writeBytes s.mem (State.addr (s.gpr .r1)) (outputBytes v n)} s') := by
  induction n generalizing s with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ _ => rfl, (writeBytes_nil s.mem (State.addr (s.gpr .r1))).symm, rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    apply WP.mono (ih (by omega_arith) s hv fit writable)
    intro s₁ keep₁
    have ptr₁ := keep₁.reg .r1 (by decide)
    have val₁ : s₁.gpr (wordReg n) = (v.getD n 0).setWidth 32 :=
      (keep₁.reg _ (by simpa using (wordReg_separate n).1)).trans (hv n (by omega_arith))
    obtain ⟨s₂, run₂, keep₂⟩ := storeWord_ok s₁ n (by omega_arith) _ val₁
      (by rw [ptr₁]; exact fit) (by rw [keep₁.wr, ptr₁]; exact writable)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    refine ⟨fun r hr => (keep₂.reg r hr).trans (keep₁.reg r hr), ?_,
      keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
    rw [keep₂.mem, keep₁.mem, ptr₁, outputBytes_write _ _ _ n (by omega_arith)]

theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : Words s v)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (writable : ∀ j < 8, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1) :
    WP isa (.block blockStore) s (fun s' =>
      Keep [.r12] {s with mem := s.mem.writeW (State.addr (s.gpr .r1)) (pack v)} s') := by
  apply WP.mono (storeWords_ok 4 (by decide) s v hv fit writable)
  intro s' h
  rw [outputBytes_pack] at h
  exact h

end VG.Proof.Rc2.Arm

end

section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm

theorem exec_ldr (s : State) (t n : Reg) (off : Nat) (ho : off < 4096)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.ldr t n off) s =
      some (s.setReg t (s.mem.readW (State.addr (s.gpr n) + BitVec.ofNat 64 off) 32)) := by
  simp only [exec, ho, ite_true, State.load32, addr_add fit, h, Option.map_some]

theorem exec_str (s : State) (t n : Reg) (off : Nat) (ho : off < 4096)
    (fit : (s.gpr n).toNat + off < 2 ^ 32)
    (h : InRegions s.wr (State.addr (s.gpr n) + BitVec.ofNat 64 off) 4) :
    exec (.str t n off) s =
      some {s with mem := s.mem.writeW (State.addr (s.gpr n) + BitVec.ofNat 64 off) (s.gpr t)} := by
  simp only [exec, ho, ite_true, State.store32, addr_add fit, h]

end VG.Proof.Rc2.Arm

end

/-! # Where RC2 (and TDEA) save their callee-saved registers in scratch

The `i`th register of a list at byte `4 * i`; the saving and restoring are
`VG.Arm.Spill`'s. -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm

/-- Each register of `regs`, the `i`th at byte `4 * i`. -/
def slotsOf (regs : List Reg) : List (Reg × Nat) := regs.zipIdx.map fun (r, i) => (r, 4 * i)

end VG.Proof.Rc2.Arm
