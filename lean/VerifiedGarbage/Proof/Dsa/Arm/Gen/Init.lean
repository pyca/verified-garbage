module

public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.SearchInit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Dsa.Arm.Generation
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.SearchInit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Starting the DSA parameter search on ARMv7: correctness, constant time

`init` compares `p_len` with 128, 256 and 384, then writes the words
`[4096, p_len, 32769 p_len, 512 p_len]` as halves and returns 1, or zeros
and 0 (the RSA prime search's `clear`, with its proof,
`Proof/RsaKeyGen/Arm/SearchInit.lean`, whose slots this proof reuses). Its
branches depend on `p_len` alone, which is public, as is the state's
address: a taint check.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen.Init

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Proof.RsaKeyGen.Arm (writeSlots slot_writeSlots wordsAt_slots)
open VG.Proof.RsaKeyGen.Arm.SearchInit (Space clear_ok zeros zeros_words shl32)
open VG.Impl.Dsa.Arm.Generation (init initWords)

/-- The words for a width `L`, as halves. -/
def words (L : Nat) : List (Nat × BitVec 32) :=
  [(1, 0), (3, 0), (5, 0), (7, 0), (2, BitVec.ofNat 32 L), (4, BitVec.ofNat 32 (32769 * L)),
    (6, BitVec.ofNat 32 (512 * L)), (0, 4096)]

theorem words_ok {B : BitVec 32} {s : State} (h : Space B s) {L : Nat} (hL : s.gpr .r1 = BitVec.ofNat 32 L)
    (hb : L ≤ 384) :
    WP isa (.block initWords) s fun t => t.gpr .r0 = 1 ∧ t.mem = writeSlots s.mem (State.addr B) (words L) := by
  unfold initWords words writeSlots
  ffrun [h.addr (d := 0) (by decide), h.addr (d := 4) (by decide), h.addr (d := 8) (by decide),
    h.addr (d := 12) (by decide), h.addr (d := 16) (by decide), h.addr (d := 20) (by decide),
    h.addr (d := 24) (by decide), h.addr (d := 28) (by decide),
    h.space.write (off := 0) (by decide), h.space.write (off := 4) (by decide),
    h.space.write (off := 8) (by decide), h.space.write (off := 12) (by decide),
    h.space.write (off := 16) (by decide), h.space.write (off := 20) (by decide),
    h.space.write (off := 24) (by decide), h.space.write (off := 28) (by decide), hL,
    shl32 L 15 (by omega), shl32 L 9 (by omega), ← BitVec.ofNat_add,
    show ((4096 : BitVec 16).setWidth 32) = (4096 : BitVec 32) from rfl]
  simp only [List.foldl_cons, List.foldl_nil, show L * 2 ^ 15 + L = 32769 * L by omega,
    show L * 2 ^ 9 = 512 * L by omega]

/-- `cmp r1, #c`: whether `p_len` is `c`. -/
theorem cmpW_ok (s : State) (c : BitVec 32) (enc : encodable c = true) :
    WP isa (.block [.cmp .r1 (.imm c)]) s fun t =>
      (t.z = decide (s.gpr .r1 = c) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest_all [] ?_ (by rfl) (by rfl)
  ffrun [enc]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro hz
    calc
      s.gpr .r1 = (s.gpr .r1 - c) + c := (BitVec.sub_add_cancel _ _).symm
      _ = 0#32 + c := congrArg (fun x : BitVec 32 => x + c) hz
      _ = c := BitVec.zero_add _
  · intro hz
    rw [hz, BitVec.sub_self]
    rfl

/-- The words written, or zeros. -/
def InitPost (L : Nat) (m : Mem) (B : BitVec 32) (t : State) : Prop :=
  if Spec.Dsa.generationPLenValid L then t.gpr .r0 = 1 ∧ t.mem = writeSlots m (State.addr B) (words L)
  else t.gpr .r0 = 0 ∧ t.mem = writeSlots m (State.addr B) zeros

theorem init_ok {s : State} {B : BitVec 32} (h : Space B s) :
    WP isa init s (InitPost (s.gpr .r1).toNat s.mem B) := by
  have hL : s.gpr .r1 = BitVec.ofNat 32 (s.gpr .r1).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have valid : ∀ t, t.mem = s.mem → Rest [] s t → Spec.Dsa.generationPLenValid (s.gpr .r1).toNat →
      (s.gpr .r1).toNat ≤ 384 → WP isa (.block initWords) t (InitPost (s.gpr .r1).toNat s.mem B) := by
    intro t hm k hv hb
    refine WP.mono (words_ok (h.congr k.wr (k.gpr .r0 (by decide))) (by rw [k.gpr .r1 (by decide)]; exact hL) hb)
      fun u ⟨h0, hmu⟩ => ?_
    unfold InitPost
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    exact ⟨h0, by rw [hmu, hm]⟩
  unfold init
  refine WP.seq (WP.mono (cmpW_ok s 128 (by decide)) fun t₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_)
  by_cases e₁ : (s.gpr .r1).toNat = 128
  · refine WP.ite true (by show some t₁.z = _; rw [z₁, decide_eq_true (BitVec.eq_of_toNat_eq (by rw [e₁]; rfl))]) (fun _ =>
      valid t₁ m₁ k₁ (by simp [Spec.Dsa.generationPLenValid, e₁]) (by omega)) (by intro h; cases h)
  refine WP.ite false (by show some t₁.z = _; rw [z₁, decide_eq_false (fun h => e₁ (by rw [h]; rfl))])
    (by intro h; cases h) fun _ => ?_
  refine WP.seq (WP.mono (cmpW_ok t₁ 0x100 (by decide)) fun t₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
  rw [k₁.gpr .r1 (by decide)] at z₂
  by_cases e₂ : (s.gpr .r1).toNat = 256
  · refine WP.ite true (by show some t₂.z = _; rw [z₂, decide_eq_true (BitVec.eq_of_toNat_eq (by rw [e₂]; rfl))]) (fun _ =>
      valid t₂ (m₂.trans m₁) (k₁.trans k₂) (by simp [Spec.Dsa.generationPLenValid, e₂]) (by omega))
      (by intro h; cases h)
  refine WP.ite false (by show some t₂.z = _; rw [z₂, decide_eq_false (fun h => e₂ (by rw [h]; rfl))])
    (by intro h; cases h) fun _ => ?_
  refine WP.seq (WP.mono (cmpW_ok t₂ 0x180 (by decide)) fun t₃ ⟨⟨z₃, m₃⟩, k₃⟩ => ?_)
  rw [k₂.gpr .r1 (by decide), k₁.gpr .r1 (by decide)] at z₃
  have k₁₃ := k₁.trans (k₂.trans k₃)
  have m₁₃ := m₃.trans (m₂.trans m₁)
  by_cases e₃ : (s.gpr .r1).toNat = 384
  · refine WP.ite true (by show some t₃.z = _; rw [z₃, decide_eq_true (BitVec.eq_of_toNat_eq (by rw [e₃]; rfl))]) (fun _ =>
      valid t₃ m₁₃ k₁₃ (by simp [Spec.Dsa.generationPLenValid, e₃]) (by omega)) (by intro h; cases h)
  refine WP.ite false (by show some t₃.z = _; rw [z₃, decide_eq_false (fun h => e₃ (by rw [h]; rfl))])
    (by intro h; cases h) fun _ => ?_
  refine WP.mono (clear_ok (h.congr k₁₃.wr (k₁₃.gpr .r0 (by decide)))) fun u ⟨h0, hmu⟩ => ?_
  unfold InitPost
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [Spec.Dsa.generationPLenValid, e₁, e₂, e₃]))]
  exact ⟨h0, by rw [hmu, m₁₃]⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 32⟩] ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32

def initPost (s t : State) : Prop :=
  match Spec.Dsa.parameterInit (s.gpr .r1).toNat with
  | none => ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 = List.replicate 4 0
  | some values => ((t.gpr .r1 ++ t.gpr .r0).setWidth 32).toNat = 1 ∧
      ∃ first, Spec.Rsa.wordsAt t.mem (State.addr (s.gpr .r0)) 4 =
        (values ++ [first]).map (BitVec.ofNat 64) ∧
        Spec.Entropy.RequestValid (Spec.Dsa.parameterEntropy (s.gpr .r1).toNat) 0 first

def initPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem words_words (m : Mem) (B : Addr) (L : Nat) (hL : L ≤ 384) :
    Spec.Rsa.wordsAt (writeSlots m B (words L)) B 4 =
      [BitVec.ofNat 64 4096, BitVec.ofNat 64 L, BitVec.ofNat 64 (32769 * L), BitVec.ofNat 64 (512 * L)] := by
  have hi := slot_writeSlots m B (N := 8) (by decide) (words L) (by
    simp only [words, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)
  refine wordsAt_slots _ _ (by decide) (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    rw [hi _ (by decide)] <;> rfl

private theorem result_post {s t : State} (h : InitPost (s.gpr .r1).toNat s.mem (s.gpr .r0) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost Spec.Dsa.parameterInit
  split at h
  · rename_i hv
    have hb : (s.gpr .r1).toNat ≤ 384 := by
      simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv; omega
    have hp : 0 < (s.gpr .r1).toNat := by
      simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [BitVec.setWidth_append_eq_right, h.1]; rfl, 512 * (s.gpr .r1).toNat, ?_, ?_⟩
    · rw [h.2, words_words _ _ _ hb]; rfl
    · unfold Spec.Entropy.RequestValid Spec.Dsa.parameterEntropy; omega
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [BitVec.setWidth_append_eq_right, h.1]; rfl, by rw [h.2, zeros_words]⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom⟩ := h
  have sp : Space (s.gpr .r0) s := ⟨⟨hroom, by rw [hwr]; exact List.mem_singleton_self _⟩, rfl⟩
  obtain ⟨tr, t, he, hp, k⟩ := withRest_all [.r0, .r12] (init_ok sp) (by rfl) (by rfl)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp⟩, result_post hp⟩

/-- The initial taint: the arguments are public. -/
def initTaint : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1], flags := false }

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) initTaint (fun s₁ s₂ _ _ hp => ?_) (by taint_decide)
  obtain ⟨_, p0, p1⟩ := hp
  have wf : ∀ s, VG.Arm.Taint.Wf initTaint s := fun s =>
    ⟨(fun h => absurd rfl h), (fun _ h => by simp [initTaint] at h), (fun h => absurd h (by decide)),
      (fun _ h => by simp [initTaint] at h)⟩
  refine ⟨⟨fun r hr => ?_, fun h => by simp [initTaint] at h⟩, (fun h => absurd rfl h), wf s₁, wf s₂,
    (fun _ h => by simp [initTaint] at h), (fun _ h => by simp [initTaint] at h),
    (fun h => absurd h (by decide)), (fun k hk => absurd hk (Nat.not_lt_zero k))⟩
  simp only [initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

private def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 128 | _ => 0
  sp := 0x3000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.Dsa.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs, reduceClassify, Loc.val, State.addr]
      [initSat] using initSat

end VG.Proof.Dsa.Arm.Gen.Init
