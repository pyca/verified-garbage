module

public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Step
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Bitsliced DES rounds and passes on ARMv7

`round_ok`: the code of a round copies the round key at the key pointer
(word 74 of the working space) into words 72 and 73, steps the pointer by
`δ d` (8 or −8) and does to the state words what `roundW` does with the
key's low 48 bits. `pass_ok`: a pass points the key pointer at its first key
in the schedule (whose address is word 76), runs eight pairs of rounds
(counted down in word 75) and exchanges the halves: what `passW` does with
the component schedule. `passes_ok`: the three passes do what `tdeaW` does.
They write only the first 76 words of the working space.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Bitslice VG.Impl.TripleDes.Arm.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.Arm.Straight (wordAddr add_ofNat_ofNat in_off toNat_addr)
open VG.Proof.X25519.Arm (dpVal op2_imm op2_reg)

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 32 := if d = .encrypt then 8 else -8

/-- The schedule at `Sb` is readable, does not wrap around and is apart from
the working space. -/
structure Sched (s : State) (Sb : BitVec 32) : Prop where
  rd : (⟨State.addr Sb, 384⟩ : Region) ∈ s.rd
  fit : Sb.toNat + 384 ≤ 2 ^ 32
  apart : (⟨State.addr Sb, 384⟩ : Region).Disjoint (frameR s)

theorem Sched.congr {s s' : State} {Sb : BitVec 32} (h : Sched s Sb) (hb : s'.gpr .r3 = s.gpr .r3)
    (hr : s'.rd = s.rd) : Sched s' Sb where
  rd := by rw [hr]; exact h.rd
  fit := h.fit
  apart := by rw [frameR, hb]; exact h.apart

/-- A round key's pointer: to word `i < 48` of the schedule. -/
def KeyAt (Sb P : BitVec 32) : Prop := ∃ i < 48, P = Sb + BitVec.ofNat 32 (8 * i)

/-- The key at `P`: the low 48 bits of its doubleword. -/
def keyW (m : Mem) (P : BitVec 32) : BitVec 48 := (m.readW (State.addr P) 64).setWidth 48

theorem keyAt_addr {Sb P : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) (hk : KeyAt Sb P) :
    ∃ i < 48, P = Sb + BitVec.ofNat 32 (8 * i) ∧
      State.addr P = State.addr Sb + BitVec.ofNat 64 (8 * i) ∧ P.toNat + 8 ≤ 2 ^ 32 := by
  obtain ⟨i, hi, rfl⟩ := hk
  refine ⟨i, hi, rfl, addr_add (by omega_using [hf, hi]), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [hi]),
    Nat.mod_eq_of_lt (by omega_using [hf, hi])]
  omega_using [hf, hi]

theorem keyAt_rd {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {off : Nat}
    (ho : off + 4 ≤ 8) : InRegions (s.rd ++ s.wr) (State.addr (P + BitVec.ofNat 32 off)) 4 := by
  obtain ⟨i, hi, rfl⟩ := hk
  rw [add_ofNat_ofNat]
  exact in_off (List.mem_append_left _ hs.rd) hs.fit (by omega_using [hi, ho]) (by decide)

/-- A round key is not in the working space. -/
theorem keyW_frame {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {n : Nat}
    (hn : n ≤ 256) {m : Mem} (hf : Frame [headR s n] s.mem m) : keyW m P = keyW s.mem P := by
  obtain ⟨i, hi, -, ha, -⟩ := keyAt_addr hs.fit hk
  rw [keyW, keyW, ha]
  refine congrArg (BitVec.setWidth 48) (hf.readW (r := ⟨State.addr Sb, 384⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (fun r hr => ?_) (by decide))
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

/-- The two words of a key. -/
theorem keyWords_read (m : Mem) {P : BitVec 32} (hP : P.toNat + 8 ≤ 2 ^ 32) :
    KeyWords (m.readW (State.addr (P + BitVec.ofNat 32 0)) 32)
      (m.readW (State.addr (P + BitVec.ofNat 32 4)) 32) (keyW m P) := by
  rw [BitVec.add_zero, addr_add (by omega_using [hP]), Mem.readW_lo32 rfl, Mem.readW_hi32 rfl, keyW]
  constructor
  · intro b hb
    simp only [BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show b < 48 by omega_using [hb]]
  · intro b hb
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', show b < 32 by omega_using [hb],
      decide_true, Bool.true_and, show 32 + b < 48 by omega_using [hb]]

/-! ## A round -/

theorem keyLoad_ok (d : Direction) {s : State} (h : Room s) {Sb P : BitVec 32} (hs : Sched s Sb)
    (hk : KeyAt Sb P) (hP : fw s 74 = P) :
    ∃ s', runBlock isa (keyLoad d) s = some s' ∧
      KeyWords (fw s' 72) (fw s' 73) (keyW s.mem P) ∧ fw s' 74 = P + δ d ∧
      (∀ x < 64, words s' x = words s x) ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [headR s 75] s.mem s'.mem := by
  obtain ⟨-, -, -, -, hfit⟩ := keyAt_addr hs.fit hk
  have e₁ := exec_ldrFw h (t := .r0) (off := kpOff) 74 rfl (by decide)
  let s₁ := s.setReg .r0 (fw s 74)
  have p₁ : s₁.gpr .r0 = P := by simp only [s₁, RegUpd.gpr_setReg_self, hP]
  have e₂ := exec_ldr (s := s₁) (t := .r1) (n := .r0) (off := 0) (by decide)
    (by rw [p₁]; exact keyAt_rd hs hk (by decide))
  let s₂ := s₁.setReg .r1 (s₁.mem.readW (State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0)) 32)
  have p₂ : s₂.gpr .r0 = P := by simp only [s₂, RegUpd.gpr_setReg, reduceCtorEq, ite_false, p₁]
  have e₃ := exec_ldr (s := s₂) (t := .r2) (n := .r0) (off := 4) (by decide)
    (by rw [p₂]; exact keyAt_rd hs hk (by decide))
  let s₃ := s₂.setReg .r2 (s₂.mem.readW (State.addr (s₂.gpr .r0 + BitVec.ofNat 32 4)) 32)
  have h₃ : Room s₃ := h.congr rfl rfl
  have e₄ := exec_strFw h₃ (t := .r1) (off := kloOff) 72 rfl (by decide)
  let s₄ := stFw s₃ 72 (s₃.gpr .r1)
  have h₄ : Room s₄ := h₃.stFw _ _
  have e₅ := exec_strFw h₄ (t := .r2) (off := khiOff) 73 rfl (by decide)
  let s₅ := stFw s₄ 73 (s₄.gpr .r2)
  have h₅ : Room s₅ := h₄.stFw _ _
  have e₆ := exec_dp (s := s₅) (op := if d = .encrypt then .add else .sub) (d := .r0) (n := .r0)
    (op2_imm (v := 8) (by decide))
  let s₆ := s₅.setReg .r0 (dpVal (if d = .encrypt then .add else .sub) (s₅.gpr .r0) 8)
  have h₆ : Room s₆ := h₅.congr rfl rfl
  have e₇ := exec_strFw h₆ (t := .r0) (off := kpOff) 74 rfl (by decide)
  have lo : s₃.gpr .r1 = s.mem.readW (State.addr (P + BitVec.ofNat 32 0)) 32 := by
    simp only [s₃, s₂, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, p₁]; rfl
  have hi : s₄.gpr .r2 = s.mem.readW (State.addr (P + BitVec.ofNat 32 4)) 32 := by
    show s₃.gpr .r2 = _
    simp only [s₃, RegUpd.gpr_setReg_self, p₂]; rfl
  have nx : s₆.gpr .r0 = P + δ d := by
    have : s₅.gpr .r0 = P := p₂
    simp only [s₆, RegUpd.gpr_setReg_self, this, δ]
    cases d
    · rfl
    · exact BitVec.sub_eq_add_neg _ _
  have f : ∀ j, j < 256 → fw (stFw s₆ 74 (s₆.gpr .r0)) j =
      if j = 74 then P + δ d else if j = 73 then s.mem.readW (State.addr (P + BitVec.ofNat 32 4)) 32
      else if j = 72 then s.mem.readW (State.addr (P + BitVec.ofNat 32 0)) 32 else fw s j := by
    intro j hj
    rw [fw_stFw h₆ (by decide) hj, nx]
    by_cases e74 : j = 74
    · rw [ite_eq_left e74, ite_eq_left e74]
    rw [ite_eq_right e74, ite_eq_right e74]
    show fw s₅ j = _
    rw [fw_stFw h₄ (by decide) hj, hi]
    by_cases e73 : j = 73
    · rw [ite_eq_left e73, ite_eq_left e73]
    rw [ite_eq_right e73, ite_eq_right e73, fw_stFw h₃ (by decide) hj, lo]
    rfl
  refine ⟨stFw s₆ 74 (s₆.gpr .r0), ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [keyLoad, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some, runBlock_cons, e₂,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons,
      e₅, runStep_some, runBlock_cons, e₆, runStep_some, runBlock_cons, e₇, runStep_some,
      runBlock_nil]
  · rw [f 72 (by decide), f 73 (by decide)]
    exact keyWords_read s.mem hfit
  · rw [f 74 (by decide)]; rfl
  · have hx' : spills + x < 256 := by unfold spills; omega_using [hx]
    rw [words, f _ hx', ite_eq_right (by unfold spills; omega_using [hx]),
      ite_eq_right (by unfold spills; omega_using [hx]), ite_eq_right (by unfold spills; omega_using [hx])]
    rfl
  · have f₁ : Frame [headR s 75] s.mem s₄.mem := stFw_frame h₃ (by decide) (by decide) _
    have f₂ : Frame [headR s 75] s₄.mem s₅.mem := stFw_frame h₄ (by decide) (by decide) _
    have f₃ : Frame [headR s 75] s₅.mem (stFw s₆ 74 (s₆.gpr .r0)).mem :=
      stFw_frame h₆ (by decide) (by decide) _
    exact (f₁.trans f₂).trans f₃

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : KeyWords (fw s 72) (fw s 73) k) :
    ∃ s', runBlock isa (stepsCode ρ n) s = some s' ∧
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, w₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega_using [hn])
    have h₁ : Room s₁ := h.congr g₁ wr₁
    have k₁ : KeyWords (fw s₁ 72) (fw s₁ 73) k := by
      rw [fw_of_frame h g₁ f₁ (by decide) (by decide), fw_of_frame h g₁ f₁ (by decide) (by decide)]
      exact hkey
    obtain ⟨s₂, run₂, w₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := sboxStep_ok ρ (j := n) (by omega_using [hn]) h₁ k k₁
    refine ⟨s₂, ?_, fun x hx => ?_, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
    · rw [stepsCode_succ]; exact runBlock_cat_some run₁ run₂
    · rw [w₂ x hx, steps_succ]
      exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega_using [hn]) w₁ (w₁ x hx)
    · rw [stR_congr g₁] at f₂; exact f₁.trans f₂

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) {Sb P : BitVec 32}
    (hs : Sched s Sb) (hk : KeyAt Sb P) (hP : fw s 74 = P) :
    ∃ s', runBlock isa (round d ρ) s = some s' ∧
      (∀ x < 64, words s' x = roundW ρ (keyW s.mem P) (words s) x) ∧ fw s' 74 = P + δ d ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [headR s 75] s.mem s'.mem := by
  obtain ⟨s₁, run₁, k₁, p₁, w₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := keyLoad_ok d h hs hk hP
  have h₁ : Room s₁ := h.congr g₁ wr₁
  obtain ⟨s₂, run₂, w₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := stepsCode_ok ρ (keyW s.mem P) (Nat.le_refl 8) h₁ k₁
  refine ⟨s₂, ?_, fun x hx => ?_, ?_, g₂.trans g₁, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [round_eq]; exact runBlock_cat_some run₁ run₂
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8) w₁ x hx
  · rw [fw_of_frame h₁ g₂ f₂ (by decide) (by decide), p₁]
  · rw [stR_congr g₁] at f₂
    exact f₁.trans (headR_mono (by decide) f₂)

/-! ## Pairs of rounds -/

/-- The count of pairs left, one less. -/
def countDown : List Instr := [.ldr .r0 base cntOff, .subs .r0 .r0 (.imm 1), .str .r0 base cntOff]

theorem roundPair_eq (d : Direction) : roundPair d = round d .ba ++ (round d .ab ++ countDown) := by
  simp only [roundPair, countDown, List.append_assoc]

theorem countDown_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa countDown s = some s' ∧ fw s' 75 = fw s 75 - 1 ∧
      s'.z = (fw s 75 - 1 == 0) ∧ (∀ j < 256, j ≠ 75 → fw s' j = fw s j) ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [headR s 76] s.mem s'.mem := by
  have e₁ := exec_ldrFw h (t := .r0) (off := cntOff) 75 rfl (by decide)
  let s₁ := s.setReg .r0 (fw s 75)
  have e₂ := exec_subs (s := s₁) (d := .r0) (n := .r0) (op2_imm (v := 1) (by decide))
  let s₂ := (subFlags s₁ (s₁.gpr .r0) 1).setReg .r0 (s₁.gpr .r0 - 1)
  have h₂ : Room s₂ := h.congr rfl rfl
  have e₃ := exec_strFw h₂ (t := .r0) (off := cntOff) 75 rfl (by decide)
  have v : s₂.gpr .r0 = fw s 75 - 1 := by
    simp only [s₂, s₁, RegUpd.gpr_setReg_self]
  refine ⟨stFw s₂ 75 (s₂.gpr .r0), ?_, ?_, ?_, fun j hj hne => ?_, rfl, rfl, rfl, rfl,
    stFw_frame h₂ (by decide) (by decide) _⟩
  · rw [countDown, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some, runBlock_cons, e₂,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]
  · rw [fw_stFw h₂ (by decide) (by decide), ite_eq_left rfl, v]
  · show (s₁.gpr .r0 - 1 == 0) = _
    simp only [s₁, RegUpd.gpr_setReg_self]
  · rw [fw_stFw h₂ (by decide) hj, ite_eq_right hne]; rfl

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) {Sb P : BitVec 32} (hs : Sched s Sb)
    (hk₁ : KeyAt Sb P) (hk₂ : KeyAt Sb (P + δ d)) (hP : fw s 74 = P) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab (keyW s.mem (P + δ d))
        (roundW .ba (keyW s.mem P) (words s)) x) ∧
      fw s' 74 = P + δ d + δ d ∧ fw s' 75 = fw s 75 - 1 ∧ s'.z = (fw s 75 - 1 == 0) ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [headR s 76] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, p₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := round_ok d .ba h hs hk₁ hP
  have h₁ : Room s₁ := h.congr g₁ wr₁
  have hs₁ : Sched s₁ Sb := hs.congr g₁ rd₁
  obtain ⟨s₂, run₂, w₂, p₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := round_ok d .ab h₁ hs₁ hk₂ p₁
  have g₂' : s₂.gpr .r3 = s.gpr .r3 := g₂.trans g₁
  have h₂ : Room s₂ := h.congr g₂' (wr₂.trans wr₁)
  have f₁₂ : Frame [headR s 75] s.mem s₂.mem := f₁.trans (by rw [← headR_congr g₁]; exact f₂)
  obtain ⟨s₃, run₃, c₃, z₃, o₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := countDown_ok h₂
  have c₂ : fw s₂ 75 = fw s 75 := fw_of_frame h g₂' f₁₂ (by decide) (by decide)
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, by rw [c₃, c₂], by rw [z₃, c₂], g₃.trans g₂',
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [roundPair_eq]; exact runBlock_cat_some run₁ (runBlock_cat_some run₂ run₃)
  · have : words s₃ x = words s₂ x := by
      rw [words, o₃ _ (by unfold spills; omega_using [hx]) (by unfold spills; omega_using [hx])]; rfl
    rw [this, w₂ x hx, keyW_frame hs hk₂ (by decide) f₁]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · rw [o₃ _ (by decide) (by decide), p₂]
  · exact (headR_mono (by decide) f₁₂).trans (by rw [← headR_congr g₂']; exact f₃)

/-! ## A pass -/

/-- The word of the component that is round `r`'s key. -/
def ix (d : Direction) (r : Nat) : Nat := if d = .encrypt then r else 15 - r

theorem kaddr : ∀ c < 3, ∀ d : Direction, ∀ r < 16,
    BitVec.ofNat 32 (keyOff c d) + BitVec.ofNat 32 r * δ d = BitVec.ofNat 32 (8 * (16 * c + ix d r)) := by
  intro c hc d r hr
  cases d
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 32 (keyOff c .encrypt) + BitVec.ofNat 32 r * δ .encrypt =
      BitVec.ofNat 32 (8 * (16 * c + ix .encrypt r))) c hc r hr
  · exact (by decide : ∀ c < 3, ∀ r < 16, BitVec.ofNat 32 (keyOff c .decrypt) + BitVec.ofNat 32 r * δ .decrypt =
      BitVec.ofNat 32 (8 * (16 * c + ix .decrypt r))) c hc r hr

theorem kptr_succ (a₀ δ : BitVec 32) (r : Nat) :
    a₀ + BitVec.ofNat 32 r * δ + δ = a₀ + BitVec.ofNat 32 (r + 1) * δ := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul]
  exact congrArg (fun t => a₀ + (BitVec.ofNat 32 r * δ + t)) (BitVec.one_mul δ).symm

/-- The keys of a pass: those at `P + r δ`. -/
def keyOf (m : Mem) (P δ : BitVec 32) (r : Nat) : BitVec 48 := keyW m (P + BitVec.ofNat 32 r * δ)

/-- The pass's first key's pointer. -/
def passP (Sb : BitVec 32) (c : Nat) (d : Direction) : BitVec 32 := Sb + BitVec.ofNat 32 (keyOff c d)

theorem ix_lt (d : Direction) {r : Nat} (hr : r < 16) : ix d r < 16 := by
  unfold ix; split <;> omega_arith

theorem passKeyAt (Sb : BitVec 32) {c : Nat} (hc : c < 3) (d : Direction) {r : Nat} (hr : r < 16) :
    KeyAt Sb (passP Sb c d + BitVec.ofNat 32 r * δ d) := by
  have := ix_lt d hr
  refine ⟨16 * c + ix d r, by omega_using [hc, this], ?_⟩
  rw [passP, BitVec.add_assoc, kaddr c hc d r hr]

theorem keyOf_pass (m : Mem) {Sb : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) {c : Nat} (hc : c < 3)
    (d : Direction) {r : Nat} (hr : r < 16) :
    keyOf m (passP Sb c d) (δ d) r =
      roundKey (componentSchedule (scheduleAt m (State.addr Sb)) c) d r := by
  have hi := ix_lt d hr
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl,
    componentSchedule_readW m _ _ _ hc hi, keyOf, keyW, passP, BitVec.add_assoc, kaddr c hc d r hr,
    addr_add (by omega_using [hf, hc, hi])]

/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (Sb : BitVec 32) (c : Nat) (d : Direction) (m : Nat) (s : State) :
    Prop where
  le : m ≤ 8
  base : s.gpr .r3 = s₀.gpr .r3
  ptr : fw s 74 = passP Sb c d + BitVec.ofNat 32 (2 * m) * δ d
  cnt : fw s 75 = BitVec.ofNat 32 (8 - m)
  wds : ∀ x < 64, words s x =
    VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP Sb c d) (δ d)) m (words s₀) x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [headR s₀ 76] s₀.mem s.mem

theorem pair_step {s₀ : State} (h₀ : Room s₀) {Sb : BitVec 32} (hs₀ : Sched s₀ Sb) {c : Nat}
    (hc : c < 3) {d : Direction} {m : Nat} (hm : m < 8) {s : State} (I : PairInv s₀ Sb c d m s) :
    ∃ s', runBlock isa (roundPair d) s = some s' ∧ PairInv s₀ Sb c d (m + 1) s' ∧
      s'.z = decide (m + 1 = 8) := by
  have h : Room s := h₀.congr I.base I.wr
  have hs : Sched s Sb := hs₀.congr I.base I.rd
  have hk₁ := passKeyAt Sb hc d (r := 2 * m) (by omega_using [hm])
  have hk₂ := passKeyAt Sb hc d (r := 2 * m + 1) (by omega_using [hm])
  rw [← kptr_succ] at hk₂
  obtain ⟨s', run, w, p74, p75, pz, g, rd, wr, sp, f⟩ := roundPair_ok d h hs hk₁ hk₂ I.ptr
  have rk : ∀ r < 16, keyW s.mem (passP Sb c d + BitVec.ofNat 32 r * δ d) =
      keyW s₀.mem (passP Sb c d + BitVec.ofNat 32 r * δ d) := fun r hr =>
    keyW_frame hs₀ (passKeyAt Sb hc d hr) (by decide) I.frame
  have cnt : fw s 75 - 1 = BitVec.ofNat 32 (8 - (m + 1)) := by
    rw [I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 32 (8 - m) - 1 = BitVec.ofNat 32 (8 - (m + 1))) m hm
  refine ⟨s', run, ⟨by omega_using [hm], g.trans I.base, ?_, by rw [p75, cnt], fun x hx => ?_,
    rd.trans I.rd, wr.trans I.wr, sp.trans I.sp, ?_⟩, ?_⟩
  · rw [p74, kptr_succ, kptr_succ]; congr 3
  · have e : passP Sb c d + BitVec.ofNat 32 (2 * m) * δ d + δ d =
        passP Sb c d + BitVec.ofNat 32 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega_using [hm]), rk _ (by omega_using [hm])]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · exact I.frame.trans (by rw [← headR_congr I.base]; exact f)
  · rw [pz, cnt]
    exact (by decide : ∀ m < 8, (BitVec.ofNat 32 (8 - (m + 1)) == 0) = decide (m + 1 = 8)) m hm

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) {Sb : BitVec 32} (hs₀ : Sched s₀ Sb) {c : Nat}
    (hc : c < 3) (d : Direction) {s : State} (I : PairInv s₀ Sb c d 0 s) :
    WP isa (.loop (.block (roundPair d)) .ne) s (PairInv s₀ Sb c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ Sb c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  obtain ⟨v', run, J', z⟩ := pair_step h₀ hs₀ hc hm J
  refine WP.of_runBlock ⟨v', run, ?_⟩
  rw [show isa.eval .ne v' = some !v'.z from rfl, z]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], 8 - (m + 1), by omega_using [hm, hn], m + 1, by omega_using [hm, e], rfl, J'⟩

theorem passStart_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32}
    (hS : fw s 76 = Sb) :
    ∃ s', runBlock isa (passStart c d) s = some s' ∧ PairInv s Sb c d 0 s' := by
  have e₁ := exec_ldrFw h (t := .r0) (off := schedOff) 76 rfl (by decide)
  let s₁ := s.setReg .r0 (fw s 76)
  have enc : encodable (BitVec.ofNat 32 (keyOff c d)) = true := by
    cases d
    · exact (by decide : ∀ c < 3, encodable (BitVec.ofNat 32 (keyOff c .encrypt)) = true) c hc
    · exact (by decide : ∀ c < 3, encodable (BitVec.ofNat 32 (keyOff c .decrypt)) = true) c hc
  have e₂ := exec_dp (s := s₁) (op := .add) (d := .r0) (n := .r0) (op2_imm enc)
  let s₂ := s₁.setReg .r0 (dpVal .add (s₁.gpr .r0) (BitVec.ofNat 32 (keyOff c d)))
  have h₂ : Room s₂ := h.congr rfl rfl
  have e₃ := exec_strFw h₂ (t := .r0) (off := kpOff) 74 rfl (by decide)
  let s₃ := stFw s₂ 74 (s₂.gpr .r0)
  have h₃ : Room s₃ := h₂.stFw _ _
  have e₄ := exec_mov (s := s₃) (d := .r0) (o := .imm 8) (op2_imm (by decide))
  let s₄ := s₃.setReg .r0 8
  have h₄ : Room s₄ := h₃.congr rfl rfl
  have e₅ := exec_strFw h₄ (t := .r0) (off := cntOff) 75 rfl (by decide)
  have p : s₂.gpr .r0 = passP Sb c d := by
    simp only [s₂, s₁, RegUpd.gpr_setReg_self, hS, dpVal, passP]
  have z : BitVec.ofNat 32 (2 * 0) * δ d = 0#32 := by cases d <;> decide
  refine ⟨stFw s₄ 75 (s₄.gpr .r0), ?_, ⟨by decide, rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, ?_⟩⟩
  · rw [passStart, runBlock_cons, show base = .r3 from rfl, e₁, runStep_some, runBlock_cons, e₂,
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons,
      e₅, runStep_some, runBlock_nil]
  · rw [fw_stFw h₄ (by decide) (by decide), ite_eq_right (by decide)]
    show fw s₃ 74 = _
    rw [fw_stFw h₂ (by decide) (by decide), ite_eq_left rfl, p, z, BitVec.add_zero]
  · rw [fw_stFw h₄ (by decide) (by decide), ite_eq_left rfl]
    simp only [s₄, RegUpd.gpr_setReg_self]; rfl
  · rw [words_stFw h₄ (by decide) (by decide) hx]
    show words s₃ x = _
    rw [words_stFw h₂ (by decide) (by decide) hx]
    rfl
  · have f₁ : Frame [headR s 76] s.mem s₃.mem := stFw_frame h₂ (by decide) (by decide) _
    have f₂ : Frame [headR s 76] s₃.mem (stFw s₄ 75 (s₄.gpr .r0)).mem :=
      stFw_frame h₄ (by decide) (by decide) _
    exact f₁.trans f₂

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32}
    (hs : Sched s Sb) (hS : fw s 76 = Sb) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x =
        passW (componentSchedule (scheduleAt s.mem (State.addr Sb)) c) d (words s) x) ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [headR s 76] s.mem s'.mem := by
  unfold pass
  apply WP.seq
  obtain ⟨s₁, run₁, I0⟩ := passStart_ok c hc d h hS
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  refine WP.mono (pairLoop_ok h hs hc d I0) fun v J => ?_
  have hv : Room v := h.congr J.base J.wr
  obtain ⟨v', run, w, g, rd, wr, sp, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, g.trans J.base, rd.trans J.rd, wr.trans J.wr,
    sp.trans J.sp, ?_⟩
  · rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
    refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
    rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8
      (fun r hr => keyOf_pass _ hs.fit hc d hr)]
  · rw [stR_congr J.base] at f
    exact J.frame.trans (headR_mono (by decide) f)

/-! ## The three passes -/

theorem scheduleAt_frame {s : State} {Sb : BitVec 32} (hs : Sched s Sb) {n : Nat} (hn : n ≤ 256)
    {m : Mem} (hf : Frame [headR s n] s.mem m) :
    scheduleAt m (State.addr Sb) = scheduleAt s.mem (State.addr Sb) :=
  VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

theorem passes_ok (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32} (hs : Sched s Sb)
    (hS : fw s 76 = Sb) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (State.addr Sb)) d (words s) x) ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [headR s 76] s.mem s'.mem := by
  have step : ∀ (c : Nat) (_ : c < 3) (d' : Direction) {u : State}, u.gpr .r3 = s.gpr .r3 →
      u.rd = s.rd → u.wr = s.wr → Frame [headR s 76] s.mem u.mem →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (State.addr Sb)) c) d' (words u) x) → u'.gpr .r3 = u.gpr .r3 →
        u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → Frame [headR u 76] u.mem u'.mem → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u gu rdu wru fu Q hQ
    have hu : Room u := h.congr gu wru
    have hsu : Sched u Sb := hs.congr gu rdu
    refine WP.mono (pass_ok c hc d' hu hsu ((fw_of_frame h gu fu (by decide) (by decide)).trans hS))
      fun u' ⟨w, g, rd, wr, sp, f⟩ => hQ u' ?_ g rd wr sp f
    rw [scheduleAt_frame hs (by decide) fu] at w; exact w
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ rfl rfl rfl (Frame.refl _ _) fun u₁ w₁ g₁ rd₁ wr₁ sp₁ f₁ => ?_
    apply WP.seq
    refine step _ (by decide) _ g₁ rd₁ wr₁ f₁ fun u₂ w₂ g₂ rd₂ wr₂ sp₂ f₂ => ?_
    have g₂' : u₂.gpr .r3 = s.gpr .r3 := g₂.trans g₁
    have f₁₂ : Frame [headR s 76] s.mem u₂.mem := f₁.trans (by rw [← headR_congr g₁]; exact f₂)
    refine step _ (by decide) _ g₂' (rd₂.trans rd₁) (wr₂.trans wr₁) f₁₂
      fun u₃ w₃ g₃ rd₃ wr₃ sp₃ f₃ => ⟨fun x hx => ?_, g₃.trans g₂', rd₃.trans (rd₂.trans rd₁),
        wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁),
        f₁₂.trans (by rw [← headR_congr g₂']; exact f₃)⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.Arm.Bitsliced
