module

public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Step
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Bitsliced DES rounds and passes on x86 (32-bit)

As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Pass.lean`). `round_ok`: the
code of a round copies the round key at the key pointer (word `kpSlot` of
the working space) into words `kloSlot` and `khiSlot`, steps the pointer by
`δ d` (8 or −8) and does to the state words what `roundW` does with the
key's low 48 bits. `pass_ok`: a pass points the key pointer at its first key
in the schedule (whose address is word `schedSlot`), runs eight pairs of
rounds (counted down in word `cntSlot`) and exchanges the halves: what
`passW` does with the component schedule. `passes_ok`: the three passes do
what `tdeaW` does. They write only the first 82 words of the working space.
-/

-- separate module: builds in parallel with `Transpose`, which does not import it

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Wp VG.Bitslice VG.Impl.TripleDes.X86.Bitslice VG.Spec.TripleDes
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step steps roundW passW tdeaW steps_succ)
open VG.Proof.TripleDes (roundKey componentSchedule_readW)
open VG.X86.Straight (wordAddr addr_add_ofNat)

/-- The key pointer's step. -/
def δ (d : Direction) : BitVec 32 := if d = .encrypt then 8 else -8

/-- The schedule at `Sb` is readable, does not wrap around and is apart from
the working space. -/
structure Sched (s : State) (Sb : BitVec 32) : Prop where
  rd : (⟨Sb.setWidth 64, 384⟩ : Region) ∈ s.rd
  fit : Sb.toNat + 384 ≤ 2 ^ 32
  apart : (⟨Sb.setWidth 64, 384⟩ : Region).Disjoint (frameR s)

theorem Sched.congr {s s' : State} {Sb : BitVec 32} (h : Sched s Sb) (hb : s'.gpr .ebp = s.gpr .ebp)
    (hr : s'.rd = s.rd) : Sched s' Sb where
  rd := by rw [hr]; exact h.rd
  fit := h.fit
  apart := by rw [frameR, hb]; exact h.apart

/-- A round key's pointer: to word `i < 48` of the schedule. -/
def KeyAt (Sb P : BitVec 32) : Prop := ∃ i < 48, P = Sb + BitVec.ofNat 32 (8 * i)

/-- The key at `P`: the low 48 bits of its doubleword. -/
def keyW (m : Mem) (P : BitVec 32) : BitVec 48 := (m.readW (P.setWidth 64) 64).setWidth 48

theorem keyAt_addr {Sb P : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) (hk : KeyAt Sb P) :
    ∃ i < 48, P = Sb + BitVec.ofNat 32 (8 * i) ∧
      P.setWidth 64 = Sb.setWidth 64 + BitVec.ofNat 64 (8 * i) ∧ P.toNat + 8 ≤ 2 ^ 32 := by
  obtain ⟨i, hi, rfl⟩ := hk
  refine ⟨i, hi, rfl, addr_eq (by omega_using [hf, hi]), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [hi]),
    Nat.mod_eq_of_lt (by omega_using [hf, hi])]
  omega_using [hf, hi]

/-- A word of a round key, in the schedule. -/
theorem keyAt_contains {Sb P : BitVec 32} (hf : Sb.toNat + 384 ≤ 2 ^ 32) (hk : KeyAt Sb P) {off : Nat}
    (ho : off + 4 ≤ 8) : (⟨Sb.setWidth 64, 384⟩ : Region).Contains (addr P off) 4 := by
  obtain ⟨i, hi, rfl⟩ := hk
  rw [addr_add_ofNat, addr_eq (by omega_using [hf, hi, ho])]
  exact Offset.contains_base _ (by omega_using [hi, ho]) (by omega_using [hi, ho])

theorem keyAt_rd {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {off : Nat}
    (ho : off + 4 ≤ 8) : InRegions (s.rd ++ s.wr) (addr P off) 4 :=
  ⟨_, List.mem_append_left _ hs.rd, keyAt_contains hs.fit hk ho⟩

/-- A round key is not in the working space. -/
theorem keyW_frame {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {n : Nat}
    (hn : n ≤ wsWords) {m : Mem} (hf : Frame [headR s n] s.mem m) : keyW m P = keyW s.mem P := by
  obtain ⟨i, hi, -, ha, -⟩ := keyAt_addr hs.fit hk
  rw [keyW, keyW, ha]
  refine congrArg (BitVec.setWidth 48) (hf.readW (r := ⟨Sb.setWidth 64, 384⟩)
    (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (fun r hr => ?_) (by decide))
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

/-- A word of a round key, after writes to the working space. -/
theorem keyWord_frame {s : State} {Sb P : BitVec 32} (hs : Sched s Sb) (hk : KeyAt Sb P) {n : Nat}
    (hn : n ≤ wsWords) {m : Mem} (hf : Frame [headR s n] s.mem m) {off : Nat} (ho : off + 4 ≤ 8) :
    m.readW (addr P off) 32 = s.mem.readW (addr P off) 32 := by
  refine hf.readW (r := ⟨Sb.setWidth 64, 384⟩) (keyAt_contains hs.fit hk ho) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

/-- The two words of a key. -/
theorem keyWords_read (m : Mem) {P : BitVec 32} (hP : P.toNat + 8 ≤ 2 ^ 32) :
    KeyWords (m.readW (addr P 0) 32) (m.readW (addr P 4) 32) (keyW m P) := by
  rw [addr_eq (by omega_using [hP]), addr_eq (by omega_using [hP]), BitVec.add_zero, Mem.readW_lo32 rfl,
    Mem.readW_hi32 rfl, keyW]
  constructor
  · intro b hb
    simp only [BitVec.getLsbD_setWidth, hb, decide_true, Bool.true_and,
      show b < 48 by omega_using [hb]]
  · intro b hb
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', show b < 32 by omega_using [hb],
      decide_true, Bool.true_and, show 32 + b < 48 by omega_using [hb]]

/-! ## A round -/

/-- What a block that stores only to the working space's first `n` words keeps. -/
structure Kept (n : Nat) (s s' : State) : Prop where
  ebp : s'.gpr .ebp = s.gpr .ebp
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [headR s n] s.mem s'.mem

theorem Kept.refl (n : Nat) (s : State) : Kept n s s := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Kept.trans {n : Nat} {s₁ s₂ s₃ : State} (h₁ : Kept n s₁ s₂) (h₂ : Kept n s₂ s₃) : Kept n s₁ s₃ :=
  ⟨h₂.ebp.trans h₁.ebp, h₂.esp.trans h₁.esp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.frame.trans (by rw [← headR_congr h₁.ebp]; exact h₂.frame)⟩

theorem Kept.mono {n n' : Nat} {s s' : State} (h : Kept n s s') (hn : n ≤ n') : Kept n' s s' :=
  ⟨h.ebp, h.esp, h.rd, h.wr, headR_mono hn h.frame⟩

theorem Kept.room {n : Nat} {s s' : State} (h : Kept n s s') (hr : Room s) : Room s' :=
  hr.congr h.ebp h.wr

theorem Kept.sched {n : Nat} {s s' : State} {Sb : BitVec 32} (h : Kept n s s') (hs : Sched s Sb) :
    Sched s' Sb := hs.congr h.ebp h.rd

theorem Kept.fw {n : Nat} {s s' : State} (h : Kept n s s') (hr : Room s) {k : Nat} (hn : n ≤ k)
    (hk : k < wsWords) : fw s' k = fw s k := fw_of_frame hr h.ebp h.frame hn hk

theorem keyLoad_ok (d : Direction) {s : State} (h : Room s) {Sb P : BitVec 32} (hs : Sched s Sb)
    (hk : KeyAt Sb P) (hP : fw s kpSlot = P) :
    WP isa (.block (keyLoad d)) s fun s' =>
      KeyWords (fw s' kloSlot) (fw s' khiSlot) (keyW s.mem P) ∧ fw s' kpSlot = P + δ d ∧
      (∀ k, k < kloSlot → fw s' k = fw s k) ∧ Kept 81 s s' := by
  obtain ⟨-, -, -, -, hfit⟩ := keyAt_addr hs.fit hk
  unfold keyLoad
  refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h (by decide)) fun s₁ u₁ => ?_
  have p₁ : s₁.gpr .eax = P := u₁.gpr.trans hP
  refine wp_ldm (B := P) p₁ (by rw [u₁.rd, u₁.wr]; exact keyAt_rd hs hk (by decide)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebp = s.gpr .ebp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stm (B := s.gpr .ebp) b₂ (by rw [u₂.wr, u₁.wr]; exact slot_in h (by decide)) fun s₃ u₃ => ?_
  have m₃ : s₃.mem = s.mem.writeW (wordAddr (s.gpr .ebp) kloSlot) (s.mem.readW (addr P 0) 32) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.mem]
  have k₃ : Kept 81 s s₃ := ⟨by rw [u₃.gpr]; exact b₂,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], by rw [m₃]; exact stFw_frame h (k := kloSlot) (by decide) (by decide) _⟩
  have h₃ : Room s₃ := k₃.room h
  refine wp_ldm (B := P) (by rw [u₃.gpr, u₂.other _ (by decide)]; exact p₁)
    (by rw [k₃.rd, k₃.wr]; exact keyAt_rd hs hk (by decide)) fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .ebp = s₃.gpr .ebp := u₄.other _ (by decide)
  refine wp_stm (B := s₃.gpr .ebp) b₄ (by rw [u₄.wr]; exact slot_in h₃ (by decide)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₃.mem.writeW (wordAddr (s₃.gpr .ebp) khiSlot) (s.mem.readW (addr P 4) 32) := by
    rw [u₅.mem, u₄.mem, u₄.gpr, keyWord_frame hs hk (by decide) k₃.frame (by decide)]
  have k₅ : Kept 81 s₃ s₅ := ⟨by rw [u₅.gpr]; exact b₄, by rw [u₅.gpr, u₄.other _ (by decide)],
    by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr],
    by rw [m₅]; exact stFw_frame h₃ (k := khiSlot) (by decide) (by decide) _⟩
  have h₅ : Room s₅ := k₅.room h₃
  have a₅ : s₅.gpr .eax = P := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide)]; exact p₁
  -- The pointer stepped and stored: what both directions end with.
  have fin : ∀ s₆ : State, s₆.gpr .eax = P + δ d → (∀ r, r ≠ .eax → s₆.gpr r = s₅.gpr r) → s₆.mem = s₅.mem →
      s₆.rd = s₅.rd → s₆.wr = s₅.wr →
      WP isa (.block [.store (ws kpSlot) .eax]) s₆ fun s' =>
        KeyWords (fw s' kloSlot) (fw s' khiSlot) (keyW s.mem P) ∧ fw s' kpSlot = P + δ d ∧
        (∀ k, k < kloSlot → fw s' k = fw s k) ∧ Kept 81 s s' := by
    intro s₆ a₆ g₆ m₆ rd₆ wr₆
    have b₆ : s₆.gpr .ebp = s₅.gpr .ebp := g₆ _ (by decide)
    refine wp_stm (B := s₅.gpr .ebp) b₆ (by rw [wr₆]; exact slot_in h₅ (by decide)) fun s₇ u₇ =>
      WP.block_nil ?_
    have m₇ : s₇.mem = s₅.mem.writeW (wordAddr (s₅.gpr .ebp) kpSlot) (P + δ d) := by
      rw [u₇.mem, m₆, a₆]
    have k₇ : Kept 81 s₅ s₇ := ⟨by rw [u₇.gpr]; exact b₆, by rw [u₇.gpr, g₆ _ (by decide)],
      by rw [u₇.rd, rd₆], by rw [u₇.wr, wr₆],
      by rw [m₇]; exact stFw_frame h₅ (k := kpSlot) (by decide) (by decide) _⟩
    have f : ∀ j, j < wsWords → fw s₇ j =
        if j = kpSlot then P + δ d else if j = khiSlot then s.mem.readW (addr P 4) 32
        else if j = kloSlot then s.mem.readW (addr P 0) 32 else fw s j := by
      intro j hj
      rw [fw_write h₅ m₇ k₇.ebp (by decide) hj]
      by_cases e80 : j = kpSlot
      · rw [ite_eq_left e80, ite_eq_left e80]
      rw [ite_eq_right e80, ite_eq_right e80, fw_write h₃ m₅ k₅.ebp (by decide) hj]
      by_cases e79 : j = khiSlot
      · rw [ite_eq_left e79, ite_eq_left e79]
      rw [ite_eq_right e79, ite_eq_right e79, fw_write h m₃ k₃.ebp (by decide) hj]
    refine ⟨?_, ?_, fun k hk => ?_, k₃.trans (k₅.trans k₇)⟩
    · rw [f kloSlot (by decide), f khiSlot (by decide)]
      exact keyWords_read s.mem hfit
    · rw [f kpSlot (by decide)]; rfl
    · unfold kloSlot at hk
      rw [f k (by unfold wsWords; omega_using [hk]), ite_eq_right (by unfold kpSlot; omega_using [hk]),
        ite_eq_right (by unfold khiSlot; omega_using [hk]), ite_eq_right (by unfold kloSlot; omega_using [hk])]
  cases d
  · refine wp_addi fun s₆ u₆ => fin s₆ ?_ (fun r hr => u₆.other r hr) u₆.mem u₆.rd u₆.wr
    rw [u₆.gpr, a₅]; rfl
  · refine wp_subi fun s₆ u₆ _ _ => fin s₆ ?_ (fun r hr => u₆.other r hr) u₆.mem u₆.rd u₆.wr
    rw [u₆.gpr, a₅]; exact BitVec.sub_eq_add_neg _ _

def stepsCode (ρ : Role) (n : Nat) : List Instr := (List.range n).flatMap (sboxStep ρ)

theorem stepsCode_succ (ρ : Role) (n : Nat) :
    stepsCode ρ (n + 1) = stepsCode ρ n ++ sboxStep ρ n := by
  simp only [stepsCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem stepsCode_ok (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {s : State} (h : Room s)
    (hkey : KeyWords (fw s kloSlot) (fw s khiSlot) k) :
    WP isa (.block (stepsCode ρ n)) s fun s' =>
      (∀ x < 64, words s' x = steps ρ k n (words s) x) ∧ Kept (spills + 64) s s' := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, Kept.refl _ _⟩
  | succ n ih =>
    rw [stepsCode_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s₁ ⟨w₁, k₁⟩ => ?_
    have h₁ : Room s₁ := k₁.room h
    have key₁ : KeyWords (fw s₁ kloSlot) (fw s₁ khiSlot) k := by
      rw [k₁.fw h (by decide) (by decide), k₁.fw h (by decide) (by decide)]
      exact hkey
    refine WP.mono (sboxStep_ok ρ (j := n) (by omega_using [hn]) h₁ k key₁)
      fun s₂ ⟨w₂, g₂, sp₂, rd₂, wr₂, f₂⟩ => ⟨fun x hx => ?_, k₁.trans ⟨g₂, sp₂, rd₂, wr₂, f₂⟩⟩
    rw [w₂ x hx, steps_succ]
    exact VG.Proof.TripleDes.Bitslice.step_congr ρ k (by omega_using [hn]) w₁ (w₁ x hx)

theorem round_eq (d : Direction) (ρ : Role) : round d ρ = keyLoad d ++ stepsCode ρ 8 := rfl

theorem round_ok (d : Direction) (ρ : Role) {s : State} (h : Room s) {Sb P : BitVec 32}
    (hs : Sched s Sb) (hk : KeyAt Sb P) (hP : fw s kpSlot = P) :
    WP isa (.block (round d ρ)) s fun s' =>
      (∀ x < 64, words s' x = roundW ρ (keyW s.mem P) (words s) x) ∧ fw s' kpSlot = P + δ d ∧
      Kept 81 s s' := by
  rw [round_eq, WP.block_append_iff]
  refine WP.mono (keyLoad_ok d h hs hk hP) fun s₁ ⟨key₁, p₁, w₁, k₁⟩ => ?_
  have h₁ : Room s₁ := k₁.room h
  refine WP.mono (stepsCode_ok ρ (keyW s.mem P) (Nat.le_refl 8) h₁ key₁) fun s₂ ⟨w₂, k₂⟩ =>
    ⟨fun x hx => ?_, ?_, k₁.trans (k₂.mono (by decide))⟩
  · rw [w₂ x hx]
    exact VG.Proof.TripleDes.Bitslice.steps_congr ρ _ (Nat.le_refl 8)
      (fun y hy => w₁ _ (by unfold spills kloSlot; omega_using [hy])) x hx
  · rw [k₂.fw h₁ (by decide) (by decide), p₁]

/-! ## Pairs of rounds -/

/-- The count of pairs left, one less. -/
def countDown : List Instr :=
  [.mov .eax (.mem (ws cntSlot)), .alu .sub .eax (.imm 1), .store (ws cntSlot) .eax]

theorem roundPair_eq (d : Direction) : roundPair d = round d .ba ++ (round d .ab ++ countDown) := by
  simp only [roundPair, countDown, List.append_assoc]

theorem countDown_ok {s : State} (h : Room s) :
    WP isa (.block countDown) s fun s' =>
      fw s' cntSlot = fw s cntSlot - 1 ∧ s'.zf = some (fw s cntSlot - 1 == 0) ∧
      (∀ j < wsWords, j ≠ cntSlot → fw s' j = fw s j) ∧ Kept 82 s s' := by
  unfold countDown
  refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h (by decide)) fun s₁ u₁ => ?_
  refine wp_subi fun s₂ u₂ _ z₂ => ?_
  have b₂ : s₂.gpr .ebp = s.gpr .ebp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stm (B := s.gpr .ebp) b₂ (by rw [u₂.wr, u₁.wr]; exact slot_in h (by decide)) fun s₃ u₃ =>
    WP.block_nil ?_
  have v : s₂.gpr .eax = fw s cntSlot - 1 := by rw [u₂.gpr, u₁.gpr]; rfl
  have m₃ : s₃.mem = s.mem.writeW (wordAddr (s.gpr .ebp) cntSlot) (fw s cntSlot - 1) := by
    rw [u₃.mem, u₂.mem, u₁.mem, v]
  have b₃ : s₃.gpr .ebp = s.gpr .ebp := by rw [u₃.gpr]; exact b₂
  refine ⟨?_, ?_, fun j hj hne => ?_, b₃, by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
    by rw [m₃]; exact stFw_frame h (k := cntSlot) (by decide) (by decide) _⟩
  · rw [fw_write h m₃ b₃ (by decide) (by decide), ite_eq_left rfl]
  · rw [u₃.zf, z₂, u₁.gpr]; rfl
  · rw [fw_write h m₃ b₃ (by decide) hj, ite_eq_right hne]

theorem roundPair_ok (d : Direction) {s : State} (h : Room s) {Sb P : BitVec 32} (hs : Sched s Sb)
    (hk₁ : KeyAt Sb P) (hk₂ : KeyAt Sb (P + δ d)) (hP : fw s kpSlot = P) :
    WP isa (.block (roundPair d)) s fun s' =>
      (∀ x < 64, words s' x = roundW .ab (keyW s.mem (P + δ d))
        (roundW .ba (keyW s.mem P) (words s)) x) ∧
      fw s' kpSlot = P + δ d + δ d ∧ fw s' cntSlot = fw s cntSlot - 1 ∧
      s'.zf = some (fw s cntSlot - 1 == 0) ∧ Kept 82 s s' := by
  rw [roundPair_eq, WP.block_append_iff]
  refine WP.mono (round_ok d .ba h hs hk₁ hP) fun s₁ ⟨w₁, p₁, k₁⟩ => ?_
  have h₁ : Room s₁ := k₁.room h
  rw [WP.block_append_iff]
  refine WP.mono (round_ok d .ab h₁ (k₁.sched hs) hk₂ p₁) fun s₂ ⟨w₂, p₂, k₂⟩ => ?_
  have k₁₂ : Kept 81 s s₂ := k₁.trans k₂
  have h₂ : Room s₂ := k₁₂.room h
  refine WP.mono (countDown_ok h₂) fun s₃ ⟨c₃, z₃, o₃, k₃⟩ => ?_
  have c₂ : fw s₂ cntSlot = fw s cntSlot := k₁₂.fw h (by decide) (by decide)
  refine ⟨fun x hx => ?_, ?_, by rw [c₃, c₂], by rw [z₃, c₂], (k₁₂.mono (by decide)).trans k₃⟩
  · have : words s₃ x = words s₂ x := by
      rw [words, o₃ _ (by unfold spills wsWords; omega_using [hx]) (by unfold spills cntSlot; omega_using [hx])]
      rfl
    rw [this, w₂ x hx, keyW_frame hs hk₂ (by decide) k₁.frame]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _ w₁ x hx
  · rw [o₃ _ (by decide) (by decide), p₂]

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
      roundKey (componentSchedule (scheduleAt m (Sb.setWidth 64)) c) d r := by
  have hi := ix_lt d hr
  unfold roundKey
  rw [show (if d = .encrypt then r else 15 - r) = ix d r from rfl,
    componentSchedule_readW m _ _ _ hc hi, keyOf, keyW, passP, BitVec.add_assoc, kaddr c hc d r hr]
  exact congrArg (fun a => (m.readW a 64).setWidth 48) (addr_eq (by omega_using [hf, hc, hi]))

/-- What the loop of pairs keeps after `m` pairs from `s₀`. -/
structure PairInv (s₀ : State) (Sb : BitVec 32) (c : Nat) (d : Direction) (m : Nat) (s : State) :
    Prop where
  le : m ≤ 8
  ptr : fw s kpSlot = passP Sb c d + BitVec.ofNat 32 (2 * m) * δ d
  cnt : fw s cntSlot = BitVec.ofNat 32 (8 - m)
  wds : ∀ x < 64, words s x =
    VG.Proof.TripleDes.Bitslice.pairs (keyOf s₀.mem (passP Sb c d) (δ d)) m (words s₀) x
  kept : Kept 82 s₀ s

theorem pair_step {s₀ : State} (h₀ : Room s₀) {Sb : BitVec 32} (hs₀ : Sched s₀ Sb) {c : Nat}
    (hc : c < 3) {d : Direction} {m : Nat} (hm : m < 8) {s : State} (I : PairInv s₀ Sb c d m s) :
    WP isa (.block (roundPair d)) s fun s' =>
      PairInv s₀ Sb c d (m + 1) s' ∧ s'.zf = some (decide (m + 1 = 8)) := by
  have h : Room s := I.kept.room h₀
  have hs : Sched s Sb := I.kept.sched hs₀
  have hk₁ := passKeyAt Sb hc d (r := 2 * m) (by omega_using [hm])
  have hk₂ := passKeyAt Sb hc d (r := 2 * m + 1) (by omega_using [hm])
  rw [← kptr_succ] at hk₂
  refine WP.mono (roundPair_ok d h hs hk₁ hk₂ I.ptr) fun s' ⟨w, p80, p81, pz, k⟩ => ?_
  have rk : ∀ r < 16, keyW s.mem (passP Sb c d + BitVec.ofNat 32 r * δ d) =
      keyW s₀.mem (passP Sb c d + BitVec.ofNat 32 r * δ d) := fun r hr =>
    keyW_frame hs₀ (passKeyAt Sb hc d hr) (by decide) I.kept.frame
  have cnt : fw s cntSlot - 1 = BitVec.ofNat 32 (8 - (m + 1)) := by
    rw [I.cnt]
    exact (by decide : ∀ m < 8, BitVec.ofNat 32 (8 - m) - 1 = BitVec.ofNat 32 (8 - (m + 1))) m hm
  refine ⟨⟨by omega_using [hm], ?_, by rw [p81, cnt], fun x hx => ?_, I.kept.trans k⟩, ?_⟩
  · rw [p80, kptr_succ, kptr_succ]; congr 3
  · have e : passP Sb c d + BitVec.ofNat 32 (2 * m) * δ d + δ d =
        passP Sb c d + BitVec.ofNat 32 (2 * m + 1) * δ d := kptr_succ _ _ _
    rw [w x hx, e, rk _ (by omega_using [hm]), rk _ (by omega_using [hm])]
    simp only [VG.Proof.TripleDes.Bitslice.pairs]
    exact VG.Proof.TripleDes.Bitslice.roundW_congr .ab _
      (VG.Proof.TripleDes.Bitslice.roundW_congr .ba _ I.wds) x hx
  · rw [pz, cnt]
    exact congrArg some
      ((by decide : ∀ m < 8, (BitVec.ofNat 32 (8 - (m + 1)) == 0) = decide (m + 1 = 8)) m hm)

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

theorem pairLoop_ok {s₀ : State} (h₀ : Room s₀) {Sb : BitVec 32} (hs₀ : Sched s₀ Sb) {c : Nat}
    (hc : c < 3) (d : Direction) {s : State} (I : PairInv s₀ Sb c d 0 s) :
    WP isa (.loop (.block (roundPair d)) .ne) s (PairInv s₀ Sb c d 8) := by
  refine WP.loop (M := isa) (fun n v => ∃ m, m < 8 ∧ n = 8 - m ∧ PairInv s₀ Sb c d m v) ?_ 8 s
    ⟨0, by decide, rfl, I⟩
  intro n v ⟨m, hm, hn, J⟩
  refine WP.mono (pair_step h₀ hs₀ hc hm J) fun v' ⟨J', z⟩ => ?_
  rw [eval_ne, z]
  by_cases e : m + 1 = 8
  · left; exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp [e], 8 - (m + 1), by omega_using [hm, hn], m + 1, by omega_using [hm, e], rfl, J'⟩

theorem passStart_ok (c : Nat) (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32}
    (hS : fw s schedSlot = Sb) :
    WP isa (.block (passStart c d)) s (PairInv s Sb c d 0) := by
  unfold passStart
  refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h (by decide)) fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebp = s.gpr .ebp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_stm (B := s.gpr .ebp) b₂ (by rw [u₂.wr, u₁.wr]; exact slot_in h (by decide)) fun s₃ u₃ => ?_
  have p : s₂.gpr .eax = passP Sb c d := by rw [u₂.gpr, u₁.gpr, passP, ← hS]; rfl
  have m₃ : s₃.mem = s.mem.writeW (wordAddr (s.gpr .ebp) kpSlot) (passP Sb c d) := by
    rw [u₃.mem, u₂.mem, u₁.mem, p]
  have k₃ : Kept 82 s s₃ := ⟨by rw [u₃.gpr]; exact b₂,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], by rw [m₃]; exact stFw_frame h (k := kpSlot) (by decide) (by decide) _⟩
  have h₃ : Room s₃ := k₃.room h
  refine wp_movi fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .ebp = s₃.gpr .ebp := u₄.other _ (by decide)
  refine wp_stm (B := s₃.gpr .ebp) b₄ (by rw [u₄.wr]; exact slot_in h₃ (by decide)) fun s₅ u₅ =>
    WP.block_nil ?_
  have m₅ : s₅.mem = s₃.mem.writeW (wordAddr (s₃.gpr .ebp) cntSlot) (8 : BitVec 32) := by
    rw [u₅.mem, u₄.mem, u₄.gpr]
  have k₅ : Kept 82 s₃ s₅ := ⟨by rw [u₅.gpr]; exact b₄, by rw [u₅.gpr, u₄.other _ (by decide)],
    by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr],
    by rw [m₅]; exact stFw_frame h₃ (k := cntSlot) (by decide) (by decide) _⟩
  have z : BitVec.ofNat 32 (2 * 0) * δ d = 0#32 := by cases d <;> decide
  have f : ∀ j, j < wsWords → fw s₅ j =
      if j = cntSlot then 8 else if j = kpSlot then passP Sb c d else fw s j := by
    intro j hj
    rw [fw_write h₃ m₅ k₅.ebp (by decide) hj]
    by_cases e : j = cntSlot
    · rw [ite_eq_left e, ite_eq_left e]
    rw [ite_eq_right e, ite_eq_right e, fw_write h m₃ k₃.ebp (by decide) hj]
  refine ⟨by decide, ?_, ?_, fun x hx => ?_, k₃.trans k₅⟩
  · rw [f kpSlot (by decide), z, BitVec.add_zero]; rfl
  · rw [f cntSlot (by decide)]; rfl
  · rw [words, f _ (by unfold spills wsWords; omega_using [hx]),
      ite_eq_right (by unfold spills cntSlot; omega_using [hx]),
      ite_eq_right (by unfold spills kpSlot; omega_using [hx])]
    rfl

theorem pass_ok (c : Nat) (hc : c < 3) (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32}
    (hs : Sched s Sb) (hS : fw s schedSlot = Sb) :
    WP isa (pass c d) s fun s' =>
      (∀ x < 64, words s' x =
        passW (componentSchedule (scheduleAt s.mem (Sb.setWidth 64)) c) d (words s) x) ∧
      Kept 82 s s' := by
  unfold pass
  apply WP.seq
  refine WP.mono (passStart_ok c d h hS) fun s₁ I0 => ?_
  apply WP.seq
  refine WP.mono (pairLoop_ok h hs hc d I0) fun v J => ?_
  have hv : Room v := J.kept.room h
  obtain ⟨v', run, w, g, sp, rd, wr, f⟩ := swapHalves_ok hv
  refine WP.of_runBlock ⟨v', run, fun x hx => ?_, J.kept.trans ⟨g, sp, rd, wr, headR_mono (by decide) f⟩⟩
  rw [w x hx, VG.Proof.TripleDes.Bitslice.passW]
  refine VG.Proof.TripleDes.Bitslice.swapW_congr (fun y hy => ?_) x hx
  rw [J.wds y hy, VG.Proof.TripleDes.Bitslice.pairs_keys_congr 8
    (fun r hr => keyOf_pass _ hs.fit hc d hr)]

/-! ## The three passes -/

theorem scheduleAt_frame {s : State} {Sb : BitVec 32} (hs : Sched s Sb) {n : Nat} (hn : n ≤ wsWords)
    {m : Mem} (hf : Frame [headR s n] s.mem m) :
    scheduleAt m (Sb.setWidth 64) = scheduleAt s.mem (Sb.setWidth 64) :=
  VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.apart.sub_right (Region.sub_prefix (by omega_using [hn]))

theorem passes_ok (d : Direction) {s : State} (h : Room s) {Sb : BitVec 32} (hs : Sched s Sb)
    (hS : fw s schedSlot = Sb) :
    WP isa (passes d) s fun s' =>
      (∀ x < 64, words s' x = tdeaW (scheduleAt s.mem (Sb.setWidth 64)) d (words s) x) ∧
      Kept 82 s s' := by
  have step : ∀ (c : Nat) (_ : c < 3) (d' : Direction) {u : State}, Kept 82 s u →
      ∀ {Q : State → Prop}, (∀ u', (∀ x < 64, words u' x = passW (componentSchedule
        (scheduleAt s.mem (Sb.setWidth 64)) c) d' (words u) x) → Kept 82 u u' → Q u') →
      WP isa (pass c d') u Q := by
    intro c hc d' u ku Q hQ
    have hu : Room u := ku.room h
    have hsu : Sched u Sb := ku.sched hs
    refine WP.mono (pass_ok c hc d' hu hsu ((ku.fw h (by decide) (by decide)).trans hS))
      fun u' ⟨w, k⟩ => hQ u' ?_ k
    rw [scheduleAt_frame hs (by decide) ku.frame] at w; exact w
  cases d
  all_goals
    unfold passes
    apply WP.seq
    refine step _ (by decide) _ (Kept.refl _ _) fun u₁ w₁ k₁ => ?_
    apply WP.seq
    refine step _ (by decide) _ k₁ fun u₂ w₂ k₂ => ?_
    refine step _ (by decide) _ (k₁.trans k₂) fun u₃ w₃ k₃ => ⟨fun x hx => ?_, (k₁.trans k₂).trans k₃⟩
    rw [w₃ x hx]
    simp only [tdeaW]
    exact VG.Proof.TripleDes.Bitslice.passW_congr _ _
      (fun y hy => by rw [w₂ y hy]; exact VG.Proof.TripleDes.Bitslice.passW_congr _ _ w₁ y hy) x hx

end VG.Proof.TripleDes.X86.Bitsliced
