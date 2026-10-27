module

public import VerifiedGarbage.Impl.Idea.RISCV64
public import VerifiedGarbage.Spec.Idea.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.RISCV64.Invert
import VerifiedGarbage.Proof.Idea.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Idea.RISCV64.Invert
meta import VerifiedGarbage.Proof.Idea.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Impl.Idea.RISCV64
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# IDEA key expansion on RISC-V

`expandKey_verified`: `Impl.Idea.RISCV64.expandKey` meets the shared
contract. The key, as a 128-bit number, is loaded into `a2` (its high half)
and `a3` (`keyLoad_ok`); after `j` rotations by 25 bits (`rotate_ok`) bit `i`
of the pair is bit `i - 25 j` (modulo 128) of the key (`KInv`), which is
where `Impl.Idea.keyBit` puts the bits of subkeys `8j … 8j + 7`
(`expandKey_getLsbD`), and each is stored a byte at a time
(`expandSub_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64 VG.Impl.Idea VG.RISCV64.ByteLoad

/-! ## Bits -/

/-- Bit `8k + b` of eight bytes, the first most significant. -/
theorem append8_getLsbD (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) {k b : Nat} (hk : k < 8) (hb : b < 8) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7).getLsbD (8 * k + b) =
      ([b7, b6, b5, b4, b3, b2, b1, b0].getD k 0).getLsbD b := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals
    simp (disch := omega) only [BitVec.getLsbD_append, ite_eq_left, ite_eq_right, List.getD_cons_zero,
      List.getD_cons_succ]
    congr 1
    omega

theorem be64_getLsbD (m : Mem) (p : Addr) (off : Nat) {k b : Nat} (hk : k < 8) (hb : b < 8) :
    (be64 m p off).getLsbD (8 * k + b) = (m (p + BitVec.ofNat 64 (off + (7 - k)))).getLsbD b := by
  unfold be64
  rw [append8_getLsbD _ _ _ _ _ _ _ _ hk hb]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals rfl

/-- Bit `i` of the key at `p` as a 128-bit number. -/
theorem keyAt_getLsbD (m : Mem) (p : Addr) {i : Nat} (hi : i < 128) :
    (Spec.Idea.keyValue (Spec.Idea.keyAt m p)).getLsbD i =
      (m (p + BitVec.ofNat 64 (15 - i / 8))).getLsbD (i % 8) := by
  rw [keyValue_getLsbD _ hi, keyAt_getD _ _ (by omega)]

/-- The bit of the key that is at bit `i` of the pair after `j` rotations. -/
def src (j i : Nat) : Nat := (i + 128 - 25 * j % 128) % 128

/-! ## The invariant -/

/-- After `j` rotations and `n` subkeys, from `s₀`: the pair holds the key
rotated, and the first `n` subkeys are stored. -/
structure KInv (s₀ : State) (j n : Nat) (t : State) : Prop where
  le : n ≤ 52
  keep : Keep [.a2, .a3, .t0, .t1] s₀ t
  hi : ∀ i < 64, (t.gpr .a2).getLsbD i =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .a0))).getLsbD (src j (64 + i))
  lo : ∀ i < 64, (t.gpr .a3).getLsbD i =
    (Spec.Idea.keyValue (Spec.Idea.keyAt s₀.mem (s₀.gpr .a0))).getLsbD (src j i)
  frame : Frame [⟨s₀.gpr .a1, 104⟩] s₀.mem t.mem
  words : ∀ k < n, t.mem (s₀.gpr .a1 + BitVec.ofNat 64 (2 * k + 1)) ++
    t.mem (s₀.gpr .a1 + BitVec.ofNat 64 (2 * k)) =
      (Spec.Idea.expandKey (Spec.Idea.keyAt s₀.mem (s₀.gpr .a0))).getD k 0

/-- What `vg_idea_expand_key` needs of its state: the key (16 bytes at `a0`)
readable and the schedule (104 bytes at `a1`) writable. -/
structure KeyPre (s : State) : Prop where
  key : ⟨s.gpr .a0, 16⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .a1, 104⟩ ∈ s.wr

/-! ## The pieces -/

theorem keyLoad_ok (s : State) (hp : KeyPre s) :
    WP isa (.block (Impl.Words.RISCV64.loadBE64 .a2 .t0 .a0 0 ++
      Impl.Words.RISCV64.loadBE64 .a3 .t0 .a0 8)) s (KInv s 0 0) := by
  rw [WP.block_append_iff]
  have h0 : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 0) 8 :=
    ⟨_, hp.key, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (loadBE64_ok (by decide) (by decide) (by decide) (by decide) h0) fun s₁ h₁ => ?_
  have e₁ : s₁.gpr .a0 = s.gpr .a0 ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    rw [h₁]; exact ⟨by simp [State.write], rfl, rfl⟩
  have h8 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .a0 + BitVec.ofNat 64 8) 8 := by
    rw [e₁.1, e₁.2.1, e₁.2.2]
    exact ⟨_, hp.key, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (loadBE64_ok (by decide) (by decide) (by decide) (by decide) h8) fun s₂ h₂ => ?_
  subst h₂
  subst h₁
  have hk (i : Nat) (hi : i < 128) := keyAt_getLsbD s.mem (s.gpr .a0) hi
  refine ⟨by decide, ⟨fun r hr => ?_, rfl, rfl⟩, fun i hi => ?_, fun i hi => ?_, Frame.refl _ _,
    fun k hk => absurd hk (by omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.write, hr.1, hr.2.1, hr.2.2.1]
  · simp only [State.write, ite_eq_right (show Reg.a2 ≠ Reg.a3 by decide),
      ite_eq_right (show Reg.a2 ≠ Reg.t0 by decide), ite_true]
    have := be64_getLsbD s.mem (s.gpr .a0) 0 (k := i / 8) (b := i % 8) (by omega) (by omega)
    rw [show 8 * (i / 8) + i % 8 = i by omega] at this
    rw [this, show src 0 (64 + i) = 64 + i by simp only [src]; omega, hk _ (by omega),
      show (64 + i) % 8 = i % 8 by omega, show 15 - (64 + i) / 8 = 0 + (7 - i / 8) by omega]
  · simp only [State.write, reduceCtorEq, ↓reduceIte]
    have := be64_getLsbD s.mem (s.gpr .a0) 8 (k := i / 8) (b := i % 8) (by omega) (by omega)
    rw [show 8 * (i / 8) + i % 8 = i by omega] at this
    rw [this, show src 0 i = i by simp only [src]; omega, hk _ (by omega),
      show 15 - i / 8 = 8 + (7 - i / 8) by omega]

theorem rotate_ok (s₀ : State) (j n : Nat) (t : State) (hi : KInv s₀ j n t) :
    WP isa (.block rotate) t (KInv s₀ (j + 1) n) := by
  have h : WP isa (.block rotate) t fun u =>
      u.gpr .a2 = t.gpr .a2 <<< 25 ||| t.gpr .a3 >>> 39 ∧
      u.gpr .a3 = t.gpr .a3 <<< 25 ||| t.gpr .a2 >>> 39 ∧ u.mem = t.mem ∧
      Keep [.a2, .a3, .t0, .t1] t u := by
    refine WP.mono (WP.keep [.a2, .a3, .t0, .t1] (Q := fun u =>
      u.gpr .a2 = t.gpr .a2 <<< 25 ||| t.gpr .a3 >>> 39 ∧
      u.gpr .a3 = t.gpr .a3 <<< 25 ||| t.gpr .a2 >>> 39 ∧ u.mem = t.mem) ?_ (by decide) rfl)
      fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold rotate
    mrun
  refine WP.mono h fun u ⟨u2, u3, um, ue⟩ =>
    ⟨hi.le, (hi.keep.trans ue).mono (by decide), fun i hi' => ?_, fun i hi' => ?_,
      um ▸ hi.frame, fun k hk => um ▸ hi.words k hk⟩
  · rw [u2, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h25 : i < 25
    · simp only [h25, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or,
        show i < 64 from hi']
      rw [hi.lo _ (by omega)]
      congr 1; simp only [src]; omega
    · rw [BitVec.getLsbD_of_ge (t.gpr .a3) (39 + i) (by omega)]
      simp only [h25, decide_false, Bool.not_false, Bool.and_true, Bool.or_false,
        show i < 64 from hi', decide_true, Bool.true_and]
      rw [hi.hi _ (by omega)]
      congr 1; simp only [src]; omega
  · rw [u3, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h25 : i < 25
    · simp only [h25, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or,
        show i < 64 from hi']
      rw [hi.hi _ (by omega)]
      congr 1; simp only [src]; omega
    · rw [BitVec.getLsbD_of_ge (t.gpr .a2) (39 + i) (by omega)]
      simp only [h25, decide_false, Bool.not_false, Bool.and_true, Bool.or_false,
        show i < 64 from hi', decide_true, Bool.true_and]
      rw [hi.lo _ (by omega)]
      congr 1; simp only [src]; omega

/-- A 16-bit window, as `storeKey` stores it, read back little-endian. -/
theorem window_getLsbD (x : BitVec 64) {b : Nat} (hb : b < 16) :
    ((x >>> 8).setWidth 8 ++ x.setWidth 8).getLsbD b = x.getLsbD b := by
  rw [BitVec.getLsbD_append]
  by_cases h : b < 8
  · simp [h]
  · simp only [h, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show b - 8 < 8 by omega, decide_true, Bool.true_and]
    congr 1; omega

theorem expandSub_ok (s₀ : State) (hp : KeyPre s₀) (j i : Nat) (hi8 : i < 8) (hn : 8 * j + i < 52)
    (t : State) (hi : KInv s₀ j (8 * j + i) t) :
    WP isa (.block (expandSub j i)) t (KInv s₀ j (8 * j + i + 1)) := by
  have ha : t.gpr .a1 = s₀.gpr .a1 := hi.keep.gpr (by decide)
  have hw (o : Nat) (ho : o < 104) : InRegions t.wr (t.gpr .a1 + BitVec.ofNat 64 o) 1 := by
    rw [ha, hi.keep.2.2]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega) (by omega)⟩
  unfold expandSub
  rw [show ∀ (x : Instr) (l : List Instr), x :: l = [x] ++ l from fun _ _ => rfl,
    WP.block_append_iff]
  have hs : WP isa (.block [.shift .srl .d .t0 (half i) (16 * (3 - i % 4))]) t fun u =>
      u.gpr .t0 = t.gpr (half i) >>> (16 * (3 - i % 4)) ∧ u.mem = t.mem ∧ Keep [.t0] t u := by
    refine WP.mono (WP.keep (c := .block [.shift .srl .d .t0 (half i) (16 * (3 - i % 4))]) [.t0]
      (Q := fun u => u.gpr .t0 = t.gpr (half i) >>> (16 * (3 - i % 4)) ∧ u.mem = t.mem) ?_
      (by simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl) fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    mrun [show 16 * (3 - i % 4) < 64 by omega]
  refine WP.mono hs fun u ⟨u0, um, ue⟩ => ?_
  have ua : u.gpr .a1 = t.gpr .a1 := ue.gpr (by decide)
  refine WP.mono (storeKey_ok (r := .t0) (by decide) (8 * j + i) hn u
    (by rw [ua, ue.2.2]; exact hw _ (by omega)) (by rw [ua, ue.2.2]; exact hw _ (by omega)))
    fun v ⟨vm, ve⟩ => ?_
  rw [ua, ha, u0, um] at vm
  refine ⟨by omega, ((hi.keep.trans ue).trans ve).mono (by decide), fun b hb => ?_, fun b hb => ?_,
    ?_, fun k hk => ?_⟩
  · rw [ve.gpr (by decide), ue.gpr (by decide)]; exact hi.hi b hb
  · rw [ve.gpr (by decide), ue.gpr (by decide)]; exact hi.lo b hb
  · rw [vm]
    have hc (o : Nat) (ho : o < 104) : (⟨s₀.gpr .a1, 104⟩ : Region).Contains
        (s₀.gpr .a1 + BitVec.ofNat 64 o) 1 := Offset.contains_base _ (by omega) (by omega)
    exact (hi.frame.write (List.mem_singleton_self _) _ (hc _ (by omega))).write
      (List.mem_singleton_self _) _ (hc _ (by omega))
  · rw [vm, write1_off _ _ _ (by omega) (by omega), write1_off _ _ _ (by omega) (by omega),
      write1_off _ _ _ (by omega) (by omega), write1_off _ _ _ (by omega) (by omega)]
    by_cases he : k = 8 * j + i
    · subst he
      simp only [↓reduceIte, show ¬ (2 * (8 * j + i) = 2 * (8 * j + i) + 1) by omega]
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      rw [window_getLsbD _ hb, BitVec.getLsbD_ushiftRight, expandKey_getLsbD _ (by omega) hb]
      unfold half
      by_cases h4 : i < 4
      · rw [ite_eq_left h4, hi.hi _ (by omega), show i % 4 = i by omega]
        congr 1; simp only [src, keyBit, show (8 * j + i) / 8 = j by omega,
          show (8 * j + i) % 8 = i by omega]; omega
      · rw [ite_eq_right h4, hi.lo _ (by omega), show i % 4 = i - 4 by omega]
        congr 1; simp only [src, keyBit, show (8 * j + i) / 8 = j by omega,
          show (8 * j + i) % 8 = i by omega]; omega
    · simp only [show ¬ (2 * k + 1 = 2 * (8 * j + i) + 1) by omega,
        show ¬ (2 * k + 1 = 2 * (8 * j + i)) by omega, show ¬ (2 * k = 2 * (8 * j + i) + 1) by omega,
        show ¬ (2 * k = 2 * (8 * j + i)) by omega, ↓reduceIte]
      exact hi.words k (by omega)

/-- The subkeys `8j … 8j + c - 1`. -/
theorem expandSubs_ok (s₀ : State) (hp : KeyPre s₀) (j : Nat) :
    ∀ c ≤ 8, 8 * j + c ≤ 52 → ∀ t, KInv s₀ j (8 * j) t →
      WP isa (.block ((List.range c).flatMap (expandSub j))) t (KInv s₀ j (8 * j + c))
  | 0, _, _, t, hi => WP.block_nil hi
  | c + 1, hc, hj, t, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (expandSubs_ok s₀ hp j c (by omega) (by omega) t hi) fun u hu =>
      expandSub_ok s₀ hp j c (by omega) (by omega) u hu

theorem expandGroup_ok (s₀ : State) (hp : KeyPre s₀) (j : Nat) (hj : j ≤ 6) (t : State)
    (hi : KInv s₀ j (8 * j) t) :
    WP isa (.block (expandGroup j)) t (KInv s₀ j (min (8 * j + 8) 52)) := by
  unfold expandGroup
  by_cases h6 : j < 6
  · rw [ite_eq_left h6, show min (8 * j + 8) 52 = 8 * j + 8 by omega]
    exact expandSubs_ok s₀ hp j 8 (by decide) (by omega) t hi
  · rw [ite_eq_right h6, show min (8 * j + 8) 52 = 8 * j + 4 by omega]
    exact expandSubs_ok s₀ hp j 4 (by decide) (by omega) t hi

theorem groups_ok (s₀ : State) (hp : KeyPre s₀) :
    ∀ c ≤ 6, ∀ t, KInv s₀ 0 8 t →
      WP isa (.block ((List.range c).flatMap fun j => rotate ++ expandGroup (j + 1))) t
        (KInv s₀ c (min (8 * c + 8) 52))
  | 0, _, t, hi => WP.block_nil hi
  | c + 1, hc, t, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (groups_ok s₀ hp c (by omega) t hi) fun u hu => ?_
    rw [WP.block_append_iff]
    refine WP.mono (rotate_ok s₀ c _ u hu) fun v hv => ?_
    rw [show min (8 * c + 8) 52 = 8 * (c + 1) by omega] at hv
    exact expandGroup_ok s₀ hp (c + 1) (by omega) v hv

/-! ## The function -/

/-- `vg_idea_expand_key` on RISC-V. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 16⟩
    let out : Region := ⟨s.gpr .a1, 104⟩
    s.rd = [key] ∧ s.wr = [out] ∧ key.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .a1) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

theorem expandKey_eq : expandKey = .block ((Impl.Words.RISCV64.loadBE64 .a2 .t0 .a0 0 ++
    Impl.Words.RISCV64.loadBE64 .a3 .t0 .a0 8) ++ (expandGroup 0 ++
    (List.range 6).flatMap fun j => rotate ++ expandGroup (j + 1))) := by
  simp only [expandKey, List.append_assoc]

theorem expand_wp (s : State) (hs : expandContract.pre s) :
    WP isa expandKey s (expandContract.post s) := by
  obtain ⟨hrd, hwr, _⟩ := hs
  have hp : KeyPre s := ⟨by rw [hrd, hwr]; simp, by rw [hwr]; simp⟩
  rw [expandKey_eq, WP.block_append_iff]
  refine WP.mono (keyLoad_ok s hp) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (expandGroup_ok s hp 0 (by decide) s₁ h₁) fun s₂ h₂ => ?_
  refine WP.mono (groups_ok s hp 6 (by decide) s₂ h₂) fun s' hi => ?_
  show Spec.Idea.scheduleAt s'.mem (s.gpr .a1) = _
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn, scheduleAt_getD _ _ hn]
  exact hi.words n (by omega)

/-- The registers `expandKey` writes. -/
abbrev expandWrites : List Reg := [.a2, .a3, .t0, .t1]

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandContract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ :=
    WP.keep expandWrites (expand_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

theorem expand_ct : ConstantTime isa expandContract.pre expandContract.pub expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

def expandSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 104⟩]

theorem expandKey_verified : Verified RISCV64.target expandKey
    (Spec.Idea.expandKeyContract RISCV64.abi) :=
  Verified.of_correct expand_correct expand_ct (by
    sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost,
      RISCV64.abi, RISCV64.argRegs, expandContract] [expandSat] using expandSat)

end VG.Proof.Idea.RISCV64
