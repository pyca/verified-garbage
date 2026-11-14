module

public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Seed.PPC64LE.Lanes
import VerifiedGarbage.Proof.Seed.PPC64LE.Round
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Seed.PPC64LE.KeyRound
public import VerifiedGarbage.Proof.Seed.KeySchedule
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Seed.PPC64LE.Batch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Seed
import VerifiedGarbage.Proof.Seed.PPC64LE.Setup

/-! ### `Seed.PPC64LE.KeyBody`, which only this module used -/

section

/-! ### `Seed.PPC64LE.KeyStore`, which only this module used -/

section

/-!
# Copying `G`'s outputs on PPC64LE

`keyStore_ok`: `keyStore k` copies the sixteen lanes of `G`'s words to the
schedule's words from `k`; `keyMove_ok`: `keyMove` copies the second sixteen
inputs of `G` to its words.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .r4 + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) (hk : k ≤ 16) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        [ldW .r9 (tSlot 0) w, .store .w .r9 .r4 (4 * (k + w))]) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .r4 + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hf⟩ := keyStore_ok k hk h hw hsep n (by omega_using [hn])
    have r8 : t.gpr .r8 = s.gpr .r8 := hg _ (by decide)
    have r4 : t.gpr .r4 = s.gpr .r4 := hg _ (by decide)
    have room : Room t := room_congr h r8 hwr
    have hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, r8]
      refine hf.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr .r8, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega_using [hn])
    let t1 := t.write .r9 ((lv t (tSlot 0) n).setWidth 64)
    have e1 : exec (ldW .r9 (tSlot 0) n) t = some t1 := exec_ldW_lane room mem_tA (by omega_using [hn]) .r9
    have hw1 : InRegions t1.wr (t1.gpr .r4 + BitVec.ofNat 64 (4 * (k + n))) 4 := by
      simp only [t1, wr_write, gpr_write_of_ne _ _ (show ¬ Reg.r4 = .r9 by decide), hwr, r4]
      exact hw n (by omega_using [hn])
    let t2 := setMem t1 (t.mem.writeW (s.gpr .r4 + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n))
    have e2 : exec (.store .w .r9 .r4 (4 * (k + n))) t1 = some t2 := by
      rw [exec_store_w (show Reg.r4 ≠ .r0 by decide) (by omega_using [hk, hn]) hw1]
      simp only [t1, t2, gpr_write_self, gpr_write_of_ne _ _ (show ¬ Reg.r4 = .r9 by decide), r4,
        mem_write, setWidth_setWidth_32, hlane]
      rfl
    refine ⟨t2, ?_, fun w hw' => ?_, fun r hr => ?_, hrd, hwr, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans ht (by rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some,
        runBlock_nil])
    · simp only [t2, mem_setMem]
      by_cases hwn : w = n
      · subst hwn; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hwn]) (by omega_using [hk, hn, hw']) (by omega_using [hk, hn])) (by decide)]
        exact hv w (by omega_using [hw', hwn])
    · simp only [t2, gpr_setMem, t1, gpr_write_of_ne _ _ hr]; exact hg r hr
    · simp only [t2, mem_setMem]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hk]))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [ldW .r9 uSlot w, stW (tSlot 0) w .r9])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_ldW_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_stW_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, gpr_write_self,
        setWidth_setWidth_32, mem_setMem, mem_write,
        laneA_write _ _ (show ¬ Reg.r8 = .r9 by decide)]
    · simp only [gpr_write_of_ne _ _ h1, gpr_setMem]

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.KeyRounds`, which only this module used -/

section

/-!
# The sixteen rounds of the key schedule on PPC64LE

`keyRounds_ok`: after `n` rounds, `r6` and `r7` hold the key words of
round `n + 1` (`keyWords`), and the lanes of `G`'s first `2 * n` inputs hold
them (`gInput`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

theorem hi_append (a b : BitVec 32) : ((a ++ b) >>> 32).setWidth 32 = a := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [show ¬ (32 + i < 32) by omega_using [], hi]

theorem split64 (t : BitVec 64) : t.extractLsb' 32 32 ++ t.setWidth 32 = t := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split <;> simp_all <;> (congr 1; omega_arith)

theorem ror56 (t : BitVec 64) : t.rotateRight 56 = t.rotateLeft 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]

theorem kcs_eq : ∀ j < 16, kcs.getD j 0 = Spec.Seed.kc.getD j 0 := by decide

/-- The key words `k` as `r6` and `r7` hold them. -/
def kx (k : Quad) : BitVec 64 := k.1 ++ k.2.1
def ky (k : Quad) : BitVec 64 := k.2.2.1 ++ k.2.2.2

/-- After `n` rounds of the key schedule. -/
structure KeyInv (key : Spec.Seed.Block) (s₀ : State) (n : Nat) (s : State) : Prop where
  r6 : s.gpr .r6 = kx (keyWords key n)
  r7 : s.gpr .r7 = ky (keyWords key n)
  lanes : ∀ i < 2 * n, lv s (gSlot i) (i % 16) = gInput key i
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r6 → r ≠ .r7 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [arraysR s₀] s₀.mem s.mem

theorem keyRounds_ok (key : Spec.Seed.Block) {s₀ : State} (h : Room s₀)
    (h10 : s₀.gpr .r6 = kx (keyWords key 0)) (h11 : s₀.gpr .r7 = ky (keyWords key 0)) :
    ∀ n ≤ 16, ∃ s, runBlock isa ((List.range n).flatMap keyRound) s₀ = some s ∧ KeyInv key s₀ n s
  | 0, _ => ⟨s₀, runBlock_nil, h10, h11, fun i hi => by omega, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s, hs, inv⟩ := keyRounds_ok key h h10 h11 n (by omega_using [hn])
    have r9 : s.gpr .r8 = s₀.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s', hs', l0, l1, lk, r6', r7', regs', rd', wr', sp', f'⟩ :=
      keyRound_ok (j := n) (by omega_using [hn]) (room_congr h r9 inv.wr)
    refine ⟨s', ?_, ⟨?_, ?_, fun i hi => ?_, fun r a b c d e => ?_, by rw [sp', inv.sp], by rw [rd', inv.rd],
      by rw [wr', inv.wr], ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans hs hs'
    · rw [r6', inv.r6]
      simp only [keyWords, keyStep]
      split
      · simp only [kx]; exact (split64 _).symm
      · rfl
    · rw [r7', inv.r7]
      simp only [keyWords, keyStep]
      split
      · rfl
      · simp only [ky, ror56]; exact (split64 _).symm
    · have g0 : gInput key (2 * n) = (keyWords key n).1 + (keyWords key n).2.2.1 - Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show 2 * n / 2 = n by omega_using [], show 2 * n % 2 = 0 by omega_using [], ite_true]
      have g1 : gInput key (2 * n + 1) =
          (keyWords key n).2.1 - (keyWords key n).2.2.2 + Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show (2 * n + 1) / 2 = n by omega_using [], show (2 * n + 1) % 2 = 1 by omega_using []]
        rfl
      by_cases hi0 : i = 2 * n
      · subst hi0
        rw [l0, g0, gIn0, inv.r6, inv.r7, kx, ky, hi_append, hi_append, kcs_eq n (by omega_using [hn])]
      by_cases hi1 : i = 2 * n + 1
      · subst hi1
        rw [l1, g1, gIn1, inv.r6, inv.r7, kx, ky, BitVec.setWidth_append_eq_right,
          BitVec.setWidth_append_eq_right, kcs_eq n (by omega_using [hn])]
      · rw [lk _ (gSlot_mem i) _ (Nat.mod_lt _ (by decide)) (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi0)
          (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi1)]
        exact inv.lanes i (by omega_using [hi, hi0, hi1])
    · rw [regs' r a b c d e, inv.regs r a b c d e]
    · have : arraysR s = arraysR s₀ := by simp only [arraysR, r9]
      rw [this] at f'
      exact inv.frame.trans f'

end VG.Proof.Seed.PPC64LE

end

end


/-!
# The key schedule's computation on PPC64LE

`keyBody_ok`: from `r6 = Key0 || Key1` and `r7 = Key2 || Key3`, the rounds,
the two `g16`s and the copies write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

/-- The rounds and the count of halves, between loading the key and the loop. -/
def keyPre : List Instr := (List.range 16).flatMap keyRound ++ [.li .r6 2]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hx5 : s'.gpr .r8 = s.gpr .r8) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hx5]
  refine hf.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega_using [hb, this]))).symm

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .r6 = kx (keyWords key 0)) (h4 : s.gpr .r7 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .r6 = BitVec.ofNat 64 2 ∧ (∀ r ∈ [Reg.r8, .r4], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  let s2 := s1.write .r6 (BitVec.ofNat 64 2)
  have e2 : runBlock isa [.li .r6 2] s1 = some s2 := by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]
  have g2 : ∀ r, r ≠ .r6 → s2.gpr r = s1.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have r8_1 : s1.gpr .r8 = s.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have r8_2 : s2.gpr .r8 = s.gpr .r8 := (g2 _ (by decide)).trans r8_1
  have lv2 : ∀ k b, lv s2 k b = lv s1 k b := fun k b => by
    simp only [lv, laneA, g2 _ (show Reg.r8 ≠ .r6 by decide)]; rfl
  refine ⟨s2, runBlock_trans e1 e2, room_congr h r8_2 inv.wr, fun w hw => ?_, fun w hw => ?_,
    by simp [s2, gpr_write], fun r hr => ?_, inv.rd, inv.wr, inv.frame⟩
  · rw [lv2, ← inv.lanes w (by omega_using [hw]), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv2, ← inv.lanes (16 + w) (by omega_using [hw]), gSlot_hi hw, show (16 + w) % 16 = w by omega_using [hw]]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [g2 _ (by decide), inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- `add r4, r4, 64; sub r6, r6, 1`. -/
theorem halfTail_ok (t : State) :
    ∃ t', runBlock isa [.addi .r4 .r4 64, .subi .r6 .r6 1] t = some t' ∧
      t'.gpr .r4 = t.gpr .r4 + BitVec.ofNat 64 64 ∧ t'.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addi' (by decide), runStep_some, runBlock_cons, exec_subi' (by decide),
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp [gpr_write, h1, h2]

/-- After `c` of the two halves: `r4` at the schedule's word `16 c`, `r6` the
halves left, `G`'s words holding the next sixteen inputs, the schedule's
words before `16 c` done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  r8 : t.gpr .r8 = s.gpr .r8
  r4 : t.gpr .r4 = S + BitVec.ofNat 64 (64 * c)
  r6 : t.gpr .r6 = BitVec.ofNat 64 (2 - c)
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      t.gpr .r8 = s.gpr .r8 → t.rd = s.rd → t.wr = s.wr → Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf (.nonzero .d .r6)) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  have scrS : ∀ t : State, t.gpr .r8 = s.gpr .r8 → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  have workS : ∀ t : State, t.gpr .r8 = s.gpr .r8 → workR t = workR s := fun t h => by simp only [workR, h]
  have schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_using []))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, room2, rd2, wr2, -, regs2, f2⟩ := g16_lanes hi.room
  have r8_2 : t2.gpr .r8 = s.gpr .r8 := (regs2 _ (by decide)).trans hi.r8
  have r4_2 : t2.gpr .r4 = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.r4
  have out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 r8_2]; simp only [outR, r4_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Offset.sub_base _ (by omega_using [hc]))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 (by decide) room2
    (fun w hw => by
      rw [r4_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega_using [hc, hw]) (by omega_using [hc, hw])⟩) out2 16 (Nat.le_refl _)
  obtain ⟨t4, e4, r4_4', r6_4', g4, m4, rd4, wr4⟩ := halfTail_ok t3
  have r8_4 : t4.gpr .r8 = s.gpr .r8 := by rw [g4 _ (by decide) (by decide), g3 _ (by decide), r8_2]
  have r6_4 : t4.gpr .r6 = BitVec.ofNat 64 (2 - (c + 1)) := by
    rw [r6_4', g3 _ (by decide), regs2 _ (by decide), hi.r6, Offset.ofNat_sub_ofNat (by omega_using [hc])]
    congr 1
  have r4_4 : t4.gpr .r4 = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [r4_4', g3 _ (by decide), r4_2, Offset.add_add, show 64 * c + 64 = 64 * (c + 1) by omega_using []]
  have ev4 : isa.eval (.nonzero .d .r6) t4 = some (decide (c = 0)) := by
    show some (t4.gpr .r6 != 0) = _
    rw [r6_4]
    congr 1
    have : 2 - (c + 1) < 2 ^ 64 := by omega_using []
    rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;> decide
  -- the schedule's words so far
  have lvS : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
      ∀ i, (∀ r ∈ rs, (⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
      t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 :=
    fun t t' rs hf i hd => hf.readW (Region.contains_self _ _) hd (by decide)
  have done4 : ∀ i < 16 * (c + 1), t4.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i) := by
    intro i hi'
    rw [m4]
    by_cases hlo : i < 16 * c
    · rw [lvS t2 t3 _ f3 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, r4_2, Nat.mul_zero]
          rw [BitVec.add_zero]
          exact Offset.disjoint _ (Or.inl (by omega_using [hlo])) (by omega_using [hc, hi']) (by omega_using [hc])),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.r8]
          exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hc, hi']))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega_using [hlo]⟩
      have := v3 w (by omega_using [hi'])
      rw [r4_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega_using []] at this
      rw [this, g2 w (by omega_using [hi']), hi.cur w (by omega_using [hi'])]
  have frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.r8]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, r4_2, Nat.mul_zero]; rw [BitVec.add_zero]
      exact Offset.sub_base _ (by omega_using [hc])
  have room4 : Room t4 := room_congr hi.room (r8_4.trans hi.r8.symm) (by rw [wr4, wr3, wr2, hi.wr])
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (decide (c = 0)) ev4 (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    have hc0 : c = 0 := by simpa using hb
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, g5⟩ := keyMove_ok room4
    refine WP.of_runBlock ⟨t5, e5, .inr ⟨?_, 1, by omega_using [], 1, by omega_using [], rfl, ?_⟩⟩
    · show some (t5.gpr .r6 != 0) = some true
      rw [g5 _ (by decide) (by decide), r6_4]
      decide
    have r8_5 : t5.gpr .r8 = s.gpr .r8 := (g5 _ (by decide) (by decide)).trans r8_4
    have workF : Frame [workR s] t4.mem t5.mem := by
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 r8_4]; exact arraysR_sub_work t4⟩
    refine ⟨room5, r8_5, by rw [g5 _ (by decide) (by decide), r4_4], by rw [g5 _ (by decide) (by decide), r6_4],
      fun w hw => ?_, fun h => absurd h (by decide), fun i hi' => ?_, by rw [rd5, rd4, rd3, rd2, hi.rd],
      by rw [wr5, wr4, wr3, wr2, hi.wr],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · rw [v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by
          simp only [lv, laneA, m4, g4 _ (show Reg.r8 ≠ .r4 by decide) (show Reg.r8 ≠ .r6 by decide)],
        lv_frame (g3 _ (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t5 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hi'])))]
      exact done4 i hi'
  · -- the end
    have hc1 : c = 1 := by simp at hb; omega_using [hc, hb]
    subst hc1
    refine WP.block_nil (.inl ⟨?_, hQ t4 done4 r8_4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) frame4⟩)
    show some (t4.gpr .r6 != 0) = some false
    rw [r6_4]
    decide

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.KeyLoad`, which only this module used -/

section

/-!
# Loading the key on PPC64LE

`keyLoad2_ok`: `keyLoad2 d k` puts the key's big-endian words `k` and
`k + 4` in `d = Key_k || Key_k+1`.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .r9) (hd3 : d ≠ .r3) {k : Nat} (hk : k ≤ 8) (hk4 : k % 4 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .r3)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .r3)) (k + 4) ∧
      (∀ r, r ≠ .r9 → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  let W0 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 k) 32
  let W1 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (k + 4)) 32
  obtain ⟨s1, e1, u1⟩ := step_x s (.li .r9 k) .r9 (BitVec.ofNat 64 k) (exec_li (by omega))
  obtain ⟨s2, e2, u2⟩ := step_x s1 (.loadRev .w .r9 .r3 .r9) .r9 ((rev32 W0).setWidth 64)
    (by rw [exec_loadRev_w (by decide) (by rw [u1.self, u1.other (by decide), u1.rd, u1.wr]; exact hr),
      u1.self, u1.other (by decide), u1.mem])
  obtain ⟨s3, e3, u3⟩ := step_x s2 (.lsl .r9 .r9 32) .r9 (s2.gpr .r9 <<< 32) (exec_lsl (by decide))
  have r3₃ : s3.gpr .r3 = s.gpr .r3 := by rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain ⟨s4, e4, u4⟩ := step_x s3 (.li d (k + 4)) d (BitVec.ofNat 64 (k + 4)) (exec_li (by omega_using [hk]))
  have r3₄ : s4.gpr .r3 = s.gpr .r3 := by rw [u4.other (Ne.symm hd3), r3₃]
  have hr4 : InRegions (s4.rd ++ s4.wr) (s4.gpr .r3 + s4.gpr d) 4 := by
    rw [u4.self, r3₄, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr'
  obtain ⟨s5, e5, u5⟩ := step_x s4 (.loadRev .w d .r3 d) d ((rev32 W1).setWidth 64)
    (by rw [exec_loadRev_w (by decide) hr4, u4.self, r3₄, u4.mem, m3])
  obtain ⟨s6, e6, u6⟩ := step_x s5 (.logic .or d d .r9) d (s5.gpr d ||| s5.gpr .r9) exec_logic
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · rw [u6.self, u5.self, u5.other (Ne.symm hd), u4.other (Ne.symm hd), u3.self, u2.self,
      wordAt_blockAt _ _ (by omega_using [hk]), wordAt_blockAt _ _ (by omega_using [hk]), BitVec.or_comm,
      show rev32 = byteRev32 from rfl]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64) (b := byteRev32 W0) (b' := byteRev32 W1)
    rw [BitVec.setWidth_eq] at this
    rw [this]
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, m3]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

end VG.Proof.Seed.PPC64LE

end

end


/-!
# Key expansion on PPC64LE

`expandKey_ok`: after saving the callee-saved registers, `expandKey` loads
the key, computes the schedule (`keyBody_ok`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE
  VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .r5, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .r4, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .r3, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r4, 128⟩
  keyBuf : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .r4, 128⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .r4) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .r3))
  frame : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩, ⟨s.gpr .r4, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (([movR .r8 .r5] ++
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2)) ++
    (keyLoad2 .r6 0 ++ keyLoad2 .r7 8) ++ keyPre)) (.seq (.loop keyHalf (.nonzero .d .r6)) (.block restore)) := by
  simp only [expandKey, keyPre, Impl.Seed.PPC64LE.keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .r3)
  rw [expandKey_eq_code]
  -- `r8 := r5`
  let s₁ := s.write .r8 (s.gpr .r5)
  have e₁ : runBlock isa [movR .r8 .r5] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  have r9₁ : s₁.gpr .r8 = s.gpr .r5 := by simp [s₁, gpr_write]
  have g₁ : ∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have scr₁ : scratchR s₁ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  have room₁ : Room s₁ := .of_mem (by rw [scr₁]; exact h.scratch)
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, -, f₂, set₂, -⟩ := stores_ok room₁
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  have G₂ : ∀ r, r ≠ .r8 → s₂.gpr r = s.gpr r := fun r a => by rw [g₂, g₁ r a]
  have r9₂ : s₂.gpr .r8 = s.gpr .r5 := by rw [g₂, r9₁]
  have f₂' : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩] s.mem s₂.mem := by rw [← scr₁]; exact f₂
  have rd₂' : s₂.rd = s.rd := by rw [rd₂]; rfl
  have wr₂' : s₂.wr = s.wr := by rw [wr₂]; rfl
  -- the key
  have r3₂ : s₂.gpr .r3 = s.gpr .r3 := G₂ _ (by decide)
  have hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r3 + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₂', wr₂', r3₂]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain ⟨s₃, e₃, v₃, g₃, m₃, rd₃, wr₃, -⟩ := keyLoad2_ok (s := s₂) (d := .r6) (by decide) (by decide) (k := 0) (by decide)
    (by decide) (hkey 0 (by decide)) (hkey 4 (by decide))
  have r3₃ : s₃.gpr .r3 = s.gpr .r3 := by rw [g₃ _ (by decide) (by decide), r3₂]
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄, -⟩ := keyLoad2_ok (s := s₃) (d := .r7) (by decide) (by decide) (k := 8) (by decide)
    (by decide)
    (by rw [rd₃, wr₃, r3₃, ← r3₂]; exact hkey 8 (by decide))
    (by rw [rd₃, wr₃, r3₃, ← r3₂]; exact hkey 12 (by decide))
  have key₂ : Spec.Seed.blockAt s₂.mem (s.gpr .r3) = key := blockAt_frame f₂' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  have G₄ : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r7 → s₄.gpr r = s₂.gpr r := fun r a b c => by
    rw [g₄ r a c, g₃ r a b]
  have h3 : s₄.gpr .r6 = kx (keyWords key 0) := by
    rw [g₄ _ (by decide) (by decide), v₃, r3₂, key₂]; rfl
  have h4 : s₄.gpr .r7 = ky (keyWords key 0) := by
    rw [v₄, r3₃, m₃, key₂]; rfl
  have r9₄ : s₄.gpr .r8 = s.gpr .r5 := by rw [G₄ _ (by decide) (by decide) (by decide), r9₂]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  have mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  have scr₄ : scratchR s₄ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₄]
  have room₄ : Room s₄ := .of_mem (by rw [scr₄, wr₄']; exact h.scratch)
  have r4₄ : s₄.gpr .r4 = s.gpr .r4 := by rw [G₄ _ (by decide) (by decide) (by decide), G₂ _ (by decide)]
  -- the rounds, and the count of halves
  obtain ⟨s₅, e₅, room₅, cur₅, next₅, r6₅, g₅, rd₅, wr₅, f₅⟩ := keyPre_ok key room₄ h3 h4
  have r9₅ : s₅.gpr .r8 = s₄.gpr .r8 := g₅ _ (by simp)
  have r4₅ : s₅.gpr .r4 = s.gpr .r4 := (g₅ _ (by simp)).trans r4₄
  have scr₅ : scratchR s₅ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅, r9₄]
  have h0 : HalfInv key s₅ (s.gpr .r4) 0 s₅ :=
    ⟨room₅, rfl, by rw [r4₅]; exact (BitVec.add_zero _).symm, r6₅,
      fun w hw => by rw [cur₅ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₅, fun i hi => by omega, rfl, rfl,
      Frame.refl _ _⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, runBlock_trans (runBlock_trans (runBlock_trans e₁ e₂)
    (runBlock_trans e₃ e₄)) e₅, WP.seq (keyHalves_wp key
      (by rw [wr₅, wr₄']; exact h.schedIn) (by rw [scr₅]; exact h.schedBuf) h0
      fun s₆ v₆ r9₆ rd₆ wr₆ f₆ => ?_)⟩)
  have room₆ : Room s₆ := room_congr room₅ r9₆ wr₆
  obtain ⟨s', e', m', -, set', -⟩ := loads_ok room₆ Impl.Seed.PPC64LE.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact e', ?_⟩
  have workR₅ : workR s₅ = ⟨s.gpr .r5, 8 * 112⟩ := by simp only [workR, r9₅, r9₄]
  rw [workR₅] at f₆
  have arr₄ : Region.Sub (arraysR s₄) ⟨s.gpr .r5, 8 * 112⟩ := by
    have := arraysR_sub_work s₄; simp only [workR, r9₄] at this; exact this
  have f₄₆ : Frame [⟨s.gpr .r5, 8 * 112⟩, ⟨s.gpr .r4, 128⟩] s₄.mem s₆.mem :=
    (f₅.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₄⟩).trans f₆
  have frame : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩, ⟨s.gpr .r4, 128⟩] s.mem s'.mem := by
    rw [m']
    refine (f₂'.mono (by simp)).trans ?_
    rw [← mem₄]
    refine f₄₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨fun q hq => ?_, ?_, frame⟩
  · have hq' := savedRegs_ok q hq
    rw [set' q hq]
    have e6 : slotW s₆ q.2 = slotW s₄ q.2 := by
      show s₆.mem.readW (StraightK.wordAddr (s₆.gpr .r8) q.2) 64 =
        s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) q.2) 64
      rw [r9₆, r9₅, r9₄]
      refine f₄₆.readW (r := ⟨StraightK.wordAddr (s.gpr .r5) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    have e4 : slotW s₄ q.2 = slotW s₂ q.2 := by
      show s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) q.2) 64 =
        s₂.mem.readW (StraightK.wordAddr (s₂.gpr .r8) q.2) 64
      rw [mem₄, r9₄, r9₂]
    rw [e6, e4, set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.PPC64LE
