module
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Seed.X86_64.ConstantTime
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.Seed.X86_64.ExpandKey
public import VerifiedGarbage.Proof.Seed.X86_64.Lanes
import VerifiedGarbage.Proof.Seed.X86_64.Copy
import VerifiedGarbage.Proof.Seed.X86_64.Round
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Seed.X86_64.G16
public import VerifiedGarbage.Proof.Seed.X86_64.KeyRound
public import VerifiedGarbage.Proof.Seed.KeySchedule
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Seed.X86_64.Batch
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Seed.X86_64.Ecb
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Seed.X86_64.Setup
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-! ### `Seed.X86_64.KeyVerified`, which only this module used -/

section

/-! ### `Seed.X86_64.Key`, which only this module used -/

section

/-! ### `Seed.X86_64.KeyBody`, which only this module used -/

section

/-! ### `Seed.X86_64.KeyStore`, which only this module used -/

section

/-!
# Copying `G`'s outputs on x86-64

`keyStore_ok`: `keyStore k` copies the sixteen lanes of `G`'s words to the
schedule's words from `k`; `keyMove_ok`: `keyMove` copies the second sixteen
inputs of `G` to its words.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

-- The steps share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .rsi + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) (hk : 4 * k + 64 < 2 ^ 64) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        [.mov32 .rax (.mem (lane .r9 (tSlot 0) w)),
         .store32 { base := .rsi, disp := ((4 * (k + w) : Nat) : Int) } .rax]) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hf⟩ := keyStore_ok k h hw hsep hk n (by omega_using [hn])
    obtain r9 : t.gpr .r9 = s.gpr .r9 := hg _ (by decide)
    obtain rsi : t.gpr .rsi = s.gpr .rsi := hg _ (by decide)
    obtain room : Room t := room_congr h r9 hwr
    obtain hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, r9]
      refine hf.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr .r9, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega_using [hn])
    let t1 := t.setReg32 .rax (lv t (tSlot 0) n)
    obtain e1 : exec (.mov32 .rax (.mem (lane .r9 (tSlot 0) n))) t = some t1 :=
      exec_mov32_lane room (by decide) (by omega_using [hn]) .rax
    obtain hea : t1.ea { base := .rsi, disp := ((4 * (k + n) : Nat) : Int) } =
        s.gpr .rsi + BitVec.ofNat 64 (4 * (k + n)) := by
      rw [ea_off]; simp only [t1, State.setReg32, gpr_setReg]; simp [rsi]
    obtain hw1 : InRegions t1.wr (t1.ea { base := .rsi, disp := ((4 * (k + n) : Nat) : Int) }) 4 := by
      rw [hea]; simp only [t1, State.setReg32, wr_setReg, hwr]; exact hw n (by omega_using [hn])
    let t2 := setMem t1 (t.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n))
    obtain e2 : exec (.store32 { base := .rsi, disp := ((4 * (k + n) : Nat) : Int) } .rax) t1 = some t2 := by
      rw [exec_store32 hw1, hea]
      simp only [t1, t2, State.setReg32, gpr_setReg, ite_true, setWidth_setWidth_32, hlane]
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
    · simp only [t2, gpr_setMem, t1, State.setReg32, gpr_setReg, hr, ite_false]; exact hg r hr
    · simp only [t2, mem_setMem]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hk]))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [.mov32 .rax (.mem (lane .r9 uSlot w)), .store32 (lane .r9 (tSlot 0) w) .rax])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_mov32_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_store32_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, State.setReg32, gpr_setReg,
        reduceCtorEq, ↓reduceIte, setWidth_setWidth_32, mem_setMem, mem_setReg, laneA_setMem,
        laneA_setReg _ _ (show ¬ Reg.r9 = .rax by decide)]
    · simp only [State.setReg32, gpr_setReg, gpr_setMem, h1, ↓reduceIte]

end VG.Proof.Seed.X86_64

end

end

/-! ### `Seed.X86_64.KeyRounds`, which only this module used -/

section

/-!
# The sixteen rounds of the key schedule on x86-64

`keyRounds_ok`: after `n` rounds, `r10` and `r11` hold the key words of
round `n + 1` (`keyWords`), and the lanes of `G`'s first `2 * n` inputs hold
them (`gInput`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

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

/-- The key words `k` as `r10` and `r11` hold them. -/
def kx (k : Quad) : BitVec 64 := k.1 ++ k.2.1
def ky (k : Quad) : BitVec 64 := k.2.2.1 ++ k.2.2.2

/-- After `n` rounds of the key schedule. -/
structure KeyInv (key : Spec.Seed.Block) (s₀ : State) (n : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = kx (keyWords key n)
  r11 : s.gpr .r11 = ky (keyWords key n)
  lanes : ∀ i < 2 * n, lv s (gSlot i) (i % 16) = gInput key i
  regs : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [arraysR s₀] s₀.mem s.mem

theorem keyRounds_ok (key : Spec.Seed.Block) {s₀ : State} (h : Room s₀)
    (h10 : s₀.gpr .r10 = kx (keyWords key 0)) (h11 : s₀.gpr .r11 = ky (keyWords key 0)) :
    ∀ n ≤ 16, ∃ s, runBlock isa ((List.range n).flatMap keyRound) s₀ = some s ∧ KeyInv key s₀ n s
  | 0, _ => ⟨s₀, runBlock_nil, h10, h11, fun i hi => by omega, fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s, hs, inv⟩ := keyRounds_ok key h h10 h11 n (by omega_using [hn])
    obtain r9 : s.gpr .r9 = s₀.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s', hs', l0, l1, lk, r10', r11', regs', rd', wr', f'⟩ :=
      keyRound_ok (j := n) (by omega_using [hn]) (room_congr h r9 inv.wr)
    refine ⟨s', ?_, ⟨?_, ?_, fun i hi => ?_, fun r a b c d => ?_, by rw [rd', inv.rd], by rw [wr', inv.wr], ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans hs hs'
    · rw [r10', inv.r10]
      simp only [keyWords, keyStep]
      split
      · simp only [kx]; exact (split64 _).symm
      · rfl
    · rw [r11', inv.r11]
      simp only [keyWords, keyStep]
      split
      · rfl
      · simp only [ky, ror56]; exact (split64 _).symm
    · have g0 : gInput key (2 * n) = (keyWords key n).1 + (keyWords key n).2.2.1 - Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show 2 * n / 2 = n by omega_using [], show 2 * n % 2 = 0 by omega_using [], ite_true]
      obtain g1 : gInput key (2 * n + 1) =
          (keyWords key n).2.1 - (keyWords key n).2.2.2 + Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show (2 * n + 1) / 2 = n by omega_using [], show (2 * n + 1) % 2 = 1 by omega_using []]
        rfl
      by_cases hi0 : i = 2 * n
      · subst hi0
        rw [l0, g0, gIn0, inv.r10, inv.r11, kx, ky, hi_append, hi_append, kcs_eq n (by omega_using [hn])]
      by_cases hi1 : i = 2 * n + 1
      · subst hi1
        rw [l1, g1, gIn1, inv.r10, inv.r11, kx, ky, BitVec.setWidth_append_eq_right,
          BitVec.setWidth_append_eq_right, kcs_eq n (by omega_using [hn])]
      · rw [lk _ (gSlot_mem i) _ (Nat.mod_lt _ (by decide)) (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi0)
          (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi1)]
        exact inv.lanes i (by omega_using [hi, hi0, hi1])
    · rw [regs' r a b c d, inv.regs r a b c d]
    · have : arraysR s = arraysR s₀ := by simp only [arraysR, r9]
      rw [this] at f'
      exact inv.frame.trans f'

end VG.Proof.Seed.X86_64

end

end


/-!
# The key schedule's computation on x86-64

`keyBody_ok`: from `r10 = Key0 || Key1` and `r11 = Key2 || Key3`, the rounds,
the two `g16`s and the copies write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed
open VG.Impl.Aes.X86_64 (movR)

/-- The rounds and the schedule's end, between loading the key and the loop. -/
def keyPre : List Instr :=
  (List.range 16).flatMap keyRound ++ [movR .rdx .rsi, .alu .add .rdx (.imm 128)]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hr9 : s'.gpr .r9 = s.gpr .r9) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hr9]
  refine hf.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega_using [hb, this]))).symm

theorem arraysR_sub_work' (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩ ⟨s.gpr .r9, 8 * 125⟩
  exact Offset.sub_base _ (by omega_using [])

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s) (hm : MasksIn s)
    (h10 : s.gpr .r10 = kx (keyWords key 0)) (h11 : s.gpr .r11 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧ MasksIn s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .rdx = s.gpr .rsi + BitVec.ofNat 64 128 ∧ (∀ r ∈ [Reg.r9, .rsi, .rsp], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h10 h11 16 (Nat.le_refl _)
  let s2 := s1.setReg .rdx (s1.gpr .rsi)
  let s3 := (arithFlags s2 (s2.gpr .rdx + (128 : BitVec 32).signExtend 64)
    (2 ^ 64 ≤ (s2.gpr .rdx).toNat + ((128 : BitVec 32).signExtend 64).toNat)
    (addOverflow (s2.gpr .rdx) ((128 : BitVec 32).signExtend 64)
      (s2.gpr .rdx + (128 : BitVec 32).signExtend 64))).setReg .rdx (s2.gpr .rdx + (128 : BitVec 32).signExtend 64)
  have e3 : runBlock isa [movR .rdx .rsi, .alu .add .rdx (.imm 128)] s1 = some s3 := rfl
  obtain g3 : ∀ r, r ≠ .rdx → s3.gpr r = s1.gpr r := fun r hr => by
    simp only [s3, s2, gpr_setReg, hr, ↓reduceIte, gpr_arithFlags]
  have m3 : s3.mem = s1.mem := rfl
  obtain r9_1 : s1.gpr .r9 = s.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain r9_3 : s3.gpr .r9 = s.gpr .r9 := (g3 _ (by decide)).trans r9_1
  obtain lv3 : ∀ k b, lv s3 k b = lv s1 k b := fun k b => by simp only [lv, laneA, m3, g3 _ (show Reg.r9 ≠ .rdx by decide)]
  refine ⟨s3, runBlock_trans e1 e3, room_congr h r9_3 inv.wr,
    masks_of_arrays hm r9_3 (by rw [m3]; exact inv.frame), fun w hw => ?_, fun w hw => ?_, ?_, fun r hr => ?_,
    inv.rd, inv.wr, by rw [m3]; exact inv.frame⟩
  · rw [lv3, ← inv.lanes w (by omega_using [hw]), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv3, ← inv.lanes (16 + w) (by omega_using [hw]), gSlot_hi hw, show (16 + w) % 16 = w by omega_using [hw]]
  · simp only [s3, s2, gpr_setReg_self]
    rw [inv.regs .rsi (by decide) (by decide) (by decide) (by decide)]
    rfl
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [g3 _ (by decide), inv.regs _ (by decide) (by decide) (by decide) (by decide)]

theorem endTest (S : Addr) : ∀ k ≤ 2,
    (S + BitVec.ofNat 64 (64 * k) - (S + BitVec.ofNat 64 128) == 0) = decide (k = 2)
  | 0, _ | 1, _ | 2, _ => by rw [Offset.add_sub_add_left]; decide

theorem eval_ne' (t : State) : isa.eval .ne t = t.zf.map (!·) := rfl

/-- `cmp rsi, rdx`. -/
theorem cmp_ok (t : State) :
    ∃ t', runBlock isa [.alu .cmp .rsi (.reg .rdx)] t = some t' ∧ t'.gpr = t.gpr ∧
      t'.zf = some (t.gpr .rsi - t.gpr .rdx == 0) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  ⟨_, rfl, by funext r; simp only [gpr_arithFlags], rfl, rfl, rfl, rfl⟩

/-- `add rsi, 64; cmp rsi, rdx`. -/
theorem addCmp_ok (t : State) :
    ∃ t', runBlock isa [.alu .add .rsi (.imm 64), .alu .cmp .rsi (.reg .rdx)] t = some t' ∧
      t'.gpr .rsi = t.gpr .rsi + BitVec.ofNat 64 64 ∧ (∀ r, r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      t'.zf = some (t.gpr .rsi + BitVec.ofNat 64 64 - t.gpr .rdx == 0) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  let t1 := (arithFlags t (t.gpr .rsi + (64 : BitVec 32).signExtend 64)
    (2 ^ 64 ≤ (t.gpr .rsi).toNat + ((64 : BitVec 32).signExtend 64).toNat)
    (addOverflow (t.gpr .rsi) ((64 : BitVec 32).signExtend 64)
      (t.gpr .rsi + (64 : BitVec 32).signExtend 64))).setReg .rsi (t.gpr .rsi + (64 : BitVec 32).signExtend 64)
  have e1 : runBlock isa [.alu .add .rsi (.imm 64)] t = some t1 := rfl
  obtain r1 : t1.gpr .rsi = t.gpr .rsi + BitVec.ofNat 64 64 := by simp only [t1, gpr_setReg_self]; rfl
  obtain g1 : ∀ r, r ≠ .rsi → t1.gpr r = t.gpr r := fun r hr => by
    simp only [t1, gpr_setReg, hr, ↓reduceIte, gpr_arithFlags]
  obtain ⟨t2, e2, g2, z2, m2, rd2, wr2⟩ := cmp_ok t1
  refine ⟨t2, runBlock_trans e1 e2, by rw [g2, r1], fun r hr => by rw [g2, g1 r hr], ?_, m2, rd2, wr2⟩
  rw [z2, r1, g1 _ (by decide)]

/-- After `c` of the two halves: `rsi` at the schedule's word `16 c`, `G`'s
words holding the next sixteen inputs, the schedule's words before `16 c`
done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  masks : MasksIn t
  r9 : t.gpr .r9 = s.gpr .r9
  rsp : t.gpr .rsp = s.gpr .rsp
  rsi : t.gpr .rsi = S + BitVec.ofNat 64 (64 * c)
  rdx : t.gpr .rdx = S + BitVec.ofNat 64 128
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      t.gpr .r9 = s.gpr .r9 → t.gpr .rsp = s.gpr .rsp → t.rd = s.rd → t.wr = s.wr →
      Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf .ne) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  obtain scrS : ∀ t : State, t.gpr .r9 = s.gpr .r9 → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  obtain workS : ∀ t : State, t.gpr .r9 = s.gpr .r9 → workR t = workR s := fun t h => by simp only [workR, h]
  obtain schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_using []))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, masks2, room2, rd2, wr2, regs2, f2⟩ := g16_lanes hi.room hi.masks
  obtain r9_2 : t2.gpr .r9 = s.gpr .r9 := (regs2 _ (by decide)).trans hi.r9
  obtain rsi_2 : t2.gpr .rsi = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.rsi
  obtain out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 r9_2]; simp only [outR, rsi_2, Nat.mul_zero, ofNat_zero_add]
    exact hsep.sub_left (Offset.sub_base _ (by omega_using [hc]))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 room2
    (fun w hw => by
      rw [rsi_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega_using [hc, hw]) (by omega_using [hc, hw])⟩) out2 (by decide) 16 (Nat.le_refl _)
  obtain r9_3 : t3.gpr .r9 = s.gpr .r9 := (g3 _ (by decide)).trans r9_2
  obtain masks3 : MasksIn t3 := masks_of_frame masks2 (g3 _ (by decide)) f3 out2
  obtain ⟨t4, e4, rsi4, g4, z4, m4, rd4, wr4⟩ := addCmp_ok t3
  obtain r9_4 : t4.gpr .r9 = s.gpr .r9 := (g4 _ (by decide)).trans r9_3
  obtain rsi_4 : t4.gpr .rsi = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [rsi4, g3 _ (by decide), rsi_2, Offset.add_add]; congr 2
  obtain rdx_4 : t4.gpr .rdx = S + BitVec.ofNat 64 128 := by
    rw [g4 _ (by decide), g3 _ (by decide), regs2 _ (by decide), hi.rdx]
  obtain zf4 : t4.zf = some (decide (c = 1)) := by
    rw [z4, ← g4 _ (show Reg.rdx ≠ .rsi by decide), ← rsi4, rsi_4, rdx_4, endTest S (c + 1) (by omega_using [hc])]
    congr 1
  -- the schedule's words so far
  obtain lvS : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
      ∀ i, (∀ r ∈ rs, (⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
      t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 :=
    fun t t' rs hf i hd => hf.readW (Region.contains_self _ _) hd (by decide)
  obtain done4 : ∀ i < 16 * (c + 1), t4.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i) := by
    intro i hi'
    rw [m4]
    by_cases hlo : i < 16 * c
    · rw [lvS t2 t3 _ f3 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, rsi_2, Nat.mul_zero, ofNat_zero_add]
          exact Offset.disjoint _ (Or.inl (by omega_using [hlo])) (by omega_using [hc, hi']) (by omega_using [hc])),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.r9]
          exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hc, hi']))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega_using [hlo]⟩
      have := v3 w (by omega_using [hi'])
      rw [rsi_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega_using []] at this
      rw [this, g2 w (by omega_using [hi']), hi.cur w (by omega_using [hi'])]
  obtain frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.r9]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, rsi_2, Nat.mul_zero, ofNat_zero_add]
      exact Offset.sub_base _ (by omega_using [hc])
  obtain room4 : Room t4 := room_congr hi.room (r9_4.trans hi.r9.symm) (by rw [wr4, wr3, wr2, hi.wr])
  obtain masks4 : MasksIn t4 := fun kv hkv => by
    rw [← masks3 kv hkv]
    show t4.mem.readW (Straight.wordAddr (t4.gpr .r9) kv.1) 64 = t3.mem.readW (Straight.wordAddr (t3.gpr .r9) kv.1) 64
    rw [m4, g4 _ (by decide)]
  obtain rsp4 : t4.gpr .rsp = s.gpr .rsp := by
    rw [g4 _ (by decide), g3 _ (by decide), regs2 _ (by decide), hi.rsp]
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (!decide (c = 1)) (by rw [eval_ne', zf4]; rfl) (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    obtain hc0 : c = 0 := by simp at hb; omega_using [hc, hb]
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, g5⟩ := keyMove_ok room4
    obtain ⟨t6, e6, gg6, z6, m6, rd6, wr6⟩ := cmp_ok t5
    obtain g6 : ∀ r, r ≠ .rax → r ≠ .rcx → t6.gpr r = t4.gpr r := fun r h1 h2 => by rw [gg6, g5 r h1 h2]
    refine WP.of_runBlock ⟨t6, runBlock_trans e5 e6, .inr ⟨?_, 1, by omega_using [], 1, by omega_using [], rfl, ?_⟩⟩
    · rw [eval_ne', z6, ← gg6, g6 _ (by decide) (by decide), g6 _ (by decide) (by decide), rsi_4, rdx_4,
        endTest S (0 + 1) (by omega_using [])]
      rfl
    obtain r9_6 : t6.gpr .r9 = s.gpr .r9 := (g6 _ (by decide) (by decide)).trans r9_4
    obtain workF : Frame [workR s] t4.mem t6.mem := by
      rw [m6]
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 r9_4]; exact arraysR_sub_work' t4⟩
    refine ⟨room_congr room4 (r9_6.trans r9_4.symm) (by rw [wr6, wr5]), ?_,
      r9_6, by rw [g6 _ (by decide) (by decide), rsp4], by rw [g6 _ (by decide) (by decide), rsi_4],
      by rw [g6 _ (by decide) (by decide), rdx_4], fun w hw => ?_, fun h => absurd h (by decide),
      fun i hi' => ?_, by rw [rd6, rd5, rd4, rd3, rd2, hi.rd], by rw [wr6, wr5, wr4, wr3, wr2, hi.wr],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · exact masks_of_arrays masks4 (g6 _ (by decide) (by decide)) (by rw [m6]; exact f5)
    · rw [show lv t6 (tSlot 0) w = lv t5 (tSlot 0) w by simp only [lv, laneA, m6, gg6],
        v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by simp only [lv, laneA, m4, g4 _ (show Reg.r9 ≠ .rsi by decide)],
        lv_frame (g3 _ (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t6 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hi'])))]
      exact done4 i hi'
  · -- the end
    obtain hc1 : c = 1 := by simp at hb; omega_using [hb]
    subst hc1
    refine WP.block_nil (.inl ⟨by rw [eval_ne', zf4]; rfl, hQ t4 done4 r9_4 rsp4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) frame4⟩)

end VG.Proof.Seed.X86_64

end

end

/-! ### `Seed.X86_64.KeyLoad`, which only this module used -/

section

/-!
# Loading the key on x86-64

`keyLoad_ok`: `keyLoad` puts the key's big-endian words in `r10 = Key0 || Key1`
and `r11 = Key2 || Key3` (`kx`, `ky` of `keyWords key 0`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed

theorem step_mov32_mem {s : State} (d : Reg) {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 4) :
    ∃ t, exec (.mov32 d (.mem m)) s = some t ∧ Upd s t d ((s.mem.readW (s.ea m) 32).setWidth 64) :=
  ⟨_, exec_mov32_mem h, upd_of rfl⟩

theorem step_bswap32 (s : State) (d : Reg) :
    ∃ t, exec (.bswap32 d) s = some t ∧ Upd s t d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) :=
  ⟨_, rfl, upd_of rfl⟩

theorem step_shl (s : State) (d : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    ∃ t, exec (.shift .shl d n) s = some t ∧ Upd s t d (s.gpr d <<< n) := by
  refine ⟨_, ?_, upd_flags (some ((s.gpr d).getLsbD (64 - n)))
    (if n = 1 then some ((s.gpr d <<< n).msb ^^ (s.gpr d).getLsbD (64 - n)) else none)
    (some (s.gpr d <<< n == 0)) (some (s.gpr d <<< n).msb) rfl⟩
  simp only [reduceExec, execShift, h1, h2, and_self, ite_true]

theorem step_or_reg (s : State) (d r : Reg) :
    ∃ t, exec (.alu .or d (.reg r)) s = some t ∧ Upd s t d (s.gpr d ||| s.gpr r) :=
  ⟨_, rfl, ⟨fun x => by rw [gpr_setReg, gpr_arithFlags], rfl, rfl, rfl⟩⟩

/-- `keyLoad2 d k`: the key's big-endian words `k` and `k + 4`, into `d`. -/
theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .rax) {k : Nat} (hk : k ≤ 8)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .rdi)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .rdi)) (k + 4) ∧
      (∀ r, r ≠ .rax → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s1, e1, u1⟩ := step_mov32_mem (s := s) .rax (m := { base := .rdi, disp := ((k : Nat) : Int) })
    (by rw [ea_off]; exact hr)
  obtain ⟨s2, e2, u2⟩ := step_bswap32 s1 .rax
  obtain ⟨s3, e3, u3⟩ := step_shl s2 .rax (n := 32) (by decide) (by decide)
  obtain rdi3 : s3.gpr .rdi = s.gpr .rdi := by
    rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  obtain ⟨s4, e4, u4⟩ := step_mov32_mem (s := s3) d (m := { base := .rdi, disp := ((k + 4 : Nat) : Int) })
    (by rw [ea_off, rdi3, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr')
  obtain ⟨s5, e5, u5⟩ := step_bswap32 s4 d
  obtain ⟨s6, e6, u6⟩ := step_or_reg s5 d .rax
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    rw [u6.self, u5.self, u4.self, setWidth_setWidth_32, u5.other (Ne.symm hd), u4.other (Ne.symm hd),
      u3.self, u2.self, u1.self, setWidth_setWidth_32, ea_off, ea_off, rdi3, m3,
      wordAt_blockAt _ _ (by omega_using [hk]), wordAt_blockAt _ _ (by omega_using [hk]), BitVec.or_comm]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64)
      (b := byteRev32 (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 k) 32))
      (b' := byteRev32 (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (k + 4)) 32))
    rw [BitVec.setWidth_eq] at this
    rw [this]
    rfl
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]

end VG.Proof.Seed.X86_64

end

end


/-!
# Key expansion on x86-64

`expandKey_ok`: after saving the callee-saved registers and writing the
masks, `expandKey` loads the key, computes the schedule (`keyBody_ok`) and
restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64 VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other and the return address. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .rdx, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .rsi, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .rdi, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .rdi, 16⟩ : Region).Disjoint ⟨s.gpr .rsi, 128⟩
  keyBuf : (⟨s.gpr .rdi, 16⟩ : Region).Disjoint ⟨s.gpr .rdx, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .rsi, 128⟩ : Region).Disjoint ⟨s.gpr .rdx, 8 * scratchSlots⟩
  retSched : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 128⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  gpr : gprPreserved s s'
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .rsi) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .rdi))
  frame : Frame [⟨s.gpr .rdx, 8 * scratchSlots⟩, ⟨s.gpr .rsi, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (([movR .r9 .rdx] ++
    (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1)).map (fun p => st p.1 p.2) ++ setG16Masks) ++
    Impl.Seed.X86_64.keyLoad ++ keyPre)) (.seq (.loop keyHalf .ne) (.block restore)) := by
  simp only [expandKey, keyPre, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .rdi)
  rw [expandKey_eq_code]
  -- `r9 := rdx`
  let s₁ := s.setReg .r9 (s.gpr .rdx)
  have e₁ : runBlock isa [movR .r9 .rdx] s = some s₁ := rfl
  obtain r9₁ : s₁.gpr .r9 = s.gpr .rdx := gpr_setReg_self (s := s) _ _
  obtain g₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := fun r hr => gpr_setReg_of_ne (s := s) _ hr
  obtain scr₁ : scratchR s₁ = ⟨s.gpr .rdx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  obtain room₁ : Room s₁ := ⟨_, Nat.le_refl _, by rw [r9₁]; exact h.scratch⟩
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, set₂, keep₂⟩ := stores_ok room₁
    (Impl.Seed.X86_64.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  obtain room₂ : Room s₂ := room_congr room₁ (by rw [g₂]) wr₂
  obtain ⟨s₃, e₃, g₃, rd₃, wr₃, f₃, set₃, keep₃⟩ := masks_ok room₂ maskSlots (by decide) (by decide)
  obtain G₃ : ∀ r, r ≠ .r9 → r ≠ t0 → s₃.gpr r = s.gpr r := fun r a b => by rw [g₃ r b, g₂, g₁ r a]
  obtain r9₃ : s₃.gpr .r9 = s.gpr .rdx := by rw [g₃ _ (by decide), g₂, r9₁]
  obtain f₃' : Frame [⟨s.gpr .rdx, 8 * scratchSlots⟩] s.mem s₃.mem := by
    rw [← scr₁]
    refine f₂.trans ?_
    have : scratchR s₂ = scratchR s₁ := by simp only [scratchR, g₂]
    rw [← this]; exact f₃
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂]; rfl
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂]; rfl
  obtain room₃ : Room s₃ := ⟨_, Nat.le_refl _, by rw [r9₃, wr₃']; exact h.scratch⟩
  -- the key
  obtain rdi₃ : s₃.gpr .rdi = s.gpr .rdi := G₃ _ (by decide) (by decide)
  obtain hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdi + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₃', wr₃', rdi₃]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄⟩ := keyLoad2_ok (s := s₃) (d := .r10) (by decide) (k := 0) (by decide)
    (hkey 0 (by decide)) (hkey 4 (by decide))
  obtain rdi₄ : s₄.gpr .rdi = s.gpr .rdi := by rw [g₄ _ (by decide) (by decide), rdi₃]
  obtain ⟨s₅, e₅, v₅, g₅, m₅, rd₅, wr₅⟩ := keyLoad2_ok (s := s₄) (d := .r11) (by decide) (k := 8) (by decide)
    (by rw [rd₄, wr₄, rdi₄, ← rdi₃]; exact hkey 8 (by decide))
    (by rw [rd₄, wr₄, rdi₄, ← rdi₃]; exact hkey 12 (by decide))
  obtain key₃ : Spec.Seed.blockAt s₃.mem (s.gpr .rdi) = key := blockAt_frame f₃' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  obtain G₅ : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s₅.gpr r = s₃.gpr r := fun r a b c => by
    rw [g₅ r a c, g₄ r a b]
  obtain h10 : s₅.gpr .r10 = kx (keyWords key 0) := by
    rw [g₅ _ (by decide) (by decide), v₄, rdi₃, key₃]; rfl
  obtain h11 : s₅.gpr .r11 = ky (keyWords key 0) := by
    rw [v₅, rdi₄, m₄, key₃]; rfl
  obtain r9₅ : s₅.gpr .r9 = s.gpr .rdx := by rw [G₅ _ (by decide) (by decide) (by decide), r9₃]
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃']
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃']
  obtain mem₅ : s₅.mem = s₃.mem := by rw [m₅, m₄]
  obtain scr₅ : scratchR s₅ = ⟨s.gpr .rdx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  obtain room₅ : Room s₅ := ⟨_, Nat.le_refl _, by rw [r9₅, wr₅']; exact h.scratch⟩
  obtain masks₅ : MasksIn s₅ := fun kv hkv => by
    rw [← set₃ kv hkv]
    show s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) kv.1) 64 = s₃.mem.readW (Straight.wordAddr (s₃.gpr .r9) kv.1) 64
    rw [mem₅, r9₅, r9₃]
  obtain rsi₅ : s₅.gpr .rsi = s.gpr .rsi := by rw [G₅ _ (by decide) (by decide) (by decide), G₃ _ (by decide) (by decide)]
  -- the rounds, and the schedule's end
  obtain ⟨s₆, e₆, room₆, masks₆, cur₆, next₆, rdx₆, g₆, rd₆, wr₆, f₆⟩ := keyPre_ok key room₅ masks₅ h10 h11
  obtain r9₆ : s₆.gpr .r9 = s₅.gpr .r9 := g₆ _ (by simp)
  obtain rsi₆ : s₆.gpr .rsi = s.gpr .rsi := (g₆ _ (by simp)).trans rsi₅
  obtain scr₆ : scratchR s₆ = ⟨s.gpr .rdx, 8 * scratchSlots⟩ := by simp only [scratchR, r9₆, r9₅]
  obtain h0 : HalfInv key s₆ (s.gpr .rsi) 0 s₆ :=
    ⟨room₆, masks₆, rfl, rfl, by rw [rsi₆]; exact (BitVec.add_zero _).symm, by rw [rdx₆, rsi₅],
      fun w hw => by rw [cur₆ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₆, fun i hi => by omega, rfl, rfl,
      Frame.refl _ _⟩
  refine WP.seq (WP.of_runBlock ⟨s₆, runBlock_trans (runBlock_trans (runBlock_trans
    (runBlock_trans e₁ e₂) e₃) (runBlock_trans e₄ e₅)) e₆, WP.seq (keyHalves_wp key
      (by rw [wr₆, wr₅']; exact h.schedIn) (by rw [scr₆]; exact h.schedBuf) h0
      fun s₇ v₇ r9₇ rsp₇ rd₇ wr₇ f₇ => ?_)⟩)
  obtain room₇ : Room s₇ := room_congr room₆ r9₇ wr₇
  obtain ⟨s', e', m', set', keep'⟩ := loads_ok room₇ Impl.Seed.X86_64.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact e', ?_⟩
  obtain workR₆ : workR s₆ = ⟨s.gpr .rdx, 8 * 125⟩ := by simp only [workR, r9₆, r9₅]
  rw [workR₆] at f₇
  obtain arr₅ : Region.Sub (arraysR s₅) ⟨s.gpr .rdx, 8 * 125⟩ := by
    have := arraysR_sub_work' s₅; simp only [workR, r9₅] at this; exact this
  -- `s₅`'s memory to `s₇`'s
  obtain f₅₇ : Frame [⟨s.gpr .rdx, 8 * 125⟩, ⟨s.gpr .rsi, 128⟩] s₅.mem s₇.mem :=
    (f₆.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₅⟩).trans f₇
  obtain frame : Frame [⟨s.gpr .rdx, 8 * scratchSlots⟩, ⟨s.gpr .rsi, 128⟩] s.mem s'.mem := by
    rw [m']
    refine (f₃'.mono (by simp)).trans ?_
    rw [← mem₅]
    refine f₅₇.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, frame⟩
  · have saved : ∀ q ∈ Impl.Seed.X86_64.savedRegs, s'.gpr q.1 = s.gpr q.1 := by
      intro q hq
      obtain hq' := savedRegs_ok q hq
      rw [set' q hq]
      obtain e7 : slotW s₇ q.2 = slotW s₅ q.2 := by
        show s₇.mem.readW (Straight.wordAddr (s₇.gpr .r9) q.2) 64 =
          s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) q.2) 64
        rw [r9₇, r9₆, r9₅]
        refine f₅₇.readW (r := ⟨Straight.wordAddr (s.gpr .rdx) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
        · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
      obtain e5 : slotW s₅ q.2 = slotW s₃ q.2 := by
        show s₅.mem.readW (Straight.wordAddr (s₅.gpr .r9) q.2) 64 =
          s₃.mem.readW (Straight.wordAddr (s₃.gpr .r9) q.2) 64
        rw [mem₅, r9₅, r9₃]
      rw [e7, e5, keep₃ _ hq'.1 (fun p hp => by have := maskSlots_lt p hp; omega),
        set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact saved (.rbx, 125) (by decide)
    · exact saved (.rbp, 126) (by decide)
    · rw [keep' .rsp (by decide), rsp₇, g₆ _ (by simp), G₅ _ (by decide) (by decide) (by decide),
        G₃ _ (by decide) (by decide)]
    · exact saved (.r12, 127) (by decide)
    · exact saved (.r13, 128) (by decide)
    · exact saved (.r14, 129) (by decide)
    · exact saved (.r15, 130) (by decide)
  · refine frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.retBuf
    · exact h.retSched
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₇ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.X86_64

end

end


/-! # Key expansion meets its contract, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 16⟩
    let sched : Region := ⟨s.gpr .rsi, 128⟩
    let buf : Region := ⟨s.gpr .rdx, 1056⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧
      sched.Disjoint buf ∧ ret.Disjoint sched ∧ ret.Disjoint buf
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .rsi) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .rdi))
  pub := PublicRegs [.rdi, .rsi, .rdx, .rsp]

def keySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 1056⟩]

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.X86_64.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb, rs, rb⟩ := hs
  obtain ⟨t, s', he, hp⟩ := expandKey_ok (s := s)
    { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb
      retSched := rs
      retBuf := rb }
  exact ⟨t, s', he, abiPreserved_of_exec (c := Impl.Seed.X86_64.expandKey) (by lit_decide) he hp.gpr, hp.sched⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp := by simp [PublicRegs]

theorem expandKey_verified : Verified target Impl.Seed.X86_64.expandKey
    (Proof.Seed.expandKeyScratchContract abi 132) := by
  refine Verified.of_correct expandKey_correct (expandKey_constantTime _) ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, publicRegs_four] [keySatState] using keySatState

end VG.Proof.Seed.X86_64

end

end


/-!
# SEED on x86-64, with its working space on the stack

Key expansion runs its code, proved with the working space as an argument,
in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key and the round keys:
1064 bytes, the 1056 of the working space and 8 to keep `rsp` aligned. The
code uses no other stack. ECB does the same around calls of the blocks
functions (`EcbCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64

theorem expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey)
      (Spec.Seed.expandKeyContract X86_64.abi 1064) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 132) (post := Proof.Seed.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 1064) expandKey_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.expandKeyPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.X86_64
