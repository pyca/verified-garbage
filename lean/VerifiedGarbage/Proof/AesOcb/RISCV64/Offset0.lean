module

-- separate module: its proofs (about 4 s) build in parallel with `NonceBlock`'s, which `Nonce` also imports

public import VerifiedGarbage.Proof.Ocb.Stretch
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.AesOcb.RISCV64.PadTo
import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Cmac.Dbl64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.BE64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Impl.AesOcb.RISCV64

/-!
# AES-OCB on RISC-V: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two big-endian doublewords, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
big-endian, to `W + ofsO` and `W + o0O` (`offset0_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/Offset0.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.RISCV64.Steps VG.RISCV64.BE64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask shl3)
open VG.Proof.AesGcm.RISCV64 (in_left in_off)
open VG.Impl.Words.RISCV64 (storeBE)

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_v {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 64 v >>> k) &&& BitVec.ofNat 64 1 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem sel_mask0 (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (BitVec.ofNat 64 0 - (if b = true then 1 else 0))) = if b then x' else x :=
  sel_mask x x' b

/-- The mask of a stage: all ones in `t5` if bit `k` of `bottom` (in `t4`) is set. -/
theorem stageMask_ok (s : State) {k v : Nat} (hk6 : k < 64) (hv : v < 64) (h4 : s.gpr .t4 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stageMask k) s = some s' ∧
      s'.gpr .t5 = BitVec.ofNat 64 0 - (if v.testBit k then 1 else 0) ∧
      (∀ r, r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨_, by
        simp only [stageMask, ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
          runBlock_nil, exec_logicImm (show imm12 1 by decide), exec_li (show imm12 0 by decide),
          exec_sub] <;> rfl, ?_, fun r a b => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h4]
      rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from rfl,
        ← bit_v hv 0, BitVec.ushiftRight_zero]
    · simp [gpr_write, a, b]
    all_goals rfl
  · refine ⟨_, by
        simp only [stageMask, show k ≠ 0 by omega, ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons,
          runStep_some, runBlock_nil, exec_shift_d hk6, exec_logicImm (show imm12 1 by decide),
          exec_li (show imm12 0 by decide), exec_sub] <;> rfl, ?_, fun r a b => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h4]
      rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from rfl,
        ← bit_v hv k]
    · simp [gpr_write, a, b]
    all_goals rfl

/-- The registers a stage writes. -/
abbrev stageRegs : List Reg := [.t1, .t2, .t3, .t5, .t6, .a6]

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (h4 : s.gpr .t4 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .t1 ++ s'.gpr .t2 ++ s'.gpr .t3 = shlIf (v.testBit k) a (s.gpr .t1 ++ s.gpr .t2 ++ s.gpr .t3) ∧
      (∀ r, r ∉ stageRegs → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r5₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := stageMask_ok s hk6 hv h4
  have c1 : 64 - a < 64 := by omega
  have r1₁ := g₁ .t1 (by decide) (by decide)
  have r2₁ := g₁ .t2 (by decide) (by decide)
  have r3₁ := g₁ .t3 (by decide) (by decide)
  obtain ⟨s₂, run₂, h₂⟩ : ∃ s₂, runBlock isa
      (([(Reg.t1, Reg.t2), (.t2, .t3)].flatMap fun (x, y) =>
        ([.shift .sll .d .t6 x a, .shift .srl .d .a6 y (64 - a), .logic .or .t6 .t6 .a6] : List Instr) ++ sel x) ++
        ([.shift .sll .d .t6 .t3 a] : List Instr) ++ sel .t3) s₁ = some s₂ ∧ s₂ = _ := by
    exact ⟨_, by
      simp only [sel, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
        runBlock_cons, runStep_some, runBlock_nil, exec_shift_d ha', exec_shift_d c1, exec_logic] <;> rfl, rfl⟩
  subst h₂
  refine ⟨_, by rw [stage, List.append_assoc, List.append_assoc, Interleave.runBlock_append, run₁, Option.bind_some,
    ← List.append_assoc, run₂], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ↓reduceIte, reduceCtorEq, r5₁, r1₁, r2₁, r3₁]
    rw [sel_mask0, sel_mask0, sel_mask0]
    unfold shlIf
    split
    · exact shl3 _ _ _ ha ha'
    · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ↓reduceIte]
    exact g₁ r hr.2.2.2.1 hr.2.2.2.2.1
  · exact m₁
  · exact sp₁
  · exact rd₁
  · exact wr₁

/-- A stage, followed by more code. -/
theorem wp_stage {is : List Instr} {Q : State → Prop} {s : State} {k a v : Nat} (hk6 : k < 64) (ha : 0 < a)
    (ha' : a < 64) (hv : v < 64) (h4 : s.gpr .t4 = BitVec.ofNat 64 v)
    (K : ∀ s', s'.gpr .t1 ++ s'.gpr .t2 ++ s'.gpr .t3 = shlIf (v.testBit k) a (s.gpr .t1 ++ s.gpr .t2 ++ s.gpr .t3) →
      (∀ r, r ∉ stageRegs → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.sp = s.sp → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (stage k a ++ is)) s Q := by
  obtain ⟨s', run, w, g, m, sp, rd, wr⟩ := stage_ok s hk6 ha ha' hv h4
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s', run, K s' w g m sp rd wr⟩)

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- The registers `offset0` writes. -/
abbrev off0Regs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a6]

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ∉ off0Regs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem offset0_ok {K W : Addr} (L : Lay K W) {s : State} (hs0 : s.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {v : Nat} (hv : v < 64) (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    WP isa (.block offset0) s
      (Off0Post W ((stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s) := by
  have rr : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    fun h => in_left (in_off hw h (by decide))
  simp only [botO] at hbot
  simp only [offset0, List.append_assoc]
  refine wp_loadBE64 (a := W + BitVec.ofNat 64 112) (by decide) (by decide) (by decide) (by decide)
    (by rw [hs0]; rfl) (rr (by decide)) fun a₁ b₁ ua₁ ub₁ => ?_
  have s0₁ : b₁.gpr .s0 = W := by rw [ub₁.other _ (by decide), ua₁.other _ (by decide), hs0]
  have k₁ : b₁.mem = s.mem ∧ b₁.rd = s.rd ∧ b₁.wr = s.wr := ⟨by rw [ub₁.mem, ua₁.mem],
    by rw [ub₁.rd, ua₁.rd], by rw [ub₁.wr, ua₁.wr]⟩
  refine wp_loadBE64 (a := W + BitVec.ofNat 64 120) (by decide) (by decide) (by decide) (by decide)
    (by rw [s0₁]; rfl) (by rw [k₁.2.1, k₁.2.2]; exact rr (by decide)) fun a₂ b₂ ua₂ ub₂ => ?_
  refine wp_sll (by decide) fun t₃ u₃ => wp_srl (by decide) fun t₄ u₄ => wp_or fun t₅ u₅ =>
    wp_xor fun t₆ u₆ => ?_
  have s0₆ : t₆.gpr .s0 = W := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      ub₂.other _ (by decide), ua₂.other _ (by decide), s0₁]
  have k₆ : t₆.mem = s.mem ∧ t₆.rd = s.rd ∧ t₆.wr = s.wr := ⟨by
      rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, ub₂.mem, ua₂.mem, k₁.1],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, ub₂.rd, ua₂.rd, k₁.2.1],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, ub₂.wr, ua₂.wr, k₁.2.2]⟩
  refine wp_ld (a := W + BitVec.ofNat 64 288) (by decide) (by rw [s0₆]; rfl) (Spill.al8 L.wal (by decide))
    (by rw [k₆.2.1, k₆.2.2]; exact rr (by decide)) fun s₁ u₇ => ?_
  have w₁ : s₁.gpr .t1 ++ s₁.gpr .t2 ++ s₁.gpr .t3 = stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) := by
    have y : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t6 → s₁.gpr r = b₂.gpr r := fun r h3 h4 h6 => by
      rw [u₇.other _ h4, u₆.other _ h3, u₅.other _ h3, u₄.other _ h6, u₃.other _ h3]
    have x₁ : b₂.gpr .t1 = byteRev64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) := by
      rw [ub₂.other _ (by decide), ua₂.other _ (by decide), ub₁.gpr]
    have x₂ : b₂.gpr .t2 = byteRev64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
      rw [ub₂.gpr, k₁.1]
    have x₃ : s₁.gpr .t3 = ((b₂.gpr .t1 <<< 8) ||| (b₂.gpr .t2 >>> 56)) ^^^ b₂.gpr .t1 := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
    have hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
        byteRev64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++
          byteRev64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
      have := Proof.Cmac.blockAt_byteRev s.mem (W + BitVec.ofNat 64 112)
      rw [BitVec.add_zero, Offset.add_add] at this
      exact this.symm
    rw [y _ (by decide) (by decide) (by decide), y _ (by decide) (by decide) (by decide), x₃, x₁, x₂, stretch, hb,
      Proof.Ocb.stretch_words]
  have r4₁ : s₁.gpr .t4 = BitVec.ofNat 64 v := by rw [u₇.gpr, k₆.1, hbot]
  have g₁ : ∀ r, r ∉ [Reg.t0, .t1, .t2, .t3, .t4, .t6] → s₁.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other _ hr.2.2.2.2.1, u₆.other _ hr.2.2.2.1, u₅.other _ hr.2.2.2.1, u₄.other _ hr.2.2.2.2.2,
      u₃.other _ hr.2.2.2.1, ub₂.other _ hr.2.2.1, ua₂.other _ hr.1, ub₁.other _ hr.2.1, ua₁.other _ hr.1]
  have keep : ∀ {t t' : State}, (∀ r, r ∉ stageRegs → t'.gpr r = t.gpr r) →
      t.gpr .t4 = BitVec.ofNat 64 v → t'.gpr .t4 = BitVec.ofNat 64 v := fun g h => by rw [g _ (by decide), h]
  refine wp_stage (k := 0) (a := 1) (by decide) (by decide) (by decide) hv r4₁ fun s₂ w₂ g₂ m₂ sp₂ rd₂ wr₂ => ?_
  refine wp_stage (k := 1) (a := 2) (by decide) (by decide) (by decide) hv (keep g₂ r4₁)
    fun s₃ w₃ g₃ m₃ sp₃ rd₃ wr₃ => ?_
  refine wp_stage (k := 2) (a := 4) (by decide) (by decide) (by decide) hv (keep g₃ (keep g₂ r4₁))
    fun s₄ w₄ g₄ m₄ sp₄ rd₄ wr₄ => ?_
  refine wp_stage (k := 3) (a := 8) (by decide) (by decide) (by decide) hv (keep g₄ (keep g₃ (keep g₂ r4₁)))
    fun s₅ w₅ g₅ m₅ sp₅ rd₅ wr₅ => ?_
  refine wp_stage (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep g₅ (keep g₄ (keep g₃ (keep g₂ r4₁)))) fun s₆ w₆ g₆ m₆ sp₆ rd₆ wr₆ => ?_
  refine wp_stage (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
    (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ r4₁))))) fun s₇ w₇ g₇ m₇ sp₇ rd₇ wr₇ => ?_
  have hw7 : s₇.gpr .t1 ++ s₇.gpr .t2 ++ s₇.gpr .t3 =
      stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .t1 ++ s₇.gpr .t2 =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← top2 _ _ (s₇.gpr .t3), hw7, Proof.Ocb.offset_shl _ (by omega)]
  have hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, u₇.mem, k₆.1]
  have hsp₇ : s₇.sp = s.sp := by
    rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, ub₂.sp, ua₂.sp, ub₁.sp, ua₁.sp]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, u₇.rd, k₆.2.1]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, u₇.wr, k₆.2.2]
  have g₁₇ : ∀ r, r ∉ off0Regs → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [off0Regs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h' : r ∉ stageRegs := by
      simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]
    rw [g₇ r h', g₆ r h', g₅ r h', g₄ r h', g₃ r h', g₂ r h',
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => in_off hw h (by decide)
  rw [show storeBE 8 .t2 .t0 .s0 (o0O + 8) = storeBE 8 .t2 .t0 .s0 (o0O + 8) ++ [] from
    (List.append_nil _).symm]
  refine wp_storeBE8 (a := W + BitVec.ofNat 64 16) (by decide) (by decide) (by decide)
    (by rw [g₁₇ _ (by decide), hs0]; rfl) (by rw [hwr₇]; exact ww (by decide)) fun c₁ d₁ mc₁ ud₁ => ?_
  have e₁ : ∀ r, r ≠ .t0 → d₁.gpr r = s₇.gpr r := fun r h => by rw [ud₁.other _ h, mc₁.gpr]
  refine wp_storeBE8 (a := W + BitVec.ofNat 64 24) (by decide) (by decide) (by decide)
    (by rw [e₁ _ (by decide), g₁₇ _ (by decide), hs0]; rfl)
    (by rw [ud₁.wr, mc₁.wr, hwr₇]; exact ww (by decide)) fun c₂ d₂ mc₂ ud₂ => ?_
  have e₂ : ∀ r, r ≠ .t0 → d₂.gpr r = s₇.gpr r := fun r h => by rw [ud₂.other _ h, mc₂.gpr, e₁ r h]
  refine wp_storeBE8 (a := W + BitVec.ofNat 64 320) (by decide) (by decide) (by decide)
    (by rw [e₂ _ (by decide), g₁₇ _ (by decide), hs0]; rfl)
    (by rw [ud₂.wr, mc₂.wr, ud₁.wr, mc₁.wr, hwr₇]; exact ww (by decide)) fun c₃ d₃ mc₃ ud₃ => ?_
  have e₃ : ∀ r, r ≠ .t0 → d₃.gpr r = s₇.gpr r := fun r h => by rw [ud₃.other _ h, mc₃.gpr, e₂ r h]
  refine wp_storeBE8 (a := W + BitVec.ofNat 64 328) (by decide) (by decide) (by decide)
    (by rw [e₃ _ (by decide), g₁₇ _ (by decide), hs0]; rfl)
    (by rw [ud₃.wr, mc₃.wr, ud₂.wr, mc₂.wr, ud₁.wr, mc₁.wr, hwr₇]; exact ww (by decide))
    fun c₄ s₈ mc₄ ud₄ => WP.block_nil ?_
  have m₈ : s₈.mem = (((s.mem.writeW (W + BitVec.ofNat 64 16) (byteRev64 (s₇.gpr .t1))).writeW
      (W + BitVec.ofNat 64 24) (byteRev64 (s₇.gpr .t2))).writeW (W + BitVec.ofNat 64 320)
      (byteRev64 (s₇.gpr .t1))).writeW (W + BitVec.ofNat 64 328) (byteRev64 (s₇.gpr .t2)) := by
    rw [ud₄.mem, mc₄.mem, e₃ _ (by decide), ud₃.mem, mc₃.mem, e₂ _ (by decide), ud₂.mem, mc₂.mem,
      e₁ _ (by decide), ud₁.mem, mc₁.mem, hm₇]
  have val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (byteRev64 (s₇.gpr .t1)) ++ Proof.Cmac.le8 (byteRev64 (s₇.gpr .t2))) =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [Proof.Cmac.le8_byteRev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  have f320 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 320, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 320) (byteRev64 (s₇.gpr .t1))).writeW (W + BitVec.ofNat 64 328)
        (byteRev64 (s₇.gpr .t2))) := fun M => by
    rw [← addr8 W 320]; exact Proof.Cmac.frame_store2 _ _ _
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [m₈]
    show Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 320, 16⟩] _ _
    exact ((((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains W (e := 16) (k := 16) (d := 24) (n := 8) (by decide) (by decide)
        (by decide))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains W (e := 320) (k := 16) (d := 328) (n := 8) (by decide) (by decide) (by decide))
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 16) = _
    rw [m₈, Proof.Ocb.blockAtMem_frame (f320 _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 320) (k := 16) (.inl (by decide)) (by decide) (by decide))]
    rw [show W + BitVec.ofNat 64 24 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_store2, val]
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 320) = _
    rw [m₈, show W + BitVec.ofNat 64 328 = W + BitVec.ofNat 64 320 + BitVec.ofNat 64 8 from (addr8 W 320).symm,
      blockAtMem_store2, val]
  · rw [ud₄.other _ (by rintro rfl; exact hr (by decide)), mc₄.gpr,
      e₃ r (by rintro rfl; exact hr (by decide)), g₁₇ r hr]
  · rw [ud₄.sp, mc₄.sp, ud₃.sp, mc₃.sp, ud₂.sp, mc₂.sp, ud₁.sp, mc₁.sp, hsp₇]
  · rw [ud₄.rd, mc₄.rd, ud₃.rd, mc₃.rd, ud₂.rd, mc₂.rd, ud₁.rd, mc₁.rd, hrd₇]
  · rw [ud₄.wr, mc₄.wr, ud₃.wr, mc₃.wr, ud₂.wr, mc₂.wr, ud₁.wr, mc₁.wr, hwr₇]

end VG.Proof.AesOcb.RISCV64
