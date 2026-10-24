module

public import VerifiedGarbage.Proof.Ocb.Stretch
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Env
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.AesOcb.PPC64LE.PadTo
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Cmac.Dbl64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-OCB on PPC64LE: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed doublewords, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`). As on AArch64
(`Proof/AesOcb/AArch64/Offset0.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask shl3)
open VG.Proof.AesGcm.PPC64LE (in_left in_off)

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

/-- The mask of a stage: all ones in `r7` if bit `k` of `bottom` (in `r6`) is set. -/
theorem stageMask_ok (s : State) {k v : Nat} (hk6 : k < 64) (hv : v < 64) (h6 : s.gpr .r6 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stageMask k) s = some s' ∧
      s'.gpr .r7 = BitVec.ofNat 64 0 - (if v.testBit k then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨_, by
        simp only [stageMask, ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
          runBlock_nil, exec_li (show 1 < 2 ^ 15 by decide), exec_li (show 0 < 2 ^ 15 by decide), exec_logic,
          exec_sub] <;> rfl, ?_, fun r a b c => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h6]
      rw [← bit_v hv 0, BitVec.ushiftRight_zero]
    · simp [gpr_write, a, b, c]
    all_goals rfl
  · refine ⟨_, by
        simp only [stageMask, show k ≠ 0 by omega, ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons,
          runStep_some, runBlock_nil, exec_lsr_d hk6, exec_li (show 1 < 2 ^ 15 by decide),
          exec_li (show 0 < 2 ^ 15 by decide), exec_logic, exec_sub] <;> rfl, ?_, fun r a b c => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h6]
      rw [← bit_v hv k]
    · simp [gpr_write, a, b, c]
    all_goals rfl

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .r3 ++ s'.gpr .r4 ++ s'.gpr .r5 = shlIf (v.testBit k) a (s.gpr .r3 ++ s.gpr .r4 ++ s.gpr .r5) ∧
      (∀ r, r ∉ [.r0, .r3, .r4, .r5, .r7, .r8, .r9] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r7₁, g₁, m₁, sp₁, lr₁, rd₁, wr₁⟩ := stageMask_ok s hk6 hv h6
  have c1 : 64 - a < 64 := by omega
  have r3₁ := g₁ .r3 (by decide) (by decide) (by decide)
  have r4₁ := g₁ .r4 (by decide) (by decide) (by decide)
  have r5₁ := g₁ .r5 (by decide) (by decide) (by decide)
  obtain ⟨s₂, run₂, h₂⟩ : ∃ s₂, runBlock isa
      (([(Reg.r3, Reg.r4), (.r4, .r5)].flatMap fun (x, y) =>
        ([.lsl .r8 x a, .lsr .d .r9 y (64 - a), .logic .or .r8 .r8 .r9] : List Instr) ++ sel x) ++
        ([.lsl .r8 .r5 a] : List Instr) ++ sel .r5) s₁ = some s₂ ∧ s₂ = _ := by
    exact ⟨_, by
      simp only [sel, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil,
        runBlock_cons, runStep_some, runBlock_nil, exec_lsl ha', exec_lsr_d c1, exec_logic] <;> rfl, rfl⟩
  subst h₂
  refine ⟨_, by rw [stage, List.append_assoc, List.append_assoc, runBlock_append, run₁, Option.bind_some,
    ← List.append_assoc, run₂], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ↓reduceIte, reduceCtorEq, r7₁, r3₁, r4₁, r5₁]
    rw [sel_mask0, sel_mask0, sel_mask0]
    unfold shlIf
    split
    · exact shl3 _ _ _ ha ha'
    · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2,
      ↓reduceIte]
    exact g₁ r hr.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1
  · exact m₁
  · exact sp₁
  · exact lr₁
  · exact rd₁
  · exact wr₁

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- The registers `offset0` writes. -/
abbrev off0Regs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ∉ off0Regs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem offset0_ok {K W : Addr} (L : Lay K W) {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {v : Nat} (hv : v < 64) (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    WP isa (.block offset0) s
      (Off0Post W ((stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s) := by
  have rr : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    fun h => in_left (in_off hw h (by decide))
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, r6₁, g₁, m₁, sp₁, lr₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.li .r0 tmpO, .loadRev .d .r3 .r31 .r0, .li .r0 (tmpO + 8), .loadRev .d .r4 .r31 .r0,
       .lsl .r5 .r3 8, .lsr .d .r8 .r4 56, .logic .or .r5 .r5 .r8, .logic .xor .r5 .r5 .r3,
       .load .d .r6 .r31 botO] s = some s₁ ∧
      s₁.gpr .r3 ++ s₁.gpr .r4 ++ s₁.gpr .r5 = stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .r6 = BitVec.ofNat 64 v ∧
      (∀ r, r ∉ [.r0, .r3, .r4, .r5, .r6, .r8] → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.lr = s.lr ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    have r₀ := rr (d := 112) (by decide)
    have r₁ := rr (d := 120) (by decide)
    have r₂ := rr (d := 288) (by decide)
    refine ⟨_, by
      simp only [tmpO, botO, runBlock_cons, runStep_some, runBlock_nil, exec_li (show 112 < 2 ^ 15 by decide),
        exec_li (show 112 + 8 < 2 ^ 15 by decide), gpr_write, rd_write, wr_write, mem_write, ↓reduceIte,
        reduceCtorEq, h31, exec_loadRev_d, r₀, r₁, r₂, exec_lsl (show 8 < 64 by decide),
        exec_lsr_d (show 56 < 64 by decide), exec_logic, exec_load_d, ne_eq, not_false_eq_true, Nat.reduceLT,
        Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, and_self] <;> rfl, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h31]
      have hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
          rev64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++ rev64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
        have := Proof.Gcm.PPC64LE.blockAt_rev s.mem (W + BitVec.ofNat 64 112)
        rw [BitVec.add_zero, Offset.add_add] at this
        exact this.symm
      rw [stretch, hb, Proof.Ocb.stretch_words]
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h31, mem_write, hbot]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
    all_goals rfl
  -- the six stages
  have keep : ∀ {t t' : State}, (∀ r, r ∉ [.r0, .r3, .r4, .r5, .r7, .r8, .r9] → t'.gpr r = t.gpr r) →
      t.gpr .r6 = BitVec.ofNat 64 v → t'.gpr .r6 = BitVec.ofNat 64 v := fun g h => by rw [g _ (by decide), h]
  obtain ⟨s₂, run₂, w₂, g₂, m₂, sp₂, lr₂, rd₂, wr₂⟩ :=
    stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv r6₁
  obtain ⟨s₃, run₃, w₃, g₃, m₃, sp₃, lr₃, rd₃, wr₃⟩ :=
    stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv (keep g₂ r6₁)
  obtain ⟨s₄, run₄, w₄, g₄, m₄, sp₄, lr₄, rd₄, wr₄⟩ :=
    stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv (keep g₃ (keep g₂ r6₁))
  obtain ⟨s₅, run₅, w₅, g₅, m₅, sp₅, lr₅, rd₅, wr₅⟩ :=
    stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv (keep g₄ (keep g₃ (keep g₂ r6₁)))
  obtain ⟨s₆, run₆, w₆, g₆, m₆, sp₆, lr₆, rd₆, wr₆⟩ :=
    stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
      (keep g₅ (keep g₄ (keep g₃ (keep g₂ r6₁))))
  obtain ⟨s₇, run₇, w₇, g₇, m₇, sp₇, lr₇, rd₇, wr₇⟩ :=
    stage_ok s₆ (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
      (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ r6₁)))))
  have hw7 : s₇.gpr .r3 ++ s₇.gpr .r4 ++ s₇.gpr .r5 =
      stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .r3 ++ s₇.gpr .r4 =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← top2 _ _ (s₇.gpr .r5), hw7, Proof.Ocb.offset_shl _ (by omega)]
  have hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  have hsp₇ : s₇.sp = s.sp := by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]
  have hlr₇ : s₇.lr = s.lr := by rw [lr₇, lr₆, lr₅, lr₄, lr₃, lr₂, lr₁]
  have hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  have hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  have g₁₇ : ∀ r, r ∉ off0Regs → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [off0Regs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h' : r ∉ [Reg.r0, .r3, .r4, .r5, .r7, .r8, .r9] := by
      simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]
    rw [g₇ r h', g₆ r h', g₅ r h', g₄ r h', g₃ r h', g₂ r h',
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  have h31₇ : s₇.gpr .r31 = W := by rw [g₁₇ _ (by decide), h31]
  have ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₇.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [hwr₇]; exact in_off hw h (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, sp₈, lr₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa
      [.li .r0 ofsO, .storeRev .d .r3 .r31 .r0, .li .r0 (ofsO + 8), .storeRev .d .r4 .r31 .r0,
       .li .r0 o0O, .storeRev .d .r3 .r31 .r0, .li .r0 (o0O + 8), .storeRev .d .r4 .r31 .r0] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (rev64 (s₇.gpr .r3))).writeW (W + BitVec.ofNat 64 24)
        (rev64 (s₇.gpr .r4))).writeW (W + BitVec.ofNat 64 320) (rev64 (s₇.gpr .r3))).writeW
        (W + BitVec.ofNat 64 328) (rev64 (s₇.gpr .r4)) ∧
      (∀ r, r ≠ .r0 → s₈.gpr r = s₇.gpr r) ∧ s₈.sp = s₇.sp ∧ s₈.lr = s₇.lr ∧ s₈.rd = s₇.rd ∧
      s₈.wr = s₇.wr := by
    have w₁₆ := ww (d := 16) (by decide)
    have w₂₄ := ww (d := 24) (by decide)
    have w₃₂₀ := ww (d := 320) (by decide)
    have w₃₂₈ := ww (d := 328) (by decide)
    refine ⟨_, by
      simp only [ofsO, o0O, runBlock_cons, runStep_some, runBlock_nil, exec_li (show 16 < 2 ^ 15 by decide),
        exec_li (show 16 + 8 < 2 ^ 15 by decide), exec_li (show 320 < 2 ^ 15 by decide),
        exec_li (show 320 + 8 < 2 ^ 15 by decide), gpr_write, ↓reduceIte, reduceCtorEq, h31₇, wr_write,
        exec_storeRev_d, w₁₆, w₂₄, w₃₂₀, w₃₂₈, ne_eq, not_false_eq_true, Nat.reduceAdd, mem_write] <;> rfl, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h31₇, mem_write]
    · simp [gpr_write, h1]
    all_goals rfl
  have val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (rev64 (s₇.gpr .r3)) ++ Proof.Cmac.le8 (rev64 (s₇.gpr .r4))) =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [show rev64 = byteRev64 from rfl, Proof.Cmac.le8_byteRev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  have run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  have f320 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 320, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 320) (rev64 (s₇.gpr .r3))).writeW (W + BitVec.ofNat 64 328)
        (rev64 (s₇.gpr .r4))) := fun M => by
    rw [← addr8 W 320]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.of_runBlock ⟨s₈, run, ?_, ?_, ?_, fun r hr => ?_, by rw [sp₈, hsp₇], by rw [lr₈, hlr₇],
    by rw [rd₈, hrd₇], by rw [wr₈, hwr₇]⟩
  · rw [m₈, ← hm₇]
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
  · rw [g₈ r (by rintro rfl; exact hr (by decide)), g₁₇ r hr]

end VG.Proof.AesOcb.PPC64LE
