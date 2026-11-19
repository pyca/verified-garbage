module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
public import VerifiedGarbage.Proof.Ocb.Stretch
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
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
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Ocb.Nonce
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK

/-! ### `AesOcb.PPC64LE.Offset0`, which only this module used -/

section

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
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv]),
    show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  obtain h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega_using [h]

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
        simp only [stageMask, show k ≠ 0 by omega_using [hk], ↓reduceIte, List.cons_append, List.nil_append, runBlock_cons,
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
  obtain c1 : 64 - a < 64 := by omega_using [ha]
  obtain r3₁ := g₁ .r3 (by decide) (by decide) (by decide)
  obtain r4₁ := g₁ .r4 (by decide) (by decide) (by decide)
  obtain r5₁ := g₁ .r5 (by decide) (by decide) (by decide)
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
    show ¬ 64 + i < 64 by omega_using [], ↓reduceIte, show 64 + i - 64 = i by omega_using []]

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
  obtain rr : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
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
    obtain r₀ := rr (d := 112) (by decide)
    obtain r₁ := rr (d := 120) (by decide)
    obtain r₂ := rr (d := 288) (by decide)
    refine ⟨_, by
      simp only [tmpO, botO, runBlock_cons, runStep_some, runBlock_nil, exec_li (show 112 < 2 ^ 15 by decide),
        exec_li (show 112 + 8 < 2 ^ 15 by decide), gpr_write, rd_write, wr_write, mem_write, ↓reduceIte,
        reduceCtorEq, h31, exec_loadRev_d, r₀, r₁, r₂, exec_lsl (show 8 < 64 by decide),
        exec_lsr_d (show 56 < 64 by decide), exec_logic, exec_load_d, ne_eq, not_false_eq_true, Nat.reduceLT,
        Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, and_self] <;> rfl, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h31]
      obtain hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
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
  obtain keep : ∀ {t t' : State}, (∀ r, r ∉ [.r0, .r3, .r4, .r5, .r7, .r8, .r9] → t'.gpr r = t.gpr r) →
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
  obtain hw7 : s₇.gpr .r3 ++ s₇.gpr .r4 ++ s₇.gpr .r5 =
      stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  obtain hO : s₇.gpr .r3 ++ s₇.gpr .r4 =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← top2 _ _ (s₇.gpr .r5), hw7, Proof.Ocb.offset_shl _ (by omega_using [hv])]
  obtain hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  obtain hsp₇ : s₇.sp = s.sp := by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]
  obtain hlr₇ : s₇.lr = s.lr := by rw [lr₇, lr₆, lr₅, lr₄, lr₃, lr₂, lr₁]
  obtain hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  obtain hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  obtain g₁₇ : ∀ r, r ∉ off0Regs → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [off0Regs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain h' : r ∉ [Reg.r0, .r3, .r4, .r5, .r7, .r8, .r9] := by
      simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]
    rw [g₇ r h', g₆ r h', g₅ r h', g₄ r h', g₃ r h', g₂ r h',
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  obtain h31₇ : s₇.gpr .r31 = W := by rw [g₁₇ _ (by decide), h31]
  obtain ww : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₇.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [hwr₇]; exact in_off hw h (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, sp₈, lr₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa
      [.li .r0 ofsO, .storeRev .d .r3 .r31 .r0, .li .r0 (ofsO + 8), .storeRev .d .r4 .r31 .r0,
       .li .r0 o0O, .storeRev .d .r3 .r31 .r0, .li .r0 (o0O + 8), .storeRev .d .r4 .r31 .r0] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (rev64 (s₇.gpr .r3))).writeW (W + BitVec.ofNat 64 24)
        (rev64 (s₇.gpr .r4))).writeW (W + BitVec.ofNat 64 320) (rev64 (s₇.gpr .r3))).writeW
        (W + BitVec.ofNat 64 328) (rev64 (s₇.gpr .r4)) ∧
      (∀ r, r ≠ .r0 → s₈.gpr r = s₇.gpr r) ∧ s₈.sp = s₇.sp ∧ s₈.lr = s₇.lr ∧ s₈.rd = s₇.rd ∧
      s₈.wr = s₇.wr := by
    obtain w₁₆ := ww (d := 16) (by decide)
    obtain w₂₄ := ww (d := 24) (by decide)
    obtain w₃₂₀ := ww (d := 320) (by decide)
    obtain w₃₂₈ := ww (d := 328) (by decide)
    refine ⟨_, by
      simp only [ofsO, o0O, runBlock_cons, runStep_some, runBlock_nil, exec_li (show 16 < 2 ^ 15 by decide),
        exec_li (show 16 + 8 < 2 ^ 15 by decide), exec_li (show 320 < 2 ^ 15 by decide),
        exec_li (show 320 + 8 < 2 ^ 15 by decide), gpr_write, ↓reduceIte, reduceCtorEq, h31₇, wr_write,
        exec_storeRev_d, w₁₆, w₂₄, w₃₂₀, w₃₂₈, ne_eq, not_false_eq_true, Nat.reduceAdd, mem_write] <;> rfl, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, reduceCtorEq, h31₇, mem_write]
    · simp [gpr_write, h1]
    all_goals rfl
  obtain val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (rev64 (s₇.gpr .r3)) ++ Proof.Cmac.le8 (rev64 (s₇.gpr .r4))) =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [show rev64 = byteRev64 from rfl, Proof.Cmac.le8_byteRev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  obtain run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  obtain f320 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 320, 16⟩] M
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

end

end

/-! ### `AesOcb.PPC64LE.NonceBlock`, which only this module used -/

section

/-!
# AES-OCB on PPC64LE: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the 1 before where the nonce goes, the
nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into the first
byte, and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`). As on AArch64
(`Proof/AesOcb/AArch64/LNtz.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)
open VG.Proof.AesGcm.PPC64LE (copyLoop_ok in_left in_off and15)
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li wp_stb wp_lbz wp_std wp_sub)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or, wp_and → cwp_and, wp_lsl → cwp_lsl

theorem or_byte (b : Byte) (v : Nat) :
    (BitVec.setWidth 64 b ||| BitVec.ofNat 64 v).setWidth 8 = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 64 by omega_arith, hi,
    decide_true, Bool.true_and]

theorem and_byte (b : Byte) (v : Nat) :
    (BitVec.setWidth 64 b &&& BitVec.ofNat 64 v).setWidth 8 = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 64 by omega_arith, hi,
    decide_true, Bool.true_and]

theorem and63 (b : Byte) : BitVec.setWidth 64 b &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_arith), show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem lsl4_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem one_byte : (BitVec.ofNat 64 1).setWidth 8 = (1 : Byte) := by decide

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega_arith), List.getElem?_append_left (by simp; omega_arith),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega_arith]
  · rw [List.getElem?_append_left (by simp; omega_arith), List.getElem?_append_right (by simp; omega_arith)]
    simp [show min k L.length = k by omega_arith]
  · rw [List.getElem?_append_right (by simp; omega_arith)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega_arith, ↓reduceIte]
    congr 2; omega_arith

/-- The registers `nonceBlock` writes. -/
abbrev nonceRegs : List Reg := [.r0, .r3, .r4, .r5, .r6]

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ∉ nonceRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- After the first block of `nonceBlock`, from `s` (through `s₁`, after the zeros). -/
def NonceHead (W N : Addr) (nl : Nat) (s s₂ : State) : Prop :=
  ∃ s₁, BlkStep W tmpO 0 [.r0] s s₁ ∧ s₂.gpr .r4 = W + BitVec.ofNat 64 (128 - nl) ∧ s₂.gpr .r3 = N ∧
    s₂.gpr .r5 = BitVec.ofNat 64 nl ∧ (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s.gpr r) ∧
    s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧ s₂.sp = s.sp ∧ s₂.lr = s.lr ∧
    s₂.rd = s.rd ∧ s₂.wr = s.wr

/-- The first block of `nonceBlock`: zeros, the 1 before where the nonce
goes, and the arguments of the copy. -/
theorem nonceHead_ok {W N : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {nl : Nat}
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (h24 : s.gpr .r24 = N) (h25 : s.gpr .r25 = BitVec.ofNat 64 nl) :
    WP isa (.block (zero16 tmpO ++ ([.addi .r4 .r31 (tmpO + 15), .sub .r4 .r4 .r25, .li .r0 1, .stb .r0 .r4 0,
      .addi .r4 .r4 1, Impl.AesGcm.PPC64LE.mov .r3 .r24, Impl.AesGcm.PPC64LE.mov .r5 .r25] : List Instr))) s
      (NonceHead W N nl s) := by
  obtain wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  refine WP.block_append (WP.mono (zero16_ok (s := s) (d := tmpO) (by decide) h31 (wW (by decide))
    (wW (by decide))) fun s₁ B₁ => ?_)
  obtain e1 : W + BitVec.ofNat 64 (tmpO + 15) - BitVec.ofNat 64 nl = W + BitVec.ofNat 64 (127 - nl) :=
    Offset.add_ofNat_sub W (a := 127) (by omega_arith)
  obtain e2 : W + BitVec.ofNat 64 (127 - nl) + BitVec.ofNat 64 1 = W + BitVec.ofNat 64 (128 - nl) := by
    rw [Offset.add_add]; congr 2; omega_arith
  refine wp_addi (by decide) (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => wp_li (by decide) fun t₃ u₃ =>
    wp_stb (a := W + BitVec.ofNat 64 (127 - nl)) (by decide) (by decide) ?_ ?_ fun t₄ u₄ =>
    wp_addi (by decide) (by decide) fun t₅ u₅ => cwp_or fun t₆ u₆ => cwp_or fun t₇ u₇ => WP.block_nil ?_
  · rw [BitVec.add_zero, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide),
      B₁.gpr _ (by decide), h31, h25, e1]
  · rw [u₃.wr, u₂.wr, u₁.wr, B₁.wr]; exact wW (by omega_arith)
  obtain r4₄ : t₄.gpr .r4 = W + BitVec.ofNat 64 (127 - nl) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide),
      B₁.gpr _ (by decide), h31, h25, e1]
  refine ⟨s₁, B₁, ?_, ?_, ?_, fun r h0 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, r4₄, e2]
  · rw [u₇.other _ (by decide), u₆.gpr, BitVec.or_self, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), h24]
  · rw [u₇.gpr, BitVec.or_self, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), h25]
  · rw [u₇.other _ h5, u₆.other _ h3, u₅.other _ h4, u₄.gpr, u₃.other _ h0, u₂.other _ h4, u₁.other _ h4,
      B₁.gpr _ (by simp [h0])]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, one_byte, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, B₁.sp]
  · rw [u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr, B₁.lr]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, B₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, B₁.wr]

theorem w127_ne_w112 (W : Addr) : (W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112) = False := by
  simp only [eq_iff_iff, iff_false]
  intro h
  have := congrArg (· - W) h
  simp only [Offset.add_sub_cancel_left] at this
  exact absurd this (by decide)

/-- The last block: `TAGLEN mod 128` into the first byte, `bottom`, and the
last byte's bits cleared. -/
theorem nonceTail_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {t : Nat}
    (ht : t < 2 ^ 64) (h19 : s.gpr .r19 = BitVec.ofNat 64 t) :
    WP isa (.block [.li .r0 15, .logic .and .r3 .r19 .r0, .lsl .r3 .r3 4, .lbz .r4 .r31 tmpO,
        .logic .or .r4 .r4 .r3, .stb .r4 .r31 tmpO, .lbz .r4 .r31 (tmpO + 15), .li .r0 63,
        .logic .and .r3 .r4 .r0, .store .d .r3 .r31 botO, .li .r0 0xc0, .logic .and .r4 .r4 .r0,
        .stb .r4 .r31 (tmpO + 15)]) s fun s₁ =>
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 112)
          (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16)))).writeW (W + BitVec.ofNat 64 288)
          (BitVec.ofNat 64 ((s.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.lr = s.lr ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 1 := in_left (in_off hw (by decide) (by decide))
  obtain w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 1 := in_off hw (by decide) (by decide)
  obtain r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 127) 1 := in_left (in_off hw (by decide) (by decide))
  obtain w₂ : InRegions s.wr (W + BitVec.ofNat 64 127) 1 := in_off hw (by decide) (by decide)
  obtain w₃ : InRegions s.wr (W + BitVec.ofNat 64 288) 8 := in_off hw (by decide) (by decide)
  refine wp_li (by decide) fun t₁ u₁ => cwp_and fun t₂ u₂ => cwp_lsl (by decide) fun t₃ u₃ => ?_
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r3 → t₃.gpr r = s.gpr r := fun r a b => by
    rw [u₃.other _ b, u₂.other _ b, u₁.other _ a]
  obtain r3₃ : t₃.gpr .r3 = BitVec.ofNat 64 (16 * (t % 16)) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h19, and15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht,
      lsl4_ofNat]
  obtain k₃ : t₃.mem = s.mem ∧ t₃.rd = s.rd ∧ t₃.wr = s.wr := ⟨by rw [u₃.mem, u₂.mem, u₁.mem],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  refine wp_lbz (a := W + BitVec.ofNat 64 112) (by decide) (by decide) (by rw [g₃ _ (by decide) (by decide), h31]; rfl)
    (by rw [k₃.2.1, k₃.2.2]; exact r₁) fun t₄ u₄ => cwp_or fun t₅ u₅ =>
    wp_stb (a := W + BitVec.ofNat 64 112) (by decide) (by decide)
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide) (by decide), h31]; rfl)
      (by rw [u₅.wr, u₄.wr, k₃.2.2]; exact w₁) fun t₆ u₆ => ?_
  obtain g₆ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → t₆.gpr r = s.gpr r := fun r a b c => by
    rw [u₆.gpr, u₅.other _ c, u₄.other _ c, g₃ r a b]
  obtain m₆ : t₆.mem = s.mem.writeW (W + BitVec.ofNat 64 112)
      (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16))) := by
    rw [u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.other _ (by decide), r3₃, u₄.mem, k₃.1, or_byte]
  refine wp_lbz (a := W + BitVec.ofNat 64 127) (by decide) (by decide) (by rw [g₆ _ (by decide) (by decide) (by decide), h31]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, k₃.2.1, k₃.2.2]; exact r₂) fun t₇ u₇ =>
    wp_li (by decide) fun t₈ u₈ => cwp_and fun t₉ u₉ =>
    wp_std (a := W + BitVec.ofNat 64 288) (by decide) (by decide)
      (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        g₆ _ (by decide) (by decide) (by decide), h31]; rfl)
      (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.2.2]; exact w₃) fun t₁₀ u₁₀ =>
    wp_li (by decide) fun t₁₁ u₁₁ => cwp_and fun t₁₂ u₁₂ =>
    wp_stb (a := W + BitVec.ofNat 64 127) (by decide) (by decide)
      (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide) (by decide), h31]; rfl)
      (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.2.2]; exact w₂)
      fun t₁₃ u₁₃ => WP.block_nil ?_
  obtain b127 : t₆.mem (W + BitVec.ofNat 64 127) = s.mem (W + BitVec.ofNat 64 127) := by
    rw [m₆, WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (w127_ne_w112 W)]
  obtain r4₇ : t₇.gpr .r4 = BitVec.setWidth 64 (s.mem (W + BitVec.ofNat 64 127)) := by rw [u₇.gpr, b127]
  refine ⟨?_, fun r a b c => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₃.mem, u₁₂.gpr, u₁₁.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), r4₇, and_byte, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.gpr, u₈.gpr,
      u₈.other _ (by decide), r4₇, and63, u₉.mem, u₈.mem, u₇.mem, m₆]
  · rw [u₁₃.gpr, u₁₂.other _ c, u₁₁.other _ a, u₁₀.gpr, u₉.other _ b, u₈.other _ a, u₇.other _ c, g₆ r a b c]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, k₃.2.1]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.2.2]

theorem nonceBlock_ok {K W : Addr} (L : Lay K W) {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {N : Addr} {nl t : Nat} (h24 : s.gpr .r24 = N) (h25 : s.gpr .r25 = BitVec.ofNat 64 nl)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64) (hB : Buf W s N nl) :
    WP isa nonceBlock s (NoncePost W t (bytesAt s.mem N nl) s) := by
  unfold nonceBlock
  refine WP.seq (WP.mono (nonceHead_ok h31 hw h1 h15 h24 h25) fun s₂ H => ?_)
  obtain ⟨s₁, B₁, x11₂, x12₂, x13₂, g₂, m₂, sp₂, lr₂, rd₂, wr₂⟩ := H
  have f₁ := B₁.frame
  have z₁ := B₁.val
  obtain hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂]; exact hB.rd
  obtain hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂]; exact Proof.AesGcm.PPC64LE.covers_off hw (by omega_arith) (by decide)
  obtain hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega_arith))
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [show W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) by
      rw [Offset.add_add]; congr 2; omega_arith]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega_arith),
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  refine WP.seq (WP.mono (copyLoop_ok s₂ ⟨x12₂, x11₂, x13₂, h1, by omega_arith, hS₂, hD₂, hSD⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, o₃⟩ := h₃
  obtain ⟨rd₃, wr₃, sp₃, lr₃⟩ := o₃.keeps
  rw [eN] at m₃
  obtain h31₃ : s₃.gpr .r31 = W := by
    rw [o₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide), h31]
  obtain h19₃ : s₃.gpr .r19 = BitVec.ofNat 64 t := by
    rw [o₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide), h19]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂]
  obtain fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact contains_pre _ (by omega_arith))
  refine WP.mono (nonceTail_ok h31₃ (by rw [wr₃']; exact hw) ht h19₃) fun s₄ ⟨m₄, g₄, sp₄, lr₄, rd₄, wr₄⟩ => ?_
  -- the bytes at `W + tmpO`, step by step
  obtain hlen : (bytesAt s.mem N nl).length = nl := length_bytesAt _ _ _
  obtain L₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := bytesAt_of_zero z₁
  obtain e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega_arith]
  obtain e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega_arith]
  obtain L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - nl) ++ [1] ++ Spec.Ocb.zeros (nl) := by
    rw [m₂, e127, bytesAt_writeW8_at _ _ _ (by omega_arith) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - nl) 16 = 15 - nl by omega_arith,
      show 16 - (15 - nl + 1) = nl by omega_arith]
  obtain L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega_arith) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega_arith]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_singleton, List.append_assoc]
    simp only [show min (16 - nl) (15 - nl) = 15 - nl by omega_arith, show 16 - nl - (15 - nl) = 1 by omega_arith,
      show 16 - (15 - nl) = nl + 1 by omega_arith]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - nl - 16 = 0 by omega_arith, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ nl + 1 by simp), show nl - (nl + 1 - 1) = 0 by omega_arith,
      List.append_nil]
  obtain L₃d : ∀ k < 16, (bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega_arith) (by rw [hlen]; omega_arith) hk
      rw [hlen] at this; rw [L₃]; exact this
  obtain b0 : s₃.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  obtain e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add W 112 15).symm
  obtain b15 : s₃.mem (W + BitVec.ofNat 64 127) = nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  obtain fr288 : ∀ (M : Mem) (v : BitVec 64), Frame [⟨W + BitVec.ofNat 64 288, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 288) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₄, b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr288 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 288) (k := 8) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega_arith, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega_arith]
        exact L₃d (k + 1) hk
  obtain hlen16 := length_bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16
  obtain f₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
    ((f₁.trans f₂).mono (fun r hr => by simp at hr; simp [hr])).trans ((fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact Offset.sub_base _ (by omega_arith)⟩))
  refine ⟨?_, ?_, ?_, fun r hr => ?_, by rw [sp₄, sp₃, sp₂], by rw [lr₄, lr₃, lr₂], by rw [rd₄, rd₃, rd₂],
    by rw [wr₄, wr₃']⟩
  · rw [m₄]
    refine ((f₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · show blockAtMem s₄.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega_arith) (by omega_arith) hk]
  · show s₄.mem.readW (W + BitVec.ofNat 64 288) 64 = _
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15, Proof.Ocb.nonceN_bottom _ _ (by omega_arith) (by omega_arith)]
  · simp only [nonceRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ r hr.1 hr.2.1 hr.2.2.1, o₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2,
      g₂ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1]

end VG.Proof.AesOcb.PPC64LE

end

end


/-!
# AES-OCB on PPC64LE: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `encOne_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`). As on AArch64 (`Proof/AesOcb/AArch64/LNtz.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxInv ctxLstar)
open VG.Proof.Ocb (blockAtMem_frame)

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hR])]

theorem ctxLstar_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W D n) m m') : ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

/-- What `nonce` writes: `[16, 128)` and `[256, 2560)` of `W`. -/
abbrev nonceR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 112⟩, wB W]

theorem nonceR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (nonceR W) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact in_mutA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- A part of `W` within `[16, 128)` or from 256 on, as a part `nonce` writes. -/
theorem in_nonceR {W : Addr} {d k : Nat} (h : (16 ≤ d ∧ d + k ≤ 128) ∨ (256 ≤ d ∧ d + k ≤ 2560)) :
    ∃ r' ∈ nonceR W, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W h₁ (by omega_using [h₂])⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB h₁ h₂⟩

/-- What `nonce` leaves. -/
structure NonceOk (V : Reg → BitVec 64) (sp : Addr) (o : Block) (s s' : State) : Prop where
  env : Env V sp s'
  frame : Frame (nonceR (V .r31)) s.mem s'.mem
  ofs : blockAtMem s'.mem (V .r31 + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (V .r31 + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (V .r31 + BitVec.ofNat 64 d) = blockAtMem s.mem (V .r31 + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {s : State} (E : Env V sp s)
    {N : Addr} {nl t : Nat} (h24 : s.gpr .r24 = N) (h25 : s.gpr .r25 = BitVec.ofNat 64 nl)
    (h19 : V .r19 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64) (hB : Buf (V .r31) s N nl)
    {D : Addr} {n : Nat} (hKD : (⟨V .r29, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    WP isa nonce s (NonceOk V sp (Spec.Ocb.offset0 (ctxCiph s.mem (V .r29) R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E.r31 E.perm.w h24 h25 (E.r19.trans h19) h1 h15 ht hB) fun s₁ P₁ => ?_)
  obtain E₁ : Env V sp s₁ := E.others P₁.gpr P₁.sp P₁.rd P₁.wr
  obtain F₁ : Frame (nonceR (V .r31)) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  refine WP.seq (WP.mono (encOne_ok L hR h28 E₁ (d := tmpO) (by decide)) fun s₂ P₂ => ?_)
  obtain E₂ : Env V sp s₂ := P₂.env E₁
  obtain F₂ : Frame (nonceR (V .r31)) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  obtain ktop : blockAtMem s₂.mem (V .r31 + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem (V .r29) R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [P₂.enc0, P₁.blk]
    exact congrFun (ctxCiph_mut L hKD (nonceR_mut F₁) hR) _
  obtain hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  obtain bot₂ : s₂.mem.readW (V .r31 + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨V .r31 + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), P₁.bot]
  refine WP.mono (offset0_ok L E₂.r31 E₂.perm.w hbv bot₂) fun s₃ P₃ => ?_
  refine ⟨E₂.others P₃.gpr P₃.sp P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_nonceR (.inl ⟨by decide, by decide⟩)
    · exact in_nonceR (.inr ⟨by decide, by decide⟩)
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega_arith) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega_using [h₂]) (by omega_using [h₂]) (by decide)
        · exact L.w_w (by omega_using [h₂]) (by omega_using [h₂]) (by decide)),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega_using [h₂]) (by omega_using [h₂]) (by decide))]

end VG.Proof.AesOcb.PPC64LE
