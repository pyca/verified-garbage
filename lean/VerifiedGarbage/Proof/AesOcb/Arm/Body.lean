module

public import VerifiedGarbage.Proof.AesOcb.Arm.HashChunk
public import VerifiedGarbage.Proof.AesOcb.Arm.Words
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesOcb.Arm.RestTag
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Ocb.Bytes
public import VerifiedGarbage.Proof.AesOcb.Arm.Calls
import VerifiedGarbage.Proof.AesOcb.Arm.NonceBlock
import VerifiedGarbage.Proof.Ocb.Stretch32
public import VerifiedGarbage.Proof.Ocb.Stretch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `AesOcb.Arm.Nonce`, which the modules that import this one used -/

section

/-! ### `AesOcb.Arm.Offset0`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
four byte-reversed words, computes the last two words of `Stretch`
(`Proof.Ocb.stretch_words32`), shifts the six words left by `bottom` in six
masked stages (`stage_ok`, `stage32_ok`, `Proof.Ocb.shl_stages`), and stores
the top four, byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`), as
on AArch64 (`Proof.AesOcb.AArch64.offset0_ok`) with 32-bit words.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask32 shl6 shl6_32 bit32 bit32_0)
open VG.Proof.AesGcm.Arm (mem_store rd_store wr_store sp_store gpr_store)

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- The six words of `Stretch`, high to low. -/
abbrev words (s : State) : BitVec 192 :=
  s.gpr .r0 ++ s.gpr .r1 ++ s.gpr .r2 ++ s.gpr .r3 ++ s.gpr .r4 ++ s.gpr .r5

/-- The registers a stage writes. -/
abbrev stageRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r7, .r8]

/-- The mask of a stage in `r7`. -/
theorem stageMask_ok (s : State) {k v : Nat} (hk : k ≤ 5) (hv : v < 64) (h6 : s.gpr .r6 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stageMask k) s = some s' ∧
      s'.gpr .r7 = (0 : BitVec 32) - (if v.testBit k then 1 else 0) ∧ Ran [.r7, .r8] s.mem s s' := by
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨_, by orun [stageMask], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    simp only [gpr_setReg, ite_true, h6, bit32_0 hv]
    rfl
  · have h1 : 1 ≤ k := by omega_using [hk0]
    obtain h31 : k ≤ 31 := by omega_using [hk]
    refine ⟨_, by orun [stageMask, hk0, h1, h31], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h6, bit32 hv]
    rfl

/-- The words of a stage. -/
def stageWords (a : Nat) : List Instr :=
  ([(Reg.r0, Reg.r1), (.r1, .r2), (.r2, .r3), (.r3, .r4), (.r4, .r5)].flatMap fun (x, y) =>
    [.mov .r8 (.shifted x .lsl a), .dp .orr .r8 .r8 (.shifted y .lsr (32 - a))] ++ sel x) ++
  [.mov .r8 (.shifted .r5 .lsl a)] ++ sel .r5

theorem stage_eq (k a : Nat) : stage k a = stageMask k ++ stageWords a := by
  simp only [stage, stageWords, List.append_assoc]

/-- The words of a stage, with the mask in `r7`. -/
theorem stageWords_ok (s : State) {a : Nat} (ha : 0 < a) (ha' : a < 32) (b : Bool)
    (h7 : s.gpr .r7 = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ s', runBlock isa (stageWords a) s = some s' ∧ words s' = shlIf b a (words s) ∧
      Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r8] s.mem s s' := by
  have h1 : 1 ≤ a := ha
  obtain h31 : a ≤ 31 := by omega_using [ha']
  obtain h1' : 1 ≤ 32 - a := by omega_using [ha']
  obtain h31' : 32 - a ≤ 31 := by omega_using [ha]
  refine ⟨_, by orun [stageWords, sel, h1, h31, h1', h31', List.flatMap_cons, List.flatMap_nil], ?_, by rfl,
    by others_tac, by rfl, by rfl, by rfl⟩
  simp only [words, gpr_setReg, ite_true, ite_false, reduceCtorEq, h7]
  simp only [sel_mask32]
  cases b
  · rfl
  · exact shl6 _ _ _ _ _ _ ha ha'

/-- The words of the last stage. -/
def stageWords32 : List Instr :=
  ([(Reg.r0, Reg.r1), (.r1, .r2), (.r2, .r3), (.r3, .r4), (.r4, .r5)].flatMap fun (x, y) =>
    [.mov .r8 (.reg y)] ++ sel x) ++
  [.mov .r8 (Impl.AesGcm.Arm.imm 0)] ++ sel .r5

theorem stage32_eq : stage32 = stageMask 5 ++ stageWords32 := by
  simp only [stage32, stageWords32, List.append_assoc]

theorem stageWords32_ok (s : State) (b : Bool) (h7 : s.gpr .r7 = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ s', runBlock isa stageWords32 s = some s' ∧ words s' = shlIf b 32 (words s) ∧
      Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r8] s.mem s s' := by
  refine ⟨_, by orun [stageWords32, sel, List.flatMap_cons, List.flatMap_nil], ?_, by rfl,
    by others_tac, by rfl, by rfl, by rfl⟩
  simp only [words, gpr_setReg, ite_true, ite_false, reduceCtorEq, h7, sel_mask32]
  cases b
  · rfl
  · exact shl6_32 _ _ _ _ _ _

/-- A stage, from `bottom` in `r6`. -/
theorem stage_ok (s : State) {k a v : Nat} (hk : k ≤ 5) (ha : 0 < a) (ha' : a < 32) (hv : v < 64)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧ words s' = shlIf (v.testBit k) a (words s) ∧
      Ran stageRegs s.mem s s' := by
  obtain ⟨s₁, run₁, h7, R₁⟩ := stageMask_ok s hk hv h6
  obtain ⟨s₂, run₂, w₂, R₂⟩ := stageWords_ok s₁ ha ha' _ h7
  refine ⟨s₂, by rw [stage_eq, runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_⟩
  · have e : words s₁ = words s := by
      simp only [words, R₁.gpr .r0 (by decide), R₁.gpr .r1 (by decide), R₁.gpr .r2 (by decide),
        R₁.gpr .r3 (by decide), R₁.gpr .r4 (by decide), R₁.gpr .r5 (by decide)]
    rw [w₂, e]
  · refine ⟨by rw [R₂.mem, R₁.mem], fun r hr => ?_, by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd], by rw [R₂.wr, R₁.wr]⟩
    simp only [stageRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]

theorem stage32_ok (s : State) {v : Nat} (hv : v < 64) (h6 : s.gpr .r6 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa stage32 s = some s' ∧ words s' = shlIf (v.testBit 5) 32 (words s) ∧
      Ran stageRegs s.mem s s' := by
  obtain ⟨s₁, run₁, h7, R₁⟩ := stageMask_ok s (k := 5) (by decide) hv h6
  obtain ⟨s₂, run₂, w₂, R₂⟩ := stageWords32_ok s₁ _ h7
  refine ⟨s₂, by rw [stage32_eq, runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_⟩
  · have e : words s₁ = words s := by
      simp only [words, R₁.gpr .r0 (by decide), R₁.gpr .r1 (by decide), R₁.gpr .r2 (by decide),
        R₁.gpr .r3 (by decide), R₁.gpr .r4 (by decide), R₁.gpr .r5 (by decide)]
    rw [w₂, e]
  · refine ⟨by rw [R₂.mem, R₁.mem], fun r hr => ?_, by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd], by rw [R₂.wr, R₁.wr]⟩
    simp only [stageRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : Others [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The head of `offset0`: `Stretch` in `r0`–`r5` and `bottom` in `r6`. -/
def off0Head : List Instr :=
  [.ldr .r0 .r11 tmpO, .ldr .r1 .r11 (tmpO + 4), .ldr .r2 .r11 (tmpO + 8), .ldr .r3 .r11 (tmpO + 12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .mov .r4 (.shifted .r0 .lsl 8), .dp .orr .r4 .r4 (.shifted .r1 .lsr 24), .dp .eor .r4 .r4 (.reg .r0),
   .mov .r5 (.shifted .r1 .lsl 8), .dp .orr .r5 .r5 (.shifted .r2 .lsr 24), .dp .eor .r5 .r5 (.reg .r1),
   .ldr .r6 .r11 botO]

/-- The tail of `offset0`: the top four words, byte-reversed, to `W + ofsO`
and `W + o0O`. -/
def off0Tail : List Instr :=
  [.rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .str .r0 .r11 ofsO, .str .r1 .r11 (ofsO + 4), .str .r2 .r11 (ofsO + 8), .str .r3 .r11 (ofsO + 12),
   .str .r0 .r11 o0O, .str .r1 .r11 (o0O + 4), .str .r2 .r11 (o0O + 8), .str .r3 .r11 (o0O + 12)]

theorem offset0_eq : offset0 = off0Head ++ stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++
    stage32 ++ off0Tail := by
  simp only [offset0, off0Head, off0Tail, List.append_assoc, List.cons_append, List.nil_append]

theorem offset0_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {v : Nat} (hv : v < 64)
    (hbot : s.mem.readW (State.addr p.W + BitVec.ofNat 64 botO) 32 = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      Off0Post (State.addr p.W)
        ((stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  obtain ew : ∀ k, k < 2560 → State.addr (p.W + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 k :=
    fun k hk => L.wA hk
  obtain e112 := ew 112 (by decide)
  obtain e116 := ew 116 (by decide)
  obtain e120 := ew 120 (by decide)
  obtain e124 := ew 124 (by decide)
  obtain e208 := ew 208 (by decide)
  obtain r112 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 112) 4 := E.perm.wR (by decide)
  obtain r116 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 116) 4 := E.perm.wR (by decide)
  obtain r120 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 120) 4 := E.perm.wR (by decide)
  obtain r124 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 124) 4 := E.perm.wR (by decide)
  obtain r208 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 208) 4 := E.perm.wR (by decide)
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, r6₁, R₁⟩ : ∃ s₁, runBlock isa off0Head s = some s₁ ∧
      words s₁ = stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .r6 = BitVec.ofNat 32 v ∧ Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r6] s.mem s s₁ := by
    refine ⟨_, by orun [off0Head, E.r11, e112, e116, e120, e124, e208, r112, r116, r120, r124, r208], ?_, ?_,
      by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [words, gpr_setReg, ite_true, ite_false, reduceCtorEq, rev_eq]
      obtain hb : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
          byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 112) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 116) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 120) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 124) 32) := by
        have := Proof.Cmac.ofBytes_rev4 s.mem (State.addr p.W + BitVec.ofNat 64 112)
        simp only [Offset.add_add] at this
        exact this
      rw [stretch, hb, Proof.Ocb.stretch_words32]
    · simp only [gpr_setReg, ite_true, hbot]
  obtain keep : ∀ {t t' : State}, Ran stageRegs t.mem t t' → t.gpr .r6 = BitVec.ofNat 32 v →
      t'.gpr .r6 = BitVec.ofNat 32 v := fun R h => by rw [R.gpr _ (by decide), h]
  obtain ⟨s₂, run₂, w₂, R₂⟩ := stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv r6₁
  obtain ⟨s₃, run₃, w₃, R₃⟩ := stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv (keep R₂ r6₁)
  obtain ⟨s₄, run₄, w₄, R₄⟩ := stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep R₃ (keep R₂ r6₁))
  obtain ⟨s₅, run₅, w₅, R₅⟩ := stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep R₄ (keep R₃ (keep R₂ r6₁)))
  obtain ⟨s₆, run₆, w₆, R₆⟩ := stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep R₅ (keep R₄ (keep R₃ (keep R₂ r6₁))))
  obtain ⟨s₇, run₇, w₇, R₇⟩ := stage32_ok s₆ hv (keep R₆ (keep R₅ (keep R₄ (keep R₃ (keep R₂ r6₁)))))
  obtain hw7 : words s₇ = stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  obtain hO : s₇.gpr .r0 ++ s₇.gpr .r1 ++ s₇.gpr .r2 ++ s₇.gpr .r3 =
      (stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← Proof.Ocb.top4 _ _ _ _ (s₇.gpr .r4) (s₇.gpr .r5), show s₇.gpr .r0 ++ s₇.gpr .r1 ++ s₇.gpr .r2 ++
      s₇.gpr .r3 ++ s₇.gpr .r4 ++ s₇.gpr .r5 = words s₇ from rfl, hw7, Proof.Ocb.offset_shl _ (by omega_using [hv])]
  obtain hm₇ : s₇.mem = s.mem := by rw [R₇.mem, R₆.mem, R₅.mem, R₄.mem, R₃.mem, R₂.mem, R₁.mem]
  obtain hsp₇ : s₇.sp = s.sp := by rw [R₇.sp, R₆.sp, R₅.sp, R₄.sp, R₃.sp, R₂.sp, R₁.sp]
  obtain hrd₇ : s₇.rd = s.rd := by rw [R₇.rd, R₆.rd, R₅.rd, R₄.rd, R₃.rd, R₂.rd, R₁.rd]
  obtain hwr₇ : s₇.wr = s.wr := by rw [R₇.wr, R₆.wr, R₅.wr, R₄.wr, R₃.wr, R₂.wr, R₁.wr]
  obtain g₁₇ : Others [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s s₇ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain h' : r ∉ stageRegs := by
      simp [stageRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2]
    rw [R₇.gpr r h', R₆.gpr r h', R₅.gpr r h', R₄.gpr r h', R₃.gpr r h', R₂.gpr r h',
      R₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  obtain r11₇ : s₇.gpr .r11 = p.W := by rw [g₁₇ _ (by decide), E.r11]
  obtain P₇ : Perm p s₇ := E.perm.of_eq hrd₇ hwr₇
  obtain ww : ∀ d, d + 4 ≤ 2560 → InRegions s₇.wr (State.addr p.W + BitVec.ofNat 64 d) 4 := fun d h => P₇.wW h
  obtain e16 := ew 16 (by decide)
  obtain e20 := ew 20 (by decide)
  obtain e24 := ew 24 (by decide)
  obtain e28 := ew 28 (by decide)
  obtain e224 := ew 224 (by decide)
  obtain e228 := ew 228 (by decide)
  obtain e232 := ew 232 (by decide)
  obtain e236 := ew 236 (by decide)
  obtain w16 := ww 16 (by decide)
  obtain w20 := ww 20 (by decide)
  obtain w24 := ww 24 (by decide)
  obtain w28 := ww 28 (by decide)
  obtain w224 := ww 224 (by decide)
  obtain w228 := ww 228 (by decide)
  obtain w232 := ww 232 (by decide)
  obtain w236 := ww 236 (by decide)
  obtain ⟨s₈, run₈, m₈, R₈⟩ : ∃ s₈, runBlock isa off0Tail s₇ = some s₈ ∧
      s₈.mem = Proof.Cmac.store4 (Proof.Cmac.store4 s₇.mem (State.addr p.W + BitVec.ofNat 64 16)
          (byteRev32 (s₇.gpr .r0)) (byteRev32 (s₇.gpr .r1)) (byteRev32 (s₇.gpr .r2)) (byteRev32 (s₇.gpr .r3)))
        (State.addr p.W + BitVec.ofNat 64 224)
          (byteRev32 (s₇.gpr .r0)) (byteRev32 (s₇.gpr .r1)) (byteRev32 (s₇.gpr .r2)) (byteRev32 (s₇.gpr .r3)) ∧
      Ran [.r0, .r1, .r2, .r3] s₈.mem s₇ s₈ := by
    refine ⟨_, by orun [off0Tail, r11₇, e16, e20, e24, e28, e224, e228, e232, e236, w16, w20, w24, w28, w224, w228,
      w232, w236], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, rev_eq, Proof.Cmac.store4,
      Offset.add_add]
  obtain val : ∀ (M : Mem) (C : Addr), blockAtMem (Proof.Cmac.store4 M C
      (byteRev32 (s₇.gpr .r0)) (byteRev32 (s₇.gpr .r1)) (byteRev32 (s₇.gpr .r2)) (byteRev32 (s₇.gpr .r3))) C =
      (stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := fun M C => by
    rw [blockAtMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, ← hO]
    exact Proof.Cmac.ofBytes_toBytes _
  refine ⟨s₈, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [R₈.sp, hsp₇], by rw [R₈.rd, hrd₇], by rw [R₈.wr, hwr₇]⟩
  · rw [offset0_eq, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  · rw [m₈, ← hm₇]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp [ofsO])).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp [o0O]))
  · rw [m₈, Proof.Ocb.blockAtMem_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 224) (k := 16) (.inl (by decide)) (by decide) (by decide))]
    exact val _ _
  · rw [m₈]; exact val _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₈.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₁₇ r (by simp [hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: `Offset_0` (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers it in
place (`encOne_ok`) into `Ktop`, and takes `Offset_0` from `Stretch`
(`offset0_ok`): §4.2's `Offset_0` (`Proof.Ocb.offset0_eq`), at `W + ofsO` and
`W + o0O` (`nonce_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- What `nonce` writes. -/
abbrev nonceR (p : Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 o0O, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP]

/-- What `nonce` leaves, from `t`. -/
structure NonceOut (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (nonceR p) t.mem t'.mem
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl)
  o0 : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl)

theorem nonce_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (h4 : t.gpr .r4 = p.N) (h5 : t.gpr .r5 = BitVec.ofNat 32 p.nl) :
    WP isa nonce t (NonceOut p t) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E A h4 h5) fun t₁ N₁ => ?_)
  have E₁ : Env p t₁ := E.of_others N₁.gpr N₁.sp N₁.rd N₁.wr
  refine WP.seq (WP.mono (encOne_ok L E₁ (d := tmpO) (by decide) (by decide)) fun t₂ C₂ => ?_)
  have E₂ := C₂.env E₁
  -- `bottom`, kept through the call
  have hv : ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat < 64 :=
    BitVec.isLt _
  have hbot : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 botO) 32 =
      BitVec.ofNat 32 ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat := by
    rw [C₂.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide), N₁.bot]
  obtain ⟨t₃, run₃, O₃⟩ := offset0_ok L E₂ hv hbot
  refine WP.of_runBlock ⟨t₃, run₃, ?_⟩
  have hK : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
      Spec.Ocb.aesWith p.R (sched p t.mem) (Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl) &&&
        ~~~(63 : Block)) := by
    have := C₂.out 0 (by decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at this
    rw [this, encF_ciph, N₁.blk]
    refine congrArg (fun w => Spec.Ocb.aesWith p.R w _) ?_
    exact Proof.Cmac.bytesAt_frame N₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (L.k_w' (d := tmpO) (k := 16) (by decide)).sub_left
          (Region.sub_prefix (show 16 * (p.R + 1) ≤ 256 by have := L.rounds_le; omega_using [this]))
      · exact (L.k_w' (d := botO) (k := 4) (by decide)).sub_left
          (Region.sub_prefix (show 16 * (p.R + 1) ≤ 256 by have := L.rounds_le; omega_using [this]))) (by have := L.rounds_le; omega_using [this])
  have hO : (stretch (blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb'
      (64 - ((Proof.Ocb.nonceN p.tl (bytesAt t.mem (State.addr p.N) p.nl)).extractLsb' 0 6).toNat) 128 =
      Spec.Ocb.offset0 (Spec.Ocb.aesWith p.R (sched p t.mem)) p.tl (bytesAt t.mem (State.addr p.N) p.nl) := by
    rw [hK, Proof.Ocb.offset0_eq]; rfl
  refine ⟨E₂.of_others O₃.gpr O₃.sp O₃.rd O₃.wr, by rw [O₃.rd, C₂.rd, N₁.rd], by rw [O₃.wr, C₂.wr, N₁.wr], ?_,
    by rw [O₃.ofs, hO], by rw [O₃.o0, hO]⟩
  exact ((N₁.frame.mono (by simp)).trans (C₂.frame.mono (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [tmpO]))).trans (O₃.frame.mono (by simp))

end VG.Proof.AesOcb.Arm

end

end

/-! ### `AesOcb.Arm.Whole`, which only this module used -/

section

/-! ### `AesOcb.Arm.Pass`, which only this module used -/

section

/-!
# AES-OCB on ARMv7: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`: for block `i` it computes
`Offset_{i+1}` (`lNtz_ok`, `xorB_wp`), then runs `body` on the block, which
replaces it with `fB` of it and the offset, and the checksum with `fC` of
them (`BodyOk`: `xorOfs`, `addCk ++ xorOfs`, `xorOfs ++ addCk`); `pass_ok`
gives the blocks and the checksum after all `m`, as on AArch64
(`Proof.AesOcb.AArch64.pass_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_ne' z_subFlags dec32 z_dec)

/-- The data block at offset `k` of the data, as a 64-bit address. -/
theorem dA {p : Prm} (L : Lay p) {k : Nat} (h : k + 16 ≤ p.n) :
    State.addr (p.D + BitVec.ofNat 32 k) = State.addr p.D + BitVec.ofNat 64 k :=
  addr_add (by have := L.dw; omega_arith)

/-- What a body does to the block at `B` (in `r4`) and the checksum, with the
offset at `W + ofsO`. -/
def BodyOk (p : Prm) (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ (t : State) (k : Nat), Env p t → t.gpr .r4 = p.D + BitVec.ofNat 32 k → k + 16 ≤ p.n →
    WP isa (.block body) t fun t' =>
      blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 k) =
        fB (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k))
          (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)) ∧
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = fC (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO))
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k)) (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)) ∧
      Frame [⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t'.mem ∧
      Others [.r0, .r1] t t' ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr

section
variable {p : Prm} (L : Lay p)
include L

theorem bW {k : Nat} (h : k + 16 ≤ p.n) :
    (⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ :=
  (L.d_w' (by decide)).sub_left (Offset.sub_base _ h)

theorem bO {k : Nat} (h : k + 16 ≤ p.n) :
    (⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ :=
  (L.d_w' (by decide)).sub_left (Offset.sub_base _ h)

/-- `(r4) ⊕= W + ofsO`. -/
theorem xorOfs_wp {t : State} (E : Env p t) {k : Nat} (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 k)
    (hk : k + 16 ≤ p.n) :
    WP isa (.block xorOfs) t (Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.D + BitVec.ofNat 64 k)
      (State.addr p.D + BitVec.ofNat 64 k) (State.addr p.W + BitVec.ofNat 64 ofsO)) t) := by
  have fw := L.ww
  have fd := L.dw
  obtain e := dA L hk
  have := xorB_wp (s := t) (pb := .r4) (qb := .r11) (cb := .r4) (pd := 0) (qd := ofsO) (cd := 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) (by rw [E.r11]; simp only [ofsO]; omega_arith)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith)
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega_arith)))
    (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega_arith))
  rw [h4, E.r11, e, BitVec.add_zero] at this
  exact this

/-- `W + ckO ⊕= (r4)`. -/
theorem addCk_wp {t : State} (E : Env p t) {k : Nat} (h4 : t.gpr .r4 = p.D + BitVec.ofNat 32 k)
    (hk : k + 16 ≤ p.n) :
    WP isa (.block addCk) t (Ran [.r0, .r1] (Proof.Cmac.xor4Mem t.mem (State.addr p.W + BitVec.ofNat 64 ckO)
      (State.addr p.W + BitVec.ofNat 64 ckO) (State.addr p.D + BitVec.ofNat 64 k)) t) := by
  have fw := L.ww
  have fd := L.dw
  obtain e := dA L hk
  have := xorB_wp (s := t) (pb := .r11) (qb := .r4) (cb := .r11) (pd := ckO) (qd := 0) (cd := ckO) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [E.r11]; simp only [ckO]; omega_arith)
    (by rw [h4, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) (by rw [E.r11]; simp only [ckO]; omega_arith)
    (by rw [E.r11]; exact E.perm.wCR (by decide))
    (by rw [h4, e, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_left (Proof.AesGcm.Arm.covers_off E.perm.d hk (by omega_arith)))
    (by rw [E.r11]; exact E.perm.wC (by decide))
  rw [h4, E.r11, e, BitVec.add_zero] at this
  exact this

theorem xorOfs_ok : BodyOk p xorOfs (fun b o => b ^^^ o) (fun c _ _ => c) := by
  intro t k E h4 hk
  refine WP.mono (xorOfs_wp L E h4 hk) fun t' R => ⟨?_, ?_, ?_, R.gpr, R.sp, R.rd, R.wr⟩
  · rw [R.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bO L hk))]
  · rw [R.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (bW L hk).symm)]
  · rw [R.mem]; exact (Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp)

theorem sealPre_ok : BodyOk p (addCk ++ xorOfs) (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := by
  intro t k E h4 hk
  refine WP.block_append (WP.mono (addCk_wp L E h4 hk) fun t₁ R₁ => ?_)
  obtain E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  obtain fr₁ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  refine WP.mono (xorOfs_wp L E₁ (by rw [R₁.gpr _ (by decide), h4]) hk) fun t₂ R₂ =>
    ⟨?_, ?_, ?_, fun r hr => by rw [R₂.gpr r hr, R₁.gpr r hr], by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd],
      by rw [R₂.wr, R₁.wr]⟩
  · rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bO L hk)),
      blockAtMem_frame fr₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact bW L hk),
      blockAtMem_frame fr₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))]
  · rw [R₂.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (bW L hk).symm), R₁.mem,
      blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bW L hk).symm)]
  · rw [R₂.mem]
    exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))

theorem openPost_ok : BodyOk p (xorOfs ++ addCk) (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := by
  intro t k E h4 hk
  refine WP.block_append (WP.mono (xorOfs_wp L E h4 hk) fun t₁ R₁ => ?_)
  obtain E₁ : Env p t₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  obtain fr₁ : Frame [⟨State.addr p.D + BitVec.ofNat 64 k, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain b₁ : blockAtMem t₁.mem (State.addr p.D + BitVec.ofNat 64 k) =
      blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k) ^^^ blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) := by
    rw [R₁.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bO L hk))]
  refine WP.mono (addCk_wp L E₁ (by rw [R₁.gpr _ (by decide), h4]) hk) fun t₂ R₂ =>
    ⟨?_, ?_, ?_, fun r hr => by rw [R₂.gpr r hr, R₁.gpr r hr], by rw [R₂.sp, R₁.sp], by rw [R₂.rd, R₁.rd],
      by rw [R₂.wr, R₁.wr]⟩
  · rw [R₂.mem, blockAtMem_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact bW L hk), b₁]
  · rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (bW L hk).symm), b₁,
      blockAtMem_frame fr₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (bW L hk).symm)]
  · rw [R₂.mem]
    exact (fr₁.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))

end

/-- The registers a pass writes. -/
abbrev passRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr]

/-- What a pass writes, over `m` blocks. -/
abbrev passR (p : Prm) (m : Nat) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩, ⟨State.addr p.D, 16 * m⟩]

/-- A pass over the `m` whole blocks of the data (`X k` at its start, `t₀`),
after `i` of them. -/
structure PassInv (p : Prm) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame (passR p m) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * i)
  r6 : t.gpr .r6 = BitVec.ofNat 32 (i + 1)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (m - i)
  ofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l i
  ck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : Others passRegs t₀ t

theorem pass_step {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    (hm : 16 * m ≤ p.n) {t₀ t : State} {i : Nat} (hi : i < m) (P : PassInv p m O0 l X fB ckF t₀ t i) :
    WP isa (.seq nextOffset (.block (body ++ nextBlock))) t fun t' =>
      PassInv p m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.z = decide (i + 1 = m) := by
  have fw := L.ww
  have n32 := L.n_lt
  have E := P.env
  unfold nextOffset
  refine WP.seq (WP.seq (WP.mono (lNtz_ok L E (i := i + 1) (by omega_arith) (by omega_arith) P.r6 P.l0) fun t₁ P₁ => ?_))
  obtain E₁ : Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  refine WP.mono (xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11) (pd := ofsO) (qd := lO) (cd := ofsO)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [E₁.r11]; simp only [ofsO]; omega_arith) (by rw [E₁.r11]; simp only [lO]; omega_arith)
    (by rw [E₁.r11]; simp only [ofsO]; omega_arith) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_
  rw [E₁.r11] at R₂
  obtain E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  obtain g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    obtain h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', P₁.gpr r hr]
  obtain fW₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  obtain kD₂ : ∀ {k : Nat}, k + 16 ≤ p.n → blockAtMem t₂.mem (State.addr p.D + BitVec.ofNat 64 k) =
      blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 k) := fun hk =>
    blockAtMem_frame fW₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hk)
  obtain ofs₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l (i + 1) := by
    rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inl (by decide)) (by decide) (by decide))),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      P.ofs, P₁.val]
    rfl
  obtain ck₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF i := by
    rw [blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.ck]
  obtain Bi₂ : blockAtMem t₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) = X i := by
    rw [kD₂ (by omega_arith), P.blk i hi]; simp
  -- the body
  refine WP.block_append (WP.mono (hB t₂ (16 * i) E₂ (by rw [g₂ _ (by decide), P.r4]) (by omega_arith))
    fun t₃ ⟨blk₃, ck₃, fr₃, g₃, sp₃, rd₃, wr₃⟩ => ?_)
  obtain g₃' : ∀ r, r ∉ ntzRegs → t₃.gpr r = t.gpr r := fun r hr => by
    obtain h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [g₃ r h', g₂ r hr]
  obtain r4₃ : t₃.gpr .r4 = p.D + BitVec.ofNat 32 (16 * i) := by rw [g₃' _ (by decide), P.r4]
  obtain r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (m - i) := by rw [g₃' _ (by decide), P.r5]
  obtain r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (i + 1) := by rw [g₃' _ (by decide), P.r6]
  refine WP.of_runBlock ⟨_, by orun [nextBlock, r4₃, r5₃, r6₃], ?_⟩
  obtain kB₃ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.D + BitVec.ofNat 64 (16 * i), 16⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩ →
      blockAtMem t₃.mem Q = blockAtMem t₂.mem Q := fun h₁ h₂ =>
    blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂)
  refine ⟨⟨E₂.of_others (rs := [.r0, .r1, .r4, .r5, .r6]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ↓reduceIte]
      exact g₃ r (by simp [hr.1, hr.2.1])) (by simp [sp_setReg, Proof.AesGcm.Arm.sp_subFlags, sp₃])
      (by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, rd₃]) (by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, wr₃]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact P.frame.trans ((fW₂.mono (by simp)).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩, by simp, fun _ h => h⟩))
  · simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, rd₃, R₂.rd, P₁.rd, P.rd]
  · simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, wr₃, R₂.wr, P₁.wr, P.wr]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    rw [show 16 * i + 16 = 16 * (i + 1) by omega_arith]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega_arith)]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kB₃ (bO L (by omega_arith)).symm (L.w_w (.inl (by decide)) (by decide) (by decide)), ofs₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [ck₃, ck₂, Bi₂, ofs₂, hckF i hi]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    by_cases hki : k = i
    · subst hki
      rw [blk₃, Bi₂, ofs₂]; simp
    · rw [kB₃ (Offset.disjoint _ (by omega_arith) (by omega_arith) (by have := L.dw; omega_arith)) (bW L (by omega_arith)),
        kD₂ (by omega_arith), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega_arith]
      · simp [hk', show ¬ k < i + 1 by omega_arith]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    obtain l0D : (⟨State.addr p.W + BitVec.ofNat 64 l0O, 16⟩ : Region).Disjoint
        ⟨State.addr p.D + BitVec.ofNat 64 (16 * i), 16⟩ :=
      ((L.d_w' (d := l0O) (k := 16) (by decide)).sub_left (Offset.sub_base _ (by omega_arith))).symm
    rw [kB₃ l0D (L.w_w (.inr (by decide)) (by decide) (by decide)), blockAtMem_frame fW₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)), P.l0]
  · simp only [passRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, ite_false]
    rw [g₃' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      P.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega_arith), z_dec hi (by omega_arith)]

theorem pass_ok {p : Prm} (L : Lay p) {m : Nat} {O0 l : Block} {X : Nat → Block}
    {fB : Block → Block → Block} {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr}
    (hB : BodyOk p body fB fC) (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    (hm : 16 * m ≤ p.n) (hm0 : 0 < m) {t₀ t : State} (P : PassInv p m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t (fun t' => PassInv p m O0 l X fB ckF t₀ t' m) := by
  refine WP.loop (M := isa)
    (fun (k : Nat) (u : State) => ∃ i, k = m - i ∧ i < m ∧ PassInv p m O0 l X fB ckF t₀ u i) ?_
    (m - 0) _ ⟨0, rfl, hm0, P⟩
  rintro k u ⟨i, rfl, hi, P⟩
  refine WP.mono (pass_step L hB hckF hm hi P) fun u' ⟨P', z⟩ => ?_
  by_cases he : i + 1 = m
  · left
    exact ⟨(eval_ne' z).trans (by simp [he]), he ▸ P'⟩
  · right
    exact ⟨(eval_ne' z).trans (by simp [he]), m - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, P'⟩

end VG.Proof.AesOcb.Arm

end

end


/-!
# AES-OCB on ARMv7: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`, as on AArch64
(`Proof.AesOcb.AArch64.whole_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (below)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called, the data and the stack below `SP`. -/
abbrev wholeR (p : Prm) (m : Nat) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 512, 2048⟩, ⟨State.addr p.D, 16 * m⟩, below p.SP]

theorem wholeR_mut {p : Prm} (L : Lay p) {m : Nat} (hm : 16 * m ≤ p.n) {M M' : Mem} (h : Frame (wholeR p m) M M') :
    Frame (mutR p) M M' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inr ⟨by decide, by decide⟩)
  · simpa using data_mut L (a := 0) (l := 16 * m) (by omega_arith)
  · exact below_mut L

/-- The registers `whole` writes. -/
abbrev wholeRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr]

/-- What `whole` leaves. -/
structure WholePost (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck
  gpr : Others wholeRegs t t'

/-- The start of a pass: `r4 ← D`, `r5 ← m`, `r6 ← 1`. -/
theorem passStart_run {p : Prm} {t : State} (h8 : t.gpr .r8 = p.D) {m : Nat} (h7 : t.gpr .r7 = BitVec.ofNat 32 m) :
    ∃ t', runBlock isa passStart t = some t' ∧
      t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * 0) ∧ t'.gpr .r5 = BitVec.ofNat 32 (m - 0) ∧
      t'.gpr .r6 = BitVec.ofNat 32 (0 + 1) ∧ Ran [.r4, .r5, .r6] t.mem t t' := by
  refine ⟨_, by orun [passStart], ?_, ?_, ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h7]
  · simp [gpr_setReg]

theorem passR_mut {p : Prm} (L : Lay p) {m : Nat} (hm : 16 * m ≤ p.n) {M M' : Mem} (h : Frame (passR p m) M M') :
    Frame (mutR p) M M' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inl (by decide))
  · exact w_mut L (.inl (by decide))
  · simpa using data_mut L (a := 0) (l := 16 * m) (by omega_arith)

theorem whole_ok (F : BlkFn) {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    {ckF1 ckF2 : Nat → Block} {p : Prm} (L : Lay p)
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    {t : State} (E : Env p t) {m : Nat} (hmn : 16 * m ≤ p.n) (hm0 : 0 < m) {O0 l : Block}
    (h8 : t.gpr .r8 = p.D) (h7 : t.gpr .r7 = BitVec.ofNat 32 m)
    (hofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) =
      fC1 (ckF1 i) (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (F.ciph p.R (sched p t.mem) (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole (blkFrame F) pre post) t (WholePost p m O0 l
      (fun k => F.ciph p.R (sched p t.mem)
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have fw := L.ww
  have fd := L.dw
  have n32 := L.n_lt
  -- the first pass
  obtain ⟨s₁, run₁, r4₁, r5₁, r6₁, R₁⟩ := passStart_run h8 h7
  obtain E₁ : Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  obtain P₀ : PassInv p m O0 l (fun k => blockAtMem s₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, r4 := r4₁, r6 := r6₁, r5 := r5₁
      ofs := by rw [R₁.mem, hofs]; rfl
      ck := by rw [R₁.mem, hck]
      blk := fun k _ => by simp
      l0 := by rw [R₁.mem, hl0]
      gpr := fun _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (pass_ok L hB1 (fun i _ => by rw [hckF1, R₁.mem]) hmn hm0 P₀) fun s₂ P₂ => ?_)
  have E₂ := P₂.env
  obtain r8₂ : s₂.gpr .r8 = p.D := by rw [P₂.gpr _ (by decide), R₁.gpr _ (by decide), h8]
  obtain r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 m := by rw [P₂.gpr _ (by decide), R₁.gpr _ (by decide), h7]
  -- the call
  refine WP.seq (WP.of_runBlock ⟨_, by orun [callArgs, E₂.r9, E₂.r10, E₂.r11, r8₂, r7₂], ?_⟩)
  obtain hB := blkFrame_ok F L (t := ((((((s₂.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 p.D).setReg .r3 (BitVec.ofNat 32 m))))
    (D := p.D) (n := m) (E₂.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac)
      (by rfl) (by rfl) (by rfl)) (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by omega_arith)
      (Proof.AesGcm.Arm.covers_prefix E₂.perm.d hmn) (L.k_d.sub_right (Region.sub_prefix hmn))
      ((L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left (Region.sub_prefix hmn))
      (L.bd.sub_right (Region.sub_prefix hmn))
  refine WP.seq (WP.mono hB fun s₃ C₃ => ?_)
  obtain g₃ : ∀ r ∈ keptRegs, s₃.gpr r = s₂.gpr r := fun r hr => by
    rw [C₃.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  obtain E₃ : Env p s₃ := E₂.keep (fun r hr => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    (by rw [C₃.sp]; rfl) (by rw [C₃.rd]; rfl) (by rw [C₃.wr]; rfl)
  obtain kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩ →
      (⟨Q, 16⟩ : Region).Disjoint (below p.SP) → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ h₃ => blockAtMem_frame C₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  obtain dW : ∀ {d : Nat}, d + 16 ≤ 512 → (⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint
      ⟨State.addr p.D, 16 * m⟩ := fun hd =>
    ((L.d_w' (k := 16) (by omega_arith)).sub_left (Region.sub_prefix hmn)).symm
  obtain kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [kC (dW (by omega_arith)) (L.w_w (.inl (by simp only [scrO]; omega_arith)) (by omega_arith) (by decide))
          (L.bw' (by omega_arith)).symm,
        blockAtMem_frame P₂.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_arith) (by omega_arith) (by decide)
          · exact L.w_w (a := _) (d := 16) (k := 16) (by omega_arith) (by omega_arith) (by decide)
          · exact L.w_w (a := _) (d := 32) (k := 16) (by omega_arith) (by omega_arith) (by decide)
          · exact dW (by omega_arith))]
  obtain o0₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0 := by
    rw [kWP (by decide), R₁.mem, ho0]
  -- `Offset_0` again
  refine WP.seq (WP.block_append (WP.mono (copy16_wp (t := s₃) (W := State.addr p.W) (sO := o0O) (dO := ofsO)
    (by rw [E₃.r11]) (by decide) (by decide) (by rw [E₃.r11]; omega_arith) (by decide) (by decide)
    (E₃.perm.wCR (by decide)) (E₃.perm.wC (by decide))) fun s₄a R₄ => ?_))
  obtain E₄a : Env p s₄a := E₃.of_others R₄.gpr R₄.sp R₄.rd R₄.wr
  obtain r8₄ : s₄a.gpr .r8 = p.D := by rw [R₄.gpr _ (by decide), g₃ _ (by decide), r8₂]
  obtain r7₄ : s₄a.gpr .r7 = BitVec.ofNat 32 m := by rw [R₄.gpr _ (by decide), g₃ _ (by decide), r7₂]
  obtain ⟨s₄, run₄, r4₄, r5₄, r6₄, R₄'⟩ := passStart_run r8₄ r7₄
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  obtain E₄ : Env p s₄ := E₄a.of_others R₄'.gpr R₄'.sp R₄'.rd R₄'.wr
  obtain m₄ : s₄.mem = copyMem s₃.mem (State.addr p.W + BitVec.ofNat 64 o0O) (State.addr p.W + BitVec.ofNat 64 ofsO) := by
    rw [R₄'.mem, R₄.mem]
  obtain kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ →
      blockAtMem s₄.mem Q = blockAtMem s₃.mem Q := fun hQ => by
    rw [m₄]; exact blockAtMem_frame (copyMem_frame _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hQ
  obtain hsched : sched p s₂.mem = sched p t.mem := by
    rw [sched_mut L (passR_mut L hmn P₂.frame), R₁.mem]
  obtain X₄ : ∀ k < m, blockAtMem s₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) =
      F.ciph p.R (sched p t.mem)
        (blockAtMem t.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) := fun k hk => by
    rw [kB₄ (bO L (by omega_arith)), C₃.out k hk]
    simp only [mem_setReg]
    rw [hsched, P₂.blk k hk]
    simp only [hk, ↓reduceIte, R₁.mem]
  obtain ck₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC (dW (by decide)) (L.w_w (.inl (by decide)) (by decide) (by decide)) (L.bw' (by decide)).symm,
      P₂.ck, hckF2₀]
  obtain P₀' : PassInv p m O0 l (fun k => blockAtMem s₄.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, r4 := r4₄, r6 := r6₄, r5 := r5₄
      ofs := by rw [m₄, blockAtMem_copy, o0₃]; rfl
      ck := by rw [kB₄ (L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by rw [kB₄ (L.w_w (.inr (by decide)) (by decide) (by decide)), kWP (by decide), R₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB2 (fun i hi => by rw [hckF2, X₄ i hi]) hmn hm0 P₀') fun s₅ P₅ => ?_
  obtain subW : ∀ r ∈ passR p m, ∃ r' ∈ wholeR p m, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, R₄'.rd, R₄.rd, C₃.rd]; simp only [rd_setReg]; rw [P₂.rd, R₁.rd],
    by rw [P₅.wr, R₄'.wr, R₄.wr, C₃.wr]; simp only [wr_setReg]; rw [P₂.wr, R₁.wr], fun k hk => ?_, P₅.ofs, P₅.ck, fun r hr => ?_⟩
  · rw [← R₁.mem]
    refine (P₂.frame.sub subW).trans ((C₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr p.D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp [scrO], fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact ((copyMem_frame _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
          (by decide)⟩).trans (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]
  · simp only [wholeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain hk : r ∈ keptRegs := by
      revert hr; cases r <;> decide
    rw [P₅.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      R₄'.gpr r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      R₄.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₃ r hk,
      P₂.gpr r (by simp [passRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      R₁.gpr r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1])]

end VG.Proof.AesOcb.Arm

end

end


/-!
# AES-OCB on ARMv7: the data (`body`)

Untrusted: everything here is checked by Lean. `body` takes the whole blocks
(if any, `wholeIte_ok`) and then the rest (if any, `restIte_ok`); for `seal`
the result is `OCB-ENCRYPT`'s ciphertext, offset and checksum
(`bodySeal_ok`), for `open` `OCB-DECRYPT`'s (`bodyOpen_ok`), as on AArch64
(`Proof.AesOcb.AArch64.bodySeal_ok`, `Proof.AesOcb.AArch64.bodyOpen_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm)
open VG.Proof.AesGcm.Arm (eval_eq' z_subFlags z_cmp0 and15 ofNat_sub32 below)

/-- What the whole blocks leave, if there are any. -/
structure WholeIte (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (wholeR p m) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck
  r8 : t'.gpr .r8 = p.D

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok (F : BlkFn) {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block}
    {ckF1 ckF2 : Nat → Block} {p : Prm} (L : Lay p)
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    {s : State} (E : Env p s) (A : Args p s.mem) {O0 l : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) =
      fC1 (ckF1 i) (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (p.n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (F.ciph p.R (sched p s.mem) (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)])
      (.ite .eq (.block []) (whole (blkFrame F) pre post))) s
      (WholeIte p (p.n / 16) O0 l
        (fun k => F.ciph p.R (sched p s.mem)
          (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (p.n / 16)) s) := by
  have n32 := L.n_lt
  obtain a₈ := E.perm.argR' L (k := 8) (by decide)
  obtain a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₈, a₁₂, A.a8, A.a12], ?_⟩)
  refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' (by
    simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, ofNat_lsr32 n32,
      Nat.reducePow, z_cmp0 (show p.n / 16 < 2 ^ 32 by omega_arith)])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hm : p.n / 16 = 0 := of_decide_eq_true hb
    refine ⟨E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl), Frame.refl _ _, rfl, rfl,
      fun k hk => absurd hk (by omega_arith), ?_, ?_, ?_⟩
    · show blockAtMem s.mem _ = _
      rw [hofs, hm]; rfl
    · show blockAtMem s.mem _ = _
      rw [hck, hm, hckF2₀, hm]
    · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]
  · have hm : p.n / 16 ≠ 0 := by simpa using hb
    refine WP.mono (whole_ok F L hB1 hB2 (E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)) (m := p.n / 16) (O0 := O0) (l := l) (Nat.mul_div_le p.n 16)
      (by omega_arith) (by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg])
      (by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ofNat_lsr32 n32]) hofs ho0 hck hl0 hckF1 hckF2₀ hckF2)
      fun t P => ⟨P.env, P.frame, P.rd, P.wr, P.blk, P.ofs, P.ck, ?_⟩
    rw [P.gpr .r8 (by decide)]
    simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]

/-- What the rest of the data leaves, if there is any: `r` bytes at `D + a`. -/
structure TailPost (enc : Bool) (p : Prm) (a r : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem
    else blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem (State.addr p.D + BitVec.ofNat 64 a) r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r)
      (Spec.Ocb.toBytes (ciphOf p t.mem (blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) ^^^ lstarOf p t.mem)))
    else bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 a) r
  ck : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (State.addr p.D + BitVec.ofNat 64 a) r)
    else blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (enc : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem)
    (h8 : t.gpr .r8 = p.D) :
    WP isa (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
        .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) (.ite .eq (.block []) (rest enc))) t
      (TailPost enc p (16 * (p.n / 16)) (p.n % 16) t) := by
  have n32 := L.n_lt
  obtain a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₁₂, A.a12, h8], ?_⟩)
  refine WP.ite (decide (p.n % 16 = 0)) (eval_eq' (by
    simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15,
      toNat_ofNat32 n32, z_cmp0 (show p.n % 16 < 2 ^ 32 by omega_arith)])) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hr : ¬ 0 < p.n % 16 := by have := of_decide_eq_true hb; omega_arith
    refine ⟨E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl), Frame.refl _ _, rfl, rfl, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte] <;> rfl
  · have hr : 0 < p.n % 16 := by have : p.n % 16 ≠ 0 := by simpa using hb
                                 omega_arith
    refine WP.mono (rest_ok enc L (E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl)) ⟨by omega_arith, hr, Nat.mod_lt _ (by decide)⟩ ?_ ?_) fun t' P =>
      ⟨P.env, P.frame, P.rd, P.wr, ?_, ?_, ?_⟩
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
        toNat_ofNat32 n32, h8]
      rw [ofNat_sub32 (Nat.mod_le _ _) n32, BitVec.add_comm, show p.n - p.n % 16 = 16 * (p.n / 16) by omega_arith]
    · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
        toNat_ofNat32 n32]
    · simp only [hr, ↓reduceIte]; exact P.ofs
    · simp only [hr, ↓reduceIte]; exact P.out
    · simp only [hr, ↓reduceIte]; exact P.ck

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad`,
`pad(·)`, the working space of the functions called, the stack and the
data. -/
abbrev bodyR (p : Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 512, 2048⟩, below p.SP,
   ⟨State.addr p.D, p.n⟩]

theorem bodyR_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (bodyR p) m m') : Frame (mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact below_mut L
    · exact ⟨_, by simp, fun _ h => h⟩

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (p : Prm) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env p t
  frame : Frame (bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem (State.addr p.D) p.n = out
  ofs : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {q : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt q i) :
    ckOf X m = Proof.Ocb.ckAt q m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega_arith)), h m (by omega_arith)]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega_arith)), h m (by omega_arith)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega_arith))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega_arith)]

section
variable {p : Prm} (L : Lay p)

include L in
/-- The rest of the data misses what `whole` writes. -/
theorem disj_whole {a r : Nat} (ha : 16 * (p.n / 16) ≤ a) (hf : a + r ≤ p.n) :
    ∀ x ∈ wholeR p (p.n / 16), (⟨State.addr p.D + BitVec.ofNat 64 a, r⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (L.d_w' (by decide)).sub_left (Offset.sub_base _ hf)
  · exact (Offset.base_disjoint _ ha (by have := L.dw; omega_arith)).symm
  · exact (L.bd.sub_right (Offset.sub_base _ hf)).symm

include L in
/-- The whole blocks miss what `rest` writes. -/
theorem disj_tail {a r : Nat} (ha : 16 * (p.n / 16) ≤ a) (hf : a + r ≤ p.n) :
    ∀ x ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩],
      (⟨State.addr p.D, 16 * (p.n / 16)⟩ : Region).Disjoint x := by
  obtain dW : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr p.D, 16 * (p.n / 16)⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ :=
    fun h => (L.d_w' h).sub_left (Region.sub_prefix (Nat.mul_div_le p.n 16))
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact dW (by decide)
  · exact (L.bd.sub_right (Region.sub_prefix (Nat.mul_div_le p.n 16))).symm
  · exact Offset.base_disjoint _ ha (by have := L.dw; omega_arith)

theorem wholeR_sub : ∀ r ∈ wholeR p (p.n / 16), ∃ r' ∈ bodyR p, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp [scrO], fun _ h => h⟩
  · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Region.sub_prefix (Nat.mul_div_le p.n 16)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem tailR_sub {a r : Nat} (h : a + r ≤ p.n) :
    ∀ x ∈ [(⟨State.addr p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP, ⟨State.addr p.D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR p, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 176, 16⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 16, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, by simp [scrO], fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨⟨State.addr p.D, p.n⟩, by simp, Offset.sub_base _ h⟩

end

/-- `body` for `seal`. -/
theorem bodySeal_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) {O0 : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s.mem) 0) :
    WP isa (body true) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.encBlocks (ciphOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ciphOf p s.mem (offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem)))
      else Proof.Ocb.encBlocks (ciphOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem
       else offAt O0 (lstarOf p s.mem) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ^^^
          pad ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16)) s) := by
  have hn := L.n_lt
  obtain hmn : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le p.n 16
  obtain hl : ∀ i < p.n / 16, blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.blockAt (bytesAt s.mem (State.addr p.D) p.n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem _ (by omega_arith)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok encF (O0 := O0) (l := lstarOf p s.mem)
    (ckF1 := ckOf fun i => blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
    L (sealPre_ok L) (xorOfs_ok L) E A hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  obtain fW : Frame (mutR p) s.mem t.mem := wholeR_mut L hmn Pw.frame
  refine WP.mono (restIte_ok true L Pw.env (A.mut L fW) Pw.r8) fun t' Pt => ?_
  obtain cT : ciphOf p t.mem = ciphOf p s.mem := by simp only [ciphOf, sched_mut L fW]
  obtain lT : lstarOf p t.mem = lstarOf p s.mem := lstar_mut L fW
  obtain pT : bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    exact Proof.Cmac.bytesAt_frame Pw.frame (disj_whole L (Nat.le_refl _) (by omega_arith)) (by omega_arith)
  obtain rest : (bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem _ hmn, show p.n - 16 * (p.n / 16) = p.n % 16 by omega_arith]
  obtain ckT : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.ckAt (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  obtain blk : bytesAt t'.mem (State.addr p.D) (16 * (p.n / 16)) =
      Proof.Ocb.encBlocks (ciphOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail L (Nat.le_refl _) (by omega_arith)) (by omega_arith),
      Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encF_ciph, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub wholeR_sub).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem (State.addr p.D) (16 * (p.n / 16)) (p.n % 16)
    rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega_arith] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show p.n % 16 = 0 by omega_arith, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

/-- `DECIPHER` with the key schedule in `m`. -/
abbrev invOf (p : Prm) (m : Mem) : Cipher := Spec.Ocb.aesInvWith p.R (sched p m)

/-- `body` for `open`. -/
theorem bodyOpen_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) {O0 : Block}
    (hofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s.mem) 0) :
    WP isa (body false) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.decBlocks (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ciphOf p s.mem (offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem)))
      else Proof.Ocb.decBlocks (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem
       else offAt O0 (lstarOf p s.mem) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.dckAt (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ciphOf p s.mem (offAt O0 (lstarOf p s.mem) (p.n / 16) ^^^ lstarOf p s.mem))))
      else Proof.Ocb.dckAt (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16)) s) := by
  have hn := L.n_lt
  obtain hmn : 16 * (p.n / 16) ≤ p.n := Nat.mul_div_le p.n 16
  obtain hl : ∀ i < p.n / 16, blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) =
      Spec.Ocb.blockAt (bytesAt s.mem (State.addr p.D) p.n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem _ (by omega_arith)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok decF (O0 := O0) (l := lstarOf p s.mem) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => invOf p s.mem
      (blockAtMem s.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (lstarOf p s.mem) (i + 1)) ^^^
        offAt O0 (lstarOf p s.mem) (i + 1))
    L (xorOfs_ok L) (openPost_ok L) E A hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  obtain fW : Frame (mutR p) s.mem t.mem := wholeR_mut L hmn Pw.frame
  refine WP.mono (restIte_ok false L Pw.env (A.mut L fW) Pw.r8) fun t' Pt => ?_
  obtain cT : ciphOf p t.mem = ciphOf p s.mem := by simp only [ciphOf, sched_mut L fW]
  obtain lT : lstarOf p t.mem = lstarOf p s.mem := lstar_mut L fW
  obtain pT : bytesAt t.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole L (Nat.le_refl _) (by omega_arith)) (by omega_arith)
  obtain rest : (bytesAt s.mem (State.addr p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt s.mem (State.addr p.D + BitVec.ofNat 64 (16 * (p.n / 16))) (p.n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem _ hmn, show p.n - 16 * (p.n / 16) = p.n % 16 by omega_arith]
  obtain ckT : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  obtain blk : bytesAt t'.mem (State.addr p.D) (16 * (p.n / 16)) =
      Proof.Ocb.decBlocks (invOf p s.mem) O0 (lstarOf p s.mem) (bytesAt s.mem (State.addr p.D) p.n) (p.n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail L (Nat.le_refl _) (by omega_arith)) (by omega_arith),
      Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decF_ciph, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  obtain e := Proof.Ocb.bytesAt_append t'.mem (State.addr p.D) (16 * (p.n / 16)) (p.n % 16)
  rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega_arith] at e
  refine ⟨Pt.env, (Pw.frame.sub wholeR_sub).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show p.n % 16 = 0 by omega_arith, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.Arm
