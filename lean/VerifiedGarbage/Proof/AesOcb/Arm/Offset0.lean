import VerifiedGarbage.Proof.AesOcb.Arm.NonceBlock
import VerifiedGarbage.Proof.Ocb.Stretch32
import VerifiedGarbage.Proof.Ocb.State

/-!
# AES-OCB on ARMv7: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
four byte-reversed words, computes the last two words of `Stretch`
(`Proof.Ocb.stretch_words32`), shifts the six words left by `bottom` in six
masked stages (`stage_ok`, `stage32_ok`, `Proof.Ocb.shl_stages`), and stores
the top four, byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`), as
on AArch64 (`Proof.AesOcb.AArch64.offset0_ok`) with 32-bit words.
-/

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
  · have h1 : 1 ≤ k := by omega
    have h31 : k ≤ 31 := by omega
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
  have h31 : a ≤ 31 := by omega
  have h1' : 1 ≤ 32 - a := by omega
  have h31' : 32 - a ≤ 31 := by omega
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
  have ew : ∀ k, k < 2560 → State.addr (p.W + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 k :=
    fun k hk => L.wA hk
  have e112 := ew 112 (by decide)
  have e116 := ew 116 (by decide)
  have e120 := ew 120 (by decide)
  have e124 := ew 124 (by decide)
  have e208 := ew 208 (by decide)
  have r112 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 112) 4 := E.perm.wR (by decide)
  have r116 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 116) 4 := E.perm.wR (by decide)
  have r120 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 120) 4 := E.perm.wR (by decide)
  have r124 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 124) 4 := E.perm.wR (by decide)
  have r208 : InRegions (s.rd ++ s.wr) (State.addr p.W + BitVec.ofNat 64 208) 4 := E.perm.wR (by decide)
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, r6₁, R₁⟩ : ∃ s₁, runBlock isa off0Head s = some s₁ ∧
      words s₁ = stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .r6 = BitVec.ofNat 32 v ∧ Ran [.r0, .r1, .r2, .r3, .r4, .r5, .r6] s.mem s s₁ := by
    refine ⟨_, by orun [off0Head, E.r11, e112, e116, e120, e124, e208, r112, r116, r120, r124, r208], ?_, ?_,
      by rfl, by others_tac, by rfl, by rfl, by rfl⟩
    · simp only [words, gpr_setReg, ite_true, ite_false, reduceCtorEq, rev_eq]
      have hb : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO) =
          byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 112) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 116) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 120) 32) ++
            byteRev32 (s.mem.readW (State.addr p.W + BitVec.ofNat 64 124) 32) := by
        have := Proof.Cmac.ofBytes_rev4 s.mem (State.addr p.W + BitVec.ofNat 64 112)
        simp only [Offset.add_add] at this
        exact this
      rw [stretch, hb, Proof.Ocb.stretch_words32]
    · simp only [gpr_setReg, ite_true, hbot]
  have keep : ∀ {t t' : State}, Ran stageRegs t.mem t t' → t.gpr .r6 = BitVec.ofNat 32 v →
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
  have hw7 : words s₇ = stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  have hO : s₇.gpr .r0 ++ s₇.gpr .r1 ++ s₇.gpr .r2 ++ s₇.gpr .r3 =
      (stretch (blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← Proof.Ocb.top4 _ _ _ _ (s₇.gpr .r4) (s₇.gpr .r5), show s₇.gpr .r0 ++ s₇.gpr .r1 ++ s₇.gpr .r2 ++
      s₇.gpr .r3 ++ s₇.gpr .r4 ++ s₇.gpr .r5 = words s₇ from rfl, hw7, Proof.Ocb.offset_shl _ (by omega)]
  have hm₇ : s₇.mem = s.mem := by rw [R₇.mem, R₆.mem, R₅.mem, R₄.mem, R₃.mem, R₂.mem, R₁.mem]
  have hsp₇ : s₇.sp = s.sp := by rw [R₇.sp, R₆.sp, R₅.sp, R₄.sp, R₃.sp, R₂.sp, R₁.sp]
  have hrd₇ : s₇.rd = s.rd := by rw [R₇.rd, R₆.rd, R₅.rd, R₄.rd, R₃.rd, R₂.rd, R₁.rd]
  have hwr₇ : s₇.wr = s.wr := by rw [R₇.wr, R₆.wr, R₅.wr, R₄.wr, R₃.wr, R₂.wr, R₁.wr]
  have g₁₇ : Others [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8] s s₇ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h' : r ∉ stageRegs := by
      simp [stageRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2]
    rw [R₇.gpr r h', R₆.gpr r h', R₅.gpr r h', R₄.gpr r h', R₃.gpr r h', R₂.gpr r h',
      R₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1])]
  have r11₇ : s₇.gpr .r11 = p.W := by rw [g₁₇ _ (by decide), E.r11]
  have P₇ : Perm p s₇ := E.perm.of_eq hrd₇ hwr₇
  have ww : ∀ d, d + 4 ≤ 2560 → InRegions s₇.wr (State.addr p.W + BitVec.ofNat 64 d) 4 := fun d h => P₇.wW h
  have e16 := ew 16 (by decide)
  have e20 := ew 20 (by decide)
  have e24 := ew 24 (by decide)
  have e28 := ew 28 (by decide)
  have e224 := ew 224 (by decide)
  have e228 := ew 228 (by decide)
  have e232 := ew 232 (by decide)
  have e236 := ew 236 (by decide)
  have w16 := ww 16 (by decide)
  have w20 := ww 20 (by decide)
  have w24 := ww 24 (by decide)
  have w28 := ww 28 (by decide)
  have w224 := ww 224 (by decide)
  have w228 := ww 228 (by decide)
  have w232 := ww 232 (by decide)
  have w236 := ww 236 (by decide)
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
  have val : ∀ (M : Mem) (C : Addr), blockAtMem (Proof.Cmac.store4 M C
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
