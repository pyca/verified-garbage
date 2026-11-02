module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Pre
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Candidate
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.RISCV64.Run

-- separate module: the whole function's proof (`code_ok`) and its constant-time proof import the frame without
-- the proofs of the ends

/-!
# A candidate on RISC-V: the frame and the entry

The 288 bytes below the stack pointer on entry (`cF`): the 96 the round's
frame uses (`rF`), then the frame of 192 bytes (`kF`, at `fb`, the body's
stack pointer and `s11`): `s0`–`s11` at `8 i`, the return address at `oRa`,
the eight register arguments at `oOut`, …, `oRand` (`svL`, `argL`), `rand_len`
and `scratch_len` at `oRandLen` and `oWsLen`, and the octets read at `oRead`.

`Fr s0 s`: what holds through the body, from the initial state `s0`: the
stack pointer, `s11` and the permissions, the frame's saved words, and memory
elsewhere but in `out`, `used`, `scratch` and the stack as `s0`'s. `entry_ok`:
the entry's saves and moves; `Fr.step`: `Fr` through code that keeps the
frame but for the octets read; `ldf_eq`, `stf_eq`: the frame's words;
`restore_ok`: the exit; `code_ok`: the whole function from its body.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd
open VG.Impl.RsaKeyGen.RISCV64.Candidate (entry restore saved frameBytes ldf stf oRa oOut oOutLen oUsed oE oELen
  oP oPLen oRand oRandLen oRead oWsLen)

/-! ## The frame's layout -/

/-- The frame's base: the body's stack pointer. -/
abbrev fb (s0 : State) : Addr := s0.sp - BitVec.ofNat 64 192
/-- The frame. -/
abbrev kF (s0 : State) : Region := ⟨fb s0, 192⟩
/-- The frame's word at `o`. -/
abbrev fw (s0 : State) (o : Nat) : Addr := fb s0 + BitVec.ofNat 64 o
/-- The round's frame, below ours. -/
abbrev rF (s0 : State) : Region := ⟨s0.sp - BitVec.ofNat 64 288, 96⟩
/-- The octets read so far. -/
abbrev rdW (s0 : State) : Region := ⟨fw s0 oRead, 8⟩

/-- The `i`-th register saved. -/
def savedR (i : Nat) : Reg := saved.getD i .s0

/-- The saved registers' slots, and the return address's. -/
def svL : List (Reg × Nat) := Spill.slots savedR 12 ++ [(.ra, 96)]

/-- The register arguments' slots. -/
def argL : List (Reg × Nat) :=
  [(.a0, 104), (.a1, 112), (.a2, 120), (.a3, 128), (.a4, 136), (.a5, 144), (.a6, 152), (.a7, 160)]

/-- The entry after the saves: the stack arguments into the frame and `s6`. -/
def tailI : List Instr :=
  [ldf .t3 frameBytes, stf .t3 oRandLen, ldf .s6 (frameBytes + 8), ldf .t3 (frameBytes + 16), stf .t3 oWsLen,
    .li .t3 0, stf .t3 oRead]

theorem entry_eq : entry =
    .addSp .t2 0 :: Spill.saveCode .t2 svL ++ (.addi .s11 .t2 0 :: Spill.saveCode .s11 argL ++ tailI) := rfl

/-- The restore: the return address, then `svL`'s registers. -/
def rsL : List (Reg × Nat) := (.ra, 96) :: Spill.slots savedR 12

theorem restore_eq : restore = .addSp .t2 0 :: Spill.restoreCode .t2 rsL := rfl

theorem svL_fits : Spill.Fits svL := by decide
theorem argL_fits : Spill.Fits argL := by decide
theorem rsL_fits : Spill.Fits rsL := by decide
theorem rsL_restorable : Spill.Restorable .t2 rsL := by decide
theorem svL_le : ∀ p ∈ svL, p.2 + 8 ≤ 104 := by decide
theorem argL_le : ∀ p ∈ argL, 104 ≤ p.2 ∧ p.2 + 8 ≤ 104 + 64 := by decide
theorem rsL_sub : ∀ p ∈ rsL, p ∈ svL := by decide
theorem rsL_saved : ∀ r ∈ preserved, (r, 8 * preserved.idxOf r) ∈ rsL := by decide
theorem rsL_t2 : ∀ p ∈ rsL, p.1 ≠ .t2 := by decide
theorem svL_t2 : ∀ p ∈ svL, p.1 ≠ .t2 := by decide
theorem argL_ne : ∀ p ∈ argL, p.1 ≠ .t2 ∧ p.1 ≠ .s11 := by decide

section
variable {s0 : State}

theorem fb_toNat (h : CIn s0) : (fb s0).toNat = s0.sp.toNat - 192 := by
  have := h.spLo
  simp only [fb]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
  simp only [BitVec.toNat_ofNat]

theorem fb_al (h : CIn s0) : (fb s0).toNat % 8 = 0 := by
  have := h.sp16; have := h.spLo; rw [fb_toNat h]; omega_arith

/-- The frame's words, to the stack arguments, do not wrap around. -/
theorem fb_fit (h : CIn s0) : (fb s0).toNat + 216 ≤ 2 ^ 64 := by
  have := h.spHi; have := h.spLo; rw [fb_toNat h]; omega_arith

theorem fw_al (h : CIn s0) {o : Nat} (h8 : o % 8 = 0) : (fw s0 o).toNat % 8 = 0 :=
  Spill.al8 (fb_al h) h8

/-- The frame's base, as an offset of the lowest byte of the stack used. -/
theorem fb_eq (s0 : State) : fb s0 = s0.sp - BitVec.ofNat 64 288 + BitVec.ofNat 64 96 :=
  Offset.sub_ofNat_eq s0.sp (by decide)

theorem fw_eq (s0 : State) (o : Nat) : fw s0 o = s0.sp - BitVec.ofNat 64 288 + BitVec.ofNat 64 (96 + o) := by
  simp only [fw, fb_eq, BitVec.add_assoc, BitVec.ofNat_add]

/-- The stack arguments, at offsets `192 + 8 i` of the frame. -/
theorem fw_arg (s0 : State) (i : Nat) : fw s0 (192 + 8 * i) = stackArgAddr s0 i := by
  simp only [fw, fb, stackArgAddr]
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem kF_contains {o n : Nat} (ho : o + n ≤ 192) : (kF s0).Contains (fw s0 o) n :=
  Offset.contains_base _ ho (by omega_arith)

/-- A range of the frame lies in the stack used. -/
theorem fw_sub (s0 : State) {o n : Nat} (ho : o + n ≤ 192) : Region.Sub ⟨fw s0 o, n⟩ (cF s0) := by
  rw [fw_eq]; exact Offset.sub_base _ (by omega_arith)

theorem kF_sub (s0 : State) : Region.Sub (kF s0) (cF s0) := by
  have := fw_sub s0 (o := 0) (n := 192) (by decide)
  simpa only [fw, BitVec.add_zero] using this

theorem rF_sub (s0 : State) : Region.Sub (rF s0) (cF s0) := Region.sub_prefix (by decide)

/-- A range of the frame is apart from the round's frame. -/
theorem fw_rF (h : CIn s0) {o n : Nat} (ho : o + n ≤ 192) : (⟨fw s0 o, n⟩ : Region).Disjoint (rF s0) := by
  rw [fw_eq]
  have := h.spLo
  have hc : (s0.sp - BitVec.ofNat 64 288).toNat + 288 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith)]
    simp only [BitVec.toNat_ofNat]; have := s0.sp.isLt; omega_arith
  have hd := Offset.disjoint (n := n) (k := 96) (s0.sp - BitVec.ofNat 64 288) (d := 96 + o) (e := 0)
    (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  simpa only [BitVec.add_zero] using hd

/-- Two ranges of the frame, apart. -/
theorem fw_fw (h : CIn s0) {o n e k : Nat} (hs : o + n ≤ e ∨ e + k ≤ o) (ho : o + n ≤ 192) (he : e + k ≤ 192) :
    (⟨fw s0 o, n⟩ : Region).Disjoint ⟨fw s0 e, k⟩ :=
  Offset.disjoint _ hs (by have := fb_fit h; omega_arith) (by have := fb_fit h; omega_arith)

/-- Two words of the frame, apart. -/
theorem fw_sep (h : CIn s0) {o e : Nat} (hs : o + 8 ≤ e ∨ e + 8 ≤ o) (ho : o + 8 ≤ 192) (he : e + 8 ≤ 192) :
    Mem.Sep (fw s0 o) 8 (fw s0 e) 8 :=
  Offset.sep _ hs (by have := fb_fit h; omega_arith) (by have := fb_fit h; omega_arith)

/-- The stack arguments are within their region. -/
theorem cA_contains {i : Nat} (hi : i < 3) : (cA s0).Contains (stackArgAddr s0 i) 8 := by
  have e : stackArgAddr s0 i = stackArgAddr s0 0 + BitVec.ofNat 64 (8 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  show (⟨stackArgAddr s0 0, 24⟩ : Region).Contains (stackArgAddr s0 i) 8
  rw [e]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-! ## Loads and stores of the frame's words -/

theorem ldf_eq (h : CIn s0) {s : State} (h11 : s.gpr .s11 = fb s0) (hw : kF s0 ∈ s.wr) {r : Reg} {o : Nat}
    (ho : o + 8 ≤ 192) (h8 : o % 8 = 0) :
    exec (ldf r o) s = some (s.write r (s.mem.readW (fw s0 o) 64)) := by
  unfold ldf
  rw [exec_load_d (by omega_arith) (by rw [h11]; exact fw_al h h8)
    ⟨_, List.mem_append_right _ hw, by rw [h11]; exact kF_contains ho⟩, h11]

theorem stf_eq (h : CIn s0) {s : State} (h11 : s.gpr .s11 = fb s0) (hw : kF s0 ∈ s.wr) {r : Reg} {o : Nat}
    (ho : o + 8 ≤ 192) (h8 : o % 8 = 0) :
    exec (stf r o) s = some { s with mem := s.mem.writeW (fw s0 o) (s.gpr r) } := by
  unfold stf
  rw [exec_store_d (by omega_arith) (by rw [h11]; exact fw_al h h8) ⟨_, hw, by rw [h11]; exact kF_contains ho⟩,
    h11]

/-- A stack argument's load, at `frameBytes + 8 i` of the frame. -/
theorem ldArg_eq (h : CIn s0) {s : State} (h11 : s.gpr .s11 = fb s0) (hr : s.rd = s0.rd) {r : Reg} {o i : Nat}
    (hi : i < 3) (ho : o = 192 + 8 * i) :
    exec (ldf r o) s = some (s.write r (s.mem.readW (stackArgAddr s0 i) 64)) := by
  unfold ldf
  subst ho
  have ha : (s.gpr .s11 + BitVec.ofNat 64 (192 + 8 * i)) = stackArgAddr s0 i := by rw [h11]; exact fw_arg s0 i
  rw [exec_load_d (by omega_arith) (by rw [ha]; rw [← fw_arg]; exact fw_al h (by omega_arith))
    ⟨_, List.mem_append_left _ (by rw [hr]; exact h.rA), by rw [ha]; exact cA_contains hi⟩, ha]

/-- The stack arguments, through what keeps the stack used, `out`, `used`
and `scratch` apart from them. -/
theorem stackArg_keep (h : CIn s0) {m : Mem} (f : Frame [cO s0, cU s0, cS s0, cF s0] s0.mem m) {i : Nat}
    (hi : i < 3) : m.readW (stackArgAddr s0 i) 64 = stackArg s0 i := by
  refine f.readW (r := cA s0) (cA_contains hi) (fun ρ hρ => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact h.oA.symm
  · exact h.uA.symm
  · exact h.SA.symm
  · exact h.FA.symm

/-! ## What holds through the body -/

/-- What holds through the body. -/
structure Fr (s0 s : State) : Prop where
  pre : CIn s0
  sp : s.sp = fb s0
  rd : s.rd = s0.rd
  wr : s.wr = kF s0 :: s0.wr
  s11 : s.gpr .s11 = fb s0
  sv : Spill.Saved (fb s0) s0.gpr svL s.mem
  args : Spill.Saved (fb s0) s0.gpr argL s.mem
  rl : s.mem.readW (fw s0 oRandLen) 64 = stackArg s0 0
  wl : s.mem.readW (fw s0 oWsLen) 64 = stackArg s0 2
  out : Frame [cO s0, cU s0, cS s0, cF s0] s0.mem s.mem

theorem Fr.load {s : State} (h : Fr s0 s) {r : Reg} {o : Nat} (ho : o + 8 ≤ 192) (h8 : o % 8 = 0) :
    exec (ldf r o) s = some (s.write r (s.mem.readW (fw s0 o) 64)) :=
  ldf_eq h.pre h.s11 (by rw [h.wr]; exact List.mem_cons_self) ho h8

theorem Fr.store {s : State} (h : Fr s0 s) {r : Reg} {o : Nat} (ho : o + 8 ≤ 192) (h8 : o % 8 = 0) :
    exec (stf r o) s = some { s with mem := s.mem.writeW (fw s0 o) (s.gpr r) } :=
  stf_eq h.pre h.s11 (by rw [h.wr]; exact List.mem_cons_self) ho h8

theorem Fr.arg {s : State} (h : Fr s0 s) {r : Reg} {d : Nat} (hp : (r, d) ∈ argL) :
    s.mem.readW (fw s0 d) 64 = s0.gpr r := h.args (r, d) hp

theorem Fr.wOut {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oOut) 64 = s0.gpr .a0 := h.arg (by decide)
theorem Fr.wOutLen {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oOutLen) 64 = s0.gpr .a1 := h.arg (by decide)
theorem Fr.wUsed {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oUsed) 64 = s0.gpr .a2 := h.arg (by decide)
theorem Fr.wE {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oE) 64 = s0.gpr .a3 := h.arg (by decide)
theorem Fr.wELen {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oELen) 64 = s0.gpr .a4 := h.arg (by decide)
theorem Fr.wP {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oP) 64 = s0.gpr .a5 := h.arg (by decide)
theorem Fr.wPLen {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oPLen) 64 = s0.gpr .a6 := h.arg (by decide)
theorem Fr.wRand {s : State} (h : Fr s0 s) : s.mem.readW (fw s0 oRand) 64 = s0.gpr .a7 := h.arg (by decide)

/-- A word of the frame, but the octets read, through what writes only `out`,
`used`, `scratch`, the round's frame and the octets read. -/
theorem fw_keep (hp : CIn s0) {m m' : Mem} (f : Frame [cO s0, cU s0, cS s0, rF s0, rdW s0] m m') {o : Nat}
    (ho : o + 8 ≤ 192) (hne : o + 8 ≤ 176 ∨ 184 ≤ o) : m'.readW (fw s0 o) 64 = m.readW (fw s0 o) 64 := by
  refine f.readW (r := ⟨fw s0 o, 8⟩) (Region.contains_self _ _) (fun ρ hρ => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl
  · exact hp.Fo.sub_left (fw_sub s0 ho)
  · exact hp.Fu.sub_left (fw_sub s0 ho)
  · exact hp.FS.sub_left (fw_sub s0 ho)
  · exact fw_rF hp ho
  · exact fw_fw hp (by simp only [oRead]; omega_arith) ho (by decide)

/-- `Fr` through code that keeps the stack pointer, the permissions and
`s11`, and writes only `out`, `used`, `scratch`, the round's frame and the
octets read. -/
theorem Fr.step {s t : State} (h : Fr s0 s) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (s11 : t.gpr .s11 = s.gpr .s11) (f : Frame [cO s0, cU s0, cS s0, rF s0, rdW s0] s.mem t.mem) : Fr s0 t := by
  have hp := h.pre
  refine ⟨hp, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, s11.trans h.s11, fun p hq => ?_, fun p hq => ?_, ?_, ?_,
    h.out.trans (f.sub fun ρ hρ => ?_)⟩
  · have := svL_le p hq
    exact (fw_keep hp f (by omega_arith) (.inl (by omega_arith))).trans (h.sv p hq)
  · have := argL_le p hq
    exact (fw_keep hp f (by omega_arith) (.inl (by omega_arith))).trans (h.args p hq)
  · exact (fw_keep hp f (by decide) (.inl (by decide))).trans h.rl
  · exact (fw_keep hp f (by decide) (.inr (by decide))).trans h.wl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨cF s0, by simp, rF_sub s0⟩
    · exact ⟨cF s0, by simp, fw_sub s0 (by decide)⟩

/-- A write of the octets read keeps `Fr`. -/
theorem rdW_frame (s : State) (v : BitVec 64) :
    Frame [cO s0, cU s0, cS s0, rF s0, rdW s0] s.mem (s.mem.writeW (fw s0 oRead) v) :=
  (Frame.refl _ _).writeW (r := rdW s0) (by simp) _ (Region.contains_self _ _)

/-! ## The entry -/

theorem entry_ok (h : CIn s0) :
    WP isa (.block entry) (allocd 192 s0) fun t =>
      Fr s0 t ∧ t.gpr .s6 = stackArg s0 1 ∧ t.mem.readW (fw s0 oRead) 64 = 0 ∧ t.syms = s0.syms := by
  have hf := fb_fit h
  have hal := fb_al h
  have inF : ∀ o, o + 8 ≤ 192 → InRegions (allocd 192 s0).wr (fw s0 o) 8 :=
    fun o ho => ⟨kF s0, List.mem_cons_self, kF_contains ho⟩
  rw [entry_eq]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), ?_⟩
  generalize hs1 : (allocd 192 s0).write .t2 ((allocd 192 s0).sp + BitVec.ofNat 64 0) = s₁
  have t21 : s₁.gpr .t2 = fb s0 := by
    rw [← hs1, gpr_write_self]; simp only [allocd, BitVec.add_zero]
  have g1 : ∀ r, r ≠ .t2 → s₁.gpr r = s0.gpr r := fun r hr => by rw [← hs1, gpr_write_of_ne _ _ hr]; rfl
  have w1 : s₁.wr = kF s0 :: s0.wr := by rw [← hs1]; rfl
  refine Spill.save_ok (b := .t2) (l := svL) (by rw [t21]; exact hal) svL_fits.1
    (fun p hp => by rw [t21, w1]; exact inF p.2 (by have := svL_le p hp; omega_arith)) ?_
  generalize hs2 : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr .t2) s₁.gpr svL } : State) = s₂
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.Bignum.RISCV64.exec_addi_lit (m := 0) (by decide), ?_⟩
  generalize hs3 : s₂.write .s11 (s₂.gpr .t2 + BitVec.ofNat 64 0) = s₃
  have t23 : s₃.gpr .s11 = fb s0 := by
    rw [← hs3, gpr_write_self, ← hs2]; simp only [BitVec.add_zero]; exact t21
  have g3 : ∀ r, r ≠ .t2 → r ≠ .s11 → s₃.gpr r = s0.gpr r := fun r hr hr' => by
    rw [← hs3, gpr_write_of_ne _ _ hr', ← hs2]; exact g1 r hr
  have w3 : s₃.wr = kF s0 :: s0.wr := by rw [← hs3, ← hs2]; exact w1
  refine Spill.save_ok (b := .s11) (l := argL) (by rw [t23]; exact hal) argL_fits.1
    (fun p hp => by rw [t23, w3]; exact inF p.2 (by have := (argL_le p hp).2; omega_arith)) ?_
  generalize hs4 : ({ s₃ with mem := Spill.saveMem s₃.mem (s₃.gpr .s11) s₃.gpr argL } : State) = s₄
  have t24 : s₄.gpr .s11 = fb s0 := by rw [← hs4]; exact t23
  have w4 : s₄.wr = kF s0 :: s0.wr := by rw [← hs4]; exact w3
  have r4 : s₄.rd = s0.rd := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  have sy4 : s₄.syms = s0.syms := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  have sp4 : s₄.sp = fb s0 := by rw [← hs4, ← hs3, ← hs2, ← hs1]; rfl
  -- the memory so far: the frame's slots
  have m4 : s₄.mem = Spill.saveMem (Spill.saveMem s0.mem (fb s0) s₁.gpr svL) (fb s0) s₃.gpr argL := by
    rw [← hs4, t23, ← hs3, ← hs2, t21]; simp only [mem_write]; rw [← hs1]; rfl
  have fK : Frame [kF s0] s0.mem s₄.mem := by
    rw [m4]
    exact (Spill.saveMem_frame_base (fun p hp => by have := svL_le p hp; omega_arith) (by decide) _ _ _).trans
      (Spill.saveMem_frame_base (fun p hp => by have := (argL_le p hp).2; omega_arith) (by decide) _ _ _)
  have sv4 : Spill.Saved (fb s0) s0.gpr svL s₄.mem := by
    have a := (Spill.saveMem_saved svL_fits s0.mem (fb s0) s₁.gpr).frame
      (Spill.saveMem_frame (lo := 104) (n := 64) argL_le (by decide) _ (fb s0) s₃.gpr)
      (fun p hp ρ hρ => by
        simp only [List.mem_singleton] at hρ; subst hρ
        have := svL_le p hp
        exact fw_fw h (.inl (by omega_arith)) (by omega_arith) (by decide))
    rw [m4]
    exact fun p hp => (a p hp).trans (g1 p.1 (svL_t2 p hp))
  have args4 : Spill.Saved (fb s0) s0.gpr argL s₄.mem := by
    have a := Spill.saveMem_saved argL_fits (Spill.saveMem s0.mem (fb s0) s₁.gpr svL) (fb s0) s₃.gpr
    rw [m4]
    exact fun p hp => (a p hp).trans (g3 p.1 (argL_ne p hp).1 (argL_ne p hp).2)
  -- the stack arguments
  have hr : ∀ {m'}, Frame [kF s0] s₄.mem m' → ∀ {i}, i < 3 → m'.readW (stackArgAddr s0 i) 64 = stackArg s0 i :=
    fun f _ hi => stackArg_keep h ((fK.trans f).sub fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact ⟨cF s0, by simp, kF_sub s0⟩) hi
  have wK : ∀ (m : Mem) {o}, o + 8 ≤ 192 → ∀ v : BitVec 64, Frame [kF s0] m (m.writeW (fw s0 o) v) :=
    fun m o ho v => (Frame.refl _ m).writeW (r := kF s0) List.mem_cons_self v (kF_contains ho)
  have kw : ∀ {t : State}, t.wr = kF s0 :: s0.wr → kF s0 ∈ t.wr := fun e => by rw [e]; exact List.mem_cons_self
  refine WP.block_cons_iff.mpr ⟨_, ldArg_eq (i := 0) h t24 r4 (by decide) rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, stf_eq h (by simp only [gpr_write, reduceCtorEq, ↓reduceIte, t24])
    (kw (by simp only [wr_write, w4])) (o := oRandLen) (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, ldArg_eq (i := 1) h (by simp only [gpr_write, reduceCtorEq, ↓reduceIte, t24])
    (by simp only [rd_write, r4]) (by decide) rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, ldArg_eq (i := 2) h (by simp only [gpr_write, reduceCtorEq, ↓reduceIte, t24])
    (by simp only [rd_write, r4]) (by decide) rfl, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, stf_eq h (by simp only [gpr_write, reduceCtorEq, ↓reduceIte, t24])
    (kw (by simp only [wr_write, w4])) (o := oWsLen) (by decide) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_li (imm := 0) (by decide), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, stf_eq h (by simp only [gpr_write, reduceCtorEq, ↓reduceIte, t24])
    (kw (by simp only [wr_write, w4])) (o := oRead) (by decide) (by decide), WP.block_nil ?_⟩
  simp only [gpr_write_self, mem_write]
  generalize hv0 : s₄.mem.readW (stackArgAddr s0 0) 64 = v0
  have e0 : v0 = stackArg s0 0 := by rw [← hv0]; exact hr (Frame.refl _ _) (by decide)
  generalize hm5 : s₄.mem.writeW (fw s0 oRandLen) v0 = m5
  have f5 : Frame [kF s0] s₄.mem m5 := by rw [← hm5]; exact wK _ (by decide) _
  have e1 : m5.readW (stackArgAddr s0 1) 64 = stackArg s0 1 := hr f5 (by decide)
  have e2 : m5.readW (stackArgAddr s0 2) 64 = stackArg s0 2 := hr f5 (by decide)
  rw [e1, e2]
  generalize hm6 : m5.writeW (fw s0 oWsLen) (stackArg s0 2) = m6
  generalize hm7 : m6.writeW (fw s0 oRead) (BitVec.ofInt 64 0) = m7
  -- the last three stores, in `[168, 192)` of the frame
  have f7 : Frame [⟨fw s0 168, 24⟩] s₄.mem m7 := by
    rw [← hm7, ← hm6, ← hm5]
    have c : ∀ o, 168 ≤ o → o + 8 ≤ 192 → (⟨fw s0 168, 24⟩ : Region).Contains (fw s0 o) 8 := fun o h1 h2 =>
      Offset.contains _ h1 (by omega_arith) (by omega_arith)
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c 168 (by decide) (by decide))).writeW List.mem_cons_self _
      (c 184 (by decide) (by decide))).writeW List.mem_cons_self _ (c 176 (by decide) (by decide))
  have d7 : ∀ o, o + 8 ≤ 168 → ∀ ρ ∈ [(⟨fw s0 168, 24⟩ : Region)], Region.Disjoint ⟨fb s0 + BitVec.ofNat 64 o, 8⟩ ρ :=
    fun o ho ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ
      exact fw_fw h (.inl ho) (by omega_arith) (by decide)
  have fK7 : Frame [kF s0] s₄.mem m7 := f7.sub fun ρ hρ => by
    simp only [List.mem_singleton] at hρ; subst hρ
    exact ⟨kF s0, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  refine ⟨⟨h, sp4, r4, w4, t24, sv4.frame f7 fun p hp => d7 p.2 (by have := svL_le p hp; omega_arith),
    args4.frame f7 fun p hp => d7 p.2 (by have := (argL_le p hp).2; omega_arith), ?_, ?_,
    (fK.trans fK7).sub fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact ⟨cF s0, by simp, kF_sub s0⟩⟩, ?_, ?_, sy4⟩
  · rw [← hm7, Mem.readW_writeW_sep (fw_sep h (by decide) (by decide) (by decide)) (by decide),
      ← hm6, Mem.readW_writeW_sep (fw_sep h (by decide) (by decide) (by decide)) (by decide),
      ← hm5, Mem.readW_writeW_self64, e0]
  · rw [← hm7, Mem.readW_writeW_sep (fw_sep h (by decide) (by decide) (by decide)) (by decide),
      ← hm6, Mem.readW_writeW_self64]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
  · rw [← hm7, Mem.readW_writeW_self64]; rfl

/-! ## The exit -/

theorem restore_ok {s : State} (h : Fr s0 s) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ preserved, t.gpr r = s0.gpr r) ∧ t.gpr .ra = s0.gpr .ra ∧ t.gpr .a0 = s.gpr .a0 ∧
        t.mem = s.mem ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [restore_eq]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), ?_⟩
  refine WP.mono (Spill.restore_wp (b := .t2) (B := fb s0) (fb_al h.pre)
    (by rw [gpr_write_self, h.sp, BitVec.add_zero]) rsL_fits.1 rsL_restorable
    (fun p hp => by
      rw [rd_write, wr_write, h.wr]
      have := svL_le p (rsL_sub p hp)
      exact ⟨kF s0, List.mem_append_right _ List.mem_cons_self, kF_contains (by omega_arith)⟩)
    (by rw [mem_write]; exact h.sv.sub rsL_sub)) fun u R => ?_
  have uother : ∀ r, r ∉ rsL.map Prod.fst → r ≠ .t2 → u.gpr r = s.gpr r := fun r hr h2 => by
    rw [R.other r hr, gpr_write_of_ne _ _ h2]
  refine ⟨fun r hr => R.gpr _ (rsL_saved r hr), R.gpr (.ra, 96) (by decide), uother _ (by decide) (by decide),
    by rw [R.mem, mem_write], by rw [R.sp, sp_write], by rw [R.rd, rd_write], by rw [R.wr, wr_write]⟩

/-! ## The function -/

/-- The body between the entry and the restore. -/
def mid (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  .seq VG.Impl.RsaKeyGen.RISCV64.Candidate.zeroOut
    (.seq (.block ([ldf .t3 oRandLen, ldf .t4 oOutLen] ++ VG.Impl.MillerRabin.RISCV64.Search.geFlag .t2 .t3 .t4))
      (.ite (.zero .t2) VG.Impl.RsaKeyGen.RISCV64.Candidate.finNone
        (VG.Impl.RsaKeyGen.RISCV64.Candidate.main trial name round)))

theorem wp_seq3 {a b c d : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a (.seq b c)) s P)
    (k : ∀ u, P u → WP isa d u Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun x hx => ?_
  rw [WP.seq_iff] at hx ⊢
  refine WP.mono hx fun y hy => ?_
  rw [WP.seq_iff]
  exact WP.mono hy k

/-- The whole function, from what the body between the entry and the
restore does. -/
theorem code_ok (h : CIn s0) {trial round : Prog isa} {name : String} {Q : BitVec 64 → Mem → Prop}
    (hm : ∀ s, Fr s0 s → s.gpr .s6 = stackArg s0 1 → s.mem.readW (fw s0 oRead) 64 = 0 → s.syms = s0.syms →
      WP isa (mid trial name round) s fun u => Fr s0 u ∧ Q (u.gpr .a0) u.mem) :
    WP isa (VG.Impl.RsaKeyGen.RISCV64.Candidate.code trial name round) s0
      fun t => abiPreserved s0 t ∧ Q (t.gpr .a0) t.mem := by
  unfold VG.Impl.RsaKeyGen.RISCV64.Candidate.code VG.Impl.RsaKeyGen.RISCV64.Candidate.body
  refine WP.alloc (by decide) (by have := h.spLo; show 192 ≤ s0.sp.toNat; omega_arith) ?_
  simp only [VG.Impl.RsaKeyGen.RISCV64.Candidate.seqs]
  refine WP.seq (WP.mono (entry_ok h) fun s ⟨fs, s6, r0, sy⟩ => ?_)
  refine wp_seq3 (hm s fs s6 r0 sy) fun u ⟨fu, qu⟩ => ?_
  refine WP.mono (restore_ok fu) fun v ⟨sv, ra, a0, vm, vsp, _, vwr⟩ => ?_
  have hfr : freed frameBytes v = { v with sp := s0.sp, wr := s0.wr } :=
    freed_eq (by rw [vwr, fu.wr]; rfl) (by rw [vsp, fu.sp]; rfl)
  rw [hfr]
  exact ⟨⟨sv, rfl, ra⟩, by show Q (v.gpr .a0) v.mem; rw [a0, vm]; exact qu⟩

end

end VG.Proof.RsaKeyGen.RISCV64.Cand
