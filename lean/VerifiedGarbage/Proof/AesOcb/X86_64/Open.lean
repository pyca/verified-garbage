module

public import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
import VerifiedGarbage.Proof.AesOcb.X86_64.Body
import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Impl.AesOcb.X86_64
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.AesOcb.X86_64.Env
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.AesOcb.X86_64.XorPad
import VerifiedGarbage.Proof.AesOcb.X86_64.Pass
import VerifiedGarbage.Proof.AesOcb.X86_64.Words
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `AesOcb.X86_64.CmpMask`, which this module and modules that import it used -/

section

/-!
# AES-OCB on x86-64: checking the tag and masking the data (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` ORs the XORs of the
first `tag_len` bytes of the received tag (at `W`) and the computed one (at
`W + t2O`) and leaves 1 at `W` if the OR is 0, else 0 (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − ok`: the data stays if the tags were
equal, and is zeroed if not (`mask_ok`). Its whole blocks go 16 bytes at a
time, with `0 − ok` in both halves of `xmm6` (`maskBlocks_wp`), the rest one
at a time (`maskBytes_wp`); both loops keep the first `j` bytes masked
(`MInv`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e eval_ne length_bytesAt)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat bytesAt_succ)

/-! ## `cmp` -/

theorem setWidth_xor_eq_zero (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64 = 0#64) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 63` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit {x : BitVec 64} (h : x.toNat < 256) : (x - 1#64) >>> 63 = if x = 0#64 then 1#64 else 0#64 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 64 - 1 % 2 ^ 64 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith), Nat.div_eq_of_lt (by omega_arith)]

/-- One step of `cmp`. -/
theorem cmpStep_ok (s : State) {W : Addr} {j T : Nat} (h15 : s.gpr .r15 = W)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (h12 : s.gpr .r12 = BitVec.ofNat 64 T)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 j) 1)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .r15, index := some .rcx },
        .movzx8 .r8 { base := .r15, index := some .rcx, disp := t2O }, .alu .xor .rax (.reg .r8),
        .alu .or .rdx (.reg .rax), addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem ∧
      s'.gpr .rdx = s.gpr .rdx ||| ((s.mem (W + BitVec.ofNat 64 j)).setWidth 64 ^^^
        (s.mem (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j)).setWidth 64) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 T == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ := ea_index s h15 h1
  have ea₂ : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofNat 64 128 =
      W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j := ea_index_disp s (d := 128) h15 h1
  refine ⟨_, by orun [ea₁, ea₂, r₀, r₁], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- `cmp`: 1 at `W` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (W + BitVec.ofNat 64 tagO)
        (if bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have r₀ := E.perm.wR6 hwn hwlt (show 224 + 8 ≤ 640 by decide)
  simp only [tlO] at htl
  obtain ⟨s₁, run₁, rdx₁, rcx₁, r12₁, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.alu .xor .rdx (.reg .rdx), .mov .rcx (.imm 0), ld .r12 .r15 tlO] s = some s₁ ∧
      s₁.gpr .rdx = 0#64 ∧ s₁.gpr .rcx = BitVec.ofNat 64 0 ∧ s₁.gpr .r12 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.r15, r₀, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, htl]
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
    all_goals rfl
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hR : ∀ {d j : Nat}, d + j < 640 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 :=
    fun h => by rw [Offset.add_add]; exact E.perm.wR6 hwn hwlt (by omega_arith)
  -- The loop: the OR of the XORs of the first `j` bytes in `rdx`.
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .ne)
    (Q := fun u => (u.gpr .rdx).toNat < 256 ∧
      (u.gpr .rdx = 0#64 ↔ bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = tl - j ∧ j < tl ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧
      u.gpr .r12 = BitVec.ofNat 64 tl ∧ (u.gpr .rdx).toNat < 256 ∧
      (u.gpr .rdx = 0#64 ↔ bytesAt s.mem W j = bytesAt s.mem (W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ?_ (tl - 0) _
    ⟨0, rfl, by omega_arith, rcx₁, r12₁, by rw [rdx₁]; decide, by rw [rdx₁]; simp [bytesAt], m₁,
      fun r _ h₂ h₃ _ h₅ => g₁ r h₂ h₃ h₅, rd₁, wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, rcx, r12, lt, iff, mem, g, rd, wr⟩
    have h15 : u.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
    obtain ⟨u', run', mem', rdx', rcx', zf', g', rd', wr'⟩ := cmpStep_ok u (W := W) (j := j) (T := tl) h15 rcx r12
      (by rw [rd, wr, show W + BitVec.ofNat 64 j = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 j by simp]
          exact hR (by omega_arith))
      (by rw [rd, wr]; exact hR (by omega_arith))
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at rdx'
    have lt' : (u'.gpr .rdx).toNat < 256 := by
      rw [rdx', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (toNat_setWidth_xor _ _)
    have iff' : u'.gpr .rdx = 0#64 ↔
        bytesAt s.mem W (j + 1) = bytesAt s.mem (W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [rdx', BitVec.or_eq_zero_iff, iff, setWidth_xor_eq_zero, bytesAt_succ, bytesAt_succ]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]; rfl
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have hz : u'.zf = some (decide (j + 1 = tl)) := by
      rw [zf', Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u'.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄ h₅]
    by_cases he : j + 1 = tl
    · left
      exact ⟨(eval_ne hz).trans (by simp [he]), lt', by rw [iff', he], by rw [mem', mem], gg, by rw [rd', rd],
        by rw [wr', wr]⟩
    · right
      exact ⟨(eval_ne hz).trans (by simp [he]), tl - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, rcx',
        by rw [g' _ (by decide) (by decide) (by decide) (by decide), r12], lt', iff', by rw [mem', mem], gg,
        by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, rd, wr⟩ := hu
    have h15 : u.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
    have w₀ : InRegions u.wr (W + BitVec.ofNat 64 0) 8 := by rw [wr]; exact E.perm.wW6 hwn hwlt (by decide)
    refine WP.of_runBlock ⟨_, by orun [h15, w₀], ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_setFlags, mem_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, sext1, mem]
      rw [show BitVec.ofNat 64 1 = 1#64 from rfl, okBit lt]
      by_cases he : bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl
      · simp only [iff.mpr he, he, ↓reduceIte]; rfl
      · simp only [mt iff.mp he, he, ↓reduceIte]; rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
      exact g r h₁ h₂ h₃ h₄ h₅
    all_goals simp only [rd, wr]

/-! ## `mask` -/

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1#64 else 0#64))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then 1#64 else 0#64) = 1#64 from rfl,
      show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

/-- `0 − ok` in both halves of an SSE register. -/
def maskX (c : Bool) : BitVec 128 := if c then BitVec.allOnes 128 else 0

theorem mask_xmm (c : Bool) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ ((0 : BitVec 64) - (if c then 1#64 else 0#64)))
      ((0 : BitVec 64) ++ ((0 : BitVec 64) - (if c then 1#64 else 0#64))) = maskX c := by
  cases c <;> decide

theorem mask_block (v : BitVec 128) (c : Bool) : XBinOp.eval .pand v (maskX c) = if c then v else 0 := by
  cases c
  · simp [maskX, XBinOp.eval]
  · simp only [maskX, XBinOp.eval, ite_true, BitVec.and_allOnes]

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h3 : s.gpr .rbx = P)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = 0 - (if c then 1#64 else 0#64))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax maskAt, .alu .and .rax (.reg .rdx), .store8 maskAt .rax, addi .rcx 1,
        .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea := ea_index s h3 h1
  refine ⟨_, by orun [maskAt, ea, rq, wq], ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdx,
      mask_byte]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
  all_goals rfl

theorem maskBlock_ok (s : State) {P : Addr} {j w : Nat} {c : Bool} (hw : 0 < w) (hw' : w < 2 ^ 64)
    (h3 : s.gpr .rbx = P) (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (hx6 : s.xmm .xmm6 = maskX c)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 w)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 16) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm7 maskAt, .xop (.bin .pand .xmm7 .xmm6), .movdquStore maskAt .xmm7,
        addi .rcx 16, .alu .sub .r8 (.imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j)
        (if c then s.mem.readW (P + BitVec.ofNat 64 j) 128 else (0 : BitVec 128)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 16) ∧ s'.gpr .r8 = BitVec.ofNat 64 (w - 1) ∧
      s'.zf = some (decide (w = 1)) ∧ s'.xmm .xmm6 = s.xmm .xmm6 ∧
      (∀ r, r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea := ea_index s h3 h1
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide
  refine ⟨_, by orun [maskAt, ea, rq, wq, State.load128, State.store128, XOp.exec], ?_, ?_, ?_, ?_, ?_,
    fun r h₁ h₂ => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm, ite_true, reduceCtorEq, ite_false, hx6,
      mask_block]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h1, e16,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq, h8, sext1]
    rw [Proof.AesCcm.X86_64.ofNat_sub (by omega_arith) hw']
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setXmm, ite_true, ite_false,
      reduceCtorEq, h8, sext1]
    rw [Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
  · simp only [xmm_setReg, xmm_arithFlags, xmm_setXmm, reduceCtorEq, ite_false]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setXmm, h₁, h₂, ite_false]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

theorem mask_add (m : Mem) (P : Addr) (c : Bool) (a b : Nat) :
    (if c then bytesAt m P (a + b) else zeros (a + b)) =
      (if c then bytesAt m P a else zeros a) ++
        (if c then bytesAt m (P + BitVec.ofNat 64 a) b else zeros b) := by
  cases c <;> simp [zeros, Proof.Ocb.bytesAt_append, ← List.replicate_append_replicate]

/-- A block written is its 16 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 128) :
    m.writeW a v = writeBytes m a ((List.range 16).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 16 v

/-- The block at `a`, or zero, written back: the 16 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 128 else (0 : BitVec 128)) =
      writeBytes m' a (if c then bytesAt m a 16 else zeros 16) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp [zeros]; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 16) hk]
    rfl

/-- What both loops keep: the first `j` bytes of the data masked. -/
structure MInv (s s₁ t : State) (D : Addr) (c : Bool) (j : Nat) : Prop where
  rcx : t.gpr .rcx = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j)
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → t.gpr r = s₁.gpr r
  xmm6 : t.xmm .xmm6 = s₁.xmm .xmm6
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem MInv.frame {s s₁ t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s s₁ t D c j) :
    Frame [⟨D, j⟩] s.mem t.mem := by
  rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)

/-- The bytes from `j` on are as they were. -/
theorem MInv.at {s s₁ t : State} {D : Addr} {c : Bool} {j i : Nat} (h : MInv s s₁ t D c j) (hi : j ≤ i)
    (hi' : i < 2 ^ 64) : t.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) :=
  (h.frame (D + BitVec.ofNat 64 i) fun r hr hcon => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Mem.sub_ofNat_toNat D hi'] at hcon; omega_arith)

theorem MInv.readW {s s₁ t : State} {D : Addr} {c : Bool} {j : Nat} (h : MInv s s₁ t D c j)
    (hj : j + 16 < 2 ^ 64) : t.mem.readW (D + BitVec.ofNat 64 j) 128 = s.mem.readW (D + BitVec.ofNat 64 j) 128 := by
  refine Mem.readW_congr fun k hk => ?_
  simp only [Offset.add_add]
  exact h.at (by omega_arith) (by omega_arith)

/-- The blocks: from `j = 16 i`, with `w − i` blocks left in `r8`, to `16 w`. -/
theorem maskBlocks_wp {s s₁ t : State} {D : Addr} {n : Nat} {c : Bool} {i : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h3 : s₁.gpr .rbx = D) (hx6 : s₁.xmm .xmm6 = maskX c)
    (hi : i < n / 16) (ht : MInv s s₁ t D c (16 * i)) (h8 : t.gpr .r8 = BitVec.ofNat 64 (n / 16 - i)) :
    WP isa maskBlocks t fun t' => MInv s s₁ t' D c (16 * (n / 16)) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n / 16 - i ∧ i < n / 16 ∧ MInv s s₁ t D c (16 * i) ∧
      t.gpr .r8 = BitVec.ofNat 64 (n / 16 - i)) ?_ (n / 16 - i) t ⟨i, rfl, hi, ht, h8⟩
  rintro k t ⟨i, rfl, hi, ht, h8⟩
  have hin : 16 * i + 16 ≤ n := by omega_arith
  have cov (rs : List Region) (h : Covers [⟨D, n⟩] rs) : InRegions rs (D + BitVec.ofNat 64 (16 * i)) 16 :=
    h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hin (by omega_arith)⟩
  obtain ⟨t', run', mem', rcx', r8', zf', x6', g', rd', wr'⟩ := maskBlock_ok t (P := D) (j := 16 * i)
    (w := n / 16 - i) (c := c) (by omega_arith) (by omega_arith) (by rw [ht.keep _ (by decide) (by decide) (by decide), h3])
    ht.rcx (by rw [ht.xmm6, hx6]) h8 (by rw [ht.rd, ht.wr]; exact cov _ hD) (by rw [ht.wr]; exact cov _ hDw)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (16 * (i + 1)) else zeros (16 * (i + 1))) := by
    rw [mem', ht.readW (by omega_arith), ht.mem, writeW_mask, show 16 * (i + 1) = 16 * i + 16 by omega_arith, mask_add,
      ← writeBytes_append _ _ _ _ (by rw [length_mask, length_mask]; omega_arith), length_mask]
  have e1 : n / 16 - i - 1 = n / 16 - (i + 1) := by omega_arith
  have hz : t'.zf = some (decide (i + 1 = n / 16)) := by
    rw [zf']; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht' : MInv s s₁ t' D c (16 * (i + 1)) :=
    ⟨by rw [rcx', show 16 * (i + 1) = 16 * i + 16 by omega_arith], hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₂ h₃, ht.keep r h₁ h₂ h₃], by rw [x6', ht.xmm6], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = n / 16
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n / 16 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ht',
      by rw [r8', e1]⟩

/-- The last bytes: from `j < n` to `n`. -/
theorem maskBytes_wp {s s₁ t : State} {D : Addr} {n : Nat} {c : Bool} {j : Nat} (hn : n < 2 ^ 64)
    (hD : Covers [⟨D, n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨D, n⟩] s.wr)
    (h3 : s₁.gpr .rbx = D) (hdx : s₁.gpr .rdx = 0 - (if c then 1#64 else 0#64))
    (h12 : s₁.gpr .r12 = BitVec.ofNat 64 n) (hj : j < n) (ht : MInv s s₁ t D c j) :
    WP isa maskBytes t fun t' => MInv s s₁ t' D c n := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ MInv s s₁ t D c j) ?_ (n - j) t ⟨j, rfl, hj, ht⟩
  rintro k t ⟨j, rfl, hj, ht⟩
  obtain ⟨t', run', mem', rcx', zf', g', x', rd', wr'⟩ := maskStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h3]) ht.rcx
    (by rw [ht.keep _ (by decide) (by decide) (by decide), hdx])
    (by rw [ht.keep _ (by decide) (by decide) (by decide), h12]) (by rw [ht.rd, ht.wr]; exact in_of_covers hD hj hn)
    (by rw [ht.wr]; exact in_of_covers hDw hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', ht.at (Nat.le_refl _) (by omega_arith), ht.mem, mask_succ,
      writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
  have ht' : MInv s s₁ t' D c (j + 1) :=
    ⟨rcx', hmem, fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂, ht.keep r h₁ h₂ h₃], by rw [x', ht.xmm6], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, ht'⟩

theorem ofNat_shr4 {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

/-- Every byte of the data ANDed with `0 − ok`: its whole blocks, then the
rest. -/
theorem mask_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {D : Addr} {n : Nat}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 208) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) (hD : DBufN K W SP wn s D n) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa mask s fun t => EnvN K W SP wn t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  have r₁ := E.perm.wR6 hwn hwlt (show 208 + 8 ≤ 640 by decide)
  have r₂ := E.perm.wR6 hwn hwlt (show 216 + 8 ≤ 640 by decide)
  have r₃ := E.perm.wR6 hwn hwlt (show 0 + 8 ≤ 640 by decide)
  simp only [tagO] at hok
  have hn := hD.lt
  obtain ⟨s₁, run₁, m₁, h3₁, h12₁, hdx₁, h1₁, h8₁, zf₁, x6₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .rbx .r15 dataO, ld .r12 .r15 lenO, .alu .xor .rdx (.reg .rdx),
        .alu .sub .rdx (.mem (at_ .r15 tagO)), .xop (.movq .xmm6 .rdx), .xop (.bin .punpcklqdq .xmm6 .xmm6),
        .mov .rcx (.imm 0), mvr .r8 .r12, .shift .shr .r8 4, .alu .test .r8 (.reg .r8)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rbx = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 n ∧
      s₁.gpr .rdx = 0 - (if c then 1#64 else 0#64) ∧ s₁.gpr .rcx = BitVec.ofNat 64 0 ∧
      s₁.gpr .r8 = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧ s₁.xmm .xmm6 = maskX c ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [h15, r₁, r₂, r₃, hdata, hlen, hok, XOp.exec], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq,
        BitVec.xor_self, sext0, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq,
        BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq,
        ofNat_shr4 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false,
        reduceCtorEq, ofNat_shr4 hn, Proof.AesCcm.X86_64.and_self_beq (show n / 16 < 2 ^ 64 by omega_arith)]
    · simp only [xmm_arithFlags, xmm_setReg, xmm_setFlags, xmm_setXmm, gpr_setXmm, gpr_setReg, gpr_arithFlags,
        ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0, hok, XBinOp.eval]
      exact mask_xmm c
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, gpr_setXmm, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : EnvN K W SP wn s₁ := E.keep g₁ rd₁ wr₁
  have inv₀ : MInv s s₁ s₁ D c 0 :=
    ⟨h1₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun _ _ _ _ => rfl, rfl, rd₁, wr₁⟩
  -- The blocks.
  have words : WP isa (.ite .e (.block []) maskBlocks) s₁ fun t => MInv s s₁ t D c (16 * (n / 16)) := by
    refine WP.ite (decide (n / 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₀
    · exact maskBlocks_wp hn hD.rd hD.wr h3₁ x6₁ (Nat.pos_of_ne_zero (of_decide_eq_false hb))
        (by simpa using inv₀) (by rw [h8₁, Nat.sub_zero])
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono words fun t ht => ?_)
  -- The rest.
  have fin {t : State} (ht : MInv s s₁ t D c n) :
      EnvN K W SP wn t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) :=
    ⟨E₁.keep (fun r hr => ht.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [ht.rd, rd₁]) (by rw [ht.wr, wr₁]), ht.rd, ht.wr, ht.mem⟩
  obtain ⟨t₁, run₂, zf₂, g₂, m₂, x₂, rd₂, wr₂⟩ : ∃ t₁, runBlock isa [.alu .cmp .rcx (.reg .r12)] t = some t₁ ∧
      t₁.zf = some (decide (16 * (n / 16) = n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.xmm = t.xmm ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by orun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, ht.rcx, ht.keep .r12 (by decide) (by decide) (by decide), h12₁]
      rw [Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    all_goals rfl
  have ht₁ : MInv s s₁ t₁ D c (16 * (n / 16)) :=
    ⟨by rw [g₂, ht.rcx], by rw [m₂, ht.mem], fun r h₁ h₂ h₃ => by rw [g₂, ht.keep r h₁ h₂ h₃],
      by rw [x₂, ht.xmm6], by rw [rd₂, ht.rd], by rw [wr₂, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₂, ?_⟩)
  refine WP.ite (decide (16 * (n / 16) = n)) (eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · rw [← of_decide_eq_true hb] at fin ⊢; exact fin ht₁
  · exact WP.mono (maskBytes_wp hn hD.rd hD.wr h3₁ hdx₁ h12₁ (by have := of_decide_eq_false hb; omega_arith) ht₁)
      fun t' ht' => fin ht'

end VG.Proof.AesOcb.X86_64

end

end

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the copy of the received tag from `tag` to `W`
(`recv`), its comparison with the computed tag (`cmp`), the mask of the
data (`mask`), the result and `restore` (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar pad zeros)
open VG.Proof.Ocb (offAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame)

/-- `recv`: the `tl` bytes of the tag at `T` copied to `W`. -/
theorem recv_ok {K W SP : Addr} {s : State} {wn : Nat} (E : EnvN K W SP wn s) {T : Addr} {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htg : s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (hT : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, wn⟩)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa recv s fun t => t.mem = writeBytes s.mem W (bytesAt s.mem T tl) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, rbx₁, rsi₁, r12₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := recvArgs_ok E htg htl (hwn := hwn) (hwlt := hwlt)
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (copyLoop_ok s₁ (S := T) (Dd := W) (n := tl) (by omega_arith) (by omega_arith) rbx₁ rsi₁ rcx₁ r12₁
    (by rw [rd₁, wr₁]; exact hT) (by rw [wr₁]; exact covers_prefix E.perm.w (by omega_arith))
    (hTW.sub_right (Region.sub_prefix (by omega_arith)))) fun t ⟨m, _, g, rd, wr⟩ => ⟨by rw [m, m₁], ?_,
      by rw [rd, rd₁], by rw [wr, wr₁]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> rw [g _ (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide)]

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    {T : Addr} (Ar : Args s K W SP N A D R nl al n tl T) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («open» (callees v)) s fun s' => gprPreserved s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n := by
  have L := Ar.lay
  unfold «open» front
  refine WP.seq (pre_wp v Ar hsp hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 fun s₃ P₃ => ?_)
  obtain hD₃ : DBuf K W SP s₃ D n := Ar.data.of_eq P₃.rd P₃.wr
  refine WP.seq (WP.mono (bodyOpen_ok v L P₃.env Ar.rounds P₃.slots.rounds hD₃ P₃.slots.data P₃.slots.len P₃.ofs
    P₃.o0 P₃.ck (by rw [P₃.lstar]; exact P₃.tbl)) fun s₄ B => ?_)
  obtain F₄ : Frame (mutR W SP D n) s₃.mem s₄.mem := bodyR_mut B.frame
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₄ Ar.rounds).trans P₃.ciph
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K) := by
    rw [body_keep L Ar.data.w B.frame (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [body_keep L Ar.data.w B.frame (d := sumO) (by decide), P₃.sum]
  -- The tag, at `W + t2O`.
  refine WP.mono (tag_ok v L B.env Ar.rounds ((kept_read L Ar.data.w F₄ (d := 232) (by decide)).trans
    P₃.slots.rounds) (.inr rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR W SP D n) s₄.mem s₅.mem := tagR_mut (by decide) T₅.frame
  obtain S₅ := Slots.of_mut L Ar.data.w (F₄.trans F₅) P₃.slots
  -- The received tag, to `W`.
  obtain tg₅ : s₅.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T := by
    rw [kept_read L Ar.data.w (F₄.trans F₅) (d := tgO) (by decide), P₃.tg]
  obtain hTs : Buf W SP s₅ T tl := Ar.tag.of_eq (T₅.rd.trans (B.rd.trans P₃.rd)) (T₅.wr.trans (B.wr.trans P₃.wr))
  refine WP.seq (WP.mono (recv_ok T₅.env Ar.t1 Ar.t16 tg₅ S₅.tl hTs.rd Ar.tag.w) fun s₅' ⟨mr, gr, rdr, wrr⟩ => ?_)
  obtain E₅' : Env K W SP s₅' := T₅.env.keep gr rdr wrr
  obtain Fr : Frame [⟨W, tl⟩] s₅.mem s₅'.mem := by
    rw [mr]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  obtain Fr' : Frame (mutR W SP D n) s₅.mem s₅'.mem := Fr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := Ar.t16; omega_arith)⟩
  obtain S₅' := Slots.of_mut L Ar.data.w Fr' S₅
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₅' Ar.t1 Ar.t16 S₅'.tl) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ : Env K W SP s₆ := E₅'.keep (fun r hr => g₆ r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₆ wr₆
  obtain F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅'.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain k₆ : ∀ {d : Nat}, 8 ≤ d → d + 8 ≤ 3584 →
      s₆.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₆, readW_writeW_off _ (by simp only [tagO]; omega_arith) (by omega_arith) (by decide)]
  obtain hD₅ : DBuf K W SP s₅' D n := hD₃.of_eq (rdr.trans (T₅.rd.trans B.rd)) (wrr.trans (T₅.wr.trans B.wr))
  let c : Bool := decide (bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ (c := c) (by rw [k₆ (by decide) (by decide)]; exact S₅'.data)
    (by rw [k₆ (by decide) (by decide)]; exact S₅'.len) (hD₅.of_eq rd₆ wr₆)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  obtain F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain F₃₇ : Frame (mutR W SP D n) s₃.mem s₇.mem :=
    (((F₄.trans F₅).trans Fr').trans (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩)).trans
    (F₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- The result, and `restore`.
  obtain ok₇ : s₇.mem.readW (W + BitVec.ofNat 64 0) 64 = if c then 1#64 else 0#64 := by
    rw [F₇.readW (r := ⟨W + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
      (by decide), m₆]
    exact (Mem.readW_writeW_self64 _ _ _).trans (by simp only [c, decide_eq_true_eq])
  obtain r₀ : InRegions (s₇.rd ++ s₇.wr) (W + BitVec.ofNat 64 0) 8 := E₇.perm.wR (by decide)
  obtain ⟨s₈, run₈, rax₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [ld .rax .r15 tagO] s₇ = some s₈ ∧
      s₈.gpr .rax = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧
      s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.r15, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  obtain E₈ : Env K W SP s₈ := E₇.keep (fun r hr => g₈ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₈ wr₈
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ := restore_ok E₈ (by rw [m₈]; exact saved_mut L Ar.data.w F₃₇ P₃.saved)
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append, run₈, Option.bind_some, run₉], ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, savO) (by decide)
    · exact hg₉ (.rbp, savO + 8) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, savO + 16) (by decide)
    · exact hg₉ (.r13, savO + 24) (by decide)
    · exact hg₉ (.r14, savO + 32) (by decide)
    · exact hg₉ (.r15, savO + 40) (by decide)
  · have fall : Frame (entryR W :: mutR W SP D n) s.mem s₇.mem :=
      P₃.frame.trans (F₃₇.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, m₈, hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    obtain hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
    obtain i₃ : Spec.Ocb.ctxInv s₃.mem K R = Spec.Ocb.ctxInv s.mem K R := by
      unfold Spec.Ocb.ctxInv
      rw [bytesAt_frame P₃.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
        · exact (k_mut L Ar.data.k r hr).sub_left (Region.sub_prefix hRb)) (by omega_arith)]
    have hout := B.out
    rw [P₃.ciph, P₃.lstar, P₃.data, i₃] at hout
    have hofs := B.ofs
    rw [P₃.lstar] at hofs
    have hck := B.ck
    rw [P₃.ciph, P₃.lstar, P₃.data, i₃] at hck
    have hTn := Ar.tag.lt
    obtain recv : bytesAt s₅'.mem W tl = bytesAt s.mem T tl := by
      rw [mr, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) (by omega_arith), length_bytesAt,
        List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil,
        buf_mut Ar.tag Ar.td (F₄.trans F₅)]
      exact bytesAt_frame P₃.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
          · exact Ar.tag.w.sub_right (Region.sub_prefix (by decide))
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))
          · exact Ar.tag.stk.symm
          · exact Ar.td
          · exact Ar.tag.w.sub_right (Lay.wSub (by decide))) (by omega_arith)
    obtain t2₅ : bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
      bytesAt_frame Fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.base_disjoint W (e := t2O) (n := tl) (k := tl) (by have := Ar.t16; unfold t2O; omega_arith)
          (by have := Ar.t16; unfold t2O; omega_arith)).symm) (by omega_arith)
    have tagv := T₅.val
    rw [hck, hofs, ld₄, sum₄, cK₄] at tagv
    obtain d₉ : bytesAt s₉.mem D n = if c then bytesAt s₄.mem D n else zeros n := by
      have hn := Ar.data.lt
      obtain d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
        rw [bytesAt_frame F₆ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
            (by omega_arith),
          bytesAt_frame Fr (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))) (by omega_arith),
          bytesAt_frame T₅.frame (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.w.sub_right (Lay.wSub (by decide))
            · exact Ar.data.stk.symm) (by omega_arith)]
      rw [hm₉, m₈, m₇, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) hn, length_mask,
        List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₆]
    rw [hax₉, rax₈, d₉, hout]
    rw [Proof.Ocb.decryptWith_eq]
    simp only [length_bytesAt, List.length_drop]
    obtain hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
        (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem T tl) := fun x hx => by
      show decide (_ = _) = true ↔ _
      rw [recv, t2₅, hx, decide_eq_true_iff, eq_comm]
    by_cases hr : 0 < n % 16
    · have h' : n - 16 * (n / 16) > 0 := by omega_arith
      simp only [h', hr, ↓reduceIte] at tagv ⊢
      rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
      obtain hc := hc _ rfl
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
    · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_arith
      simp only [h', hr, ↓reduceIte] at tagv ⊢
      rw [bytesAt_take_block _ _ Ar.t16, tagv] at hc
      obtain hc := hc _ rfl
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openPreX s) :
    WP isa («open» (callees v)) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' :=
  open_wp' v (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.X86_64
