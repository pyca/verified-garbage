import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# One of the blocks after the last group

`remBody_ok`: `StitchZH.remBody src` is, on the lower lanes, the SSE block
`remSse src` (`WP.lane0`): the block at `src + r10` and its keystream at
`r11 + r10 + 768` added, stored to `rdx + r10`, and the result, byte-reversed
and with `Y` (`xmm2`) added, multiplied by the power at `rax + r10` and added
to the products in `xmm8` … `xmm10` (`Pclmul.acc_ok`); `Y` cleared.
-/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only acc_ok eval_pxor)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchZH (remBody remNext)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- The SSE block of `remBody src`. -/
def remSse (src : Reg) : List Instr :=
  [.movdquLoad .xmm13 (atIx src .r10 0), .movdquLoad .xmm12 (atIx .r11 .r10 768),
   .xop (.bin .pxor .xmm13 .xmm12), .movdquStore (atIx .rdx .r10 0) .xmm13,
   .xop (.bin .pshufb .xmm13 .xmm0), .xop (.bin .pxor .xmm13 .xmm2), .xop (.bin .pxor .xmm2 .xmm2),
   .movdquLoad .xmm12 (atIx .rax .r10 0)] ++ Impl.Gcm.X86_64.Pclmul.acc .xmm13 .xmm12

theorem lane0_remBody (src : Reg) : lane0Block (remBody src) = some (remSse src) := rfl

/-- The registers `remBody` writes. -/
abbrev remRegs : List XReg := [.xmm13, .xmm12, .xmm2, .xmm8, .xmm9, .xmm10, .xmm11]

theorem remBody_dst (src : Reg) : ∀ r, r ∉ remRegs → r ∉ (remBody src).filterMap vdst := by
  intro r hr
  simp only [remRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  simp [remBody, Impl.Gcm.X86_64.StitchAvx.acc, vdst, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
    Ne.symm h5, Ne.symm h6, Ne.symm h7, h1, h2]

/-- The block at `src + r10` and its keystream added, and stored to `rdx + r10`. -/
theorem remXor_ok (src : Reg) (t : State)
    (hinS : InRegions (t.rd ++ t.wr) (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hinK : InRegions (t.rd ++ t.wr) (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 16)
    (hinD : InRegions t.wr (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm13 (atIx src .r10 0), .movdquLoad .xmm12 (atIx .r11 .r10 768),
      .xop (.bin .pxor .xmm13 .xmm12), .movdquStore (atIx .rdx .r10 0) .xmm13]) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int))
        (t.mem.readW (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ^^^
          t.mem.readW (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 128) ∧
      t'.xmm .xmm13 = t.mem.readW (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ^^^
          t.mem.readW (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 128 ∧
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r, r ≠ .xmm13 → r ≠ .xmm12 → t'.xmm r = t.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    State.load128, State.store128, ea_atIx, hinS, hinK, hinD, eval_pxor, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false]⟩

/-- The block in `xmm13` byte-reversed and `Y` added to it, `Y` cleared, and
the power at `rax + r10` loaded. -/
theorem remPrep_ok (t : State) (h0 : t.xmm .xmm0 = revMask)
    (hinP : InRegions (t.rd ++ t.wr) (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16) :
    WP isa (.block [.xop (.bin .pshufb .xmm13 .xmm0), .xop (.bin .pxor .xmm13 .xmm2), .xop (.bin .pxor .xmm2 .xmm2),
      .movdquLoad .xmm12 (atIx .rax .r10 0)]) t fun t' =>
      t'.xmm .xmm13 = XBinOp.eval .pshufb (t.xmm .xmm13) revMask ^^^ t.xmm .xmm2 ∧ t'.xmm .xmm2 = 0 ∧
      t'.xmm .xmm12 = t.mem.readW (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ∧
      Only [.xmm13, .xmm2, .xmm12] t t' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    State.load128, ea_atIx, hinP, h0, eval_pxor, reduceCtorEq, BitVec.xor_self,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

theorem remSse_ok (src : Reg) (t : State) (h0 : t.xmm .xmm0 = revMask)
    (hinS : InRegions (t.rd ++ t.wr) (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hinK : InRegions (t.rd ++ t.wr) (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 16)
    (hinD : InRegions t.wr (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hinP : InRegions (t.rd ++ t.wr) (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hDP : Mem.Sep (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) (128 / 8)
      (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) (128 / 8)) :
    WP isa (.block (remSse src)) t fun t' =>
      t'.mem = t.mem.writeW (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int))
        (t.mem.readW (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ^^^
          t.mem.readW (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 128) ∧
      prod t' = (prod t).acc
        (XBinOp.eval .pshufb (t.mem.readW (t.gpr src + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ^^^
          t.mem.readW (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 128) revMask ^^^
          t.xmm .xmm2)
        (t.mem.readW (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) ∧
      t'.xmm .xmm2 = 0 ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r, r ∉ remRegs → t'.xmm r = t.xmm r) := by
  rw [remSse, show ([.movdquLoad .xmm13 (atIx src .r10 0), .movdquLoad .xmm12 (atIx .r11 .r10 768),
      .xop (.bin .pxor .xmm13 .xmm12), .movdquStore (atIx .rdx .r10 0) .xmm13,
      .xop (.bin .pshufb .xmm13 .xmm0), .xop (.bin .pxor .xmm13 .xmm2), .xop (.bin .pxor .xmm2 .xmm2),
      .movdquLoad .xmm12 (atIx .rax .r10 0)] : List Instr) =
    [.movdquLoad .xmm13 (atIx src .r10 0), .movdquLoad .xmm12 (atIx .r11 .r10 768),
      .xop (.bin .pxor .xmm13 .xmm12), .movdquStore (atIx .rdx .r10 0) .xmm13] ++
    [.xop (.bin .pshufb .xmm13 .xmm0), .xop (.bin .pxor .xmm13 .xmm2), .xop (.bin .pxor .xmm2 .xmm2),
      .movdquLoad .xmm12 (atIx .rax .r10 0)] from rfl, List.append_assoc, WP.block_append_iff]
  refine WP.mono (remXor_ok src t hinS hinK hinD) fun t₁ ⟨m₁, x₁, g₁, rd₁, wr₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (remPrep_ok t₁ (by rw [k₁ _ (by decide) (by decide)]; exact h0)
    (by rw [g₁, rd₁, wr₁]; exact hinP)) fun t₂ ⟨x13, x2, x12, o₂⟩ => ?_
  refine WP.mono (acc_ok .xmm13 .xmm12 t₂ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t' ⟨p', o'⟩ => ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [o'.mem, o₂.mem, m₁]
  · rw [p', x13, x12, x₁, o₂.prod (by decide) (by decide) (by decide), g₁, m₁,
      Mem.readW_writeW_sep (fun x h₁ h₂ => hDP x h₂ h₁) (by decide), k₁ _ (by decide) (by decide)]
    simp only [prod, k₁ .xmm8 (by decide) (by decide), k₁ .xmm9 (by decide) (by decide),
      k₁ .xmm10 (by decide) (by decide)]
  · rw [o'.xmm _ (by decide), x2]
  · rw [o'.rd, o₂.rd, rd₁]
  · rw [o'.wr, o₂.wr, wr₁]
  · simp only [remRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    rw [o'.xmm r (by simp [h4, h5, h6, h7]), o₂.xmm r (by simp [h1, h2, h3]), k₁ r h1 h2]

theorem remBody_noGpr (src : Reg) : (remBody src).all noGpr = true := rfl

/-- `remBody src`, on the lower lanes. -/
theorem remBody_ok (src : Reg) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hinS : InRegions (s.rd ++ s.wr) (s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hinK : InRegions (s.rd ++ s.wr) (s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 16)
    (hinD : InRegions s.wr (s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hinP : InRegions (s.rd ++ s.wr) (s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hDP : Mem.Sep (s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) (128 / 8)
      (s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) (128 / 8)) :
    WP isa (.block (remBody src)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdx + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int))
        (s.mem.readW (s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ^^^
          s.mem.readW (s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 128) ∧
      prod (s'.proj 0) = (prod (s.proj 0)).acc
        (XBinOp.eval .pshufb (s.mem.readW (s.gpr src + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128 ^^^
          s.mem.readW (s.gpr .r11 + s.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 128) revMask ^^^
          s.lane .xmm2 0)
        (s.mem.readW (s.gpr .rax + s.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) ∧
      s'.lane .xmm2 0 = 0 ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ remRegs → s'.lane r 0 = s.lane r 0) := by
  refine WP.mono (WP.lane0 (lane0_remBody src) (remSse_ok src (s.proj 0) (by simpa using h0) hinS hinK hinD hinP hDP))
    fun s' ⟨⟨m', p', y', rd', wr', k'⟩, _, hg⟩ => ⟨by simpa using m', by simpa using p', by simpa using y',
      hg (remBody_noGpr src), by simpa using rd', by simpa using wr', fun r hr => by simpa using k' r hr⟩

/-- `add r10, 16`, `sub r9, 1`, `cmp r9, 16`. -/
theorem remNext_ok (s : State) {m : Nat} (h1 : 1 ≤ m) (h15 : m ≤ 15) {i : Nat}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + m)) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * i)) :
    WP isa (.block remNext) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * (i + 1)) ∧ s'.gpr .r9 = BitVec.ofNat 64 (16 + (m - 1)) ∧
      s'.zf = some (decide (m = 1)) ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have a10 : BitVec.ofNat 64 (16 * i) + 16 = BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]; congr 1
  have s9 : BitVec.ofNat 64 (16 + m) - 1 = BitVec.ofNat 64 (16 + (m - 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  have z9 : (BitVec.ofNat 64 (16 + (m - 1)) - 16 == 0) = decide (m = 1) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega) (by omega)]
    by_cases h : m = 1
    · subst h; rfl
    · have : BitVec.ofNat 64 (16 + (m - 1) - 16) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 + (m - 1) - 16 < 2 ^ 64 by omega)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega
      rw [beq_false_of_ne this, decide_eq_false h]
  apply WP.of_runBlock
  simp only [remNext, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, h9, h10, a10, s9, z9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl, trivial,
    trivial, trivial⟩

end VG.Proof.Gcm.X86_64.StitchZH
