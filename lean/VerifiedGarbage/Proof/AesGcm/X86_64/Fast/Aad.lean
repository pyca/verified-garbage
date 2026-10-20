module

public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM `seal_split`'s path for TLS records: the additional data

Untrusted: everything here is checked by Lean. `aadMul_ok`: the block at `T`,
byte-reversed, times the prepared `H'` at `ctx + 272` (`vg_ghash_pclmul`'s
`zero`, `acc` and `reduce`), byte-reversed again into the state's
accumulator; for a `T₁` that multiplies as `H'` (`Short.IsH1`), one step of
`GHASH` from zero.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Fast VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Short (IsH1)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Only const_ok ldrev_ok zero_ok acc_ok reduce_ok prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt ghashFrom zeros padLen ofBytes)
open VG.Spec.Aes (bytesAt)

/-- A 16-byte load into `x`, unchanged. -/
theorem ld_ok (x : XReg) (b : Reg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad x (Impl.Gcm.X86_64.Pclmul.at_ b d)]) s fun s' =>
      s'.xmm x = s.mem.readW (s.gpr b + BitVec.ofInt 64 (d : Int)) 128 ∧ Only [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm, State.load128,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- `pshufb x, xmm0` and a 16-byte store of `x` to `[b + d]`: the block there
is `x`. -/
theorem strev_ok (x : XReg) (b : Reg) (d : Nat) (s : State) (_hx : x ≠ .xmm0) (h0 : s.xmm .xmm0 = revMask)
    (hin : InRegions s.wr (s.gpr b + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.xop (.bin .pshufb x .xmm0), .movdquStore (Impl.Gcm.X86_64.Pclmul.at_ b d) x]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofInt 64 (d : Int)) (XBinOp.eval .pshufb (s.xmm x) revMask) ∧
      blockAt s'.mem (s.gpr b + BitVec.ofInt 64 (d : Int)) = s.xmm x ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ x → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, ↓reduceIte, Ne.symm _hx, h0, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl, fun r hr => by simp only [State.setMem, hr, ite_false]⟩
  simp only [State.setMem]
  rw [VG.Proof.Gcm.X86_64.blockAt_eq]
  erw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
  rw [VG.Proof.Gcm.X86_64.pshufb_rev_rev]

/-- `aadMul`: `T`, byte-reversed, times the 16 bytes at `ctx + 272`, into the
accumulator at `r14 + 16`. -/
theorem aadMul_ok {Ctx St W : Addr} (s : State) (h13 : s.gpr .r13 = Ctx) (h14 : s.gpr .r14 = St)
    (h15 : s.gpr .r15 = W) (inT : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 96) 16)
    (inH : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (outY : InRegions s.wr (St + BitVec.ofNat 64 16) 16) :
    WP isa (.block aadMul) s fun t =>
      blockAt t.mem (St + BitVec.ofNat 64 16) =
        VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc
          (blockAt s.mem (W + BitVec.ofNat 64 96)) (s.mem.readW (Ctx + BitVec.ofNat 64 272) 128)) ∧
      t.mem = s.mem.writeW (St + BitVec.ofNat 64 16) (XBinOp.eval .pshufb
        (VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc
          (blockAt s.mem (W + BitVec.ofNat 64 96)) (s.mem.readW (Ctx + BitVec.ofNat 64 272) 128))) revMask) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have e15 : s.gpr .r15 + BitVec.ofInt 64 ((96 : Nat) : Int) = W + BitVec.ofNat 64 96 := by
    rw [h15, BitVec.ofInt_natCast]
  have e13 : s.gpr .r13 + BitVec.ofInt 64 ((272 : Nat) : Int) = Ctx + BitVec.ofNat 64 272 := by
    rw [h13, BitVec.ofInt_natCast]
  simp only [aadMul, Impl.Gcm.X86_64.Pclmul.mul, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  rw [show ([.movdquLoad .xmm7 (at_ .r15 tO), .xop (.bin .pshufb .xmm7 .xmm0), .movdquLoad .xmm3 (at_ .r13 272)] ++
      _ : List Instr) = [.movdquLoad .xmm7 (at_ .r15 96), .xop (.bin .pshufb .xmm7 .xmm0)] ++
      ([.movdquLoad .xmm3 (at_ .r13 272)] ++ _) from rfl, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .r15 96 s₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), e15]; exact inT)) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [O₂.gpr _ (by decide), e15, O₂.mem] at l₃
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok .xmm3 .r13 272 s₃ (by
      rw [o₃.rd, o₃.wr, O₂.rd, O₂.wr, o₃.gpr _ (by decide), O₂.gpr _ (by decide), e13]; exact inH))
    fun s₄ ⟨l₄, o₄⟩ => ?_
  rw [o₃.gpr _ (by decide), O₂.gpr _ (by decide), e13, o₃.mem, O₂.mem] at l₄
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₄) fun s₅ ⟨p₅, o₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₅ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨p₆, o₆⟩ => ?_
  have O₆ := O₂.trans (o₃.trans (o₄.trans (o₅.trans o₆)))
  have P₆ := o₃.trans (o₄.trans (o₅.trans o₆))
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₆ (by decide) (by decide) (by decide) (by decide)
    (by rw [P₆.xmm _ (by decide), c₂])) fun s₇ ⟨r₇, o₇⟩ => ?_
  have O₇ := O₆.trans o₇
  have Q₇ := o₂.trans (P₆.trans o₇)
  refine WP.mono (strev_ok .xmm2 .r14 16 s₇ (by decide) (by rw [Q₇.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₇.wr, O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact outY)) fun t ⟨m₈, b₈, g₈, rd₈, wr₈, x₈⟩ => ?_
  rw [O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast] at m₈ b₈
  have v7 : s₅.xmm .xmm7 = blockAt s.mem (W + BitVec.ofNat 64 96) := by
    rw [(o₄.trans o₅).xmm _ (by decide), l₃]
  have v3 : s₅.xmm .xmm3 = s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 := by
    rw [o₅.xmm _ (by decide), l₄]
  refine ⟨by rw [b₈, r₇, p₆, p₅, v7, v3], by rw [m₈, O₇.mem, r₇, p₆, p₅, v7, v3], fun r hr => ?_,
    by rw [rd₈, O₇.rd], by rw [wr₈, O₇.wr]⟩
  rw [g₈, O₇.gpr r hr]

/-- `aadMul`, with the prepared power `H'` at `ctx + 272`: `GHASH` of the
block at `T` from zero. -/
theorem aadMul_ghash {H : Block} {T : Block} (h1 : IsH1 H T) (X : Block) :
    VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc X T) = ghashFrom H 0 [X] := by
  simpa using h1 0 X

/-- `aadReg`'s value: the five bytes at `A`, then zeros, byte-reversed by
`pshufb`, are their block. -/
theorem reg5_eq (m : Mem) (A : Addr) :
    XBinOp.eval .pshufb ((0 : BitVec 64) ++ ((m.readW A 32).setWidth 64 + (m (A + 4#64)).setWidth 64 <<< 32))
      revMask = Spec.Gcm.ofBytes (bytesAt m A 5 ++ zeros 11) := by
  have hx : (0 : BitVec 64) ++ ((m.readW A 32).setWidth 64 + (m (A + 4#64)).setWidth 64 <<< 32) =
      X86_64.ofBytes fun i => if i < 4 then (m.readW A 32).extractLsb' (8 * i) 8 else if i = 4 then m (A + 4#64) else 0 := by
    simp only [X86_64.ofBytes, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.lt_irrefl]
    generalize m.readW A 32 = r
    generalize m (A + 4#64) = b
    apply BitVec.eq_of_toNat_eq
    simp only [VG.Proof.Gcm.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceMul,
      Nat.reducePow, BitVec.ofNat_eq_ofNat, BitVec.toNat_zero, Nat.zero_mod, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    have := r.isLt
    have := b.isLt
    omega
  rw [hx, VG.Proof.Gcm.X86_64.pshufb_rev, show bytesAt m A 5 ++ zeros 11 = (List.range 16).map fun i =>
      if i < 5 then m (A + BitVec.ofNat 64 i) else 0 from rfl, VG.Proof.Gcm.X86_64.gcmOfBytes_eq]
  refine congrArg X86_64.ofBytes (funext fun i => ?_)
  rw [VG.Proof.Gcm.X86_64.byte_ofBytes _ (by omega)]
  generalize 15 - i = k
  by_cases h4 : k < 4
  · rw [ite_eq_left h4, ite_eq_left (by omega)]; exact (Mem.readW_byte m A h4).symm
  · rw [ite_eq_right h4]
    by_cases h5 : k = 4
    · subst h5; rfl
    · rw [ite_eq_right h5, ite_eq_right (by omega)]

/-- `aadReg`: the five bytes at `rsi` in `xmm7`, whose `pshufb` by the
reversal mask is the block of the bytes padded with zeros. -/
theorem aadReg_ok {A : Addr} (s : State) (hsi : s.gpr .rsi = A) (q₁ : InRegions (s.rd ++ s.wr) A 4)
    (q₂ : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 4) 1) :
    WP isa (.block aadReg) s fun t =>
      XBinOp.eval .pshufb (t.xmm .xmm7) revMask = Spec.Gcm.ofBytes (bytesAt s.mem A 5 ++ zeros 11) ∧
      t.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨t, run, v, m, g, rd, wr⟩ : ∃ t, runBlock isa aadReg s = some t ∧
      t.xmm .xmm7 = (0 : BitVec 64) ++ ((s.mem.readW A 32).setWidth 64 + (s.mem (A + 4#64)).setWidth 64 <<< 32) ∧
      t.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    refine ⟨_, by xrun [aadReg, BitVec.add_zero, hsi, q₁, q₂, XOp.exec], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [xmm_setXmm_self, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · rfl
    · intro r a b; simp [gpr_setXmm, gpr_setReg, gpr_setFlags, a, b]
    all_goals rfl
  exact WP.of_runBlock ⟨t, run, by rw [v, reg5_eq], m, g, rd, wr⟩

/-- `aadFull`: the sixteen bytes at `rsi` in `xmm7`, whose `pshufb` by the
reversal mask is their block. -/
theorem aadFull_ok {A : Addr} (s : State) (hsi : s.gpr .rsi = A) (q : InRegions (s.rd ++ s.wr) A 16) :
    WP isa (.block aadFull) s fun t =>
      XBinOp.eval .pshufb (t.xmm .xmm7) revMask = Spec.Gcm.ofBytes (bytesAt s.mem A 16 ++ zeros (16 - 16)) ∧
      t.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have e : s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int) = A := by
    rw [hsi, BitVec.ofInt_natCast]; exact BitVec.add_zero A
  refine WP.mono (ld_ok .xmm7 .rsi 0 s (by rw [e]; exact q)) fun t ⟨v, o⟩ => ?_
  refine ⟨?_, o.mem, fun r hr _ => o.gpr r hr, o.rd, o.wr⟩
  rw [v, e, ← VG.Proof.Gcm.X86_64.blockAt_eq, Spec.Gcm.zeros, Nat.sub_self, List.replicate_zero,
    List.append_nil]
  rfl

/-- `pshufb xmm7, xmm0`. -/
theorem pshufb7_ok (s : State) :
    WP isa (.block [.xop (.bin .pshufb .xmm7 .xmm0)]) s fun s' =>
      s'.xmm .xmm7 = XBinOp.eval .pshufb (s.xmm .xmm7) (s.xmm .xmm0) ∧ Only [.xmm7] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- `aadMulR`: `aadMul` with the block `X` in `xmm7`, byte-reversed. -/
theorem aadMulR_ok {Ctx St : Addr} {X : Block} (s : State) (h13 : s.gpr .r13 = Ctx) (h14 : s.gpr .r14 = St)
    (hv : XBinOp.eval .pshufb (s.xmm .xmm7) revMask = X)
    (inH : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (outY : InRegions s.wr (St + BitVec.ofNat 64 16) 16) :
    WP isa (.block aadMulR) s fun t =>
      blockAt t.mem (St + BitVec.ofNat 64 16) =
        VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc
          X (s.mem.readW (Ctx + BitVec.ofNat 64 272) 128)) ∧
      t.mem = s.mem.writeW (St + BitVec.ofNat 64 16) (XBinOp.eval .pshufb
        (VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc
          X (s.mem.readW (Ctx + BitVec.ofNat 64 272) 128))) revMask) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have e13 : s.gpr .r13 + BitVec.ofInt 64 ((272 : Nat) : Int) = Ctx + BitVec.ofNat 64 272 := by
    rw [h13, BitVec.ofInt_natCast]
  simp only [aadMulR, Impl.Gcm.X86_64.Pclmul.mul, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  rw [show ([.xop (.bin .pshufb .xmm7 .xmm0), .movdquLoad .xmm3 (at_ .r13 272)] ++ _ : List Instr) =
      [.xop (.bin .pshufb .xmm7 .xmm0)] ++ ([.movdquLoad .xmm3 (at_ .r13 272)] ++ _) from rfl,
    WP.block_append_iff]
  refine WP.mono (pshufb7_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [o₂.xmm .xmm0 (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq, O₂.xmm .xmm7 (by decide), hv] at l₃
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok .xmm3 .r13 272 s₃ (by
      rw [o₃.rd, o₃.wr, O₂.rd, O₂.wr, o₃.gpr _ (by decide), O₂.gpr _ (by decide), e13]; exact inH))
    fun s₄ ⟨l₄, o₄⟩ => ?_
  rw [o₃.gpr _ (by decide), O₂.gpr _ (by decide), e13, o₃.mem, O₂.mem] at l₄
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₄) fun s₅ ⟨p₅, o₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₅ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨p₆, o₆⟩ => ?_
  have O₆ := O₂.trans (o₃.trans (o₄.trans (o₅.trans o₆)))
  have P₆ := o₃.trans (o₄.trans (o₅.trans o₆))
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₆ (by decide) (by decide) (by decide) (by decide)
    (by rw [P₆.xmm _ (by decide), c₂])) fun s₇ ⟨r₇, o₇⟩ => ?_
  have O₇ := O₆.trans o₇
  have Q₇ := o₂.trans (P₆.trans o₇)
  refine WP.mono (strev_ok .xmm2 .r14 16 s₇ (by decide) (by rw [Q₇.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₇.wr, O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact outY)) fun t ⟨m₈, b₈, g₈, rd₈, wr₈, x₈⟩ => ?_
  rw [O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast] at m₈ b₈
  have v7 : s₅.xmm .xmm7 = X := by rw [(o₄.trans o₅).xmm _ (by decide), l₃]
  have v3 : s₅.xmm .xmm3 = s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 := by
    rw [o₅.xmm _ (by decide), l₄]
  refine ⟨by rw [b₈, r₇, p₆, p₅, v7, v3], by rw [m₈, O₇.mem, r₇, p₆, p₅, v7, v3], fun r hr => ?_,
    by rw [rd₈, O₇.rd], by rw [wr₈, O₇.wr]⟩
  rw [g₈, O₇.gpr r hr]

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `aadPad`'s first block: `T` zeroed, and the arguments of `copyLoop`. -/
theorem aadPadHead_ok {A : Addr} {al : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hAd : DataOk (W + BitVec.ofNat 64 16) W SP s A al) (h1 : 1 ≤ al) (h16 : al ≤ 16)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A) (hcx : s.gpr .rcx = BitVec.ofNat 64 al) :
    WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] : List Instr) ++
        ptr .rdi .r15 tO ++ ([.mov .rsi (.mem (at_ .r15 aadO))] : List Instr))) s fun s₂ =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧ LoopPre s₂ A (W + BitVec.ofNat 64 96) al := by
  have h15 := he.r15
  obtain ⟨s₂, run₂, hm₂, hdi, hsi, hcx₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] : List Instr) ++
        ptr .rdi .r15 tO ++ ([.mov .rsi (.mem (at_ .r15 aadO))] : List Instr)) s = some s₂ ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₂.gpr .rdi = W + BitVec.ofNat 64 96 ∧ s₂.gpr .rsi = A ∧ s₂.gpr .rcx = BitVec.ofNat 64 al ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have w₁ := in_off he.perm.w (show 96 + 8 ≤ 2560 by decide) (by decide)
    have w₂ := in_off he.perm.w (show 104 + 8 ≤ 2560 by decide) (by decide)
    have q₁ := he.perm.wR (show 232 + 8 ≤ 2560 by decide)
    have ka : ((s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 104) (0 : BitVec 64)).readW (W + BitVec.ofNat 64 232) 64 = A := by
      rw [← haad]
      have : ((s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
          (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64)).readW (W + BitVec.ofNat 64 232) 64 =
          s.mem.readW (W + BitVec.ofNat 64 232) 64 :=
        (zeroT_frame s.mem (W + BitVec.ofNat 64 96)).readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
      rwa [add_ofNat_assoc] at this
    refine ⟨_, by xrun [h15, w₁, w₂, q₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h15]
    · simp only [gpr_setReg, mem_setReg, mem_arithFlags, ite_true, ite_false, reduceCtorEq]
      exact ka
    · simp [gpr_setReg, hcx]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    · simp [rd_setReg, rd_arithFlags]
    · simp [wr_setReg, wr_arithFlags]
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hlt := hAd.lt
  have lp : LoopPre s₂ A (W + BitVec.ofNat 64 96) al := by
    refine ⟨hsi, hdi, hcx₂, h1, by omega, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂]; exact hAd.rd
    · exact he₂.perm.wC (by omega)
    · exact hAd.w.sub_right (Lay.wSub (by omega))
  exact WP.of_runBlock ⟨s₂, run₂, he₂, hrd₂, hwr₂, hm₂, lp⟩

/-- `aadPad`: the `al` (1 to 16) bytes at `A` padded with zeros in `T`. -/
theorem aadPad_ok {A : Addr} {al : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hAd : DataOk (W + BitVec.ofNat 64 16) W SP s A al) (h1 : 1 ≤ al) (h16 : al ≤ 16)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A) (hcx : s.gpr .rcx = BitVec.ofNat 64 al) :
    WP isa aadPad s fun t => Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      bytesAt t.mem (W + BitVec.ofNat 64 96) 16 = bytesAt s.mem A al ++ zeros (16 - al) ∧
      Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem t.mem := by
  refine WP.seq (WP.mono (aadPadHead_ok L he hAd h1 h16 haad hcx) fun s₂ ⟨he₂, hrd₂, hwr₂, hm₂, lp⟩ => ?_)
  have hlt := hAd.lt
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact zeroT_frame _ _
  have hA₂ : bytesAt s₂.mem A al = bytesAt s.mem A al :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hAd.w.sub_right (Lay.wSub (by decide))) (by omega)
  have hlen := length_bytesAt s₂.mem A al
  have fc : Frame [⟨W + BitVec.ofNat 64 96, al⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  have f₃ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  have hT : bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16 = bytesAt s.mem A al ++ zeros (16 - al) := by
    rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hA₂]
    refine congrArg (_ ++ ·) ?_
    have := zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
    rw [← hm₂, show (16 : Nat) = al + (16 - al) by omega, bytesAt_add] at this
    have e := congrArg (List.drop al) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show al + (16 - al) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  exact ⟨he₃, by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂], hT, f₃⟩

/-- `aadSome`: the `al` (1 to 16) bytes at `A`, padded with zeros, times the
16 bytes at `ctx + 272`, into the accumulator; the rest of the state's
blocks kept. -/
theorem aadSome_ok {A : Addr} {al : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hAd : DataOk (W + BitVec.ofNat 64 16) W SP s A al) (h1 : 1 ≤ al) (h16 : al ≤ 16)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A) (hcx : s.gpr .rcx = BitVec.ofNat 64 al)
    (inH : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (cw : (⟨Ctx + BitVec.ofNat 64 272, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa aadSome s fun t => Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
        VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc
          (Spec.Gcm.ofBytes (bytesAt s.mem A al ++ zeros (16 - al))) (s.mem.readW (Ctx + BitVec.ofNat 64 272) 128)) ∧
      Frame (wFrame W SP) s.mem t.mem ∧
      ∀ {a : Nat}, a + 16 ≤ 80 → (a + 16 ≤ 16 ∨ 32 ≤ a) →
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) := by
  -- After the multiplication, from a state `s'` that changed at most `T`.
  have fin : ∀ (s' t : State) (Y : BitVec 128), Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem →
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' → s'.rd = s.rd → s'.wr = s.wr →
      t.mem = s'.mem.writeW (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) Y →
      (∀ r, r ≠ .rax → t.gpr r = s'.gpr r) → t.rd = s'.rd → t.wr = s'.wr →
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame (wFrame W SP) s.mem t.mem ∧
      ∀ {a : Nat}, a + 16 ≤ 80 → (a + 16 ≤ 16 ∨ 32 ≤ a) →
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) := by
    intro s' t Y fT he' rd' wr' m g rd wr
    have fy : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] s'.mem t.mem := by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨he'.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd wr,
      rd.trans rd', wr.trans wr', ?_, fun {a} ha ho => ?_⟩
    · refine (fT.sub fun r hr => ?_).trans (fy.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact w_wFrame (.inl ⟨by decide, by decide⟩)
      · simp only [List.mem_singleton] at hr; subst hr; exact st_wFrame (d := 16) (k := 16) (by decide)
    · rw [blockAt_frame fy fun r hr => ?_, blockAt_frame fT fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr; exact L.st_w ha (.inr ⟨by decide, by decide⟩)
      · simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (by omega) ha (by decide)
  have hlt := hAd.lt
  have outY : ∀ {s' : State}, Env Ctx (W + BitVec.ofNat 64 16) W SP s' →
      InRegions s'.wr (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) 16 := fun h =>
    h.perm.stW (show 16 + 16 ≤ 80 by decide)
  unfold aadSome
  obtain ⟨s₁, run₁, zf₁, -, g₁, m₁, rd₁, wr₁⟩ := cmpImm_ok s .rcx hcx hlt (show 5 < 2 ^ 31 by decide)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.ite (decide (al = 5)) (eval_e zf₁) (fun ht => ?_) (fun _ => ?_)
  · -- Five bytes, put together in a register.
    have h5 : al = 5 := by simpa using ht
    subst h5
    have q := he₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
    obtain ⟨s₂, run₂, hsi₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s₁ = some s₂ ∧
        s₂.gpr .rsi = A ∧ (∀ r, r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [he₁.r15, q], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, m₁, haad]
      · intro r h; simp [gpr_setReg, h]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) rd₂ wr₂
    have q₁ : InRegions (s₂.rd ++ s₂.wr) A 4 := by
      have := in_off hAd.rd (d := 0) (n := 4) (by decide) (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      rwa [rd₂, wr₂, rd₁, wr₁]
    have q₂ : InRegions (s₂.rd ++ s₂.wr) (A + BitVec.ofNat 64 4) 1 := by
      rw [rd₂, wr₂, rd₁, wr₁]; exact in_off hAd.rd (by decide) (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (aadReg_ok s₂ hsi₂ q₁ q₂) fun s₃ ⟨v₃, m₃, g₃, rd₃, wr₃⟩ => ?_
    have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
    have M₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
    have inH₃ : InRegions (s₃.rd ++ s₃.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
      rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact inH
    refine WP.mono (aadMulR_ok s₃ he₃.r13 he₃.r14 v₃ inH₃ (outY he₃)) fun t ⟨b, m, g, rd, wr⟩ => ?_
    obtain ⟨E, R, Wr, F, K⟩ := fin s₃ t _ (by rw [M₃]; exact Frame.refl _ _) he₃
      (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) m g rd wr
    refine ⟨E, R, Wr, ?_, F, K⟩
    rw [b, M₃, m₂, m₁]
  · -- The length compared with 16.
    obtain ⟨s₁', run₁', zf₁', -, g₁', m₁', rd₁', wr₁'⟩ := cmpImm_ok s₁ .rcx (by rw [g₁]; exact hcx) hlt
      (show 16 < 2 ^ 31 by decide)
    refine WP.seq (WP.of_runBlock ⟨s₁', run₁', ?_⟩)
    have he₁' : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁' := he₁.keep (fun r _ => by rw [g₁']) rd₁' wr₁'
    refine WP.ite (decide (al = 16)) (eval_e zf₁') (fun ht => ?_) (fun _ => ?_)
    · -- Sixteen bytes, loaded whole.
      have hx : al = 16 := by simpa using ht
      subst hx
      have q := he₁'.perm.wR (show 232 + 8 ≤ 2560 by decide)
      obtain ⟨s₂, run₂, hsi₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s₁' = some s₂ ∧
          s₂.gpr .rsi = A ∧ (∀ r, r ≠ .rsi → s₂.gpr r = s₁'.gpr r) ∧ s₂.mem = s₁'.mem ∧ s₂.rd = s₁'.rd ∧
          s₂.wr = s₁'.wr := by
        refine ⟨_, by xrun [he₁'.r15, q], ?_, ?_, ?_, ?_, ?_⟩
        · simp [gpr_setReg, m₁', m₁, haad]
        · intro r h; simp [gpr_setReg, h]
        all_goals rfl
      refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
      have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁'.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) rd₂ wr₂
      have q₁ : InRegions (s₂.rd ++ s₂.wr) A 16 := by
        have := in_off hAd.rd (d := 0) (n := 16) (by decide) (by decide)
        simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
        rwa [rd₂, wr₂, rd₁', wr₁', rd₁, wr₁]
      rw [WP.block_append_iff]
      refine WP.mono (aadFull_ok s₂ hsi₂ q₁) fun s₃ ⟨v₃, m₃, g₃, rd₃, wr₃⟩ => ?_
      have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
      have M₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁', m₁]
      have inH₃ : InRegions (s₃.rd ++ s₃.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
        rw [rd₃, wr₃, rd₂, wr₂, rd₁', wr₁', rd₁, wr₁]; exact inH
      refine WP.mono (aadMulR_ok s₃ he₃.r13 he₃.r14 v₃ inH₃ (outY he₃)) fun t ⟨b, m, g, rd, wr⟩ => ?_
      obtain ⟨E, R, Wr, F, K⟩ := fin s₃ t _ (by rw [M₃]; exact Frame.refl _ _) he₃
        (by rw [rd₃, rd₂, rd₁', rd₁]) (by rw [wr₃, wr₂, wr₁', wr₁]) m g rd wr
      refine ⟨E, R, Wr, ?_, F, K⟩
      rw [b, M₃, m₂, m₁', m₁]
    · -- Any other length, padded in `T`.
      refine WP.seq (WP.mono (aadPad_ok L he₁' (hAd.of_eq (rd₁'.trans rd₁) (wr₁'.trans wr₁)) h1 h16
        (by rw [m₁', m₁]; exact haad) (by rw [g₁', g₁]; exact hcx)) fun s₄ ⟨he₄, rd₄, wr₄, hT₄, f₄⟩ => ?_)
      have inT : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 96) 16 :=
        in_left (in_off he₄.perm.w (show 96 + 16 ≤ 2560 by decide) (by decide))
      have inH₄ : InRegions (s₄.rd ++ s₄.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
        rw [rd₄, wr₄, rd₁', wr₁', rd₁, wr₁]; exact inH
      refine WP.mono (aadMul_ok s₄ he₄.r13 he₄.r14 he₄.r15 inT inH₄ (outY he₄)) fun t ⟨b, m, g, rd, wr⟩ => ?_
      have fT : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₄.mem := by rw [← m₁, ← m₁']; exact f₄
      obtain ⟨E, R, Wr, F, K⟩ := fin s₄ t _ fT he₄ (by rw [rd₄, rd₁', rd₁]) (by rw [wr₄, wr₁', wr₁]) m g rd wr
      refine ⟨E, R, Wr, ?_, F, K⟩
      rw [b, fT.readW (r := ⟨Ctx + BitVec.ofNat 64 272, 16⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cw.sub_right (Lay.wSub (by decide))) (by decide),
        blockAt, hT₄, m₁', m₁]

/-- `aad`: `J₀` of the 12-byte nonce at `Np`, the first counter block, and the
`al` (at most 16) bytes of additional data at `A` absorbed and padded, for
an `H'` at `ctx + 272` that multiplies as `H` (`IsH1`): what `oneAad`
leaves (`OneAad`). -/
theorem fastAad_ok {Np A : Addr} {al : Nat} {H : Block} {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H)
    (h12 : s.gpr .r12 = Np) (hbp : s.gpr .rbp = BitVec.ofNat 64 12)
    (hN : DataOk (W + BitVec.ofNat 64 16) W SP s Np 12) (hAd : DataOk (W + BitVec.ofNat 64 16) W SP s A al)
    (haad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) (h16 : al ≤ 16)
    (hP : IsH1 H (s.mem.readW (Ctx + BitVec.ofNat 64 272) 128))
    (inH : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (cw : (⟨Ctx + BitVec.ofNat 64 272, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (ct : (below SP 8).Disjoint ⟨Ctx + BitVec.ofNat 64 272, 16⟩) :
    WP isa aad s (OneAad Ctx W SP H (bytesAt s.mem Np 12) (bytesAt s.mem A al) s.mem) := by
  unfold aad
  refine WP.seq (WP.mono (WP.with_rdwr (j012_ok L ⟨he, hH, h12, hbp, hN⟩)) fun s₁ ⟨j₁, hrd₁, hwr₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.with_rdwr (initState_ok L j₁)) fun s₂ ⟨j₂, hrd₂, hwr₂⟩ => ?_)
  have f₂ := j₂.frame
  have he₂ := j₂.env
  -- What `j0` keeps.
  have kW : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 512) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (d := 16) (k := 80) (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact L.w_w (by omega) (by omega) (by decide)
      · exact (L.stk_w (by omega)).symm) (by decide)
  have dCj : ∀ {a k : Nat}, a + k ≤ 256 → ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP,
      (⟨Ctx + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_left (Lay.ctxSub hk)
    · exact L.ctx_w hk (by decide)
    · exact L.ctx_w hk (by decide)
    · exact L.ctx_w hk (by decide)
    · exact (L.stk_ctx hk).symm
  have dAj : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP, (⟨A, al⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hAd.st
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.stk.symm
  have h15₂ := he₂.r15
  have q₂ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hal₂ := kW 184 (.inl ⟨by decide, by decide⟩)
  rw [hal] at hal₂
  have hlt := hAd.lt
  obtain ⟨s₃, run₃, hcx₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)] s₂ = some s₃ ∧
      s₃.gpr .rcx = BitVec.ofNat 64 al ∧ s₃.zf = some (decide (al = 0)) ∧
      (∀ r, r ≠ .rcx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [h15₂, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hal₂]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hal₂]; rw [and_self_beq (by omega)]
    · intro r h; simp [gpr_setReg, h]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  refine WP.ite (decide (al = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · -- No additional data: the accumulator stays zero.
    have h0 : al = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₃, by rw [hm₃]; exact j₂.hH, by rw [hm₃]; exact j₂.j0, ?_, by rw [hm₃]; exact j₂.cb,
      by rw [hm₃]; exact j0Frame_one f₂⟩
    rw [hm₃]
    simpa [bytesAt, padLen, zeros] using Proof.Gcm.absorbed_nil (b := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H j₂.y
  · have h0 : al ≠ 0 := by simpa using hf
    have hA₃ : bytesAt s₃.mem A al = bytesAt s.mem A al := by rw [hm₃]; exact bytesAt_frame f₂ dAj (by omega)
    have haad₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
      rw [hm₃, kW 232 (.inr ⟨by decide, by decide⟩), haad]
    have fs₃ : Frame (wFrame W SP) s.mem s₃.mem := by rw [hm₃]; exact j0Frame_one f₂
    have dH : ∀ r ∈ wFrame W SP, (⟨Ctx + BitVec.ofNat 64 272, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact cw.sub_right (Lay.wSub (by decide))
      · exact cw.sub_right (Lay.wSub (by decide))
      · exact cw.sub_right (Lay.wSub (by decide))
      · exact ct.symm
    have hP₃ : IsH1 H (s₃.mem.readW (Ctx + BitVec.ofNat 64 272) 128) := by
      rwa [fs₃.readW (r := ⟨Ctx + BitVec.ofNat 64 272, 16⟩) (Region.contains_self _ _) dH (by decide)]
    have inH₃ : InRegions (s₃.rd ++ s₃.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
      rw [hrd₃, hwr₃, hrd₂, hwr₂, hrd₁, hwr₁]; exact inH
    refine WP.mono (aadSome_ok L he₃ (hAd.of_eq (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁]))
      (by omega) h16 haad₃ hcx₃ inH₃ cw) fun t ⟨he₅, rd₅, wr₅, b₅, f₅, keep'⟩ => ?_
    have keep : ∀ {a : Nat}, a + 16 ≤ 80 → (a + 16 ≤ 16 ∨ 32 ≤ a) →
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) =
          blockAt s₂.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) := fun ha ho => by
      rw [keep' ha ho, hm₃]
    have hH₂ : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame (fs₃.trans f₅) fun r hr => ?_]
      · exact hH
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.ctx_w (by decide) (by decide)
      · exact L.ctx_w (by decide) (by decide)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm
    have hA₄ := length_bytesAt s.mem A al
    refine ⟨he₅, hH₂, ?_, ?_, ?_, fs₃.trans f₅⟩
    · have := keep (a := 0) (by decide) (.inl (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      rw [this]; exact j₂.j0
    · rw [hA₄]
      refine Proof.Gcm.absorb_complete (x := []) (Proof.Gcm.absorbed_nil (m := s₂.mem)
        (b := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H j₂.y) ?_ rfl ?_
      · simp only [List.length_nil, Nat.zero_mod, List.append_eq, List.length_append, hA₄, Proof.Gcm.length_zeros, padLen]
        omega
      · rw [j₂.y, b₅, aadMul_ghash hP₃, hA₃, List.drop_nil, List.nil_append,
          show padLen al = 16 - al by simp only [padLen]; omega, List.append_eq]
    · rw [keep (by decide) (.inr (by decide))]; exact j₂.cb
end

end VG.Proof.AesGcm.X86_64.Fast
