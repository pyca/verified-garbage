module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesGcm.X86_64.Fast.Tail`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Fast.Aad`, which this module and modules that import it used -/

section

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
  obtain e15 : s.gpr .r15 + BitVec.ofInt 64 ((96 : Nat) : Int) = W + BitVec.ofNat 64 96 := by
    rw [h15, BitVec.ofInt_natCast]
  obtain e13 : s.gpr .r13 + BitVec.ofInt 64 ((272 : Nat) : Int) = Ctx + BitVec.ofNat 64 272 := by
    rw [h13, BitVec.ofInt_natCast]
  simp only [aadMul, Impl.Gcm.X86_64.Pclmul.mul, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  obtain O₂ := o₁.trans o₂
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
  obtain O₆ := O₂.trans (o₃.trans (o₄.trans (o₅.trans o₆)))
  obtain P₆ := o₃.trans (o₄.trans (o₅.trans o₆))
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₆ (by decide) (by decide) (by decide) (by decide)
    (by rw [P₆.xmm _ (by decide), c₂])) fun s₇ ⟨r₇, o₇⟩ => ?_
  obtain O₇ := O₆.trans o₇
  obtain Q₇ := o₂.trans (P₆.trans o₇)
  refine WP.mono (strev_ok .xmm2 .r14 16 s₇ (by decide) (by rw [Q₇.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₇.wr, O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact outY)) fun t ⟨m₈, b₈, g₈, rd₈, wr₈, x₈⟩ => ?_
  rw [O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast] at m₈ b₈
  obtain v7 : s₅.xmm .xmm7 = blockAt s.mem (W + BitVec.ofNat 64 96) := by
    rw [(o₄.trans o₅).xmm _ (by decide), l₃]
  obtain v3 : s₅.xmm .xmm3 = s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 := by
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
  obtain hx : (0 : BitVec 64) ++ ((m.readW A 32).setWidth 64 + (m (A + 4#64)).setWidth 64 <<< 32) =
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
    omega_arith
  rw [hx, VG.Proof.Gcm.X86_64.pshufb_rev, show bytesAt m A 5 ++ zeros 11 = (List.range 16).map fun i =>
      if i < 5 then m (A + BitVec.ofNat 64 i) else 0 from rfl, VG.Proof.Gcm.X86_64.gcmOfBytes_eq]
  refine congrArg X86_64.ofBytes (funext fun i => ?_)
  rw [VG.Proof.Gcm.X86_64.byte_ofBytes _ (by omega_arith)]
  generalize 15 - i = k
  by_cases h4 : k < 4
  · rw [ite_eq_left h4, ite_eq_left (by omega_arith)]; exact (Mem.readW_byte m A h4).symm
  · rw [ite_eq_right h4]
    by_cases h5 : k = 4
    · subst h5; rfl
    · rw [ite_eq_right h5, ite_eq_right (by omega_arith)]

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
  obtain e : s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int) = A := by
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
  obtain e13 : s.gpr .r13 + BitVec.ofInt 64 ((272 : Nat) : Int) = Ctx + BitVec.ofNat 64 272 := by
    rw [h13, BitVec.ofInt_natCast]
  simp only [aadMulR, Impl.Gcm.X86_64.Pclmul.mul, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  obtain O₂ := o₁.trans o₂
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
  obtain O₆ := O₂.trans (o₃.trans (o₄.trans (o₅.trans o₆)))
  obtain P₆ := o₃.trans (o₄.trans (o₅.trans o₆))
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₆ (by decide) (by decide) (by decide) (by decide)
    (by rw [P₆.xmm _ (by decide), c₂])) fun s₇ ⟨r₇, o₇⟩ => ?_
  obtain O₇ := O₆.trans o₇
  obtain Q₇ := o₂.trans (P₆.trans o₇)
  refine WP.mono (strev_ok .xmm2 .r14 16 s₇ (by decide) (by rw [Q₇.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₇.wr, O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact outY)) fun t ⟨m₈, b₈, g₈, rd₈, wr₈, x₈⟩ => ?_
  rw [O₇.gpr _ (by decide), h14, BitVec.ofInt_natCast] at m₈ b₈
  obtain v7 : s₅.xmm .xmm7 = X := by rw [(o₄.trans o₅).xmm _ (by decide), l₃]
  obtain v3 : s₅.xmm .xmm3 = s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 := by
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
    obtain w₁ := in_off he.perm.w (show 96 + 8 ≤ 2560 by decide) (by decide)
    obtain w₂ := in_off he.perm.w (show 104 + 8 ≤ 2560 by decide) (by decide)
    obtain q₁ := he.perm.wR (show 232 + 8 ≤ 2560 by decide)
    obtain ka : ((s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
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
  obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hlt := hAd.lt
  obtain lp : LoopPre s₂ A (W + BitVec.ofNat 64 96) al := by
    refine ⟨hsi, hdi, hcx₂, h1, by omega_arith, ?_, ?_, ?_⟩
    · rw [hrd₂, hwr₂]; exact hAd.rd
    · exact he₂.perm.wC (by omega_arith)
    · exact hAd.w.sub_right (Lay.wSub (by omega_arith))
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
  obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  obtain fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact zeroT_frame _ _
  obtain hA₂ : bytesAt s₂.mem A al = bytesAt s.mem A al :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hAd.w.sub_right (Lay.wSub (by decide))) (by omega_arith)
  obtain hlen := length_bytesAt s₂.mem A al
  obtain fc : Frame [⟨W + BitVec.ofNat 64 96, al⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame' _ hlen
  obtain f₃ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  obtain hT : bytesAt s₃.mem (W + BitVec.ofNat 64 96) 16 = bytesAt s.mem A al ++ zeros (16 - al) := by
    rw [hm₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by decide), hlen, hA₂]
    refine congrArg (_ ++ ·) ?_
    have := zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
    rw [← hm₂, show (16 : Nat) = al + (16 - al) by omega_arith, bytesAt_add] at this
    obtain e := congrArg (List.drop al) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show al + (16 - al) = 16 by omega_arith, Spec.Gcm.zeros, List.drop_replicate]
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
  obtain fin : ∀ (s' t : State) (Y : BitVec 128), Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem →
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' → s'.rd = s.rd → s'.wr = s.wr →
      t.mem = s'.mem.writeW (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) Y →
      (∀ r, r ≠ .rax → t.gpr r = s'.gpr r) → t.rd = s'.rd → t.wr = s'.wr →
      Env Ctx (W + BitVec.ofNat 64 16) W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame (wFrame W SP) s.mem t.mem ∧
      ∀ {a : Nat}, a + 16 ≤ 80 → (a + 16 ≤ 16 ∨ 32 ≤ a) →
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) =
          blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) := by
    intro s' t Y fT he' rd' wr' m g rd wr
    obtain fy : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] s'.mem t.mem := by
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
      · simp only [List.mem_singleton] at hr; subst hr; exact L.st_st (by omega_arith) ha (by decide)
  have hlt := hAd.lt
  obtain outY : ∀ {s' : State}, Env Ctx (W + BitVec.ofNat 64 16) W SP s' →
      InRegions s'.wr (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) 16 := fun h =>
    h.perm.stW (show 16 + 16 ≤ 80 by decide)
  unfold aadSome
  obtain ⟨s₁, run₁, zf₁, -, g₁, m₁, rd₁, wr₁⟩ := cmpImm_ok s .rcx hcx hlt (show 5 < 2 ^ 31 by decide)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.ite (decide (al = 5)) (eval_e zf₁) (fun ht => ?_) (fun _ => ?_)
  · -- Five bytes, put together in a register.
    obtain h5 : al = 5 := by simpa using ht
    subst h5
    obtain q := he₁.perm.wR (show 232 + 8 ≤ 2560 by decide)
    obtain ⟨s₂, run₂, hsi₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s₁ = some s₂ ∧
        s₂.gpr .rsi = A ∧ (∀ r, r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [he₁.r15, q], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, m₁, haad]
      · intro r h; simp [gpr_setReg, h]
      all_goals rfl
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) rd₂ wr₂
    obtain q₁ : InRegions (s₂.rd ++ s₂.wr) A 4 := by
      have := in_off hAd.rd (d := 0) (n := 4) (by decide) (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      rwa [rd₂, wr₂, rd₁, wr₁]
    obtain q₂ : InRegions (s₂.rd ++ s₂.wr) (A + BitVec.ofNat 64 4) 1 := by
      rw [rd₂, wr₂, rd₁, wr₁]; exact in_off hAd.rd (by decide) (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (aadReg_ok s₂ hsi₂ q₁ q₂) fun s₃ ⟨v₃, m₃, g₃, rd₃, wr₃⟩ => ?_
    obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
    obtain M₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
    obtain inH₃ : InRegions (s₃.rd ++ s₃.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
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
    obtain he₁' : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁' := he₁.keep (fun r _ => by rw [g₁']) rd₁' wr₁'
    refine WP.ite (decide (al = 16)) (eval_e zf₁') (fun ht => ?_) (fun _ => ?_)
    · -- Sixteen bytes, loaded whole.
      obtain hx : al = 16 := by simpa using ht
      subst hx
      obtain q := he₁'.perm.wR (show 232 + 8 ≤ 2560 by decide)
      obtain ⟨s₂, run₂, hsi₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s₁' = some s₂ ∧
          s₂.gpr .rsi = A ∧ (∀ r, r ≠ .rsi → s₂.gpr r = s₁'.gpr r) ∧ s₂.mem = s₁'.mem ∧ s₂.rd = s₁'.rd ∧
          s₂.wr = s₁'.wr := by
        refine ⟨_, by xrun [he₁'.r15, q], ?_, ?_, ?_, ?_, ?_⟩
        · simp [gpr_setReg, m₁', m₁, haad]
        · intro r h; simp [gpr_setReg, h]
        all_goals rfl
      refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
      obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁'.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) rd₂ wr₂
      obtain q₁ : InRegions (s₂.rd ++ s₂.wr) A 16 := by
        have := in_off hAd.rd (d := 0) (n := 16) (by decide) (by decide)
        simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
        rwa [rd₂, wr₂, rd₁', wr₁', rd₁, wr₁]
      rw [WP.block_append_iff]
      refine WP.mono (aadFull_ok s₂ hsi₂ q₁) fun s₃ ⟨v₃, m₃, g₃, rd₃, wr₃⟩ => ?_
      obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
      obtain M₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁', m₁]
      obtain inH₃ : InRegions (s₃.rd ++ s₃.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
        rw [rd₃, wr₃, rd₂, wr₂, rd₁', wr₁', rd₁, wr₁]; exact inH
      refine WP.mono (aadMulR_ok s₃ he₃.r13 he₃.r14 v₃ inH₃ (outY he₃)) fun t ⟨b, m, g, rd, wr⟩ => ?_
      obtain ⟨E, R, Wr, F, K⟩ := fin s₃ t _ (by rw [M₃]; exact Frame.refl _ _) he₃
        (by rw [rd₃, rd₂, rd₁', rd₁]) (by rw [wr₃, wr₂, wr₁', wr₁]) m g rd wr
      refine ⟨E, R, Wr, ?_, F, K⟩
      rw [b, M₃, m₂, m₁', m₁]
    · -- Any other length, padded in `T`.
      refine WP.seq (WP.mono (aadPad_ok L he₁' (hAd.of_eq (rd₁'.trans rd₁) (wr₁'.trans wr₁)) h1 h16
        (by rw [m₁', m₁]; exact haad) (by rw [g₁', g₁]; exact hcx)) fun s₄ ⟨he₄, rd₄, wr₄, hT₄, f₄⟩ => ?_)
      obtain inT : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 96) 16 :=
        in_left (in_off he₄.perm.w (show 96 + 16 ≤ 2560 by decide) (by decide))
      obtain inH₄ : InRegions (s₄.rd ++ s₄.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
        rw [rd₄, wr₄, rd₁', wr₁', rd₁, wr₁]; exact inH
      refine WP.mono (aadMul_ok s₄ he₄.r13 he₄.r14 he₄.r15 inT inH₄ (outY he₄)) fun t ⟨b, m, g, rd, wr⟩ => ?_
      obtain fT : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₄.mem := by rw [← m₁, ← m₁']; exact f₄
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
  refine WP.seq (WP.mono (WP.with_rdwr (j012_ok L (gs := 256) ⟨he, hH, h12, hbp, hN⟩)) fun s₁ ⟨j₁, hrd₁, hwr₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.with_rdwr (initState_ok L j₁)) fun s₂ ⟨j₂, hrd₂, hwr₂⟩ => ?_)
  have f₂ := j₂.frame
  have he₂ := j₂.env
  -- What `j0` keeps.
  obtain kW : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 512) →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    f₂.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (d := 16) (k := 80) (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact (L.stk_w (by omega_arith)).symm) (by decide)
  obtain dCj : ∀ {a k : Nat}, a + k ≤ 256 → ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP,
      (⟨Ctx + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_left (Lay.ctxSub hk)
    · exact L.ctx_w hk (by decide)
    · exact L.ctx_w hk (by decide)
    · exact L.ctx_w hk (by decide)
    · exact (L.stk_ctx hk).symm
  obtain dAj : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP, (⟨A, al⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hAd.st
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.w.sub_right (Lay.wSub (by decide))
    · exact hAd.stk.symm
  have h15₂ := he₂.r15
  obtain q₂ := he₂.perm.wR (show 184 + 8 ≤ 2560 by decide)
  obtain hal₂ := kW 184 (.inl ⟨by decide, by decide⟩)
  rw [hal] at hal₂
  have hlt := hAd.lt
  obtain ⟨s₃, run₃, hcx₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)] s₂ = some s₃ ∧
      s₃.gpr .rcx = BitVec.ofNat 64 al ∧ s₃.zf = some (decide (al = 0)) ∧
      (∀ r, r ≠ .rcx → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by xrun [h15₂, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hal₂]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, hal₂]; rw [and_self_beq (by omega_arith)]
    · intro r h; simp [gpr_setReg, h]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  refine WP.ite (decide (al = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · -- No additional data: the accumulator stays zero.
    obtain h0 : al = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨he₃, by rw [hm₃]; exact j₂.hH, by rw [hm₃]; exact j₂.j0, ?_, by rw [hm₃]; exact j₂.cb,
      by rw [hm₃]; exact j0Frame_one f₂⟩
    rw [hm₃]
    simpa [bytesAt, padLen, zeros] using Proof.Gcm.absorbed_nil (b := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H j₂.y
  · have h0 : al ≠ 0 := by simpa using hf
    obtain hA₃ : bytesAt s₃.mem A al = bytesAt s.mem A al := by rw [hm₃]; exact bytesAt_frame f₂ dAj (by omega_arith)
    obtain haad₃ : s₃.mem.readW (W + BitVec.ofNat 64 232) 64 = A := by
      rw [hm₃, kW 232 (.inr ⟨by decide, by decide⟩), haad]
    obtain fs₃ : Frame (wFrame W SP) s.mem s₃.mem := by rw [hm₃]; exact j0Frame_one f₂
    obtain dH : ∀ r ∈ wFrame W SP, (⟨Ctx + BitVec.ofNat 64 272, 16⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact cw.sub_right (Lay.wSub (by decide))
      · exact cw.sub_right (Lay.wSub (by decide))
      · exact cw.sub_right (Lay.wSub (by decide))
      · exact ct.symm
    obtain hP₃ : IsH1 H (s₃.mem.readW (Ctx + BitVec.ofNat 64 272) 128) := by
      rwa [fs₃.readW (r := ⟨Ctx + BitVec.ofNat 64 272, 16⟩) (Region.contains_self _ _) dH (by decide)]
    obtain inH₃ : InRegions (s₃.rd ++ s₃.wr) (Ctx + BitVec.ofNat 64 272) 16 := by
      rw [hrd₃, hwr₃, hrd₂, hwr₂, hrd₁, hwr₁]; exact inH
    refine WP.mono (aadSome_ok L he₃ (hAd.of_eq (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁]))
      (by omega_arith) h16 haad₃ hcx₃ inH₃ cw) fun t ⟨he₅, rd₅, wr₅, b₅, f₅, keep'⟩ => ?_
    obtain keep : ∀ {a : Nat}, a + 16 ≤ 80 → (a + 16 ≤ 16 ∨ 32 ≤ a) →
        blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) =
          blockAt s₂.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 a) := fun ha ho => by
      rw [keep' ha ho, hm₃]
    obtain hH₂ : blockAt t.mem (Ctx + BitVec.ofNat 64 240) = H := by
      rw [blockAt_frame (fs₃.trans f₅) fun r hr => ?_]
      · exact hH
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.ctx_w (by decide) (by decide)
      · exact L.ctx_w (by decide) (by decide)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm
    obtain hA₄ := length_bytesAt s.mem A al
    refine ⟨he₅, hH₂, ?_, ?_, ?_, fs₃.trans f₅⟩
    · have := keep (a := 0) (by decide) (.inl (by decide))
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
      rw [this]; exact j₂.j0
    · rw [hA₄]
      refine Proof.Gcm.absorb_complete (x := []) (Proof.Gcm.absorbed_nil (m := s₂.mem)
        (b := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H j₂.y) ?_ rfl ?_
      · simp only [List.length_nil, Nat.zero_mod, List.append_eq, List.length_append, hA₄, Proof.Gcm.length_zeros, padLen]
        omega_arith
      · rw [j₂.y, b₅, aadMul_ghash hP₃, hA₃, List.drop_nil, List.nil_append,
          show padLen al = 16 - al by simp only [padLen]; omega_arith, List.append_eq]
    · rw [keep (by decide) (.inr (by decide))]; exact j₂.cb
end

end VG.Proof.AesGcm.X86_64.Fast

end

end

/-!
# AES-GCM `seal_split`'s path for TLS records: at most 16 bytes left

Untrusted: everything here is checked by Lean. `Fast.tail` ends `seal_split`
for the at most 16 bytes left after `prefix` without `oneBlocks`: the total
length put back (`fixTlen_ok`), `H'` and `H'²` loaded from the prepared key
context (`finPowP_ok`, which `ShortFacts.pp1` and `pp2` make multiply as `H`
and `H²`), and `finish`'s end for no whole blocks (`Short.finRest_ok` with
`q = 0`). It leaves what `SealSplit.body` does (`Split.body_ok`): `tail_ok`;
and so does `Fast.run`'s choice between them on the bytes left (`fbody_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split (fixTlen_ok splitFrame BodyOk FinOk body_ok)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk IsH1 IsH2 finRest_ok)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Only const_ok)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

/-- `finPowP`: the constants, and the 16 bytes at `ctx + 272` and at
`ctx + 256` in `xmm3` and `xmm6`. -/
theorem finPowP_run {Ctx : Addr} (s : State) (h13 : s.gpr .r13 = Ctx)
    (in1 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (in2 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 256) 16) :
    WP isa (.block Impl.AesGcm.X86_64.Short.finPowP) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧ t.xmm .xmm3 = s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 ∧
      t.xmm .xmm6 = s.mem.readW (Ctx + BitVec.ofNat 64 256) 128 ∧
      Only [.xmm0, .xmm12, .xmm1, .xmm12, .xmm3, .xmm6] s t := by
  obtain e : ∀ d : Nat, s.gpr .r13 + BitVec.ofInt 64 (d : Int) = Ctx + BitVec.ofNat 64 d := fun d => by
    rw [h13, BitVec.ofInt_natCast]
  simp only [Impl.AesGcm.X86_64.Short.finPowP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  obtain O₂ := o₁.trans o₂
  rw [show ([.movdquLoad .xmm3 (at_ .r13 272), .movdquLoad .xmm6 (at_ .r13 256)] : List Instr) =
      [.movdquLoad .xmm3 (at_ .r13 272)] ++ [.movdquLoad .xmm6 (at_ .r13 256)] from rfl, WP.block_append_iff]
  refine WP.mono (ld_ok .xmm3 .r13 272 s₂ (by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), e]; exact in1))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  refine WP.mono (ld_ok .xmm6 .r13 256 s₃ (by
      rw [o₃.rd, o₃.wr, O₂.rd, O₂.wr, o₃.gpr _ (by decide), O₂.gpr _ (by decide), e]; exact in2))
    fun s₄ ⟨l₄, o₄⟩ => ?_
  rw [O₂.gpr _ (by decide), e, O₂.mem] at l₃
  rw [o₃.gpr _ (by decide), O₂.gpr _ (by decide), e, o₃.mem, O₂.mem] at l₄
  exact ⟨by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁,
      VG.Proof.Gcm.X86_64.Pclmul.rev_eq],
    by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂], by rw [o₄.xmm _ (by decide), l₃], l₄,
    O₂.trans (o₃.trans o₄)⟩

/-- `finPowP` from a prepared key context: the constants, and `H'` and `H'²`,
which multiply as `H` and `H²`. -/
theorem finPowP_ok (hF : ShortFacts) {Ctx : Addr} {H : Block} (s : State) (h13 : s.gpr .r13 = Ctx)
    (in1 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 272) 16)
    (in2 : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 256) 16)
    (p1 : s.mem.readW (Ctx + BitVec.ofNat 64 272) 128 = Spec.Gcm.preparedPower (Spec.Gcm.hpow H 1))
    (p2 : s.mem.readW (Ctx + BitVec.ofNat 64 256) 128 = Spec.Gcm.preparedPower (Spec.Gcm.hpow H 2)) :
    WP isa (.block Impl.AesGcm.X86_64.Short.finPowP) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧ IsH1 H (t.xmm .xmm3) ∧ IsH2 H (t.xmm .xmm3) (t.xmm .xmm6) ∧
      Only [.xmm0, .xmm12, .xmm1, .xmm12, .xmm3, .xmm6] s t :=
  WP.mono (finPowP_run s h13 in1 in2) fun _ ⟨x0, x1, x3, x6, o⟩ =>
    ⟨x0, x1, by rw [x3, p1]; exact hF.pp1 H, by rw [x3, x6, p1, p2]; exact hF.pp2 H, o⟩

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `tail` for the `n ≤ 16` bytes left: what `SealSplit.body` leaves
(`Split.body_ok`). -/
theorem tail_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) {R : Nat} {D : Addr} {n al N : Nat}
    {H icb : Block} {a : List Byte} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (h16 : n ≤ 16)
    (hd : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n)
    (kw : (below SP 56).Disjoint ⟨W, 2560⟩) (kd : (below SP 56).Disjoint ⟨D, n⟩)
    (kM : (below SP 56).Disjoint ⟨Ctx, (CtxMode.preparedN np hpn).len⟩) (sp : 56 ≤ SP.toNat)
    (X : CtxExt (CtxMode.preparedN np hpn) Ctx (W + BitVec.ofNat 64 16) W SP D n s)
    (hH : blockAt s.mem (Ctx + BitVec.ofNat 64 240) = H) (hcb : blockAt s.mem (cbA W) = icb)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (habs : Absorbed s.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length)))
    (haux : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N) :
    WP isa (Impl.AesGcm.X86_64.Fast.tail ks) s fun s' =>
      Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (splitFrame W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16))) := by
  have hD := hd.ok.w
  obtain b24 : Region.Sub (below SP 24) (below SP 56) := below_sub (by decide) (by decide)
  obtain kc : (below SP 56).Disjoint ⟨Ctx, 256⟩ := kM.sub_right (Region.sub_prefix (CtxMode.preparedN np hpn).ge)
  obtain h : ObPre (CtxMode.preparedN np hpn) Ctx W SP R D n s :=
    ⟨he, hR, hdat, hlen, hd, kc.sub_left b24, kw.sub_left b24, kd.sub_left b24, by omega_using [sp], X⟩
  -- The total length put back.
  unfold Impl.AesGcm.X86_64.Fast.tail
  refine WP.seq (WP.mono (fixTlen_ok he haux) fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  obtain fW : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.le_refl _) (by decide) (by have := L.ww; omega_using []))
  obtain one : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 192, 8⟩ : Region)], (⟨p, k⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain wW : ∀ {d k : Nat}, d + k ≤ 192 ∨ 200 ≤ d → d + k ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ :=
    fun h₁ h₂ => Offset.disjoint W h₁ (by have := L.ww; omega_using [h₂]) (by have := L.ww; omega_using [])
  obtain rW : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => fW.readW (Region.contains_self _ _) (one (wW h₁ h₂)) (by decide)
  obtain f₁ : Frame (oneFrameB W D SP n) s.mem s₁.mem := fW.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨W + BitVec.ofNat 64 192, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain dC := ctx_oneFrameB L hd.ctx (kc.sub_left b24)
  obtain hc₁ : ciphOf s₁.mem Ctx R = ciphOf s.mem Ctx R := ciph_frame f₁ dC hR.2
  obtain stD : (⟨W + BitVec.ofNat 64 16, 80⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ :=
    wW (.inl (by decide)) (by decide)
  obtain bW : ∀ {p : Addr}, Region.Sub ⟨p, 16⟩ ⟨W + BitVec.ofNat 64 16, 80⟩ → blockAt s₁.mem p = blockAt s.mem p :=
    fun hs => blockAt_frame fW (one (stD.sub_left hs))
  obtain hJ₁ : blockAt s₁.mem (W + BitVec.ofNat 64 16) = blockAt s.mem (W + BitVec.ofNat 64 16) :=
    bW (Region.sub_prefix (by decide))
  obtain hcb₁ : blockAt s₁.mem (cbA W) = Nat.repeat inc32 0 icb := by
    rw [bW Split.cb_sub]; exact hcb
  obtain ab₁ : Absorbed s₁.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H
      (a ++ zeros (padLen a.length) ++ bytesAt s₁.mem D (16 * 0)) := by
    rw [show bytesAt s₁.mem D (16 * 0) = [] from rfl, List.append_nil]
    obtain hm := Nat.mod_lt (a ++ zeros (padLen a.length)).length (show 16 > 0 by decide)
    refine ⟨by rw [bW Split.y_sub]; exact habs.1, ?_⟩
    rw [bytesAt_frame fW (one (stD.sub_left
      (Offset.sub_base (W + BitVec.ofNat 64 16) (d := 32) (k := 80) (by omega_using [])))) (by omega_using [])]
    exact habs.2
  obtain dDW : (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ := hD.sub_right (Lay.wSub (by decide))
  obtain ht₁ : bytesAt s₁.mem (D + BitVec.ofNat 64 (16 * 0)) n = bytesAt s.mem (D + BitVec.ofNat 64 (16 * 0)) n := by
    rw [show D + BitVec.ofNat 64 (16 * 0) = D by simp]
    exact bytesAt_frame fW (one dDW) (by have := hd.ok.wrap; omega_using [h16])
  obtain hR₁ : RoundsAt s₁.mem W R := ⟨by rw [rW 176 (.inl (by decide)) (by decide)]; exact hR.1, hR.2⟩
  -- `H'` and `H'²`.
  have cov₁ := X.cov
  rw [← rd₁, ← wr₁] at cov₁
  obtain hX : VG.Proof.Gcm.X86_64.Stitch.PowersN np s₁.mem Ctx :=
    (CtxMode.preparedN np hpn).frame fW (one (X.cw.sub_right (Lay.wSub (by decide)))) X.w X.ok
  obtain p0 := hX 0 (by have := hpn.1; omega_using [hpn])
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at p0
  obtain hH₁ : ctxH s₁.mem Ctx = H := by
    rw [ctxH_eq, blockAt_frame fW (one ((X.cw.sub_left (Offset.sub_base Ctx (show 240 + 16 ≤ 1024 by decide))).sub_right
      (Lay.wSub (by decide)))), hH]
  rw [hH₁] at p0
  unfold Impl.AesGcm.X86_64.Short.finishP
  refine WP.seq (WP.mono (finPowP_ok hF s₁ he₁.r13 (in_off cov₁ (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
    (in_off cov₁ (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64))) p0.2 p0.1) fun s₂ ⟨x0, x1, h1, h2, o₂⟩ => ?_)
  obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun g hg => o₂.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> decide)) o₂.rd o₂.wr
  refine WP.mono (finRest_ok (q := 0) hks h (by omega_using []) h16 f₁ hR₁ hc₁ hJ₁ (by rfl) hcb₁ ab₁ ht₁
    (by rw [m₁, Mem.readW_writeW_self64])
    (by rw [rW 200 (.inr (by decide)) (by decide), hdat]; simp)
    (by rw [rW 208 (.inr (by decide)) (by decide)]; exact hlen)
    (by rw [rW 184 (.inl (by decide)) (by decide)]; exact hal) he₂ o₂.mem
    (o₂.rd.trans rd₁) (o₂.wr.trans wr₁) x0 x1 h1 h2) fun t ⟨et, rdt, wrt, ft, hCt, hTt⟩ =>
      ⟨et, rdt, wrt, ft.sub fun r hr => ?_, hCt, hTt⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, b24⟩

end

/-- The bytes left compared with 17. -/
theorem lenTest_ok {Ctx St W SP : Addr} {n : Nat} (hn : n < 2 ^ 64) (s : State) (he : Env Ctx St W SP s)
    (hl : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)]) s fun t =>
      t.cf = some (decide (n < 17)) ∧ (∀ g, g ≠ .rax → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₃, run₃, ax₃, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [.mov .rax (.mem (at_ .r15 lenO))] s = some s₃ ∧
      s₃.gpr .rax = BitVec.ofNat 64 n ∧ (∀ g, g ≠ .rax → s₃.gpr g = s.gpr g) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧
      s₃.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₁, hl], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro g hg; simp [gpr_setReg, hg]
    all_goals rfl
  obtain ⟨s₄, run₄, -, cf₄, g₄, m₄, rd₄, wr₄⟩ := cmpImm_ok s₃ .rax ax₃ hn (show 17 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, cf₄,
    fun g hg => by rw [g₄, g₃ g hg], m₄.trans m₃, rd₄.trans rd₃, wr₄.trans wr₃⟩⟩)

/-- `Fast.run`'s code after `prefix`: `tail` for at most 16 bytes left, and
`SealSplit.body` otherwise. -/
theorem fbody_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (B : BlkFn (CtxMode.preparedN np hpn)) {fin : Prog isa}
    (hfin : FinOk (CtxMode.preparedN np hpn) fin) :
    BodyOk (CtxMode.preparedN np hpn) (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      (.ite .b (Impl.AesGcm.X86_64.Fast.tail ks)
        (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)))) := by
  intro Ctx W SP L R D n al N H icb a s he hR hdat hlen hd kw kd kM sp X hH hcb hal habs haux hN
  refine WP.seq (WP.mono (lenTest_ok hd.ok.lt s he hlen) fun t ⟨cf, g, m, rd, wr⟩ => ?_)
  obtain het : Env Ctx (W + BitVec.ofNat 64 16) W SP t := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide)) rd wr
  obtain hRt : RoundsAt t.mem W R := by rw [m]; exact hR
  obtain hdt := hd.of_eq rd wr
  obtain Xt := X.of_eq rd wr m
  obtain post : ∀ s' : State, (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = t.rd ∧ s'.wr = t.wr ∧
      Frame (splitFrame W D SP n) t.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf t.mem Ctx R) icb 0 (bytesAt t.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf t.mem Ctx R (blockAt t.mem (W + BitVec.ofNat 64 16)))) →
      (Env Ctx (W + BitVec.ofNat 64 16) W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (splitFrame W D SP n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem D n) ∧
      bytesAt s'.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s'.mem D n))))
        [ofBytes (lensBlock al N)] ^^^ ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16)))) :=
    fun s' ⟨e', rd', wr', f', hC, hT⟩ => ⟨e', rd'.trans rd, wr'.trans wr, m ▸ f', m ▸ hC, m ▸ hT⟩
  refine WP.ite (decide (n < 17)) (eval_b cf) (fun h => ?_) (fun h => ?_)
  · exact WP.mono (tail_ok L hF hks het hRt (by rw [m]; exact hdat) (by rw [m]; exact hlen)
      (by have := of_decide_eq_true h; omega_using [this]) hdt kw kd kM sp Xt (by rw [m]; exact hH) (by rw [m]; exact hcb)
      (by rw [m]; exact hal) (by rw [m]; exact habs) (by rw [m]; exact haux)) post
  · exact WP.mono (body_ok L B hfin het hRt (by rw [m]; exact hdat) (by rw [m]; exact hlen) hdt kw kd kM sp Xt
      (by rw [m]; exact hH) (by rw [m]; exact hcb) (by rw [m]; exact hal) (by rw [m]; exact habs)
      (by rw [m]; exact haux) hN) post

end VG.Proof.AesGcm.X86_64.Fast

end

end

/-!
# AES-GCM `seal_split`'s path for TLS records: at most 16 bytes left, in two runs

Untrusted: everything here is checked by Lean. `Short.finishP` loads `H'`
and `H'²` from the key context's address, which is public, and then ends as
`Short.finishWith` does (`Short.finRest_rel`): `finishP_rel`. Two runs test
the same public number of bytes left, so `Fast.run` takes `Fast.tail` in
both or `SealSplit.body` in both (`fbody_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split (BodyRel FinRel body_ct fixTlen_check fixTlen_oneS)
open VG.Proof.AesGcm.X86_64.Short (KsOk KsRel FinI finRest_rel rel_env_regs rel_next)
open VG.Proof.AesGcm.X86_64.StreamTo (step)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `finishP ks` in two runs with the same rounds and bytes left, the
prepared key context readable. -/
theorem finishP_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {Ctx W SP D : Addr} {R r : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => (FinI Ctx W SP D R r s₁ ∧ Covers [⟨Ctx, 1024⟩] (s₁.rd ++ s₁.wr)) ∧
        (FinI Ctx W SP D R r s₂ ∧ Covers [⟨Ctx, 1024⟩] (s₂.rd ++ s₂.wr)))
      (Short.finishP ks) fun _ _ => True := by
  have wPow : ∀ s, FinI Ctx W SP D R r s ∧ Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) →
      WP isa (.block Short.finPowP) s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (finPowP_run s h.1.env.r13 (in_off h.2 (show 272 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))
      (in_off h.2 (show 256 + 16 ≤ 1024 by decide) (by exact (by decide : (1024 : Nat) < 2 ^ 64)))) fun _ ⟨_, _, _, _, o⟩ =>
      h.1.keep (fun g hg => o.gpr g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)
  have p := rel_next (rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block Short.finPowP) ⟨_, by taint_decide⟩) wPow wPow
  unfold Short.finishP
  exact RelCT.seq p (finRest_rel hks hkr hR hr)

theorem lenTest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      hc).isSome = true := ⟨_, by taint_decide⟩

/-- `Fast.run`'s code after `prefix`, in two runs. -/
theorem fbody_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) (B : BlkFn (CtxMode.preparedN np hpn)) {fin : Prog isa}
    (hfin : FinRel (CtxMode.preparedN np hpn) fin) :
    BodyRel (CtxMode.preparedN np hpn) (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)])
      (.ite .b (Impl.AesGcm.X86_64.Fast.tail ks)
        (.frame (.push [.rax]) (.seq (oneBlocks B.enc) (.seq (.block SealSplit.fixTlen) fin)) (.pop .rax 1)))) := by
  intro Ctx W SP A D R al n L kw kd kM ka sp N
  let G : State → Prop := fun s => OneS (CtxMode.preparedN np hpn) Ctx W SP R A al D n none s ∧
    s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 N
  have hw : ∀ s, G s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17)]) s
      fun t => t.cf = some (decide (n < 17)) ∧ G t := fun s g =>
    WP.mono (lenTest_ok g.1.dD.ok.lt s g.1.env g.1.len) fun t ⟨cf, gg, m, rd, wr⟩ =>
      ⟨cf, g.1.keep (fun r hr => gg r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)) m rd wr, by rw [m]; exact g.2⟩
  have t := step [.r15] lenTest_check (P := fun s₁ s₂ => G s₁ ∧ G s₂)
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [g.1.1.env.r15, g.2.1.env.r15])
    (fun _ _ g => g) hw hw
  refine RelCT.seq t (RelCT.ite (fun _ _ h => by
    show _ = _; exact h.1.1.trans h.2.1.symm) ?_ ?_)
  · -- At most 16 bytes left: `tail`.
    refine StreamTo.RelCT.of_imp (n ≤ 16 ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ n < 2 ^ 64) (fun _ _ h => by
      have e := h.1.1.1.symm.trans h.2
      simp only [Option.some.injEq, decide_eq_true_eq] at e
      exact ⟨by omega_using [e], h.1.1.2.1.rounds.2, h.1.1.2.1.dD.ok.lt⟩) fun ⟨_, hR, hn⟩ => ?_
    unfold Impl.AesGcm.X86_64.Fast.tail
    have fx := step [.r15] fixTlen_check
      (P := fun s₁ s₂ => ((s₁.cf = some (decide (n < 17)) ∧ G s₁) ∧ s₂.cf = some (decide (n < 17)) ∧ G s₂) ∧
        isa.eval .b s₁ = some true)
      (fun _ _ g r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [g.1.1.2.1.env.r15, g.1.2.2.1.env.r15])
      (fun _ _ g => ⟨g.1.1.2, g.1.2.2⟩) (fun _ g => fixTlen_oneS L g.1 g.2) (fun _ g => fixTlen_oneS L g.1 g.2)
    refine RelCT.seq fx ((finishP_rel hks hkr (Ctx := Ctx) (W := W) (SP := SP) (D := D) hR hn).mono
      (fun _ _ g => ⟨⟨⟨g.1.env, g.1.rounds.1, g.1.dat, g.1.len⟩, g.1.ext.cov⟩,
        ⟨⟨g.2.env, g.2.rounds.1, g.2.dat, g.2.len⟩, g.2.ext.cov⟩⟩) fun _ _ g => g)
  · -- More: `body`.
    exact (body_ct L kw kd kM ka sp B hfin (N := N)).mono (fun _ _ g => ⟨g.1.1.2, g.1.2.2⟩) fun _ _ g => g

end VG.Proof.AesGcm.X86_64.Fast
