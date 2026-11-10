module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.CT
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx512
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.CT
meta import VerifiedGarbage.Impl.Sha512.X86_64.Avx512
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# SHA-512 with AVX-512VL on x86-64: the compression function

`Impl.Sha512.X86_64.Avx512.compress` is the code of
`Impl.Sha512.X86_64.Avx2Rolled` with other schedule steps, so its proof is
that one's (`correctWith`, `compress_ctWith`) given what it needs of them
(`SchedOk`): a step computes in each lane what the AVX2 step does
(`xupdV_xupd`), with rotations and three-way xors in place of shifts and
xors.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2 VG.Impl.Sha512.X86_64.Avx2Rolled
open VG.Proof.Sha512.X86_64.Avx2 VG.Proof.Sha512.X86_64.Avx2.Rolled
open VG.Spec.Sha512 (Word ssig0 ssig1)

/-! ## `vprorq` and `vpternlogd`, on quadwords -/

theorem ror_eq (hi lo : Word) (n : BitVec 8) :
    rorQwords (hi ++ lo) n = hi.rotateRight (n.toNat % 64) ++ lo.rotateRight (n.toNat % 64) := by
  simp only [rorQwords, qword_append_0, qword_append_1]

/-- `0x96`: the xor of the three. -/
theorem tern96 (a b c : BitVec 128) : ternlog a b c 0x96 = a ^^^ b ^^^ c := by
  simp only [ternlog, List.range, List.range.loop, List.foldl,
    show (0x96 : BitVec 8).getLsbD 0 = false from rfl, show (0x96 : BitVec 8).getLsbD 1 = true from rfl,
    show (0x96 : BitVec 8).getLsbD 2 = true from rfl, show (0x96 : BitVec 8).getLsbD 3 = false from rfl,
    show (0x96 : BitVec 8).getLsbD 4 = true from rfl, show (0x96 : BitVec 8).getLsbD 5 = false from rfl,
    show (0x96 : BitVec 8).getLsbD 6 = false from rfl, show (0x96 : BitVec 8).getLsbD 7 = true from rfl,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj, decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem tern96_eq (a b c d e f : Word) :
    ternlog (a ++ b) (c ++ d) (e ++ f) 0x96 = (a ^^^ c ^^^ e) ++ (b ^^^ d ^^^ f) := by
  rw [tern96, BitVec.xor_append, BitVec.xor_append]

/-! ## One lane of `schedule` -/

/-- What `Impl.Sha512.X86_64.Avx512.schedule` computes in one lane, as its
instructions do. -/
def xupdV (x₀ x₁ x₄ x₅ x₇ : BitVec 128) : BitVec 128 :=
  let t₀ := alignRight x₁ x₀ 8
  let t₁ := alignRight x₅ x₄ 8
  let y := XBinOp.eval .paddq x₀ t₁
  let y := XBinOp.eval .paddq y
    (ternlog (rorQwords t₀ 1) (rorQwords t₀ 8) (XShiftOp.eval .psrlq t₀ 7) 0x96)
  XBinOp.eval .paddq y (ternlog (rorQwords x₇ 19) (rorQwords x₇ 61) (XShiftOp.eval .psrlq x₇ 6) 0x96)

theorem xupdV_eq (w₀ w₁ w₂ w₃ w₈ w₉ w₁₀ w₁₁ w₁₄ w₁₅ : Word) :
    xupdV (w₁ ++ w₀) (w₃ ++ w₂) (w₉ ++ w₈) (w₁₁ ++ w₁₀) (w₁₅ ++ w₁₄) =
      (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅) ++ (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄) := by
  simp only [xupdV, alignRight_8, paddq_eq, ror_eq, tern96_eq,
    psrlq_eq _ _ _ (by decide : (7 : BitVec 8).toNat < 64), psrlq_eq _ _ _ (by decide : (6 : BitVec 8).toNat < 64),
    BitVec.reduceToNat, Nat.reduceMod, Spec.Sha512.ssig0, Spec.Sha512.ssig1]

theorem append_qwords (x : BitVec 128) : qword x 1 ++ qword x 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  by_cases h : i < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · simp only [h, ite_false, show i - 64 < 64 by omega, decide_true, Bool.true_and,
      show 64 + (i - 64) = i by omega]

/-- The step with AVX-512VL computes what the AVX2 step does. -/
theorem xupdV_xupd (a b c d e : BitVec 128) : xupdV a b c d e = xupd a b c d e := by
  rw [← append_qwords a, ← append_qwords b, ← append_qwords c, ← append_qwords d, ← append_qwords e,
    xupdV_eq, xupd_eq]

/-! ## Running a step -/

theorem scheduleV_ok (n : Nat) (s : State) (a b c d e a' b' c' d' e' : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 4)) = c)
    (hd : s.xmm (msg (n + 5)) = d) (he : s.xmm (msg (n + 7)) = e)
    (ha' : s.ymmHi (msg n) = a') (hb' : s.ymmHi (msg (n + 1)) = b') (hc' : s.ymmHi (msg (n + 4)) = c')
    (hd' : s.ymmHi (msg (n + 5)) = d') (he' : s.ymmHi (msg (n + 7)) = e')
    (hout : InRegions s.wr (s.ea (sSlot n)) 32) :
    WP isa (.block (scheduleR Impl.Sha512.X86_64.Avx512.schedule n)) s fun s' =>
      s'.xmm (msg n) = xupdV a b c d e ∧ s'.ymmHi (msg n) = xupdV a' b' c' d' e' ∧
      (∀ r, r ≠ msg n → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.ea (sSlot n)) (xupdV a' b' c' d' e' ++ xupdV a b c d e) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup n
  have hn' := VG.nodup_reverse hn
  have eas : s.ea (sSlot n) = s.gpr .rcx + s.gpr .rdx * BitVec.ofNat 64 2 +
      BitVec.ofInt 64 ((32 * n : Nat) : Int) := rfl
  rw [eas] at hout ⊢
  apply WP.of_runBlock
  simp only [scheduleR, Impl.Sha512.X86_64.Avx512.schedule, Impl.Sha512.X86_64.Avx512.vror,
    Impl.Sha512.X86_64.Avx512.vxor3, vb, vs, List.dropLast, List.cons_append, List.nil_append, sSlot]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 4) = x₄ at *
  generalize msg (n + 5) = x₅ at *
  generalize msg (n + 7) = x₇ at *
  simp only [t0, t1, t2, t3, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' ⊢
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, and_self, runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.ymm, State.store256, State.ea, hout, hn, hn',
    ha, hb, hc, hd, he, ha', hb', hc', hd', he', Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, rfl, trivial⟩

theorem group_check : ∀ n < 8,
    ((fps.blockFp (scheduleR Impl.Sha512.X86_64.Avx512.schedule (n + 8))).bind fun A =>
      (fps.blockFp (roundR 0 (2 * n) ++ roundR 0 (2 * n + 1))).map fun B => fps.indep A B) = some true := by
  decide +kernel

/-- The steps of `Impl.Sha512.X86_64.Avx512.schedule`. -/
theorem schedOk : SchedOk Impl.Sha512.X86_64.Avx512.schedule where
  run n s a b c d e a' b' c' d' e' ha hb hc hd he ha' hb' hc' hd' he' hout := by
    have h := scheduleV_ok n s a b c d e a' b' c' d' e' ha hb hc hd he ha' hb' hc' hd' he' hout
    simp only [xupdV_xupd] at h
    exact h
  indeps n hn := fps.indeps_of_check (group_check n hn)

/-! ## The function -/

theorem first_rel {P : State → State → Prop} (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τA s₁ s₂) :
    RelCT isa P (first Impl.Sha512.X86_64.Avx512.schedule) fun _ _ => True :=
  RelCT.taint (A := A) τA hp (by taint_decide)

/-- `vg_sha512_compress_avx512`, against the contract of the AVX2 code. -/
theorem compress_verified :
    Verified X86_64.target Impl.Sha512.X86_64.Avx512.compress Proof.Sha512.compressWideX86_64 := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correctWith schedOk (Rolled.pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    exact compress_ctWith schedOk first_rel s₁ s₂ t₁ t₂ s₁' s₂' (Rolled.pre_of s₁ h₁) (Rolled.pre_of s₂ h₂) ⟨h1, h2, h3, h4⟩ e₁ e₂
  · refine ⟨Avx2.satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.X86_64.Avx512
