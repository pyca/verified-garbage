module

public import VerifiedGarbage.Impl.AesOcb.X86_64AesNi
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.AesOcb.X86_64.Words
public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Offsets
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Ocb.State
-- separate module: it builds alongside `Group`, which `Pass` also imports

/-!
# One-pass AES-OCB with AES-NI on x86-64: the setup

Untrusted: everything here is checked by Lean. `ldx_ok`: a block read back
in two 8-byte halves (`ldx`) is the block. `keys_ok`: `rsi` the rounds and
`r10` the last round key.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesOcb.X86_64 (at_ ld st mvr addi rndO)
open VG.Impl.AesOcb.X86_64AesNi (ldx keys keysR lastKey c8 stC cO l1O l2O l3O ljO lmore ctab)
open VG.Impl.AesOcb.X86_64 (l0O)
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesOcb.X86_64 (BlkStep dbl_okX copy16_okX rv blockAtMem_eq rv_xor addr8)
open VG.Proof.AesCcm.X86_64 (in_off in_left toNat_ofNat_of_lt eval_e eval_ne)

/-- 16 bytes as two quadwords. -/
theorem readW128_q (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  have e1 := readW_extract m a (w := 128) (k := 8) (n := 8) (by omega_arith)
  have e0 := readW_extract m a (w := 128) (k := 0) (n := 8) (by omega_arith)
  rw [BitVec.add_zero] at e0
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 64
  · simp only [h, decide_true, Bool.cond_true]
    rw [← e0]; simp only [BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and]
    exact congrArg _ (by omega_arith)
  · simp only [h, decide_false, Bool.cond_false]
    rw [← e1]; simp only [BitVec.getLsbD_extractLsb', show j - 64 < 64 by omega_arith, decide_true, Bool.true_and]
    exact congrArg _ (by omega_arith)

/-- `punpcklqdq` of two quadwords in registers (`movq`). -/
theorem punpck_movq (x y : BitVec 64) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ x) ((0 : BitVec 64) ++ y) = y ++ x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [reduceXBinOpEval, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ite_true, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_true,
      Bool.true_and, Nat.mul_zero, Nat.zero_add, Bool.cond_true]
  · simp only [h, ite_false, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      show i - 64 < 64 by omega_arith, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add, Bool.cond_true,
      ite_true]

/-- `ldx x t d`: `x ←` the block at `W + d`, through `rax`, `rdx` and `t`. -/
theorem ldx_ok (x t : XReg) (d : Nat) (s : State) {W : Addr} (h15 : s.gpr .r15 = W) (hxt : x ≠ t)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8) :
    WP isa (.block (ldx x t d)) s fun s' =>
      s'.xmm x = s.mem.readW (W + BitVec.ofNat 64 d) 128 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ x → r ≠ t → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  refine ⟨_, by orun [ldx, h15, r₀, r₁, XOp.exec, State.setXmm], ?_⟩
  refine ⟨?_, fun r h1 h2 => by simp [gpr_setReg, h1, h2], rfl, rfl, rfl, fun r h1 h2 => by
    simp [xmm_setReg, h1, h2]⟩
  simp only [ite_true, hxt, ite_false, Ne.symm hxt, gpr_setReg, reduceCtorEq, punpck_movq]
  rw [readW128_q, addr8]

/-- `keys`: `rsi ←` the rounds `R` from `W + rndO`, `r10 ← rdi + 16 R`. -/
theorem keys_ok (s : State) {W : Addr} {R : Nat} (h15 : s.gpr .r15 = W)
    (hR : s.mem.readW (W + BitVec.ofNat 64 rndO) 64 = BitVec.ofNat 64 R)
    (rR : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 rndO) 8) :
    WP isa (.block keys) s fun s' =>
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R) ∧
      (∀ r, r ≠ .rsi → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm := by
  apply WP.of_runBlock
  rw [show BitVec.ofNat 64 rndO = 232#64 from rfl] at hR rR
  refine ⟨_, by orun [keys, lastKey, h15, hR, rR], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_arithFlags], ?_, fun r h1 h2 => by
    simp [gpr_setReg, gpr_arithFlags, h1, h2], by simp [mem_setReg, mem_arithFlags], by
    simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags], by
    simp [xmm_setReg, xmm_arithFlags]⟩
  simp only [gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false]
  rw [BitVec.add_comm (s.gpr .rdi)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- `lastKey`: `r10 ← rdi + 16 R`, for the rounds `R` in `rsi`. -/
theorem lastKey_ok (s : State) {R : Nat} (hsi : s.gpr .rsi = BitVec.ofNat 64 R) :
    WP isa (.block lastKey) s fun s' =>
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R) ∧ (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  refine ⟨_, by orun [lastKey], ?_⟩
  refine ⟨?_, fun r h => by simp [gpr_setReg, gpr_arithFlags, h], by simp [mem_setReg, mem_arithFlags], by
    simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags], by simp [xmm_setReg, xmm_arithFlags]⟩
  simp only [gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, hsi]
  rw [BitVec.add_comm (s.gpr .rdi)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- `keysR`: `rsi ←` the rounds `R` again, from `r10 = rdi + 16 R`. -/
theorem keysR_ok (s : State) {R : Nat} (hR : R ≤ 14) (h10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)) :
    WP isa (.block keysR) s fun s' =>
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  refine ⟨_, by orun [keysR], ?_⟩
  refine ⟨?_, fun r h => by simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h], by
    simp [mem_setReg, mem_arithFlags, mem_setFlags], by simp [rd_setReg, rd_arithFlags, rd_setFlags], by
    simp [wr_setReg, wr_arithFlags, wr_setFlags], by simp [xmm_setReg, xmm_arithFlags, xmm_setFlags]⟩
  simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, reduceCtorEq, ite_false, h10]
  rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by rw [BitVec.add_comm, BitVec.add_sub_cancel],
    Proof.AesCcm.X86_64.shr4 _ (by omega_arith), show 16 * R / 16 = R by omega_arith]

theorem shr1 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hn, toNat_ofNat_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

theorem and1 (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n &&& BitVec.signExtend 64 (1 : BitVec 32) == 0#64) = decide (n % 2 = 0) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 by decide]
  have : BitVec.ofNat 64 n &&& 1#64 = BitVec.ofNat 64 (n % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, toNat_ofNat_of_lt hn]
    rw [show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one,
      Nat.mod_eq_of_lt (a := n % 2) (by omega_arith)]
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

/-- `m / 2 ^ j`, for `j ≤ ntz m`, is even exactly while `j < ntz m`. -/
theorem even_div_iff {m j : Nat} (h0 : 0 < m) (hj : j ≤ ntz m) : (m / 2 ^ j) % 2 = 0 ↔ j < ntz m := by
  obtain ⟨u, hu, hu2⟩ := Proof.Ocb.ntz_spec m h0
  generalize ntz m = N at hu hj ⊢
  subst hu
  have hq : 2 ^ N * u / 2 ^ j = 2 ^ (N - j) * u := by
    rw [show 2 ^ N = 2 ^ j * 2 ^ (N - j) by rw [← Nat.pow_add, Nat.add_sub_of_le hj], Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos j)]
  rw [hq]
  rcases Nat.eq_zero_or_pos (N - j) with h | h
  · rw [h, Nat.pow_zero, Nat.one_mul]; omega_arith
  · obtain ⟨e, he⟩ : ∃ e, N - j = e + 1 := ⟨N - j - 1, by omega_arith⟩
    rw [he, Nat.pow_succ, Nat.mul_comm (2 ^ e), Nat.mul_assoc, Nat.mul_mod_right]
    omega_arith

theorem and1' {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n &&& 1#64 = 0#64 ↔ n % 2 = 0 := by
  have h := and1 n hn
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 by decide] at h
  constructor
  · intro e; rw [e] at h; simpa using h.symm
  · intro e
    have h' : (BitVec.ofNat 64 n &&& 1#64 == 0#64) = true := by rw [h]; simp [e]
    simpa using h'

theorem zf_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).zf = c := rfl

/-- `c8`'s loop: `L_j` at `W + ljO`, from `L_3` with `r9 = k + 1` even,
doubled while `r9`, halved each time, is even. -/
theorem dblLoop_ok (s : State) {W : Addr} {wn : Nat} {l : Block} {m : Nat} (h15 : s.gpr .r15 = W)
    (hm : 0 < m) (hm' : m < 2 ^ 64) (hev : m % 2 = 0) (h9 : s.gpr .r9 = BitVec.ofNat 64 m)
    (hW : Covers [⟨W, wn⟩] s.wr) (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64)
    (hL : blockAtMem s.mem (W + BitVec.ofNat 64 ljO) = lAt l 3) :
    WP isa (.loop (.block (Impl.AesOcb.X86_64.dbl .r15 ljO .r15 ljO ++
        ([.shift .shr .r9 1, .alu .test .r9 (.imm 1)] : List Instr))) .e) s fun s' =>
      blockAtMem s'.mem (W + BitVec.ofNat 64 ljO) = lAt l (3 + ntz m) ∧
      Frame [⟨W + BitVec.ofNat 64 ljO, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx, .r8, .r9] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm := by
  have wW : ∀ {d n : Nat}, d + n ≤ wn → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h => in_off hW h hw
  have hn0 : 0 < ntz m := (even_div_iff (j := 0) hm (Nat.zero_le _)).mp (by simpa using hev)
  refine WP.loop (M := isa) (c := .e)
    (fun (n : Nat) (t : State) => ∃ j, n = ntz m - j ∧ j < ntz m ∧ t.gpr .r9 = BitVec.ofNat 64 (m / 2 ^ j) ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 ljO) = lAt l (3 + j) ∧
      Frame [⟨W + BitVec.ofNat 64 ljO, 16⟩] s.mem t.mem ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx, .r8, .r9] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.xmm = s.xmm) ?_ (ntz m - 0) _
    ⟨0, rfl, hn0, by rw [h9]; simp, by rw [hL], Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨j, rfl, hj, r9, lj, fr, g, rd, wr, xm⟩
  have h15t : t.gpr .r15 = W := by rw [g _ (by decide), h15]
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, B₁, x₁⟩ := dbl_okX (W := W) (B := W) (b := .r15) (o := .r15) (a := ljO) (d := ljO) h15t h15t
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [rd, wr]; exact in_left (wW (by simp only [ljO]; omega_arith))) (by rw [rd, wr]; exact in_left (wW (by simp only [ljO]; omega_arith)))
    (by rw [wr]; exact wW (by simp only [ljO]; omega_arith)) (by rw [wr]; exact wW (by simp only [ljO]; omega_arith))
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  have r9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (m / 2 ^ j) := by rw [B₁.gpr _ (by decide), r9]
  have hq : m / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm'
  apply WP.of_runBlock
  refine ⟨_, by orun [r9₁], ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq, ite_false, shr1 _ hq, Nat.div_div_eq_div_mul,
    ← Nat.pow_succ, zf_setReg, zf_arithFlags, zf_setFlags, and1 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hq),
    mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, xmm_setReg, xmm_arithFlags, xmm_setFlags, gpr_setFlags]
  have lj₁ : blockAtMem t₁.mem (W + BitVec.ofNat 64 ljO) = lAt l (3 + (j + 1)) := by
    rw [B₁.val, lj, ← Nat.add_assoc]; rfl
  have fr₁ : Frame [⟨W + BitVec.ofNat 64 ljO, 16⟩] s.mem t₁.mem := fr.trans B₁.frame
  have g₁ : ∀ r, r ∉ [Reg.rax, .rdx, .rcx, .r8, .r9] → t₁.gpr r = s.gpr r := fun r hr => by
    refine (B₁.gpr r fun h => hr ?_).trans (g r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h | h <;> simp [h]
  have ev := even_div_iff (j := j + 1) hm (by omega_arith)
  by_cases hlt : j + 1 < ntz m
  · right
    have hq' : m / 2 ^ (j + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm'
    refine ⟨by simp [isa, eval, (and1' hq').mpr (ev.mpr hlt)], ntz m - (j + 1), by omega_arith, j + 1, rfl, hlt, rfl, lj₁, fr₁,
      fun r hr => ?_, by rw [B₁.rd, rd], by rw [B₁.wr, wr], by rw [x₁, xm]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    first
      | exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])
      | (simp only [hr.2.2.2.2, ite_false]; exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]))
  · left
    have he : j + 1 = ntz m := by omega_arith
    have hq' : m / 2 ^ (j + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm'
    refine ⟨by simp [isa, eval, show ¬ (BitVec.ofNat 64 (m / 2 ^ (j + 1)) &&& 1#64 = 0#64) from
      fun h => hlt (ev.mp ((and1' hq').mp h))], ?_, fr₁,
      fun r hr => ?_, by rw [B₁.rd, rd], by rw [B₁.wr, wr], by rw [x₁, xm]⟩
    · rw [lj₁, he]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      first
      | exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])
      | (simp only [hr.2.2.2.2, ite_false]; exact g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]))

theorem append_xor_append (a b c d : BitVec 64) : (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append]
  split <;> rfl

/-- `C[8]`'s slot. -/
abbrev c8O : Nat := cO + 112

/-- `c8` for the group `k` (in `r13`): `C[8] = L_2 ⊕ L_{3 + ntz(k + 1)}`,
`L_2` and `L_3` at `W + l2O` and `W + l3O`. -/
theorem c8_ok (s : State) {W : Addr} {wn : Nat} {l : Block} {k : Nat} (h15 : s.gpr .r15 = W)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 k) (hk : k + 1 < 2 ^ 64) (hW : Covers [⟨W, wn⟩] s.wr)
    (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64)
    (hL2 : blockAtMem s.mem (W + BitVec.ofNat 64 l2O) = lAt l 2)
    (hL3 : blockAtMem s.mem (W + BitVec.ofNat 64 l3O) = lAt l 3) :
    WP isa c8 s fun s' =>
      blockAtMem s'.mem (W + BitVec.ofNat 64 c8O) = lAt l 2 ^^^ lAt l (3 + ntz (k + 1)) ∧
      Frame [⟨W + BitVec.ofNat 64 ljO, 16⟩, ⟨W + BitVec.ofNat 64 c8O, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx, .r8, .r9] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm11 → x ≠ .xmm13 → s'.xmm x = s.xmm x) := by
  have wW : ∀ {d n : Nat}, d + n ≤ wn → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h => in_off hW h hw
  unfold c8
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain ⟨s₀, run₀, B₀, x₀⟩ := copy16_okX (W := W) (a := l3O) (d := ljO) h15
    (in_left (wW (by simp only [l3O]; omega_arith))) (in_left (wW (by simp only [l3O]; omega_arith)))
    (wW (by simp only [ljO]; omega_arith)) (wW (by simp only [ljO]; omega_arith))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have h13₀ : s₀.gpr .r13 = BitVec.ofNat 64 k := by rw [B₀.gpr _ (by decide), h13]
  obtain ⟨s₁, run₁, r9₁, zf₁, g₁, m₁, rd₁, wr₁, x₁⟩ : ∃ s₁, runBlock isa
      [mvr .r9 .r13, addi .r9 1, .alu .test .r9 (.imm 1)] s₀ = some s₁ ∧
      s₁.gpr .r9 = BitVec.ofNat 64 (k + 1) ∧ s₁.zf = some (decide ((k + 1) % 2 = 0)) ∧
      (∀ r, r ≠ .r9 → s₁.gpr r = s₀.gpr r) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.xmm = s₀.xmm := by
    have e : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := BitVec.ofNat_add_ofNat k 1
    refine ⟨_, by orun [h13₀], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, e]
    · simp only [zf_arithFlags, zf_setFlags, gpr_setReg, gpr_arithFlags, ite_true, e]
      simpa using congrArg some (and1 _ hk)
    · intro r hr
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, ite_false]
    all_goals simp only [mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      xmm_setReg, xmm_arithFlags, mem_setFlags, rd_setFlags, wr_setFlags, xmm_setFlags]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hlj₁ : blockAtMem s₁.mem (W + BitVec.ofNat 64 ljO) = lAt l 3 := by rw [m₁, B₀.val, hL3]
  have step : WP isa (.ite .ne (.block [])
      (.loop (.block (Impl.AesOcb.X86_64.dbl .r15 ljO .r15 ljO ++ [.shift .shr .r9 1, .alu .test .r9 (.imm 1)]))
        .e)) s₁ fun s₂ =>
      blockAtMem s₂.mem (W + BitVec.ofNat 64 ljO) = lAt l (3 + ntz (k + 1)) ∧
      Frame [⟨W + BitVec.ofNat 64 ljO, 16⟩] s₁.mem s₂.mem ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx, .r8, .r9] → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      s₂.xmm = s₁.xmm := by
    by_cases hev : (k + 1) % 2 = 0
    · refine WP.ite false (by simp [isa, eval, zf₁, hev]) (fun h => absurd h (by decide)) fun _ => ?_
      exact dblLoop_ok s₁ (by rw [g₁ _ (by decide), B₀.gpr _ (by decide), h15]) (by omega_arith) hk hev r9₁
        (by rw [wr₁, B₀.wr]; exact hW) hwn hw hlj₁
    · refine WP.ite true (by simp [isa, eval, zf₁, hev]) (fun _ => WP.block_nil ⟨by
        rw [hlj₁, Proof.Ocb.ntz_odd (by omega_arith)], Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩)
        (fun h => absurd h (by decide))
  refine WP.seq (WP.mono step fun s₂ ⟨lj₂, fr₂, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have h15₂ : s₂.gpr .r15 = W := by rw [g₂ _ (by decide), g₁ _ (by decide), B₀.gpr _ (by decide), h15]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁, B₀.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁, B₀.wr]
  have fr : Frame [⟨W + BitVec.ofNat 64 ljO, 16⟩] s.mem s₂.mem := by
    have := B₀.frame.trans (m₁ ▸ fr₂); exact this
  have l2₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 l2O) = lAt l 2 := by
    rw [← hL2]
    exact Proof.Ocb.blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by simp only [l2O, Impl.AesOcb.X86_64.ohO]; omega_arith) (by simp only [ljO]; omega_arith)
  have rLj : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 ljO) 8 := by
    rw [rd₂', wr₂']; exact in_left (wW (by simp only [ljO]; omega_arith))
  have rLj8 : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 (ljO + 8)) 8 := by
    rw [rd₂', wr₂']; exact in_left (wW (by simp only [ljO]; omega_arith))
  have rL2 : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 l2O) 8 := by
    rw [rd₂', wr₂']; exact in_left (wW (by simp only [l2O, Impl.AesOcb.X86_64.ohO]; omega_arith))
  have rL28 : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 (l2O + 8)) 8 := by
    rw [rd₂', wr₂']; exact in_left (wW (by simp only [l2O, Impl.AesOcb.X86_64.ohO]; omega_arith))
  have wC8 : InRegions s₂.wr (W + BitVec.ofNat 64 c8O) 16 := by
    rw [wr₂']; exact wW (by simp only [c8O, cO]; omega_arith)
  apply WP.of_runBlock
  refine ⟨_, by orun [stC, h15₂, rLj, rLj8, rL2, rL28, wC8, XOp.exec, State.setXmm, State.store128], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, fun x h1 h2 => ?_⟩
  · simp only [mem_setReg, mem_arithFlags, Proof.AesOcb.X86_64.blockAtMem_writeW, ite_true, reduceCtorEq,
      ite_false, gpr_setReg, gpr_arithFlags]
    rw [punpck_movq, ← append_xor_append, ← addr8 W ljO, ← addr8 W l2O, ← readW128_q, ← readW128_q, rv_xor,
      ← blockAtMem_eq, ← blockAtMem_eq, lj₂, l2₂, BitVec.xor_comm]
  · simp only [mem_setReg, mem_arithFlags]
    exact (fr.mono fun r hr => List.mem_cons.mpr (.inl (List.mem_singleton.mp hr))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, ite_false]
    rw [g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), g₁ r hr.2.2.2.2,
      B₀.gpr r (by simp [hr.1, hr.2.1])]
  · simp only [rd_setReg, rd_arithFlags]; exact rd₂'
  · simp only [wr_setReg, wr_arithFlags]; exact wr₂'
  · simp only [xmm_setReg, xmm_arithFlags, h1, h2, ite_false]
    rw [x₂, x₁, x₀]

/-- A 16-byte slot of `W` after a 16-byte write to another, or the same. -/
theorem readW_writeW_slot (m : Mem) (W : Addr) {d e : Nat} (v : BitVec 128)
    (h : d = e ∨ d + 16 ≤ e ∨ e + 16 ≤ d) (hd : d + 16 ≤ 2 ^ 64) (he : e + 16 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 d) v).readW (W + BitVec.ofNat 64 e) 128 =
      if d = e then v else m.readW (W + BitVec.ofNat 64 e) 128 := by
  rcases h with rfl | h
  · simp only [↓reduceIte]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)
  · simp only [show ¬ d = e by omega_arith, ↓reduceIte]
    exact Mem.readW_writeW_sep (Offset.sep W (h.symm.imp id id) he hd) (by decide)

/-- `lmore`: `L_1`, `L_2` and `L_3` from `L_0`. -/
theorem lmore_ok (s : State) {W : Addr} {wn : Nat} {l : Block} (h15 : s.gpr .r15 = W)
    (hW : Covers [⟨W, wn⟩] s.wr) (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64)
    (hL0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block lmore) s fun s' =>
      blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt l 0 ∧
      blockAtMem s'.mem (W + BitVec.ofNat 64 l1O) = lAt l 1 ∧
      blockAtMem s'.mem (W + BitVec.ofNat 64 l2O) = lAt l 2 ∧
      blockAtMem s'.mem (W + BitVec.ofNat 64 l3O) = lAt l 3 ∧
      Frame [⟨W + BitVec.ofNat 64 l1O, 16⟩, ⟨W + BitVec.ofNat 64 l2O, 16⟩, ⟨W + BitVec.ofNat 64 l3O, 16⟩]
        s.mem s'.mem ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx, .r8] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.xmm = s.xmm := by
  have wW : ∀ {d n : Nat}, d + n ≤ wn → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h => in_off hW h hw
  have ofs : l0O = 80 ∧ l1O = 96 ∧ l2O = 144 ∧ l3O = 320 := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨o0, o1, o2, o3⟩ := ofs
  unfold lmore
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, B₁, x₁⟩ := dbl_okX (W := W) (B := W) (b := .r15) (o := .r15) (a := l0O) (d := l1O) h15 h15
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (in_left (wW (by omega_arith))) (in_left (wW (by omega_arith))) (wW (by omega_arith)) (wW (by omega_arith))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have h15₁ : s₁.gpr .r15 = W := by rw [B₁.gpr _ (by decide), h15]
  obtain ⟨s₂, run₂, B₂, x₂⟩ := dbl_okX (W := W) (B := W) (b := .r15) (o := .r15) (a := l1O) (d := l2O) h15₁ h15₁
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [B₁.rd, B₁.wr]; exact in_left (wW (by omega_arith))) (by rw [B₁.rd, B₁.wr]; exact in_left (wW (by omega_arith)))
    (by rw [B₁.wr]; exact wW (by omega_arith)) (by rw [B₁.wr]; exact wW (by omega_arith))
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have h15₂ : s₂.gpr .r15 = W := by rw [B₂.gpr _ (by decide), h15₁]
  obtain ⟨s₃, run₃, B₃, x₃⟩ := dbl_okX (W := W) (B := W) (b := .r15) (o := .r15) (a := l2O) (d := l3O) h15₂ h15₂
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (wW (by omega_arith)))
    (by rw [B₂.rd, B₂.wr, B₁.rd, B₁.wr]; exact in_left (wW (by omega_arith)))
    (by rw [B₂.wr, B₁.wr]; exact wW (by omega_arith)) (by rw [B₂.wr, B₁.wr]; exact wW (by omega_arith))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : ∀ {m m' : Mem} {d e : Nat}, Frame [⟨W + BitVec.ofNat 64 d, 16⟩] m m' → (d + 16 ≤ e ∨ e + 16 ≤ d) →
      e + 16 ≤ wn → d + 16 ≤ wn → blockAtMem m' (W + BitVec.ofNat 64 e) = blockAtMem m (W + BitVec.ofNat 64 e) :=
    fun hf h he hd => Proof.Ocb.blockAtMem_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (h.symm.imp id id) (by omega_arith) (by omega_arith)
  have v1 : blockAtMem s₁.mem (W + BitVec.ofNat 64 l1O) = lAt l 1 := by rw [B₁.val, hL0]; rfl
  have v2 : blockAtMem s₂.mem (W + BitVec.ofNat 64 l2O) = lAt l 2 := by rw [B₂.val, v1]; rfl
  have v3 : blockAtMem s₃.mem (W + BitVec.ofNat 64 l3O) = lAt l 3 := by rw [B₃.val, v2]; rfl
  refine ⟨?_, ?_, ?_, v3, ?_, fun r hr => ?_, by rw [B₃.rd, B₂.rd, B₁.rd], by rw [B₃.wr, B₂.wr, B₁.wr],
    by rw [x₃, x₂, x₁]⟩
  · rw [keep B₃.frame (by omega_arith) (by omega_arith) (by omega_arith),
      keep B₂.frame (by omega_arith) (by omega_arith) (by omega_arith),
      keep B₁.frame (by omega_arith) (by omega_arith) (by omega_arith), hL0]
  · rw [keep B₃.frame (by omega_arith) (by omega_arith) (by omega_arith),
      keep B₂.frame (by omega_arith) (by omega_arith) (by omega_arith), v1]
  · rw [keep B₃.frame (by omega_arith) (by omega_arith) (by omega_arith), v2]
  · exact ((B₁.frame.mono fun r hr => by simp at hr ⊢; simp [hr]).trans
      (B₂.frame.mono fun r hr => by simp at hr ⊢; simp [hr])).trans
      (B₃.frame.mono fun r hr => by simp at hr ⊢; simp [hr])
  · rw [B₃.gpr r hr, B₂.gpr r hr, B₁.gpr r hr]

/-- `C[t]`'s slot, for `t` from 1 to 8. -/
abbrev cSlot (t : Nat) : Nat := cO + 16 * (t - 1)

/-- `ctab`: `C[1]` … `C[7]` from `L_0`, `L_1` and `L_2`. -/
theorem ctab_ok (s : State) {W : Addr} {wn : Nat} {l : Block} (h15 : s.gpr .r15 = W)
    (hW : Covers [⟨W, wn⟩] s.wr) (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64)
    (hL0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hL1 : blockAtMem s.mem (W + BitVec.ofNat 64 l1O) = lAt l 1)
    (hL2 : blockAtMem s.mem (W + BitVec.ofNat 64 l2O) = lAt l 2) :
    WP isa (.block ctab) s fun s' =>
      (∀ t, 1 ≤ t → t ≤ 7 → blockAtMem s'.mem (W + BitVec.ofNat 64 (cSlot t)) = cAt l t) ∧
      Frame [⟨W + BitVec.ofNat 64 cO, 112⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ x, x ≠ .xmm11 → x ≠ .xmm12 → x ≠ .xmm13 → x ≠ .xmm14 → s'.xmm x = s.xmm x) := by
  have wW : ∀ {d n : Nat}, d + n ≤ wn → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h => in_off hW h hw
  have o0 : l0O = 80 := rfl
  have o1 : l1O = 96 := rfl
  have o2 : l2O = 144 := rfl
  have oc : cO = 384 := rfl
  unfold ctab
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldx_ok .xmm12 .xmm11 l0O s h15 (by decide) (in_left (wW (by omega_arith)))
    (in_left (wW (by omega_arith)))) fun s₁ ⟨v₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide), h15]
  refine WP.mono (ldx_ok .xmm13 .xmm11 l1O s₁ h15₁ (by decide)
    (by rw [rd₁, wr₁]; exact in_left (wW (by omega_arith))) (by rw [rd₁, wr₁]; exact in_left (wW (by omega_arith))))
    fun s₂ ⟨v₂, g₂, m₂, rd₂, wr₂, x₂⟩ => ?_
  have h15₂ : s₂.gpr .r15 = W := by rw [g₂ _ (by decide) (by decide), h15₁]
  refine WP.mono (ldx_ok .xmm14 .xmm11 l2O s₂ h15₂ (by decide)
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact in_left (wW (by omega_arith)))
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact in_left (wW (by omega_arith)))) fun s₃ ⟨v₃, g₃, m₃, rd₃, wr₃, x₃⟩ => ?_
  have h15₃ : s₃.gpr .r15 = W := by rw [g₃ _ (by decide) (by decide), h15₂]
  -- The values loaded: the raw blocks of `L_0`, `L_1`, `L_2`.
  have a0 : s₃.xmm .xmm12 = s.mem.readW (W + BitVec.ofNat 64 l0O) 128 := by
    rw [x₃ _ (by decide) (by decide), x₂ _ (by decide) (by decide), v₁]
  have a1 : s₃.xmm .xmm13 = s.mem.readW (W + BitVec.ofNat 64 l1O) 128 := by
    rw [x₃ _ (by decide) (by decide), v₂, m₁]
  have a2 : s₃.xmm .xmm14 = s.mem.readW (W + BitVec.ofNat 64 l2O) 128 := by rw [v₃, m₂, m₁]
  have wC : ∀ t, t < 7 → InRegions s₃.wr (W + BitVec.ofNat 64 (cO + 16 * t)) 16 := fun t ht => by
    rw [wr₃, wr₂, wr₁]; exact wW (by omega_arith)
  have w0 := wC 0 (by decide)
  have w1 := wC 1 (by decide)
  have w2 := wC 2 (by decide)
  have w3 := wC 3 (by decide)
  have w4 := wC 4 (by decide)
  have w5 := wC 5 (by decide)
  have w6 := wC 6 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by orun [stC, h15₃, w0, w1, w2, w3, w4, w5, w6, XOp.exec, State.setXmm, State.store128], ?_⟩
  refine ⟨fun t ht1 ht7 => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, State.setMem]
    have hx : ∀ a b : BitVec 128, XBinOp.eval .pxor a b = a ^^^ b := fun _ _ => rfl
    have hm : ∀ a b : BitVec 128, XBinOp.eval .movdqa a b = b := fun _ _ => rfl
    rw [blockAtMem_eq]
    rcases (by omega_arith : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp (disch := decide) only [cSlot, readW_writeW_slot, hx, hm]
      simp only [cO, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte]
      simp only [a0, a1, a2, rv_xor, ← blockAtMem_eq, hL0, hL1, hL2, cAt, BitVec.xor_assoc]
  · simp only [mem_setReg, mem_arithFlags, State.setMem]
    rw [m₃, m₂, m₁]
    have c : ∀ k, k < 7 → (⟨W + BitVec.ofNat 64 cO, 112⟩ : Region).Contains (W + BitVec.ofNat 64 (cO + 16 * k))
        (128 / 8) := fun k hk => Offset.contains W (by omega_arith) (by omega_arith) (by omega_arith)
    have e := List.mem_singleton_self (⟨W + BitVec.ofNat 64 cO, 112⟩ : Region)
    exact ((((((((Frame.refl _ _).writeW e _ (c 0 (by decide))).writeW e _ (c 2 (by decide))).writeW e _
      (c 6 (by decide))).writeW e _ (c 1 (by decide))).writeW e _ (c 4 (by decide))).writeW e _
      (c 3 (by decide))).writeW e _ (c 5 (by decide)))
  · intro r h1 h2
    simp only [gpr_setReg, gpr_arithFlags, State.setXmm, State.setMem]
    rw [g₃ r h1 h2, g₂ r h1 h2, g₁ r h1 h2]
  · simp only [rd_setReg, rd_arithFlags, State.setXmm, State.setMem]; rw [rd₃, rd₂, rd₁]
  · simp only [wr_setReg, wr_arithFlags, State.setXmm, State.setMem]; rw [wr₃, wr₂, wr₁]
  · intro x h1 h2 h3 h4
    simp only [xmm_setReg, xmm_arithFlags, State.setXmm, State.setMem, h1, ite_false]
    rw [x₃ x h4 h1, x₂ x h3 h1, x₁ x h2 h1]

end VG.Proof.AesOcb.X86_64.AesNi
