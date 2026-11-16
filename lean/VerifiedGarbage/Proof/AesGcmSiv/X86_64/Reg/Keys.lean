module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Entry
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
public import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV in registers on x86-64: the keys

Untrusted: everything here is checked by Lean. `derive` leaves the halves of
`derive_keys` at `W + 16` (`derive_ok`), two blocks at a time in `xmm0` and
`xmm1` (`Proof.Aes.X86_64.AesNi.aes_ok`); `expand` leaves the encryption key's
schedule at `W + 248` (`expand_ok`), by `AesNi.expandKey` inline.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO ekO skO roundsO nonceO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Impl.Aes.X86_64.AesNi (aes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc punpck_movq writeW128_app shr1)
open VG.Proof.AesGcm.X86_64 (in_off ofNat_add_ofNat)

/-- What `derive` writes: the keys at `W + 16`. -/
abbrev derR (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 48⟩]

/-- After `i` blocks of `derive`: their halves at `W + 16`, and `aes`'s
arguments for the key-generating key. -/
structure DInv (K W SP : Addr) (σ : State) (R : Nat) (N : Addr) (i : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  rbx : t.gpr .rbx = BitVec.ofNat 64 i
  rdx : t.gpr .rdx = N
  rdi : t.gpr .rdi = K
  rsi : t.gpr .rsi = BitVec.ofNat 64 R
  r10 : t.gpr .r10 = K + BitVec.ofNat 64 (16 * R)
  frame : Frame (derR W) σ.mem t.mem
  out : bytesAt t.mem (W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem K R) (bytesAt σ.mem N 12) i

/-- The start of `derive`. -/
theorem derInit_ok {K W SP : Addr} {σ : State} (E : Env K W SP σ) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n σ.mem) :
    WP isa (.block (aesArgs [.mov .rdi (.reg .r13)] ++
      ([.mov .rdx (.mem (at_ .r15 nonceO)), .mov32 .rbx (imm 0)] : List Instr))) σ (DInv K W SP σ R N 0) := by
  have h15 := E.r15
  have h13 := E.r13
  have rR := S.rounds
  have rN := S.nonce
  have rr := E.perm.wR (show 200 + 8 ≤ 488 by decide)
  have rn := E.perm.wR (show 208 + 8 ≤ 488 by decide)
  obtain ⟨t, run, hm, bx, dx, di, si, r10, hg, hrd, hwr⟩ : ∃ t : State, runBlock isa
      (aesArgs [.mov .rdi (.reg .r13)] ++ [.mov .rdx (.mem (at_ .r15 nonceO)), .mov32 .rbx (imm 0)]) σ = some t ∧
      t.mem = σ.mem ∧ t.gpr .rbx = BitVec.ofNat 64 0 ∧ t.gpr .rdx = N ∧ t.gpr .rdi = K ∧
      t.gpr .rsi = BitVec.ofNat 64 R ∧ t.gpr .r10 = K + BitVec.ofNat 64 (16 * R) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t.gpr r = σ.gpr r) ∧ t.rd = σ.rd ∧ t.wr = σ.wr := by
    refine ⟨_, by srun [aesArgs, lastKey, h15, h13, rR, rN, rr, rn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, rN]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h13]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, rR]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, rR, h13, execShift]
      rw [BitVec.add_comm]; congr 1; rcases hR with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨t, run, E.keep hg hrd hwr, hrd, hwr, bx, dx, di, si, r10,
    by rw [hm]; exact Frame.refl _ _, by simp [GcmSiv.halves, bytesAt]⟩

/-! ## Blocks in registers -/

open VG.Proof.Aes.X86_64.AesNi (st getD_st getD_ofFn st_ext st_toList)
open VG.Proof.Cmac (le8 le4)

/-- The state of a register made of two quadwords: their bytes, the low
one's first. -/
theorem st_app (hi lo : BitVec 64) :
    st (hi ++ lo) = Vector.ofFn fun i : Fin 16 => (le8 lo ++ le8 hi).getD i.1 0 := by
  apply st_ext; intro i hi'
  rw [getD_st _ hi', getD_ofFn hi']
  rcases (by omega_arith : i < 8 ∨ 8 ≤ i) with h | h
  · rw [show (le8 lo ++ le8 hi).getD i 0 = lo.extractLsb' (8 * i) 8 by
      simp [le8, List.getD_eq_getElem?_getD, List.getElem?_append_left, h]]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and,
      show 8 * i + j < 64 by omega_arith, ↓reduceIte]
  · rw [show (le8 lo ++ le8 hi).getD i 0 = hi.extractLsb' (8 * (i - 8)) 8 by
      simp [le8, List.getD_eq_getElem?_getD, List.getElem?_append_right, h, show i - 8 < 8 by omega_arith]]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and,
      show ¬ 8 * i + j < 64 by omega_arith, ↓reduceIte]
    exact congrArg _ (by omega_arith)

/-- The first 8 bytes of a register's state: its low quadword's. -/
theorem take8_st (v : BitVec 128) : (st v).toList.take 8 = le8 (qword v 0) := by
  rw [st_toList, ← List.map_take, show (List.range 16).take 8 = List.range 8 from rfl, le8]
  refine List.map_congr_left fun i hi => ?_
  have hi8 : i < 8 := List.mem_range.mp hi
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byte, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add,
    show 8 * i + j < 64 by omega_arith]

/-- `punpcklqdq`: the low quadwords of both. -/
theorem punpck_lo (a b : BitVec 128) : XBinOp.eval .punpcklqdq a b = qword b 0 ++ qword a 0 := rfl

theorem or_one {i : Nat} (hi : i < 6) (hev : i % 2 = 0) (x : BitVec 64) :
    x ||| BitVec.ofNat 64 i ||| 1#64 = x ||| BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.or_assoc]; congr 1
  rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 4) with rfl | rfl | rfl <;> decide

/-- The blocks of a pair: `little_endian_uint32(i) ‖ nonce` and the next. -/
theorem derivePair_run {K W SP : Addr} {σ : State} {R : Nat} {N : Addr} {i : Nat} (hi : i < 6) (hev : i % 2 = 0)
    {t : State} (I : DInv K W SP σ R N i t) (hN : Buf K W SP σ N 12) :
    ∃ t₁ : State, runBlock isa derivePair t = some t₁ ∧
      t₁.xmm .xmm0 = t.mem.readW (N + BitVec.ofNat 64 4) 64 ++
        ((t.mem.readW N 32).setWidth 64 <<< 32 ||| BitVec.ofNat 64 i) ∧
      t₁.xmm .xmm1 = t.mem.readW (N + BitVec.ofNat 64 4) 64 ++
        ((t.mem.readW N 32).setWidth 64 <<< 32 ||| BitVec.ofNat 64 (i + 1)) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      ∀ r, r ≠ .rax → t₁.gpr r = t.gpr r := by
  have hN' := hN.of_eq I.rd I.wr
  have n₀ := in_off (d := 0) (n := 4) hN'.rd (by decide) (by decide)
  have n₄ := in_off (d := 4) (n := 8) hN'.rd (by decide) (by decide)
  simp only [BitVec.add_zero] at n₀
  have hdx := I.rdx
  refine ⟨_, by xrun [derivePair, hdx, n₀, n₄, I.rbx], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      punpck_movq, or_one hi hev, I.rbx, ne_eq, not_false_eq_true]
  · simp (config := {decide := true}) only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      punpck_movq, or_one hi hev, I.rbx, ne_eq, not_false_eq_true]
  · rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesGcmSivReg.X86_64
