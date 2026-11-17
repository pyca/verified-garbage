module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Entry
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
public import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
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

-- separate module: the keys, apart from POLYVAL

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO ekO skO roundsO nonceO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Impl.Aes.X86_64.AesNi (aes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc punpck_movq writeW128_app shr1 eval_ne)
open VG.Proof.AesGcm.X86_64 (in_off ofNat_add_ofNat bytesAt_frame)

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
    WP isa (.block (aesArgs ([.mov .rdi (.reg .r13)] : List Instr) ++
      ([.mov .rdx (.mem (at_ .r15 nonceO)), .mov32 .rbx (imm 0)] : List Instr))) σ (DInv K W SP σ R N 0) := by
  have h15 := E.r15
  have h13 := E.r13
  have rR := S.rounds
  have rN := S.nonce
  have rr := E.perm.wR (show 200 + 8 ≤ 744 by decide)
  have rn := E.perm.wR (show 208 + 8 ≤ 744 by decide)
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
  · simp only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      punpck_movq, or_one hi hev, I.rbx, ne_eq, not_false_eq_true]
  · simp only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      punpck_movq, or_one hi hev, I.rbx, ne_eq, not_false_eq_true]
  · rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_true, ite_false, reduceCtorEq]

/-- The halves of a pair stored: 16 bytes at `W + 16 + 8 i`. -/
theorem deriveKeep_run {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {i : Nat}
    (hi : i + 2 ≤ R / 2 - 1) {t : State} (E : Env K W SP t) (hbx : t.gpr .rbx = BitVec.ofNat 64 i)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 R) :
    ∃ t' : State, runBlock isa deriveKeep t = some t' ∧
      t'.mem = (t.mem.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (qword (t.xmm .xmm0) 0)).writeW
        (W + BitVec.ofNat 64 (16 + 8 * i) + BitVec.ofNat 64 8) (qword (t.xmm .xmm1) 0) ∧
      t'.gpr .rbx = BitVec.ofNat 64 (i + 2) ∧ t'.zf = some (decide (i + 2 = R / 2 - 1)) ∧
      (∀ r ∈ [Reg.rdx, .rdi, .rsi, .r10, .r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hw := L.ww
  have h15 := E.r15
  have ww := E.perm.wW (d := 16 + 8 * i) (n := 16) (by omega_arith)
  have ea : BitVec.ofNat 64 i <<< 3 + W + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 (16 + 8 * i) := by
    have e8 : BitVec.ofNat 64 i <<< 3 = BitVec.ofNat 64 (8 * i) := by
      rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [e8, BitVec.add_comm (BitVec.ofNat 64 (8 * i)) W, add_ofNat_assoc, Nat.add_comm]
  refine ⟨_, by xrun [deriveKeep, h15, hbx, hsi, ww, ea, punpck_lo], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags, mem_setXmm, gpr_setXmm,
      gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, xmm_setXmm_self,
      xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags, punpck_lo, writeW128_app, h15, hbx, ea,
      ne_eq, not_false_eq_true]
    done
  · simp only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
      ofNat_add_ofNat]
  · simp only [zf_arithFlags, zf_setXmm, zf_setReg, gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
      ite_false, reduceCtorEq, hbx, hsi, ofNat_add_ofNat]
    rw [shr1 R (by omega_arith), Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith),
      Proof.AesGcm.X86_64.sub_beq (by omega_arith) (by omega_arith)]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setXmm, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

open VG.Proof.Aes.X86_64.AesNi (aes_ok Keys XFrame)

/-- `aes`'s keys for the key-generating key. -/
theorem keysK {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    (hdi : t.gpr .rdi = K) : Keys R (bytesAt t.mem K (16 * (R + 1))) t := by
  refine ⟨by rw [hdi], by omega_arith, fun j hj => ?_⟩
  rw [hdi, Proof.Aes.X86_64.AesNi.ofInt_natCast]
  exact in_off E.perm.k (by omega_arith) (by decide)

/-- The first 8 bytes of the cipher of `little_endian_uint32(i) ‖ nonce`:
the low quadword of the register that encrypting the block left. -/
theorem half_eq {m : Mem} {K N : Addr} {R i : Nat} (hi : i < 2 ^ 32) (v' : BitVec 128)
    (h : st v' = Spec.Aes.cipher R (bytesAt m K (16 * (R + 1)))
      (st (m.readW (N + BitVec.ofNat 64 4) 64 ++ ((m.readW N 32).setWidth 64 <<< 32 ||| BitVec.ofNat 64 i)))) :
    le8 (qword v' 0) = (Spec.GcmSiv.ctxCiph m K R (Spec.GcmSiv.le32 i ++ bytesAt m N 12)).take 8 := by
  have hi32 : BitVec.ofNat 64 i = ((BitVec.ofNat 64 i).setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_arith)]
  have eb : le8 ((m.readW N 32).setWidth 64 <<< 32 ||| BitVec.ofNat 64 i) ++ le8 (m.readW (N + BitVec.ofNat 64 4) 64) =
      Spec.GcmSiv.le32 i ++ bytesAt m N 12 := by
    rw [hi32, Proof.AesGcmSiv.X86_64.le8_join, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le8_readW,
      show (12 : Nat) = 4 + 8 from rfl, Proof.Cmac.bytesAt_add, List.append_assoc]
  rw [← take8_st, h, st_app, eb]
  rfl

/-- A pair of `derive`: two more halves. -/
theorem derStep_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {σ : State} {N : Addr}
    (hN : Buf K W SP σ N 12) {i : Nat} (hi : i + 2 ≤ R / 2 - 1) (hev : i % 2 = 0) {t : State}
    (I : DInv K W SP σ R N i t) :
    WP isa (.seq (.block derivePair) (.seq (aes [.xmm0, .xmm1]) (.block deriveKeep))) t fun t' =>
      DInv K W SP σ R N (i + 2) t' ∧ t'.zf = some (decide (i + 2 = R / 2 - 1)) := by
  obtain ⟨t₁, run₁, x0, x1, m₁, rd₁, wr₁, g₁⟩ := derivePair_run (by omega_arith) hev I hN
  have E₁ : Env K W SP t₁ := I.env.keep (fun r hr => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have K₁ := keysK hR E₁ ((g₁ _ (by decide)).trans I.rdi)
  refine WP.mono (aes_ok [.xmm0, .xmm1] (by decide) (by decide) (by omega_arith) t₁ K₁
    ((g₁ _ (by decide)).trans I.rsi) (by rw [g₁ _ (by decide), g₁ _ (by decide), I.r10, I.rdi])) fun t₂ ⟨hc, hf⟩ => ?_
  have E₂ : Env K W SP t₂ := E₁.keep (fun r _ => by rw [hf.gpr]) hf.rd hf.wr
  obtain ⟨t₃, run₃, m₃, bx₃, zf₃, g₃, rd₃, wr₃⟩ := deriveKeep_run L hR hi E₂
    (by rw [hf.gpr, g₁ _ (by decide), I.rbx]) (by rw [hf.gpr, g₁ _ (by decide), I.rsi])
  refine WP.of_runBlock ⟨t₃, run₃, ⟨E₂.keep (fun r hr => g₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) rd₃ wr₃,
    by rw [rd₃, hf.rd, rd₁, I.rd], by rw [wr₃, hf.wr, wr₁, I.wr], bx₃,
    by rw [g₃ _ (by simp), hf.gpr, g₁ _ (by decide), I.rdx],
    by rw [g₃ _ (by simp), hf.gpr, g₁ _ (by decide), I.rdi],
    by rw [g₃ _ (by simp), hf.gpr, g₁ _ (by decide), I.rsi],
    by rw [g₃ _ (by simp), hf.gpr, g₁ _ (by decide), I.r10], ?_, ?_⟩, zf₃⟩
  · rw [m₃, hf.mem, m₁]
    exact I.frame.trans ((Proof.Cmac.frame_store2 _ _ _).sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub W (by omega_arith) (by omega_arith)⟩)
  · have hw := L.ww
    have hRb : 16 * (R + 1) ≤ 240 := by omega_arith
    have eK : Spec.GcmSiv.ctxCiph t.mem K R = Spec.GcmSiv.ctxCiph σ.mem K R :=
      ctxCiph_frame I.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have eN : bytesAt t.mem N 12 = bytesAt σ.mem N 12 :=
      bytesAt_frame I.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hN.w.sub_right (Lay.wSub (by decide))) (by decide)
    have h0 := hc .xmm0 (by simp)
    have h1 := hc .xmm1 (by simp)
    rw [x0, m₁] at h0
    rw [x1, m₁] at h1
    have a0 := half_eq (by omega_arith) _ h0
    have a1 := half_eq (by omega_arith) _ h1
    rw [eK, eN] at a0 a1
    have fs := Proof.Cmac.frame_store2 (m := t₂.mem) (W + BitVec.ofNat 64 (16 + 8 * i)) (qword (t₂.xmm .xmm0) 0)
      (qword (t₂.xmm .xmm1) 0)
    rw [show 8 * (i + 2) = 8 * i + 16 by omega_arith, Proof.Cmac.bytesAt_add, add_ofNat_assoc, m₃,
      Proof.Cmac.bytesAt_store2, bytesAt_frame fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith),
      hf.mem, m₁, I.out, GcmSiv.halves_succ, GcmSiv.halves_succ, a0, a1, List.append_assoc]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {σ : State} (E : Env K W SP σ) (S : Slots W R N A D al n σ.mem) (hN : Buf K W SP σ N 12) :
    WP isa derive σ (DInv K W SP σ R N (R / 2 - 1)) := by
  refine WP.seq (WP.mono (derInit_ok E hR S) fun t₀ I₀ => ?_)
  refine WP.loop (M := isa) (c := .ne) (fun m t => ∃ j, m = (R / 2 - 1) - j ∧ j < R / 2 - 1 ∧ j % 2 = 0 ∧
    DInv K W SP σ R N j t) ?_ ((R / 2 - 1) - 0) t₀ ⟨0, rfl, by omega_arith, rfl, I₀⟩
  rintro m t ⟨j, rfl, hj, hj2, I⟩
  have hev : (R / 2 - 1) % 2 = 0 := by rcases hR with h | h <;> subst h <;> decide
  refine WP.mono (derStep_ok L hR hN (by omega_arith) hj2 I) fun t' ⟨I', hz⟩ => ?_
  by_cases he : j + 2 = R / 2 - 1
  · left
    refine ⟨(eval_ne hz).trans (by simp [he]), ?_⟩
    rw [he] at I'
    exact I'
  · right; exact ⟨(eval_ne hz).trans (by simp [he]), (R / 2 - 1) - (j + 2), by omega_arith, j + 2, rfl, by omega_arith,
      by omega_arith, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {K W SP : Addr} {σ : State} {R : Nat} (hR : R = 10 ∨ R = 14) {N : Addr} {t : State}
    (I : DInv K W SP σ R N (R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt σ.mem N 12) =
      (bytesAt t.mem (W + BitVec.ofNat 64 16) 16, bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R)) := by
  have hk : Spec.GcmSiv.keyLen R / 8 + 2 = R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega_arith
  have hl : 8 * (R / 2 - 1) = 16 + Spec.GcmSiv.keyLen R := by unfold Spec.GcmSiv.keyLen; omega_arith
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, add_ofNat_assoc] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem K R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

/-! ## The schedule -/

/-- What `expand` leaves: the schedule of the encryption key at `W + 248`. -/
structure ExpPost (K W SP : Addr) (R : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  frame : Frame [⟨W + BitVec.ofNat 64 248, 240⟩] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (W + BitVec.ofNat 64 248) R =
    Spec.GcmSiv.aes (bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R))

theorem expand_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14)
    (hret : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 744⟩) {N A D : Addr} {al n : Nat} {t : State} (E : Env K W SP t)
    (S : Slots W R N A D al n t.mem) : WP isa expand t (ExpPost K W SP R t) := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 744 by decide)
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega_arith
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, hg₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
        .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO) t = some t₁ ∧
      t₁.mem = t.mem ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 32 ∧
      t₁.gpr .rsi = BitVec.ofNat 64 (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 248 ∧
      (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rR, rr], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), ofNat_add_ofNat, ofNat_add_ofNat]
      congr 1; unfold Spec.GcmSiv.keyLen; omega_arith
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have hK := Proof.AesGcm.X86_64.toNat_ofNat_of_lt (n := Spec.GcmSiv.keyLen R) (by omega_arith)
  refine WP.inline (k := Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64) Proof.Aes.X86_64.AesNi.Key.expandKey3_correct
    (rd := [⟨W + BitVec.ofNat 64 32, Spec.GcmSiv.keyLen R⟩]) (wr := [⟨W + BitVec.ofNat 64 248, 240⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, rdi, rsi, rdx, hK, E₁.rsp]
    exact ⟨trivial, trivial, hret.sub_right (Lay.wSub (by decide)), by omega_arith⟩
  · rw [hrd₁, hwr₁]
    intro a m ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Proof.AesGcm.X86_64.covers_left (E.perm.wC (d := 32) (n := Spec.GcmSiv.keyLen R) (by omega_arith)) a m
        ⟨_, List.mem_singleton_self _, hc⟩
    · exact Proof.AesGcm.X86_64.covers_left (E.perm.wC (d := 248) (n := 240) (by decide)) a m
        ⟨_, List.mem_singleton_self _, hc⟩
  · rw [hwr₁]; exact E.perm.wC (by decide)
  · intro t₂ hrd₂ hwr₂ habi hfr hgp hpost
    have sv : ∀ r ∈ calleeSaved, t₂.gpr r = t₁.gpr r := habi.1
    refine ⟨E₁.of_saved sv hrd₂ hwr₂, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁],
      fun r hr => by rw [sv r hr, hg₁ r hr], by rw [← hm₁]; exact hfr, ?_⟩
    have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen R / 4) = R := by
      unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; omega_arith
    have out := hpost
    simp only [Proof.Aes.X86_64.AesNi.Key.expandKey3X86_64, Proof.Aes.X86_64.AesNi.expandKeyX86_64,
      State.withRegions_gpr, State.withRegions_mem, rdi, rsi, rdx, hK, hr] at out
    rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

end VG.Proof.AesGcmSivReg.X86_64
