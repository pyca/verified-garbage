module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Crypt
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Siv.Spec

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_open` with the interleaved loop

Untrusted: everything here is checked by Lean. After the keys, `open`
deciphers the data and computes the tag input: for less than 256 bytes of
data, as `Impl.AesGcmSiv.X86_64.«open»` does, counter mode (`crypt`) and then
POLYVAL (`polyval`) (`classic_ok`); from 256 bytes on, `stitched`
(`stitched_ok`): POLYVAL of the additional data, the data's 256-byte groups
deciphered and absorbed by the interleaved loop (`Stitch.dec_ok`), the rest
deciphered as `crypt` does from there (`blocksFrom_ok`, `cryptTail_ok`) and
absorbed, then the lengths and the tag input. Both leave `MidPost`, from
which the rest of `open` is proven as before.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl toNat_ofNat_of_lt)

/-- What deciphering the data and computing the tag input leave, from `t`. -/
structure MidPost (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR W SP D n ++ polyR W SP) t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n)
  out : GcmSiv.Polyval.PolyvalEq → bytesAt t'.mem (W + BitVec.ofNat 64 96) 16 =
    Spec.GcmSiv.tagInput (bytesAt t.mem (W + BitVec.ofNat 64 16) 16) (bytesAt t.mem N 12) (bytesAt t'.mem D n)
      (bytesAt t.mem A al)

/-- `⟨W + d, k⟩` below the counter block misses what counter mode writes. -/
theorem lowW_cryR {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    {d k : Nat} (h₂ : d + k ≤ 96) : ∀ q ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
  fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm
    · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm

/-- A buffer apart from `W`, the stack and the data misses what counter mode writes. -/
theorem buf_cryR {K W SP D : Addr} {n : Nat} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) : ∀ q ∈ cryR W SP D n, (⟨P, len⟩ : Region).Disjoint q := fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hP.w.sub_right (Lay.wSub (by decide))
  · exact hP.w.sub_right (Lay.wSub (by decide))
  · exact hP.w.sub_right (Lay.wSub (by decide))
  · exact hP.stk.symm
  · exact hPD

/-- The data misses what POLYVAL writes. -/
theorem data_polyR {K W SP D : Addr} {n : Nat} {s : State} (hD : Buf K W SP s D n) :
    ∀ q ∈ polyR W SP, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hD.w.sub_right (Lay.wSub (by decide))
  · exact hD.w.sub_right (Lay.wSub (by decide))
  · exact hD.w.sub_right (Lay.wSub (by decide))
  · exact hD.w.sub_right (Lay.wSub (by decide))
  · exact hD.w.sub_right (Lay.wSub (by decide))
  · exact hD.stk.symm

/-- Counter mode, then POLYVAL. -/
theorem classic_ok (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP)
    {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n) (hN : Buf K W SP t N 12)
    (hDw : Covers [⟨D, n⟩] t.wr) (hND : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩) (hAD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) :
    WP isa (.seq (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (polyval v.callees wide)) t
      (MidPost K W SP R N A D al n t) := by
  refine WP.seq (WP.mono (crypt_ok v eb wide L hR E S hD hDw) fun s₃ Cr => ?_)
  have S₃ := S.of_frame Cr.frame (slots_cryR L hD)
  have hA₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16 = bytesAt t.mem (W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (lowW_cryR L hD.w (by decide)) (by decide)
  have hG₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (W + BitVec.ofNat 64 16) 16)) := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (lowW_cryR L hD.w (by decide)), hG, hA₃]
  have hY₃ : Spec.Gcm.blockAt s₃.mem (W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (lowW_cryR L hD.w (by decide)), hY]
  refine WP.mono (polyval_ok v wide L Cr.env S₃ (hA.of_eq Cr.rd Cr.wr) (hD.of_eq Cr.rd Cr.wr) (hN.of_eq Cr.rd Cr.wr)
    hG₃ hY₃) fun s₄ Po => ?_
  have d₄ : bytesAt s₄.mem D n = bytesAt s₃.mem D n :=
    Proof.AesGcm.X86_64.bytesAt_frame Po.frame (data_polyR hD) (Nat.le_of_lt hD.lt)
  refine ⟨Po.env, Po.rd.trans Cr.rd, Po.wr.trans Cr.wr,
    (Cr.frame.mono fun r hr => List.mem_append_left _ hr).trans (Po.frame.mono fun r hr => List.mem_append_right _ hr),
    by rw [d₄]; exact Cr.data, fun hpv => ?_⟩
  rw [Po.out hpv, hA₃, Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (buf_cryR hN hND) (by decide),
    Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (buf_cryR hA hAD) (Nat.le_of_lt hA.lt), d₄]

/-! ## The straight blocks of `stitched` -/

theorem shr8 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 8 = BitVec.ofNat 64 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

theorem shl8 (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 (n / 256) <<< 8 = BitVec.ofNat 64 (256 * (n / 256)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n / 256) (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem and255 (x : BitVec 64) : x &&& (BitVec.ofNat 32 255).signExtend 64 = BitVec.ofNat 64 (x.toNat % 256) := by
  rw [Proof.AesGcm.X86_64.imm_eq (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 255) (by decide),
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem dbl16 (n : Nat) :
    BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256) + (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256)) +
      (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256) + (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256))) +
      (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256) + (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256)) +
      (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256) + (BitVec.ofNat 64 (n / 256) + BitVec.ofNat 64 (n / 256)))) =
      BitVec.ofNat 64 (16 * (n / 256)) := by
  simp only [Proof.AesGcm.X86_64.ofNat_add_ofNat]
  congr 1; omega_arith

/-- The start of `stitched`: the counter block from the tag, and the
additional data's address and length. -/
theorem sHead_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) :
    ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 tagO)), .store (at_ .r15 cmO) .rax, .mov .rax (.mem (at_ .r15 (tagO + 8))),
        .movImm64 .rcx 0x8000000000000000, .alu .or .rax (.reg .rcx), .store (at_ .r15 (cmO + 8)) .rax,
        .mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] t = some t₁ ∧
      t₁.mem = (t.mem.writeW (W + BitVec.ofNat 64 96) (t.mem.readW W 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8)
        (t.mem.readW (W + BitVec.ofNat 64 8) 64 ||| 0x8000000000000000#64) ∧
      t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rT₀ : InRegions (t.rd ++ t.wr) W 8 := by simpa using E.perm.wR (show 0 + 8 ≤ 3816 by decide)
  have rT₈ := E.perm.wR (show 8 + 8 ≤ 3816 by decide)
  have rA := E.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have w₀ := E.perm.wW (show 96 + 8 ≤ 3816 by decide)
  have w₈ := E.perm.wW (show 104 + 8 ≤ 3816 by decide)
  have sA := S.aad
  have sL := S.alen
  refine ⟨_, by srun [h15, rT₀, rT₈, rA, rL, w₀, w₈], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, add_ofNat_assoc]; rfl
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact sA
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    exact sL
  · intro r h₁ h₂ h₃ h₄; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- The loop's arguments, from `W`. -/
abbrev sArgs : List Instr :=
  ptr .rdi .r15 skO ++ ([.mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r15 cmO ++
    ptr .rcx .r15 yO ++ ptr .r8 .r15 hO ++ ptr .r11 .r15 scrO ++
    ([.mov .r12 (.mem (at_ .r15 dataO)), .mov .r9 (.mem (at_ .r15 lenO)), .shift .shr .r9 8,
      .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9), .alu .add .r9 (.reg .r9)] :
      List Instr)

theorem sArgs_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa sArgs t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .rdx = W + BitVec.ofNat 64 96 ∧ t₁.gpr .rcx = W + BitVec.ofNat 64 80 ∧
      t₁.gpr .r8 = W + BitVec.ofNat 64 64 ∧ t₁.gpr .r11 = W + BitVec.ofNat 64 1768 ∧ t₁.gpr .r12 = D ∧
      t₁.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256)) ∧
      (∀ r ∈ calleeSaved, r ≠ .r12 → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rR := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sR := S.rounds
  have sD := S.data
  have sL := S.len
  have i248 := Proof.AesGcm.X86_64.imm_eq (show 248 < 2 ^ 31 by decide)
  have i96 := Proof.AesGcm.X86_64.imm_eq (show 96 < 2 ^ 31 by decide)
  have i80 := Proof.AesGcm.X86_64.imm_eq (show 80 < 2 ^ 31 by decide)
  have i64 := Proof.AesGcm.X86_64.imm_eq (show 64 < 2 ^ 31 by decide)
  have i1768 := Proof.AesGcm.X86_64.imm_eq (show 1768 < 2 ^ 31 by decide)
  refine ⟨_, by srun [sArgs, ptr, h15, rR, rD, rL], by simp only [mem_setReg, mem_arithFlags, mem_setFlags],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp only [rd_setReg, rd_arithFlags, rd_setFlags],
    by simp only [wr_setReg, wr_arithFlags, wr_setFlags]⟩
  iterate 7 simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15, sR, sD,
    i248, i96, i80, i64, i1768]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL, shr8 _ hn]
    exact dbl16 n
  · intro r hr h₁; obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉⟩ := ne_of_calleeSaved hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, n₁, n₂, n₃, n₄, n₅, n₆, n₇, n₈, n₉, ite_false]

/-- The data after its 256-byte groups. -/
theorem rest_ok {K W SP : Addr} {R : Nat} {t : State} (E : Env K W SP t) {N A D : Addr}
    {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa Impl.AesGcmSiv.X86_64Stitch.rest t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .r12 = D + BitVec.ofNat 64 (256 * (n / 256)) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 256) ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rD := E.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sD := S.data
  have sL := S.len
  have hand := and255 (BitVec.ofNat 64 n)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by srun [Impl.AesGcmSiv.X86_64Stitch.rest, h15, rD, rL], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sD, sL, shr8 _ hn, shl8 _ hn]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, sL, hand]
  · intro r h₁ h₂ h₃; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, ite_false]
  all_goals rfl

/-! ## What `stitched` keeps, and the algebra -/

/-- Parts of `W` that neither counter mode nor POLYVAL writes. -/
theorem mid_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩)
    {d k : Nat} (h : d + k ≤ 80 ∨ (144 ≤ d ∧ d + k ≤ 488)) :
    ∀ q ∈ cryR W SP D n ++ polyR W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q := fun q hq => by
  have hk : d + k ≤ 488 := by omega_arith
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact (L.stk_w' (by omega_arith)).symm
  · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact (L.stk_w' (by omega_arith)).symm

/-- A buffer apart from `W`, the stack and the data misses both. -/
theorem buf_mid {K W SP D : Addr} {n : Nat} {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) : ∀ q ∈ cryR W SP D n ++ polyR W SP, (⟨P, len⟩ : Region).Disjoint q :=
  fun q hq => by
    rcases List.mem_append.mp hq with hq | hq
    · exact buf_cryR hP hPD q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.stk.symm

theorem pad16_append {a b : List Byte} (ha : a.length % 16 = 0) :
    Spec.GcmSiv.pad16 (a ++ b) = a ++ Spec.GcmSiv.pad16 b := by
  simp only [Spec.GcmSiv.pad16, List.length_append, List.append_assoc]
  congr 3; omega_arith

/-- The tag input, with the plaintext's elements split after `16 k` bytes. -/
theorem tagInput_split (hpv : GcmSiv.Polyval.PolyvalEq) (ak nonce aad pt : List Byte) {k : Nat}
    (hk : 16 * k ≤ pt.length) :
    Spec.GcmSiv.tagInput ak nonce pt aad = GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.ghashFrom
      (GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes ak)) 0
      (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 aad) ++ Spec.GcmSiv.elems (pt.take (16 * k)) ++
        Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (pt.drop (16 * k))) ++
        [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length))]))) nonce := by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, hpv]
  have e : Spec.GcmSiv.pad16 pt = pt.take (16 * k) ++ Spec.GcmSiv.pad16 (pt.drop (16 * k)) := by
    rw [← pad16_append (by simp; omega_arith), List.take_append_drop]
  have hl : (pt.take (16 * k)).length % 16 = 0 := by simp; omega_arith
  rw [e, List.append_assoc, List.append_assoc, GcmSiv.elems_append (GcmSiv.pad16_mod _),
    GcmSiv.elems_append hl, GcmSiv.elems_append (GcmSiv.pad16_mod _),
    GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length))
      (by simp [Spec.GcmSiv.le64])]
  simp only [List.append_assoc]

/-- Counter mode with its first `k` bytes done agrees with all of it there. -/
theorem take_ctrPart (ciph : Spec.GcmSiv.Cipher) (hc : ∀ y, (ciph y).length = 16) (icb x : List Byte) {k : Nat}
    (hk : k ≤ x.length) : (GcmSiv.ctrPart ciph icb x k).take k = (Spec.GcmSiv.ctr ciph icb x).take k := by
  refine GcmSiv.ext_getD (by simp [GcmSiv.length_ctrPart, GcmSiv.length_ctr _ hc]) fun p hp => ?_
  simp only [List.length_take, GcmSiv.length_ctrPart] at hp
  rw [GcmSiv.getD_take (by omega_arith), GcmSiv.getD_take (by omega_arith), GcmSiv.getD_ctrPart _ _ _ _ (by omega_arith),
    GcmSiv.ctr_getD _ hc _ _ (by omega_arith), ite_eq_left (by omega_arith)]

/-- The counter block at `W + 96`, from its bytes. -/
theorem CtrSt.of_bytes {W : Addr} {icb : List Byte} {j : Nat} {m : Mem}
    (h : bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j) : CtrSt W icb j m := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    add_ofNat_assoc] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [Proof.Cmac.length_le4])
  refine ⟨BitVec.eq_of_toNat_eq ?_, h₂⟩
  have := congrArg Spec.GcmSiv.leNat h₁
  rwa [GcmSiv.leNat_le4, GcmSiv.leNat_le4] at this

/-! ## The loop's precondition -/

theorem spre_of {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {D : Addr} {n : Nat} (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (h256 : 256 ≤ n)
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 248) (hsi : t.gpr .rsi = BitVec.ofNat 64 R)
    (hdx : t.gpr .rdx = W + BitVec.ofNat 64 96) (hcx : t.gpr .rcx = W + BitVec.ofNat 64 80)
    (h8 : t.gpr .r8 = W + BitVec.ofNat 64 64) (h11 : t.gpr .r11 = W + BitVec.ofNat 64 1768) (h12 : t.gpr .r12 = D)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 (16 * (n / 256))) : Stitch.SPre t := by
  have hn := hD.lt
  have hnb : Stitch.nb t = 16 * (n / 256) := by
    show (t.gpr .r9).toNat = _; rw [h9, toNat_ofNat_of_lt (by omega_arith)]
  have hnr : Stitch.nr t = R := by
    show (t.gpr .rsi).toNat = _; rw [hsi, toNat_ofNat_of_lt (by rcases hR with h | h <;> subst h <;> decide)]
  have hpD : ∀ {d k : Nat}, d + k ≤ 3816 →
      (⟨D, 16 * (16 * (n / 256))⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
    fun h => (hD.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub h)
  constructor
  all_goals simp only [Stitch.dR, Stitch.kR, Stitch.cR, Stitch.yR, Stitch.pR, Stitch.dp, Stitch.kp, Stitch.cp,
    Stitch.yp, Stitch.hp, Stitch.pp, hnb, hnr, h12, hdi, hdx, hcx, h8, h11]
  · rcases hR with h | h <;> simp [h]
  · omega_arith
  · exact E.perm.wR (by decide)
  · exact E.perm.wR (by decide)
  · exact E.perm.wW (by decide)
  · exact E.perm.wW (by decide)
  · simpa using Proof.AesGcm.X86_64.in_off (d := 0) (n := 16 * (16 * (n / 256))) hDw (by omega_arith) hn
  · exact E.perm.wW (by decide)
  · exact hpD (d := 248) (k := 240) (by decide)
  · exact hpD (d := 96) (k := 16) (by decide)
  · exact hpD (d := 80) (k := 16) (by decide)
  · exact hpD (d := 1768) (k := 256) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · exact L.w_w (by omega_arith) (by decide) (by decide)
  · have := hD.wrap; omega_arith
  · rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith
  · rw [toNat_W L.ww (by decide)]; have := L.ww; omega_arith

/-! ## The data after the groups -/

/-- `mov rbx, rbp; shr rbx, 4; and rbp, 15; test rbx, rbx`. -/
theorem split16_ok {t : State} {m : Nat} (hm : m < 2 ^ 64) (hbp : t.gpr .rbp = BitVec.ofNat 64 m) :
    ∃ t₁ : State,
      runBlock isa [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)] t =
        some t₁ ∧
      t₁.gpr .rbx = BitVec.ofNat 64 (m / 16) ∧ t₁.gpr .rbp = BitVec.ofNat 64 (m % 16) ∧
      t₁.zf = some (decide (m / 16 = 0)) ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 m)
  rw [toNat_ofNat_of_lt hm, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp,
      Proof.AesGcm.X86_64.shr4 _ hm]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbp, hand]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, hbp, Proof.AesGcm.X86_64.shr4 _ hm]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
  · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
  all_goals rfl

/-- What counter mode on the rest of the data leaves, from `t`. -/
structure RestPost (K W SP : Addr) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR W SP D n) t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr ciph icb x

/-- Counter mode on the data from block `j₀`, the blocks before done. -/
theorem cryptRest_ok (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr}
    (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {j₀ : Nat} (hj₀ : 16 * j₀ ≤ n)
    (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j₀)) (hbp : t.gpr .rbp = BitVec.ofNat 64 (n - 16 * j₀))
    (C : CtrSt W icb j₀ t.mem) (hx : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * j₀))
    (hc : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.cryptRest v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) t
      (RestPost K W SP D n ciph icb x t) := by
  have hn := hD.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  have hcl : ∀ y, (ciph y).length = 16 := fun y => by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  obtain ⟨t₁, run₁, hbx₁, hbp₁, hzf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := split16_ok (m := n - 16 * j₀) (by omega_arith) hbp
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  have h12₁ : t₁.gpr .r12 = D + BitVec.ofNat 64 (16 * j₀) := by rw [hg₁ _ (by decide) (by decide), h12]
  -- The whole blocks.
  have hmid : WP isa (.ite .e (.block []) (.loop (cryptChunk ⟨eb.enc.name, eb.enc.code⟩ wide) .ne)) t₁
      (BlocksPost K W SP D n ciph icb x (n / 16) t₁) := by
    refine WP.ite (decide ((n - 16 * j₀) / 16 = 0)) (eval_e hzf₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : (n - 16 * j₀) / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [show n / 16 = j₀ by omega_arith]
      exact ⟨E₁, rfl, rfl, rfl, h12₁, by rw [hm₁]; exact C, by rw [hm₁]; exact hx, Frame.refl _ _⟩
    · have h0 : (n - 16 * j₀) / 16 ≠ 0 := by simpa using hf
      exact blocksFrom_ok eb wide L hR E₁ (hm₁ ▸ S) (hD.of_eq hrd₁ hwr₁) (by rw [hwr₁]; exact hDw) hxl
        (by omega_arith) (by omega_arith) h12₁ (by rw [hbx₁]; congr 1; omega_arith) (by rw [hm₁]; exact C) (by rw [hm₁]; exact hx)
        (by rw [hm₁]; exact hc)
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by rw [B.rbp, hbp₁]; congr 1; omega_arith
  obtain ⟨t₃, run₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa [.alu .test .rbp (.reg .rbp)] t₂ = some t₃ ∧
      t₃.zf = some (decide (n % 16 = 0)) ∧ (∀ r, t₃.gpr r = t₂.gpr r) ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr := by
    refine ⟨_, by srun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, hbp₂]
      rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
    · intro r; rfl
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env K W SP t₃ := B.env.keep (fun r _ => hg₃ r) hrd₃ hwr₃
  have F₁₃ : Frame (cryR W SP D n) t.mem t₃.mem := by rw [hm₃, ← hm₁]; exact B.frame
  refine WP.ite (decide (n % 16 = 0)) (eval_e hzf₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [hrd₃, B.rd, hrd₁], by rw [hwr₃, B.wr, hwr₁], F₁₃, ?_⟩
    rw [hm₃, B.data, show 16 * (n / 16) = n by omega_arith, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    have hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (W + BitVec.ofNat 64 248) R = ciph := by
      rw [ctxCiph_frame F₁₃ (key_cryR L hD) hRb, hc]
    refine WP.mono (cryptTail_ok v L hR E₃ (S.of_frame F₁₃ (slots_cryR L hD))
      (hD.of_eq (by rw [hrd₃, B.rd, hrd₁]) (by rw [hwr₃, B.wr, hwr₁])) (by rw [hwr₃, B.wr, hwr₁]; exact hDw) hxl
      (b := n / 16) (r := n % 16) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [hg₃, B.r12]) (by rw [hg₃, hbp₂])
      (by rw [hm₃]; exact B.ctr) (by rw [hm₃]; exact B.data) hc₃) fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, hrd₃, B.rd, hrd₁], by rw [T.wr, hwr₃, B.wr, hwr₁], F₁₃.trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

theorem bytesAt_prefix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (bytesAt m p n).take a = bytesAt m p a := by
  rw [show n = a + (n - a) by omega_arith, Proof.Cmac.bytesAt_add, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem bytesAt_suffix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (bytesAt m p n).drop a = bytesAt m (p + BitVec.ofNat 64 a) (n - a) := by
  rw [show n = a + (n - a) by omega_arith, Proof.Cmac.bytesAt_add, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  congr 1; omega_arith

/-! ## `stitched` -/

/-- Writes within `rs` that are all within `cryR ++ polyR`. -/
theorem frame_mid {rs : List Region} {W SP D : Addr} {n : Nat} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ cryR W SP D n ++ polyR W SP, Region.Sub r r') :
    Frame (cryR W SP D n ++ polyR W SP) m m' := hf.sub hs

theorem stitched_ok (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP)
    {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t) {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hA : Buf K W SP t A al) (hD : Buf K W SP t D n) (hN : Buf K W SP t N 12)
    (hDw : Covers [⟨D, n⟩] t.wr) (hND : (⟨N, 12⟩ : Region).Disjoint ⟨D, n⟩) (hAD : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩)
    (hG : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0) (h256 : 256 ≤ n) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.stitched v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) t
      (MidPost K W SP R N A D al n t) := by
  have hn := hD.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have dW : ∀ {d k : Nat}, d + k ≤ 80 ∨ (144 ≤ d ∧ d + k ≤ 488) →
      ∀ q ∈ cryR W SP D n ++ polyR W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h => mid_disj L hD.w h
  -- The head: the counter block from the tag, and the additional data's address and length.
  obtain ⟨t₁, run₁, hm₁, h12₁, hbp₁, hg₁, hrd₁, hwr₁⟩ := sHead_ok E S
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)) hrd₁ hwr₁
  have f₁ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have F₁ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₁.mem := frame_mid f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (.head _), fun _ h => h⟩
  have dD₁ : ∀ q ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide))
  have hicb : bytesAt t₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [hm₁, Proof.Cmac.bytesAt_store2, ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
      ← Proof.Cmac.bytesAt_split]
  -- POLYVAL of the additional data.
  refine WP.seq (WP.mono (absorb_ok v wide L E₁ (hA.of_eq hrd₁ hwr₁) h12₁ hbp₁) fun t₂ P₂ => ?_)
  have F₂ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₂.mem := F₁.trans (frame_mid P₂.frame fun r hr =>
    ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), fun _ h => h⟩)
  have x₂ : bytesAt t₂.mem D n = bytesAt t.mem D n := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame P₂.frame (buf_absR hD) (Nat.le_of_lt hn),
      Proof.AesGcm.X86_64.bytesAt_frame f₁ dD₁ (Nat.le_of_lt hn)]
  have c₂ : bytesAt t₂.mem (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame P₂.frame (w_absR L (.inr (.inl ⟨by decide, by decide⟩))) (by decide), hicb]
  -- The loop's arguments.
  have S₂ := S.of_frame F₂ (dW (.inr ⟨by decide, by decide⟩))
  obtain ⟨t₃, run₃, hm₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, r11₃, r12₃, r9₃, hg₃, hrd₃, hwr₃⟩ := sArgs_ok P₂.env S₂ hn
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have E₃ : Env K W SP t₃ := P₂.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have rd₃ : t₃.rd = t.rd := by rw [hrd₃, P₂.rd, hrd₁]
  have wr₃ : t₃.wr = t.wr := by rw [hwr₃, P₂.wr, hwr₁]
  have hp₃ : Stitch.SPre t₃ := spre_of L hR E₃ (hD.of_eq rd₃ wr₃) (by rw [wr₃]; exact hDw) h256 rdi₃ rsi₃ rdx₃ rcx₃
    r8₃ r11₃ r12₃ r9₃
  have hnb : Stitch.nb t₃ = 16 * (n / 256) := by
    show (t₃.gpr .r9).toNat = _; rw [r9₃, toNat_ofNat_of_lt (by omega_arith)]
  -- The loop.
  refine WP.seq (WP.mono (Stitch.dec_ok hp₃ (by rw [hnb]; omega_arith)) fun t₄ Dp => ?_)
  -- What the loop did, in the terms of `W` and the data.
  have hnr : Stitch.nr t₃ = R := by
    show (t₃.gpr .rsi).toNat = _; rw [rsi₃, toNat_ofNat_of_lt (by rcases hR with h | h <;> subst h <;> decide)]
  have hci : Stitch.ciph t₃ = Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R := by
    show Spec.GcmSiv.aesWith (Stitch.nr t₃) (bytesAt t₃.mem (t₃.gpr .rdi) (16 * (Stitch.nr t₃ + 1))) = _
    rw [hnr, rdi₃, hm₃]
    exact ctxCiph_frame F₂ (dW (.inr ⟨by decide, by decide⟩)) hRb
  have hicb₃ : Stitch.icb t₃ = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) := by
    show bytesAt t₃.mem (t₃.gpr .rdx) 16 = _; rw [rdx₃, hm₃, c₂]
  have hbA : ∀ k, Stitch.bAddr t₃ k = D + BitVec.ofNat 64 (16 * k) := fun k => by
    show t₃.gpr .r12 + _ = _; rw [r12₃]
  have hctb : ∀ k, Stitch.ctb t₃ k = Spec.Cmac.xor (bytesAt t₂.mem (D + BitVec.ofNat 64 (16 * k)) 16)
      (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R
        (Spec.GcmSiv.counterBlock (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) k)) := fun k => by
    show Spec.Cmac.xor (bytesAt t₃.mem (Stitch.bAddr t₃ k) 16) (Stitch.ciph t₃ _) = _
    rw [hbA, hm₃, hci, hicb₃]
  have Fd : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨D, 16 * (16 * (n / 256))⟩,
      ⟨W + BitVec.ofNat 64 1768, 256⟩] t₂.mem t₄.mem := by
    have h := Dp.frame
    simp only [Stitch.cR, Stitch.yR, Stitch.dR, Stitch.pR, Stitch.cp, Stitch.yp, Stitch.dp, Stitch.pp, hnb, rdx₃,
      rcx₃, r12₃, r11₃, hm₃] at h
    exact h
  have F₄ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₄.mem := F₂.trans (frame_mid Fd fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 96, 48⟩, List.mem_append_left _ (.head _), Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 80, 16⟩, List.mem_append_right _ (.tail _ (.head _)), fun _ h => h⟩
    · exact ⟨⟨D, n⟩, List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))),
        Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 1768, 2048⟩, List.mem_append_left _ (.tail _ (.tail _ (.head _))),
        Offset.sub W (by decide) (by decide)⟩)
  have hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hx₄ : bytesAt t₄.mem D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (16 * (16 * (n / 256))) := by
    have h := GcmSiv.ctrPart_stepN (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (m := t₂.mem) (m' := t₄.mem) D
      (i := 0) (k := 16 * (n / 256)) (fun l _ => hcl _)
      (by rw [hxl, x₂, Nat.mul_zero, GcmSiv.ctrPart_zero])
      (fun p hp ho => frame_outside Fd (P := D) (len := n) (a := 0) (n := 16 * (16 * (n / 256))) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))
          · exact .inl (by rw [BitVec.add_zero])
          · exact .inr (hD.w.sub_right (Lay.wSub (by decide)))) hn (by omega_arith) p (by rw [hxl] at hp; exact hp)
        (by omega_arith))
      (fun l hl => by
        have h := Dp.data l (by rw [hnb]; exact hl)
        rw [hbA, hctb] at h
        simpa only [Nat.zero_add] using h)
    rwa [hxl, Nat.zero_add] at h
  have C₄ : CtrSt W (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (16 * (n / 256)) t₄.mem := by
    refine CtrSt.of_bytes ?_
    have h := Dp.ctr
    rw [show Stitch.cp t₃ = W + BitVec.ofNat 64 96 from rdx₃, hicb₃, hnb] at h
    exact h
  have hH₂ : Spec.Gcm.blockAt t₂.mem (W + BitVec.ofNat 64 64) = Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) :=
    Proof.AesGcm.X86_64.blockAt_frame F₂ (dW (.inl (by decide)))
  have Y₄ : Spec.Gcm.blockAt t₄.mem (W + BitVec.ofNat 64 80) =
      Spec.Gcm.ghashFrom (Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64))
        (Spec.Gcm.blockAt t₂.mem (W + BitVec.ofNat 64 80))
        ((List.range (16 * (n / 256))).map fun k =>
          Spec.GcmSiv.ofBytes (bytesAt t₄.mem (D + BitVec.ofNat 64 (16 * k)) 16)) := by
    have h := Dp.y
    rw [show Stitch.yp t₃ = W + BitVec.ofNat 64 80 from rcx₃,
      show Stitch.hk t₃ = Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) by
        show Spec.Gcm.blockAt t₃.mem (t₃.gpr .r8) = _; rw [r8₃, hm₃, hH₂],
      show Stitch.y₀ t₃ = Spec.Gcm.blockAt t₂.mem (W + BitVec.ofNat 64 80) by
        show Spec.Gcm.blockAt t₃.mem (t₃.gpr .rcx) = _; rw [rcx₃, hm₃], hnb] at h
    rw [h]
    refine congrArg _ (List.map_congr_left fun k hk => ?_)
    rw [← Dp.data k (by rw [hnb]; simpa using hk), hbA]
  have E₄ : Env K W SP t₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Dp.gpr _ (by decide) (by decide) (by decide) (by decide)) Dp.rd Dp.wr
  have S₄ := S.of_frame F₄ (dW (.inr ⟨by decide, by decide⟩))
  have rd₄ : t₄.rd = t.rd := by rw [Dp.rd, rd₃]
  have wr₄ : t₄.wr = t.wr := by rw [Dp.wr, wr₃]
  -- The data after the groups: counter mode from the counter block the loop left.
  obtain ⟨t₅, run₅, hm₅, h12₅, hbp₅, hg₅, hrd₅, hwr₅⟩ := rest_ok E₄ S₄ hn
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  have E₅ : Env K W SP t₅ := E₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hrd₅ hwr₅
  have rd₅ : t₅.rd = t.rd := by rw [hrd₅, rd₄]
  have wr₅ : t₅.wr = t.wr := by rw [hwr₅, wr₄]
  have F₅ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₅.mem := by rw [hm₅]; exact F₄
  have hc₅ : Spec.GcmSiv.ctxCiph t₅.mem (W + BitVec.ofNat 64 248) R =
      Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R :=
    ctxCiph_frame F₅ (dW (.inr ⟨by decide, by decide⟩)) hRb
  refine WP.seq (WP.mono (cryptRest_ok v eb wide L hR E₅ (S.of_frame F₅ (dW (.inr ⟨by decide, by decide⟩)))
    (hD.of_eq rd₅ wr₅) (by rw [wr₅]; exact hDw) hxl (j₀ := 16 * (n / 256)) (by omega_arith)
    (by rw [h12₅, show 256 * (n / 256) = 16 * (16 * (n / 256)) by omega_arith])
    (by rw [hbp₅, show n % 256 = n - 16 * (16 * (n / 256)) by omega_arith]) (by rw [hm₅]; exact C₄)
    (by rw [hm₅]; exact hx₄) hc₅) fun t₆ Rp => ?_)
  have F₆ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₆.mem :=
    F₅.trans (frame_mid Rp.frame fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
  have rd₆ : t₆.rd = t.rd := by rw [Rp.rd, rd₅]
  have wr₆ : t₆.wr = t.wr := by rw [Rp.wr, wr₅]
  have Y₆ : Spec.Gcm.blockAt t₆.mem (W + BitVec.ofNat 64 80) = Spec.Gcm.blockAt t₄.mem (W + BitVec.ofNat 64 80) := by
    rw [Proof.AesGcm.X86_64.blockAt_frame Rp.frame (lowW_cryR L hD.w (d := 80) (k := 16) (by decide)), hm₅]
  -- The rest of the plaintext absorbed.
  have S₆ := S.of_frame F₆ (dW (.inr ⟨by decide, by decide⟩))
  obtain ⟨t₇, run₇, hm₇, h12₇, hbp₇, hg₇, hrd₇, hwr₇⟩ := rest_ok Rp.env S₆ hn
  refine WP.seq (WP.of_runBlock ⟨t₇, run₇, ?_⟩)
  have E₇ : Env K W SP t₇ := Rp.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₇ _ (by decide) (by decide) (by decide)) hrd₇ hwr₇
  have rd₇ : t₇.rd = t.rd := by rw [hrd₇, rd₆]
  have wr₇ : t₇.wr = t.wr := by rw [hwr₇, wr₆]
  refine WP.seq (WP.mono (absorb_ok v wide L E₇ ((hD.slice (a := 256 * (n / 256)) (k := n % 256) (by omega_arith)).of_eq
    rd₇ wr₇) h12₇ hbp₇) fun t₈ P₈ => ?_)
  have F₈ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₈.mem := by
    rw [← hm₇] at F₆
    exact F₆.trans (frame_mid P₈.frame fun r hr => ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr),
      fun _ h => h⟩)
  have S₈ := S.of_frame F₈ (dW (.inr ⟨by decide, by decide⟩))
  -- The lengths, and the tag input.
  refine WP.seq (WP.mono (lens_ok v L P₈.env S₈.alen S₈.len hA.lt hn) fun t₉ P₉ => ?_)
  have F₉ : Frame (cryR W SP D n ++ polyR W SP) t.mem t₉.mem :=
    F₈.trans (frame_mid P₉.frame fun r hr => ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), fun _ h => h⟩)
  have S₉ := S.of_frame F₉ (dW (.inr ⟨by decide, by decide⟩))
  have rd₉ : t₉.rd = t.rd := by rw [P₉.rd, P₈.rd, rd₇]
  have wr₉ : t₉.wr = t.wr := by rw [P₉.wr, P₈.wr, wr₇]
  obtain ⟨t₁₀, run₁₀, fr₁₀, out₁₀, hg₁₀, hrd₁₀, hwr₁₀⟩ := tagIn_ok L P₉.env S₉.nonce (hN.of_eq rd₉ wr₉)
  refine WP.of_runBlock ⟨t₁₀, run₁₀, ?_⟩
  have m₁₀D : bytesAt t₁₀.mem D n = bytesAt t₆.mem D n := by
    rw [Proof.AesGcm.X86_64.bytesAt_frame fr₁₀ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hD.w.sub_right (Lay.wSub (by decide)))
        (Nat.le_of_lt hn),
      Proof.AesGcm.X86_64.bytesAt_frame P₉.frame (buf_absR hD) (Nat.le_of_lt hn),
      Proof.AesGcm.X86_64.bytesAt_frame P₈.frame (buf_absR hD) (Nat.le_of_lt hn), hm₇]
  have pt := m₁₀D.trans Rp.data
  refine ⟨P₉.env.of_saved hg₁₀ hrd₁₀ hwr₁₀, by rw [hrd₁₀, rd₉], by rw [hwr₁₀, wr₉],
    F₉.trans (frame_mid fr₁₀ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (.head _), fun _ h => h⟩), pt, fun hpv => ?_⟩
  have hpl : (bytesAt t₁₀.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  rw [out₁₀, tagInput_split hpv _ _ _ _ (k := 16 * (n / 256)) (by rw [hpl]; omega_arith),
    Proof.AesGcm.X86_64.bytesAt_frame F₉ (buf_mid hN hND) (by decide), hpl, Proof.Cmac.bytesAt_length]
  -- `Y`, piece by piece.
  have H₁ := Proof.AesGcm.X86_64.blockAt_frame F₁ (dW (d := 64) (k := 16) (.inl (by decide)))
  have H₇ : Spec.Gcm.blockAt t₇.mem (W + BitVec.ofNat 64 64) = Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) := by
    rw [hm₇]; exact Proof.AesGcm.X86_64.blockAt_frame F₆ (dW (.inl (by decide)))
  have H₈ := Proof.AesGcm.X86_64.blockAt_frame F₈ (dW (d := 64) (k := 16) (.inl (by decide)))
  have Y₁ : Spec.Gcm.blockAt t₁.mem (W + BitVec.ofNat 64 80) = 0 := by
    rw [Proof.AesGcm.X86_64.blockAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl (by decide)) (by decide) (by decide)), hY]
  have A₁ : bytesAt t₁.mem A al = bytesAt t.mem A al :=
    Proof.AesGcm.X86_64.bytesAt_frame F₁ (buf_mid hA hAD) (Nat.le_of_lt hA.lt)
  have hdec : (List.range (16 * (n / 256))).map (fun k =>
      Spec.GcmSiv.ofBytes (bytesAt t₄.mem (D + BitVec.ofNat 64 (16 * k)) 16)) =
      Spec.GcmSiv.elems ((bytesAt t₁₀.mem D n).take (16 * (16 * (n / 256)))) := by
    rw [← GcmSiv.elems_bytesAt, pt, ← take_ctrPart _ hcl _ _ (by rw [hxl]; omega_arith), ← hx₄,
      bytesAt_prefix _ _ (by omega_arith)]
  have hrest : bytesAt t₆.mem (D + BitVec.ofNat 64 (256 * (n / 256))) (n % 256) =
      (bytesAt t₁₀.mem D n).drop (16 * (16 * (n / 256))) := by
    rw [m₁₀D, bytesAt_suffix _ _ (by omega_arith), show 16 * (16 * (n / 256)) = 256 * (n / 256) by omega_arith,
      show n - 256 * (n / 256) = n % 256 by omega_arith]
  rw [P₉.out, H₈, P₈.out, H₇, hm₇, Y₆, Y₄, P₂.out, H₁, Y₁, A₁, ← hG, hdec, hrest, Proof.Gcm.ghashFrom_append,
    Proof.Gcm.ghashFrom_append, Proof.Gcm.ghashFrom_append]


/-! ## `vg_aes_gcm_siv_open` -/

/-- `mov rax, [W + lenO]; cmp rax, 256`. -/
theorem lenCmp_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {N A D : Addr} {al n : Nat}
    (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa [.mov .rax (.mem (Impl.AesGcm.X86_64.at_ .r15 lenO)), .alu .cmp .rax (imm 256)] t =
      some t₁ ∧ t₁.cf = some (decide (n < 256)) ∧ (∀ r, r ≠ .rax → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rN := E.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sN := S.len
  refine ⟨_, by srun [h15, rN, sN], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_arithFlags, gpr_setFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rw [toNat_ofNat_of_lt hn]
    rfl
  · intro r h₁; simp only [gpr_arithFlags, gpr_setFlags, gpr_setReg, h₁, ite_false]
  all_goals rfl

theorem mid_mut (W SP D : Addr) (n : Nat) :
    ∀ r ∈ cryR W SP D n ++ polyR W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · exact cryR_mut W SP D n r hr
  · obtain ⟨r₁, h₁, s₁⟩ := polyR_mutW W SP r hr
    obtain ⟨r₂, h₂, s₂⟩ := mutW_mut W SP D n r₁ h₁
    exact ⟨r₂, h₂, fun x hx => s₂ x (s₁ x hx)⟩

/-- `vg_aes_gcm_siv_open`, for its arguments. -/
theorem openS_wp' (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' =>
      gprPreserved s s' ∧ openPost (Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16)) s' D n := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₀, run₀, E₀, S₀, sv₀, f₀, rd₀, wr₀⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have f₀' : Frame (entryR W :: mutR W SP D n) s.mem s₀.mem :=
    f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  -- The received tag, copied to `W`.
  have hTa : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₀, wr₀]; exact h
  obtain ⟨s₁, run₁, fR, hR₁, hgR, rdR, wrR⟩ := recv_ok E₀ (by rw [argT_kept f₀' Ar.argsW Ar.argsD, hT]) hTa
    ((Tb.buf (s := s) hTr).of_eq rd₀ wr₀)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E₀.of_saved hgR rdR wrR
  have fR' : Frame (mutR W SP D n) s₀.mem s₁.mem := fR.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, .head _, Region.sub_prefix (by decide)⟩
  have S₁ := slots_mut L Ar.data.w fR' S₀
  have rd₁ : s₁.rd = s.rd := by rw [rdR, rd₀]
  have wr₁ : s₁.wr = s.wr := by rw [wrR, wr₀]
  have f₁ : Frame (entryR W :: mutR W SP D n) s.mem s₁.mem :=
    f₀'.trans (fR'.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have f₀₁ : Frame [entryR W, ⟨W, 16⟩] s.mem s₁.mem :=
    (f₀.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (fR.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨W, 16⟩, .tail _ (.head _), fun _ h => h⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · exact hP.w.sub_right (Region.sub_prefix (by decide)))
      (by have := hP.lt; omega_arith)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₀₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w.sub_right (Lay.wSub (by decide))
      · exact L.k_w.sub_right (Region.sub_prefix (by decide))) hRb
  have hT₁ : bytesAt s₁.mem W 16 = bytesAt s.mem T 16 := by
    rw [hR₁]; exact tag_kept Tb f₀'
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v eb L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  have S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- Counter mode and POLYVAL, interleaved from 256 bytes of data on.
  obtain ⟨s₃, run₃, hcf₃, hg₃, hm₃, hrd₃, hwr₃⟩ := lenCmp_ok Ky.env S₂ Ar.data.lt
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := Ky.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
  have r₂ : s₂.rd = s₁.rd := Ky.rd
  have w₂ : s₂.wr = s₁.wr := Ky.wr
  have hG₂ : Spec.Gcm.blockAt s₂.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt s₂.mem (W + BitVec.ofNat 64 16) 16)) := Ky.hkey
  have nA₂ : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₂.mem P len = bytesAt s.mem P len :=
    fun hP => by rw [buf_mutW (hP.of_eq rd₁ wr₁) fK, hent hP]
  have hmid : WP isa (.ite .b (.seq (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (polyval v.callees wide))
      (Impl.AesGcmSiv.X86_64Stitch.stitched v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)) s₃
      (MidPost K W SP R N A D al n s₃) := by
    have S₃ : Slots W R N A D al n s₃.mem := hm₃ ▸ S₂
    refine WP.ite (decide (n < 256)) (eval_b hcf₃) (fun ht => ?_) (fun hf => ?_)
    · exact classic_ok v eb wide L Ar.rounds E₃ S₃ (bA₁.of_eq (by rw [hrd₃, r₂]) (by rw [hwr₃, w₂]))
        (bD₁.of_eq (by rw [hrd₃, r₂]) (by rw [hwr₃, w₂])) (bN₁.of_eq (by rw [hrd₃, r₂]) (by rw [hwr₃, w₂]))
        (by rw [hwr₃, w₂, wr₁]; exact Ar.dw) Ar.nd Ar.ad (by rw [hm₃]; exact hG₂) (by rw [hm₃]; exact Ky.acc)
    · exact stitched_ok v eb wide L Ar.rounds E₃ S₃ (bA₁.of_eq (by rw [hrd₃, r₂]) (by rw [hwr₃, w₂]))
        (bD₁.of_eq (by rw [hrd₃, r₂]) (by rw [hwr₃, w₂])) (bN₁.of_eq (by rw [hrd₃, r₂]) (by rw [hwr₃, w₂]))
        (by rw [hwr₃, w₂, wr₁]; exact Ar.dw) Ar.nd Ar.ad (by rw [hm₃]; exact hG₂) (by rw [hm₃]; exact Ky.acc)
        (by simpa using hf)
  refine WP.seq (WP.mono hmid fun s₄ Md => ?_)
  have S₄ := (show Slots W R N A D al n s₃.mem from hm₃ ▸ S₂).of_frame Md.frame
    (mid_disj L Ar.data.w (.inr ⟨by decide, by decide⟩))
  -- Its tag at `W + 128`.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Md.env S₄ (o := 128) (by decide)) fun s₅ Tg => ?_)
  -- The comparison.
  obtain ⟨s₆, run₆, hm₆, hg₆, hrd₆, hwr₆⟩ := cmp_ok Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env K W SP s₆ := Tg.env.of_saved hg₆ hrd₆ hwr₆
  have fO : Frame [wO W] s₅.mem s₆.mem := by
    rw [hm₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have S₅ := slots_mut L Ar.data.w ((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)) S₄
  have S₆ := S₅.of_frame fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
  have r₅ : s₅.rd = s₁.rd := by rw [Tg.rd, Md.rd, hrd₃, r₂]
  have w₅ : s₅.wr = s₁.wr := by rw [Tg.wr, Md.wr, hwr₃, w₂]
  have hok : s₆.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16 = bytesAt s₅.mem W 16 then 1#64 else 0#64 := by
    rw [hm₆, Mem.readW_writeW_self64]
    by_cases hc : bytesAt s₅.mem W 16 = bytesAt s₅.mem (W + BitVec.ofNat 64 128) 16
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Ne.symm hc, ↓reduceIte]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ S₆ (bD₁.of_eq (by rw [hrd₆, r₅]) (by rw [hwr₆, w₅]))
    (by rw [hwr₆, w₅, wr₁]; exact Ar.dw) hok) fun s₇ Mk => ?_)
  -- `ok` and the restore.
  have h15₇ := Mk.env.r15
  have rO := Mk.env.perm.wR (show 192 + 8 ≤ 3816 by decide)
  obtain ⟨s₈, run₈, hax₈, hm₈, hg₈, hrd₈, hwr₈⟩ : ∃ s₈ : State, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₇ =
      some s₈ ∧ s₈.gpr .rax = s₇.mem.readW (W + BitVec.ofNat 64 192) 64 ∧ s₈.mem = s₇.mem ∧
      (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by srun [h15₇, rO], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : Env K W SP s₈ := Mk.env.keep (fun r hr => hg₈ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₈ hwr₈
  have fall : Frame (mutR W SP D n) s₁.mem s₇.mem :=
    ((((fK.sub (mutW_mut W SP D n)).trans (by rw [← hm₃]; exact Frame.refl _ _)).trans
      (Md.frame.sub (mid_mut W SP D n))).trans
      (((Tg.frame.sub (tagR_mutW W SP (by decide))).sub (mutW_mut W SP D n)).trans
        (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; exact .tail _ (.head _),
          fun _ h => h⟩))).trans
      (Mk.frame.sub fun q hq => ⟨q, by
        simp only [List.mem_singleton] at hq; subst hq; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _)))),
        fun _ h => h⟩)
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ :=
    restore_ok E₈ (by rw [hm₈]; exact saved_mut L Ar.data.w (fR'.trans fall) sv₀)
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append, run₈]; exact run₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, 144) (by decide)
    · exact hg₉ (.rbp, 152) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, 160) (by decide)
    · exact hg₉ (.r13, 168) (by decide)
    · exact hg₉ (.r14, 176) (by decide)
    · exact hg₉ (.r15, 184) (by decide)
  · have fall' : Frame (entryR W :: mutR W SP D n) s.mem s₇.mem :=
      f₁.trans (fall.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
    rw [hm₉, hm₈, hsp]
    exact fall'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have tag₂ : bytesAt s₂.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Ky.frame (w0_keyR L) (by decide), hT₁]
    have tag₅ : bytesAt s₅.mem W 16 = bytesAt s.mem T 16 := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame Tg.frame (w0_tagR L) (by decide),
        Proof.AesGcm.X86_64.bytesAt_frame Md.frame (fun q hq => by
          simpa using mid_disj L Ar.data.w (d := 0) (k := 16) (.inl (by decide)) q hq)
          (by decide), hm₃, tag₂]
    have ct₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    have ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := by
      rw [ctxCiph_frame Md.frame (mid_disj L Ar.data.w (.inr ⟨by decide, by decide⟩)) hRb, hm₃]
    have pt₃ := Md.data
    rw [hm₃, tag₂, ct₂, ci] at pt₃
    have po := Md.out hpv
    rw [hm₃, ← au, nA₂ Ar.nonce, nA₂ Ar.aad, pt₃] at po
    have tg := Tg.out
    rw [ci₄, ci, po] at tg
    have dD : ∀ q ∈ tagR W SP 128, (⟨D, n⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.w.sub_right (Lay.wSub (by decide))
      · exact Ar.data.stk.symm
    have d₆ : bytesAt s₆.mem D n = bytesAt s₄.mem D n := by
      rw [Proof.AesGcm.X86_64.bytesAt_frame fO (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
          (by have := Ar.data.lt; omega_arith),
        Proof.AesGcm.X86_64.bytesAt_frame Tg.frame dD (by have := Ar.data.lt; omega_arith)]
    have ax : s₉.gpr .rax = s₆.mem.readW (W + BitVec.ofNat 64 192) 64 := by
      rw [hax₉, hax₈, Mk.frame.readW (r := ⟨W + BitVec.ofNat 64 192, 8⟩) (Region.contains_self _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm)
        (by decide)]
    have md := Mk.data
    have ax' := ax.trans hok
    rw [tg, tag₅] at ax'
    rw [tg, tag₅, d₆, pt₃] at md
    have hdec : Spec.GcmSiv.decryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T 16) =
        let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        if Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
            (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
            (bytesAt s.mem A al)) = bytesAt s.mem T 16 then
          some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
        else none := by
      unfold Spec.GcmSiv.decryptWith
      rw [← Prod.eta (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R)
        (bytesAt s.mem N 12))]
    simp only at hdec
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
      at md ax' hdec
    rw [hdec]
    refine Or.elim (Classical.em (Spec.GcmSiv.aes dk.2 (Spec.GcmSiv.tagInput dk.1 (bytesAt s.mem N 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem T 16)) (bytesAt s.mem D n))
      (bytesAt s.mem A al)) = bytesAt s.mem T 16)) (fun hc => ?_) (fun hc => ?_)
    · refine openPost_some (by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]
    · refine openPost_none (by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]) ?_ ?_
      · rw [ax']; simp only [hc, ↓reduceIte]; decide
      · rw [hm₉, hm₈, md]; simp only [hc, ↓reduceIte]

/-- `vg_aes_gcm_siv_open`. -/
theorem openS_wp (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) (hpv : GcmSiv.Polyval.PolyvalEq) {s : State} (h : openPre s) :
    WP isa (Impl.AesGcmSiv.X86_64Stitch.«open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) s fun s' =>
      gprPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTr⟩ := args_of_open h
  exact openS_wp' v eb wide hpv Ar Tb hTr rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64
