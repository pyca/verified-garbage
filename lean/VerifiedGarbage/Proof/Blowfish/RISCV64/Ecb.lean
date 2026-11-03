module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Cipher
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# Blowfish on RISC-V: ECB

`ecb_wp`: every block becomes its encryption or decryption, two at a time
(`pair_step`) and the last alone if one is left (`ecb_step`), under the
schedule copied into the frame (`main_wp`), which is zeroed before
returning; the callee-saved registers the second block uses are saved below
the caller's stack pointer and restored. The structure of PPC64LE's
(`Proof/Blowfish/PPC64LE/Ecb.lean`).

Two blocks are enciphered at once (`cipher2_run`), as one is by
`cipher_run` (`Proof/Blowfish/RISCV64/Cipher.lean`): `lookup2 j` leaves
S-box `j`'s entries for both blocks' xL (`a3`, `s1`) in the low words of
their accumulators (`t2`, `s6`), its rows (`row2_step`, by induction in
`rows2_run`) scanning each plane for both indices, and each block's end is
`extract`'s (`lookup2_run`); `f2_run` follows `f_run`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.WriteBytes (writeBytes)
open VG.Impl.Words.RISCV64 (loadBE32 storeBE)

/-- The registers the lookups of both blocks write. -/
def lookRegs2 : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

/-! ## Two blocks: the indices -/

theorem index2_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index2 j)) s fun t =>
      t.gpr .s4 = BitVec.twoPow 64 ((quarter (lo (s.gpr .s1)) j).toNat / 8) ∧ t.mem = s.mem := by
  have e : (s.gpr .s1 <<< (32 + 8 * j)) >>> 59 = BitVec.ofNat 64 ((quarter (lo (s.gpr .s1)) j).toNat / 8) := by
    have h := congrArg (fun v : BitVec 64 => v >>> 3) (index_val (s.gpr .s1) hj)
    rw [← BitVec.shiftRight_add] at h
    rw [h]
    apply BitVec.eq_of_toNat_eq
    have := (quarter (lo (s.gpr .s1)) j).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hq := (quarter (lo (s.gpr .s1)) j).isLt
  unfold index2
  brun [xL2, qReg2, mReg2, show 32 + 8 * j < 64 by omega, e]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rfl

/-! ## Two blocks: the rows -/

/-- Row `k > 0` for both blocks. -/
theorem row2_run (u : State) {k : Nat} (hk : k < 32) {B q q' : BitVec 64}
    (h7 : u.gpr .a7 = B) (h1 : u.gpr .t1 = q) (h4 : u.gpr .s4 = q')
    (r0 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (8 * k)) 8)
    (r1 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 + 8 * k)) 8)
    (r2 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (512 + 8 * k)) 8)
    (r3 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (768 + 8 * k)) 8)
    (a0 : (B + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0)
    (a1 : (B + BitVec.ofNat 64 (256 + 8 * k)).toNat % 8 = 0)
    (a2 : (B + BitVec.ofNat 64 (512 + 8 * k)).toNat % 8 = 0)
    (a3 : (B + BitVec.ofNat 64 (768 + 8 * k)).toNat % 8 = 0) :
    WP isa (.block (row2 k)) u fun t =>
      let M := (q <<< (63 - k)).sshiftRight 63
      let M' := (q' <<< (63 - k)).sshiftRight 63
      t.gpr .t2 = u.gpr .t2 ||| (u.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 &&& M) ∧
      t.gpr .t5 = u.gpr .t5 ||| (u.mem.readW (B + BitVec.ofNat 64 (256 + 8 * k)) 64 &&& M) ∧
      t.gpr .t6 = u.gpr .t6 ||| (u.mem.readW (B + BitVec.ofNat 64 (512 + 8 * k)) 64 &&& M) ∧
      t.gpr .t0 = u.gpr .t0 ||| (u.mem.readW (B + BitVec.ofNat 64 (768 + 8 * k)) 64 &&& M) ∧
      t.gpr .s6 = u.gpr .s6 ||| (u.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 &&& M') ∧
      t.gpr .s7 = u.gpr .s7 ||| (u.mem.readW (B + BitVec.ofNat 64 (256 + 8 * k)) 64 &&& M') ∧
      t.gpr .s8 = u.gpr .s8 ||| (u.mem.readW (B + BitVec.ofNat 64 (512 + 8 * k)) 64 &&& M') ∧
      t.gpr .s9 = u.gpr .s9 ||| (u.mem.readW (B + BitVec.ofNat 64 (768 + 8 * k)) 64 &&& M') ∧
      t.mem = u.mem := by
  unfold row2 rowMask2 rowMask plane2
  brun [accOf, accOf2, qReg2, mReg2, tmp2, Nat.zero_add, h7, h1, h4, r0, r1, r2, r3, a0, a1, a2, a3,
    show 63 - k < 64 by omega,
    show 8 * k < 2048 by omega, show 256 * 1 + 8 * k < 2048 by omega,
    show 256 * 2 + 8 * k < 2048 by omega, show 256 * 3 + 8 * k < 2048 by omega]

/-- Row 0 for both blocks. -/
theorem row20_run (u : State) {B q q' : BitVec 64}
    (h7 : u.gpr .a7 = B) (h1 : u.gpr .t1 = q) (h4 : u.gpr .s4 = q')
    (r0 : InRegions (u.rd ++ u.wr) B 8)
    (r1 : InRegions (u.rd ++ u.wr) (B + 256#64) 8)
    (r2 : InRegions (u.rd ++ u.wr) (B + 512#64) 8)
    (r3 : InRegions (u.rd ++ u.wr) (B + 768#64) 8)
    (a0 : B.toNat % 8 = 0) (a1 : (B + 256#64).toNat % 8 = 0)
    (a2 : (B + 512#64).toNat % 8 = 0) (a3 : (B + 768#64).toNat % 8 = 0) :
    WP isa (.block row20) u fun t =>
      let M := (q <<< (63 - 0)).sshiftRight 63
      let M' := (q' <<< (63 - 0)).sshiftRight 63
      t.gpr .t2 = u.mem.readW B 64 &&& M ∧ t.gpr .t5 = u.mem.readW (B + 256#64) 64 &&& M ∧
      t.gpr .t6 = u.mem.readW (B + 512#64) 64 &&& M ∧ t.gpr .t0 = u.mem.readW (B + 768#64) 64 &&& M ∧
      t.gpr .s6 = u.mem.readW B 64 &&& M' ∧ t.gpr .s7 = u.mem.readW (B + 256#64) 64 &&& M' ∧
      t.gpr .s8 = u.mem.readW (B + 512#64) 64 &&& M' ∧ t.gpr .s9 = u.mem.readW (B + 768#64) 64 &&& M' ∧
      t.mem = u.mem := by
  unfold row20 rowMask2 rowMask firstPlane2
  brun [accOf, accOf2, qReg2, mReg2, tmp2, h7, h1, h4, r0, r1, r2, r3, a0, a1, a2, a3]

/-- After rows `0, …, n - 1` of S-box `j` for both blocks' indices. -/
structure RowInv2 (s₀ : State) (S : Addr) (j : Nat) (idx idx' : Byte) (n : Nat) (u : State) : Prop where
  q : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)
  q' : u.gpr .s4 = BitVec.twoPow 64 (idx'.toNat / 8)
  p0 : u.gpr .t2 = scanPlane s₀.mem S j 0 idx.toNat n
  p1 : u.gpr .t5 = scanPlane s₀.mem S j 1 idx.toNat n
  p2 : u.gpr .t6 = scanPlane s₀.mem S j 2 idx.toNat n
  p3 : u.gpr .t0 = scanPlane s₀.mem S j 3 idx.toNat n
  p0' : u.gpr .s6 = scanPlane s₀.mem S j 0 idx'.toNat n
  p1' : u.gpr .s7 = scanPlane s₀.mem S j 1 idx'.toNat n
  p2' : u.gpr .s8 = scanPlane s₀.mem S j 2 idx'.toNat n
  p3' : u.gpr .s9 = scanPlane s₀.mem S j 3 idx'.toNat n
  keep : Keep lookRegs2 s₀ u
  mem : u.mem = s₀.mem

theorem row20_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx idx' : Byte)
    {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hq : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)) (hq' : u.gpr .s4 = BitVec.twoPow 64 (idx'.toNat / 8))
    (hk : Keep lookRegs2 s₀ u) (hm : u.mem = s₀.mem) :
    WP isa (.block row20) u (RowInv2 s₀ S j idx idx' 1) := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [hk.2.1, hk.2.2]
  let B := S + BitVec.ofNat 64 (1024 * j)
  have ad : ∀ b < 4, B + BitVec.ofNat 64 (256 * b) = S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * 0) :=
    fun b hb => plane_addr S j b 0 (by omega)
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 * b)) 8 :=
    fun b hb => by rw [ad b hb, hrd]; exact E.rd8 _ (by omega) (by omega)
  have hal : ∀ b < 4, (B + BitVec.ofNat 64 (256 * b)).toNat % 8 = 0 :=
    fun b hb => by rw [ad b hb]; exact al8_add E.al8 (by omega) (by omega)
  have r0 := hr 0 (by decide)
  have l0 := hal 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at r0 l0
  refine WP.mono (WP.keep [.t2, .t3, .t5, .t6, .t0, .s5, .s6, .s7, .s8, .s9, .t4]
    (row20_run u h7 hq hq' r0 (hr 1 (by decide)) (hr 2 (by decide))
    (hr 3 (by decide)) l0 (hal 1 (by decide)) (hal 2 (by decide)) (hal 3 (by decide))) (by rfl) rfl)
    fun t ⟨⟨t2, t5, t6, t0, s6, s7, s8, s9, tm⟩, tk⟩ => ?_
  have M := mask_eq idx (k := 0) (by decide)
  have M' := mask_eq idx' (k := 0) (by decide)
  have pl : ∀ b < 4, u.mem.readW (B + BitVec.ofNat 64 (256 * b)) 64 = planeWord64 s₀.mem S j b 0 :=
    fun b hb => by rw [ad b hb, hm]; rfl
  have p0 := pl 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at p0
  have e1 : (256#64 : BitVec 64) = BitVec.ofNat 64 (256 * 1) := rfl
  have e2 : (512#64 : BitVec 64) = BitVec.ofNat 64 (256 * 2) := rfl
  have e3 : (768#64 : BitVec 64) = BitVec.ofNat 64 (256 * 3) := rfl
  refine ⟨by rw [tk.gpr (by decide), hq], by rw [tk.gpr (by decide), hq'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hk.trans tk |>.mono (by decide), tm.trans hm⟩
  · rw [t2, M, p0, scanPlane_one]
  · rw [t5, M, e1, pl 1 (by decide), scanPlane_one]
  · rw [t6, M, e2, pl 2 (by decide), scanPlane_one]
  · rw [t0, M, e3, pl 3 (by decide), scanPlane_one]
  · rw [s6, M', p0, scanPlane_one]
  · rw [s7, M', e1, pl 1 (by decide), scanPlane_one]
  · rw [s8, M', e2, pl 2 (by decide), scanPlane_one]
  · rw [s9, M', e3, pl 3 (by decide), scanPlane_one]

theorem row2_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx idx' : Byte)
    {k : Nat} (hk : k < 32) {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (I : RowInv2 s₀ S j idx idx' k u) :
    WP isa (.block (row2 k)) u (RowInv2 s₀ S j idx idx' (k + 1)) := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  let B := S + BitVec.ofNat 64 (1024 * j)
  have ad : ∀ b < 4, B + BitVec.ofNat 64 (256 * b + 8 * k) = S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * k) :=
    fun b hb => plane_addr S j b k (by omega)
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 * b + 8 * k)) 8 :=
    fun b hb => by rw [ad b hb, hrd]; exact E.rd8 _ (by omega) (by omega)
  have hal : ∀ b < 4, (B + BitVec.ofNat 64 (256 * b + 8 * k)).toNat % 8 = 0 :=
    fun b hb => by rw [ad b hb]; exact al8_add E.al8 (by omega) (by omega)
  have pl : ∀ b < 4, u.mem.readW (B + BitVec.ofNat 64 (256 * b + 8 * k)) 64 = planeWord64 s₀.mem S j b k :=
    fun b hb => by rw [ad b hb, I.mem]; rfl
  have r0 := hr 0 (by decide)
  have l0 := hal 0 (by decide)
  have p0 := pl 0 (by decide)
  have r1 := hr 1 (by decide)
  have l1 := hal 1 (by decide)
  have p1 := pl 1 (by decide)
  have r2 := hr 2 (by decide)
  have l2 := hal 2 (by decide)
  have p2 := pl 2 (by decide)
  have r3 := hr 3 (by decide)
  have l3 := hal 3 (by decide)
  have p3 := pl 3 (by decide)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul] at r0 l0 p0 r1 l1 p1 r2 l2 p2 r3 l3 p3
  refine WP.mono (WP.keep [.t2, .t3, .t4, .t5, .t6, .t0, .s5, .s6, .s7, .s8, .s9, .s10]
    (row2_run u hk h7 I.q I.q' r0 r1 r2 r3 l0 l1 l2 l3)
    (by rfl) rfl) fun t ⟨⟨t2, t5, t6, t0, s6, s7, s8, s9, tm⟩, tk⟩ => ?_
  have M := mask_eq idx hk
  have M' := mask_eq idx' hk
  refine ⟨by rw [tk.gpr (by decide), I.q], by rw [tk.gpr (by decide), I.q'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    I.keep.trans tk |>.mono (by decide), tm.trans I.mem⟩
  · rw [t2, M, p0, I.p0, scanPlane_succ]
  · rw [t5, M, p1, I.p1, scanPlane_succ]
  · rw [t6, M, p2, I.p2, scanPlane_succ]
  · rw [t0, M, p3, I.p3, scanPlane_succ]
  · rw [s6, M', p0, I.p0', scanPlane_succ]
  · rw [s7, M', p1, I.p1', scanPlane_succ]
  · rw [s8, M', p2, I.p2', scanPlane_succ]
  · rw [s9, M', p3, I.p3', scanPlane_succ]

theorem rows2_succ (n : Nat) : rows2 (n + 1) = rows2 n ++ row2 (n + 1) := by
  simp only [rows2, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem rows2_run {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx idx' : Byte)
    {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hq : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)) (hq' : u.gpr .s4 = BitVec.twoPow 64 (idx'.toNat / 8))
    (hk : Keep lookRegs2 s₀ u) (hm : u.mem = s₀.mem)
    (h7₀ : s₀.gpr .a7 = S + BitVec.ofNat 64 (1024 * j)) :
    ∀ n, n < 32 → WP isa (.block (rows2 n)) u (RowInv2 s₀ S j idx idx' (n + 1)) := by
  intro n
  induction n with
  | zero => intro _; exact row20_step E hj idx idx' h7 hq hq' hk hm
  | succ n ih =>
    intro hn
    rw [rows2_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun v V => row2_step E hj idx idx' hn ?_ V
    rw [V.keep.gpr (by decide), h7₀]

/-! ## Two blocks: the entries from the accumulators -/

theorem lane2_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [.shift .srl .d mReg2 xL2 (24 - 8 * j), .logicImm .and mReg2 mReg2 7,
      .shift .sll .d mReg2 mReg2 3]) s fun t =>
      t.gpr .s5 = BitVec.ofNat 64 (8 * ((quarter (lo (s.gpr .s1)) j).toNat % 8)) ∧ t.mem = s.mem := by
  rw [← lane_val _ hj]
  brun [mReg2, xL2, show 24 - 8 * j < 64 by omega]

theorem pick2_run (u : State) {K A0 A1 A2 A3 : BitVec 64} (h3 : u.gpr .s5 = K) (h2 : u.gpr .s6 = A0)
    (h5 : u.gpr .s7 = A1) (h6 : u.gpr .s8 = A2) (h0 : u.gpr .s9 = A3) :
    WP isa (.block (pick2 0 ++ pick2 1 ++ pick2 2 ++ pick2 3 ++
      ([.logic .or (accOf2 0) (accOf2 0) (accOf2 1), .logic .or (accOf2 2) (accOf2 2) (accOf2 3),
        .logic .or (accOf2 0) (accOf2 0) (accOf2 2)] : List Instr))) u fun t =>
      t.gpr .s6 = ((A0 >>> (K.toNat % 64) &&& 255#64) ||| (A1 >>> (K.toNat % 64) &&& 255#64) <<< 8) |||
        ((A2 >>> (K.toNat % 64) &&& 255#64) <<< 16 ||| (A3 >>> (K.toNat % 64) &&& 255#64) <<< 24) ∧
        t.mem = u.mem := by
  unfold pick2
  brun [accOf2, mReg2, h3, h2, h5, h6, h0]

/-- The entry of S-box `j` for `idx`, from the accumulators of the four
planes after the 32 rows, shifted by `8 (idx mod 8)`. -/
theorem entry_eq (m : Mem) (S : Addr) {j : Nat} (hj : j < 4) (idx : Byte) {K : BitVec 64}
    (hK : K.toNat % 64 = 8 * (idx.toNat % 8)) :
    lo (((scanPlane m S j 0 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) |||
        (scanPlane m S j 1 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) <<< 8) |||
      ((scanPlane m S j 2 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) <<< 16 |||
        (scanPlane m S j 3 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) <<< 24)) =
      sEntry (scheduleAt m S) j idx := by
  rw [hK, scanPlane_all, scanPlane_all, scanPlane_all, scanPlane_all, shr_byte, shr_byte,
    shr_byte, shr_byte]
  refine word_ext fun c hc => ?_
  have e := pack_byte (fun b => (planeWord64 m S j b (idx.toNat / 8)).extractLsb' (8 * (idx.toNat % 8)) 8) hc
  rw [e, planeWord64_byte _ _ hj hc]

/-- The lookups of S-box `j` (at `sch`, moved to it) for the bytes `3 - j`
of both blocks' xL. -/
theorem lookup2_run {s : State} {S : Addr} (E : SchAt s S) {j : Nat} (hj : j < 4)
    (h7 : s.gpr .a7 = S + BitVec.ofNat 64 (1024 * j)) :
    WP isa (lookup2 j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .a3)) j) ∧
      lo (t.gpr .s6) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .s1)) j) ∧
        Keep lookRegs2 s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .a3)) j
  let idx' := quarter (lo (s.gpr .s1)) j
  have hx : extract j ++ extractB j =
      [.shift .srl .d mReg xL (24 - 8 * j), .logicImm .and mReg mReg 7, .shift .sll .d mReg mReg 3] ++
      ((pick 0 ++ pick 1 ++ pick 2 ++ pick 3 ++
        ([.logic .or acc acc (accOf 1), .logic .or (accOf 2) (accOf 2) (accOf 3), .logic .or acc acc (accOf 2)] :
          List Instr)) ++
      ([.shift .srl .d mReg2 xL2 (24 - 8 * j), .logicImm .and mReg2 mReg2 7, .shift .sll .d mReg2 mReg2 3] ++
      (pick2 0 ++ pick2 1 ++ pick2 2 ++ pick2 3 ++
      ([.logic .or (accOf2 0) (accOf2 0) (accOf2 1), .logic .or (accOf2 2) (accOf2 2) (accOf2 3),
        .logic .or (accOf2 0) (accOf2 0) (accOf2 2)] : List Instr)))) := by
    simp only [extract, extractB, List.append_assoc]
  unfold lookup2
  simp only [List.append_assoc]
  rw [hx, WP.block_append_iff]
  refine WP.mono (WP.keep [.t1, .t3] (index_run s hj) (by rfl) rfl) fun u₀ ⟨⟨u1, um₀⟩, uk₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s4, .s5] (index2_run u₀ hj) (by rfl) rfl) fun u ⟨⟨u4, um⟩, uk⟩ => ?_
  have e1 : u₀.gpr .s1 = s.gpr .s1 := uk₀.gpr (by decide)
  rw [e1] at u4
  have u1' : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8) := by rw [uk.gpr (by decide), u1]
  rw [WP.block_append_iff]
  have uk' : Keep lookRegs2 s u := (uk₀.trans uk).mono (by decide)
  refine WP.mono (rows2_run E hj idx idx' (by rw [uk'.gpr (by decide), h7]) u1' u4 uk' (um.trans um₀) h7 31
    (by decide)) fun v V => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (lane_run v hj) (by rfl) rfl) fun w ⟨⟨w3, wm⟩, wk⟩ => ?_
  have hv3 : v.gpr .a3 = s.gpr .a3 := V.keep.gpr (by decide)
  have hK : (w.gpr .t3).toNat % 64 = 8 * (idx.toNat % 8) := by
    have := idx.isLt
    rw [w3, hv3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t5, .t6, .t0] (pick_run w rfl
    ((wk.gpr (by decide)).trans V.p0) ((wk.gpr (by decide)).trans V.p1)
    ((wk.gpr (by decide)).trans V.p2) ((wk.gpr (by decide)).trans V.p3)) (by rfl) rfl)
    fun x ⟨⟨x2, xm⟩, xk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s5] (lane2_run x hj) (by rfl) rfl) fun y ⟨⟨y5, ym⟩, yk⟩ => ?_
  have hx1 : x.gpr .s1 = s.gpr .s1 := by
    rw [xk.gpr (by decide), wk.gpr (by decide), V.keep.gpr (by decide)]
  have hK' : (y.gpr .s5).toNat % 64 = 8 * (idx'.toNat % 8) := by
    have := idx'.isLt
    rw [y5, hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have g : ∀ r, r ∉ [Reg.s5] → r ∉ [Reg.t2, .t5, .t6, .t0] → r ∉ [Reg.t3] → y.gpr r = v.gpr r :=
    fun r h1 h2 h3 => by rw [yk.gpr h1, xk.gpr h2, wk.gpr h3]
  refine WP.mono (WP.keep [.s6, .s7, .s8, .s9] (pick2_run y rfl
    ((g .s6 (by decide) (by decide) (by decide)).trans V.p0')
    ((g .s7 (by decide) (by decide) (by decide)).trans V.p1')
    ((g .s8 (by decide) (by decide) (by decide)).trans V.p2')
    ((g .s9 (by decide) (by decide) (by decide)).trans V.p3')) (by rfl) rfl)
    fun t ⟨⟨t6, tm⟩, tk⟩ => ?_
  refine ⟨?_, ?_, (((V.keep.trans wk).trans xk).trans yk).trans tk |>.mono (by decide),
    by rw [tm, ym, xm, wm, V.mem]⟩
  · rw [tk.gpr (by decide), yk.gpr (by decide), x2]
    exact entry_eq s.mem S hj idx hK
  · rw [t6]
    exact entry_eq s.mem S hj idx' hK'

/-! ## Two blocks: F -/

/-- The registers F of both blocks writes. -/
def fRegs2 : List Reg := .a5 :: .s3 :: lookRegs2

theorem combine2_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (combine2 j)) u fun t =>
      lo (t.gpr .a5) = (if j = 0 then lo (u.gpr .t2) else if j = 2 then lo (u.gpr .a5) ^^^ lo (u.gpr .t2)
        else lo (u.gpr .a5) + lo (u.gpr .t2)) ∧
      lo (t.gpr .s3) = (if j = 0 then lo (u.gpr .s6) else if j = 2 then lo (u.gpr .s3) ^^^ lo (u.gpr .s6)
        else lo (u.gpr .s3) + lo (u.gpr .s6)) ∧ t.mem = u.mem := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine2, combine, fReg2, accOf2] <;> simp only [lo_xor, lo_add, BitVec.or_self, and_self]

/-- The registers F of both blocks writes, with the schedule pointer. -/
def fRegs27 : List Reg := .a7 :: fRegs2

/-- S-box `j`'s lookups, then their accumulation, for both blocks. -/
theorem step2_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs27 s₀ u)
    (hm : u.mem = s₀.mem) (h7 : u.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j))
    (hp : 0 < j → lo (u.gpr .a5) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7)) (lo (s₀.gpr .a3)) (j - 1))
    (hp' : 0 < j → lo (u.gpr .s3) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7)) (lo (s₀.gpr .s1)) (j - 1))
    {Q : State → Prop}
    (hQ : ∀ t, lo (t.gpr .a5) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7)) (lo (s₀.gpr .a3)) j →
      lo (t.gpr .s3) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7)) (lo (s₀.gpr .s1)) j →
      Keep fRegs27 s₀ t → t.mem = s₀.mem → t.gpr .a7 = u.gpr .a7 → Q t) :
    WP isa (.seq (lookup2 j) (.block (combine2 j))) u Q := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [k.2.1, k.2.2]
  have Eu : SchAt u (s₀.gpr .a7) := ⟨fun o h1 h2 => by rw [hrd]; exact E.rd8 o h1 h2, E.al8⟩
  apply WP.seq
  refine WP.mono (lookup2_run Eu hj h7) fun v ⟨v10, v11, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.a5, .s3] (combine2_run v hj) (by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun t ⟨⟨t7, t8, tm⟩, tk⟩ => hQ t ?_ ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
      (by rw [tk.gpr (by decide), vk.gpr (by decide)])
  · have e4 : u.gpr .a3 = s₀.gpr .a3 := k.gpr (by decide)
    rw [t7, v10, hm, e4, vk.gpr (by decide)]
    exact fAcc_step _ _ hj _ hp
  · have e4 : u.gpr .s1 = s₀.gpr .s1 := k.gpr (by decide)
    rw [t8, v11, hm, e4, vk.gpr (by decide)]
    exact fAcc_step _ _ hj _ hp'

/-- `nextBox` after the lookups of S-box `j < 3`, and what it keeps. -/
theorem next2_run {s₀ : State} {j : Nat} {u : State} (k : Keep fRegs27 s₀ u)
    (h7 : u.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j)) :
    WP isa (.block [nextBox]) u fun t => Keep fRegs27 s₀ t ∧ t.mem = u.mem ∧
      t.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * (j + 1)) ∧ t.gpr .a5 = u.gpr .a5 ∧
      t.gpr .s3 = u.gpr .s3 := by
  refine WP.mono (WP.keep [.a7] (nextBox_run u) (by rfl) rfl) fun t ⟨⟨t7, tm⟩, tk⟩ =>
    ⟨(k.trans tk).mono (by decide), tm, ?_, tk.gpr (by decide), tk.gpr (by decide)⟩
  rw [t7, h7, Offset.add_add]
  congr 2

theorem f2_run {s : State} (E : LookEnv s) :
    WP isa f2 s fun t =>
      lo (t.gpr .a5) = Spec.Blowfish.f (scheduleAt s.mem (s.gpr .a7)) (lo (s.gpr .a3)) ∧
      lo (t.gpr .s3) = Spec.Blowfish.f (scheduleAt s.mem (s.gpr .a7)) (lo (s.gpr .s1)) ∧
        Keep fRegs2 s t ∧ t.mem = s.mem := by
  unfold f2
  apply WP.reassoc; apply WP.seq
  refine step2_run E (j := 0) (by decide) (Keep.refl _ _) rfl (by simp) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) fun t0 h0 h0' k0 m0 e0 => ?_
  apply WP.seq
  refine WP.mono (next2_run (j := 0) k0 (by rw [e0]; simp)) fun u0 ⟨k0', m0', e0', a0, b0⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step2_run E (j := 1) (by decide) k0' (m0'.trans m0) e0' (fun _ => by rw [a0]; exact h0)
    (fun _ => by rw [b0]; exact h0') fun t1 h1 h1' k1 m1 e1 => ?_
  apply WP.seq
  refine WP.mono (next2_run (j := 1) k1 (by rw [e1, e0'])) fun u1 ⟨k1', m1', e1', a1, b1⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step2_run E (j := 2) (by decide) k1' (m1'.trans m1) e1' (fun _ => by rw [a1]; exact h1)
    (fun _ => by rw [b1]; exact h1') fun t2 h2 h2' k2 m2 e2 => ?_
  apply WP.seq
  refine WP.mono (next2_run (j := 2) k2 (by rw [e2, e1'])) fun u2 ⟨k2', m2', e2', a2, b2⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step2_run E (j := 3) (by decide) k2' (m2'.trans m2) e2' (fun _ => by rw [a2]; exact h2)
    (fun _ => by rw [b2]; exact h2') fun t3 h3 h3' k3 m3 e3 => ?_
  have back : WP isa (.block [.addi sch sch (-2048), .addi sch sch (-1024)]) t3 fun t =>
      t.gpr .a7 = t3.gpr .a7 - BitVec.ofNat 64 2048 - BitVec.ofNat 64 1024 ∧ t.mem = t3.mem := by
    brun
  refine WP.mono (WP.keep [.a7] back (by rfl) rfl) fun t ⟨⟨t7, tm⟩, tk⟩ => ?_
  have e7 : t.gpr .a7 = s.gpr .a7 := by
    rw [t7, e3, e2', BitVec.sub_sub, BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  refine ⟨?_, ?_, keep_restore ((k3.trans tk).mono (by decide)) e7, tm.trans m3⟩
  · rw [tk.gpr (by decide), h3, fAcc_three]
  · rw [tk.gpr (by decide), h3', fAcc_three]

/-! ## Two blocks: rounds -/

/-- The registers the block function of both blocks writes. -/
def cRegs2 : List Reg := cRegs ++ [.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

/-- After `i` rounds of both blocks from `s₀`. -/
structure CInv2 (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  p : u.gpr .a6 = s₀.gpr .a7 + BitVec.ofNat 64 (pBase up i)
  halves : (lo (u.gpr .a3), lo (u.gpr .a4)) =
    iter (scheduleAt s₀.mem (s₀.gpr .a7)) (ord up) i (lo (s₀.gpr .a3), lo (s₀.gpr .a4))
  halves' : (lo (u.gpr .s1), lo (u.gpr .s2)) =
    iter (scheduleAt s₀.mem (s₀.gpr .a7)) (ord up) i (lo (s₀.gpr .s1), lo (s₀.gpr .s2))
  keep : Keep cRegs2 s₀ u
  mem : u.mem = s₀.mem

theorem round2_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : u.gpr .a6 + BitVec.ofNat 64 (pAt up) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hal : a.toNat % 4 = 0) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp, .logic .xor xL2 xL2 tmp]) u fun t =>
      lo (t.gpr .a3) = lo (u.gpr .a3) ^^^ P ∧ lo (t.gpr .s1) = lo (u.gpr .s1) ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 2048 := by cases up <;> decide
  rw [← hp] at hr hP hal
  brun [xL2, ho, hr, hP, hal]
  simp only [lo_xor, lo_ext, and_self]

theorem round2_tail (u : State) (up : Bool) (S : BitVec 64) {i : Nat} (hi : i < 16)
    (h3 : u.gpr .a7 = S) (h8 : u.gpr .a6 = S + BitVec.ofNat 64 (pBase up i)) :
    WP isa (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR, .logic .or xR tmp tmp,
        .logic .xor xR2 xR2 fReg2, .logic .or tmp xL2 xL2, .logic .or xL2 xR2 xR2, .logic .or xR2 tmp tmp,
        .addi pPtr pPtr (if up then 4 else -4),
        .sub tmp pPtr sch, .addi tmp tmp (-2047), .addi tmp tmp (-2047),
        .addi tmp tmp (-(pEnd up - 4094 : Nat))]) u fun t =>
      lo (t.gpr .a3) = lo (u.gpr .a4) ^^^ lo (u.gpr .a5) ∧ lo (t.gpr .a4) = lo (u.gpr .a3) ∧
      lo (t.gpr .s1) = lo (u.gpr .s2) ^^^ lo (u.gpr .s3) ∧ lo (t.gpr .s2) = lo (u.gpr .s1) ∧
        t.gpr .a6 = S + BitVec.ofNat 64 (pBase up (i + 1)) ∧
        t.gpr .t4 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) ∧
        t.mem = u.mem := by
  have hend : pEnd up = pBase up 16 := by cases up <;> rfl
  have e4 : 4094 ≤ pEnd up := by cases up <;> decide
  cases up
  · have e : S + BitVec.ofNat 64 (4160 - 4 * i) - 4#64 = S + BitVec.ofNat 64 (4160 - 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofs_sub S (by omega)]; congr 2
    brun [xL2, xR2, fReg2, h3, h8, show pEnd false - 4094 ≤ 2048 by decide]
    simp only [pBase, Bool.false_eq_true, ite_false, lo_xor, BitVec.or_self, e]
    refine ⟨trivial, trivial, trivial, trivial, trivial, ?_⟩
    rw [sub_end S _ e4, hend]
    simp only [pBase, Bool.false_eq_true, ite_false]
  · have e : S + BitVec.ofNat 64 (4096 + 4 * i) + 4#64 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    brun [xL2, xR2, fReg2, h3, h8, show pEnd true - 4094 ≤ 2048 by decide]
    simp only [pBase, ite_true, lo_xor, BitVec.or_self, e]
    refine ⟨trivial, trivial, trivial, trivial, trivial, ?_⟩
    rw [sub_end S _ e4, hend]
    simp only [pBase, ite_true]

theorem round2_step {s₀ : State} (E : LookEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv2 s₀ up i u) :
    WP isa (round2 up) u fun u' => CInv2 s₀ up (i + 1) u' ∧
      u'.gpr .t4 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) := by
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega
  let K := scheduleAt s₀.mem (s₀.gpr .a7)
  have u3 : u.gpr .a7 = s₀.gpr .a7 := I.keep.gpr (by decide)
  unfold round2
  apply WP.seq
  refine WP.mono (WP.keep [.a3, .s1, .t4] (round2_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P _ up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega) (by omega))
    (al_add E.al (by omega) (by omega))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide) rfl) fun v ⟨⟨v4, v5, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs2 s₀ v := (I.keep.trans vk).mono (by decide)
  have Ev : LookEnv v := E.keep kv (by decide)
  apply WP.seq
  refine WP.mono (f2_run Ev) fun w ⟨w7, w7', wk, wm⟩ => ?_
  have w3 : w.gpr .a7 = s₀.gpr .a7 := by rw [wk.gpr (by decide), vk.gpr (by decide), u3]
  have w8 : w.gpr .a6 = s₀.gpr .a7 + BitVec.ofNat 64 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.a3, .a4, .s1, .s2, .a6, .t4] (round2_tail w up _ hi w3 w8) (by
    cases up <;> decide) rfl) fun x ⟨⟨x4, x5, x4', x5', x8, x12, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (v.gpr .a7) = K := by rw [vm, I.mem, vk.gpr (by decide), u3]
  refine ⟨⟨by omega, x8, ?_, ?_, ((kv.trans wk).trans xk).mono (by decide), by rw [xm, wm, vm, I.mem]⟩, x12⟩
  · have w4 : w.gpr .a3 = v.gpr .a3 := wk.gpr (by decide)
    have w5 : w.gpr .a4 = u.gpr .a4 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
    rw [x4, x5, w7, hK, w4, w5, v4, iter_succ, ← I.halves]
    simp only [roundStep]
    rw [BitVec.xor_comm (lo (u.gpr .a4))]
  · have w4 : w.gpr .s1 = v.gpr .s1 := wk.gpr (by decide)
    have w5 : w.gpr .s2 = u.gpr .s2 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
    rw [x4', x5', w7', hK, w4, w5, v5, iter_succ, ← I.halves']
    simp only [roundStep]
    rw [BitVec.xor_comm (lo (u.gpr .s2))]

theorem rounds2_run {s : State} (E : LookEnv s) (up : Bool) {u : State} (I : CInv2 s up 0 u) :
    WP isa (.loop (round2 up) (.nonzero tmp)) u (CInv2 s up 16) := by
  refine WP.loop (M := isa) (Q := CInv2 s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv2 s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round2_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [tmp, Steps.eval_nonzero, hz, ofNat_sub_bne (by cases up <;> simp [pBase] <;> omega)
    (by cases up <;> simp [pBase])]
  have e : (pBase up (i + 1) = pBase up 16) ↔ i + 1 = 16 := by cases up <;> simp [pBase] <;> omega
  by_cases e' : i + 1 = 16
  · left
    exact ⟨by simp [e.mpr e'], e' ▸ J'⟩
  · right
    have hne : ¬ pBase up (i + 1) = pBase up 16 := fun h => e' (e.mp h)
    exact ⟨by simp [hne], n - 1, by omega, i + 1, by omega, by omega, J'⟩

theorem cipher2_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : u.gpr .a6 + BitVec.ofNat 64 (pAt up) = a)
    (hb : u.gpr .a6 + BitVec.ofNat 64 (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (hla : a.toNat % 4 = 0) (hlb : b.toNat % 4 = 0)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor fReg xL tmp, .logic .xor fReg2 xL2 tmp,
        .load .w tmp pPtr (4 - pAt up), .logic .xor xL tmp xR, .logic .xor xL2 tmp xR2,
        .logic .or xR fReg fReg, .logic .or xR2 fReg2 fReg2]) u fun t =>
      lo (t.gpr .a3) = P₁₇ ^^^ lo (u.gpr .a4) ∧ lo (t.gpr .a4) = lo (u.gpr .a3) ^^^ P₁₆ ∧
      lo (t.gpr .s1) = P₁₇ ^^^ lo (u.gpr .s2) ∧ lo (t.gpr .s2) = lo (u.gpr .s1) ^^^ P₁₆ ∧
        t.mem = u.mem := by
  have ho : pAt up < 2048 := by cases up <;> decide
  have ho' : 4 - pAt up < 2048 := by cases up <;> decide
  rw [← ha] at hra h16 hla
  rw [← hb] at hrb h17 hlb
  brun [xL2, xR2, fReg2, ho, ho', hra, hrb, h16, h17, hla, hlb]
  simp only [lo_xor, lo_ext, BitVec.or_self, and_self]

/-- The block function of both blocks. -/
theorem cipher2_run {s : State} (E : LookEnv s) (up : Bool) :
    WP isa (cipher2 up) s fun t =>
      (lo (t.gpr .a3), lo (t.gpr .a4)) =
        feistel (scheduleAt s.mem (s.gpr .a7)) (ord up) (lo (s.gpr .a3)) (lo (s.gpr .a4)) ∧
      (lo (t.gpr .s1), lo (t.gpr .s2)) =
        feistel (scheduleAt s.mem (s.gpr .a7)) (ord up) (lo (s.gpr .s1)) (lo (s.gpr .s2)) ∧
      Keep cRegs2 s t ∧ t.mem = s.mem := by
  unfold cipher2
  apply WP.seq
  refine WP.mono (WP.keep [.a6] (cipher_start s up) (by cases up <;> decide) rfl)
    fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have I0 : CInv2 s up 0 u :=
    ⟨by decide, u8, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl,
      by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds2_run E up I0) fun v V => ?_
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (s.gpr .a7)
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.a3, .a4, .a5, .s1, .s2, .s3, .t4] (cipher2_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := s.gpr .a7 + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := s.gpr .a7 + BitVec.ofNat 64 (4096 + 4 * ord up 17))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [hrd]; exact E.rd _ (by omega) r16) (by rw [hrd]; exact E.rd _ (by omega) r17)
    (al_add E.al (by omega) (by omega)) (al_add E.al (by omega) (by omega))
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide) rfl)
    fun t ⟨⟨t4, t5, t4', t5', tm⟩, tk⟩ => ?_
  refine ⟨?_, ?_, (V.keep.trans tk).mono (by decide), by rw [tm, V.mem]⟩
  · rw [t4, t5, feistel_eq, ← V.halves, BitVec.xor_comm]
  · rw [t4', t5', feistel_eq, ← V.halves', BitVec.xor_comm]

/-! ## Blocks in and out of the halves -/

theorem beWord_byte (m : Mem) (p : Addr) (off : Nat) {b : Nat} (hb : b < 4) :
    (beWord m p off).extractLsb' (8 * b) 8 = m (p + BitVec.ofNat 64 (off + (3 - b))) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [beWord, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right] <;> congr 1 <;> omega

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem beWord_block (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    beWord m q o = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [beWord_byte _ _ _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega)]

/-- The block at `a1` into the halves, as big-endian words. -/
theorem loadBlock_run (u : State) {q : Addr} (hq : u.gpr .a1 = q)
    (r : InRegions (u.rd ++ u.wr) q 8) :
    WP isa (.block loadBlock) u fun t =>
      lo (t.gpr .a3) = decodeWord (blockAt u.mem q) 0 ∧ lo (t.gpr .a4) = decodeWord (blockAt u.mem q) 4 ∧
        Keep [.a3, .a4, .t4] u t ∧ t.mem = u.mem := by
  unfold loadBlock
  rw [WP.block_append_iff]
  refine WP.mono (loadBE32_ok (d := .a3) (tmp := .t4) (n := .a1) (off := 0) (by decide) (by decide)
    (by decide) (by decide) (by rw [hq]; exact CallLay.inRegions_sub r (by decide) (by decide)))
    fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (loadBE32_ok (d := .a4) (tmp := .t4) (n := .a1) (off := 4) (by decide) (by decide)
    (by decide) (by decide) (by
      simp only [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub r (by decide) (by decide))) fun u₂ e₂ => ?_
  subst e₂
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, hq,
      beWord_block _ _ (o := 0) (by decide)]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, RegUpd.mem_write, hq,
      beWord_block _ _ (o := 4) (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The halves to the block at `a1`, the next block's pointer, and the
counter less one. -/
theorem storeBlock_run (u : State) {q : Addr} (hq : u.gpr .a1 = q) (w : InRegions u.wr q 8) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = writeBytes u.mem q (beBytes 4 (u.gpr .a3) ++ beBytes 4 (u.gpr .a4)) ∧
      t.gpr .a1 = q + 8#64 ∧ t.gpr .a2 = u.gpr .a2 - 1#64 ∧ Keep [.t4, .a1, .a2] u t := by
  unfold storeBlock
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (storeBE_ok (v := .a3) (tmp := .t4) (n := .a1) (off := 0) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [hq]; exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeBE_ok (v := .a4) (tmp := .t4) (n := .a1) (off := 4) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      simp only [RegUpd.gpr_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₂ e₂ => ?_
  subst e₂
  have h1 : u.gpr .a1 = q := hq
  refine WP.mono (WP.keep [.a1, .a2] (Q := fun t => t.gpr .a1 = q + 8#64 ∧ t.gpr .a2 = u.gpr .a2 - 1#64 ∧
      t.mem = writeBytes u.mem q (beBytes 4 (u.gpr .a3) ++ beBytes 4 (u.gpr .a4))) (by
    brun [RegUpd.gpr_write, RegUpd.mem_write, h1]
    have h := WriteBytes.writeBytes_append u.mem q (beBytes 4 (u.gpr .a3)) (beBytes 4 (u.gpr .a4)) (by
      simp only [beBytes_length]; decide)
    rwa [beBytes_length] at h) (by decide) rfl) fun t ⟨⟨t1, t2, tm⟩, tk⟩ => ⟨tm, t1, ?_, ?_⟩
  · exact t2
  · refine ⟨fun r hr => ?_, tk.2.1, tk.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [tk.gpr (by simp [hr.2.1, hr.2.2])]
    simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem shr_lo (x : BitVec 64) {k : Nat} (hk : k ≤ 24) :
    (x >>> k).setWidth 8 = (lo x).extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show k + i < 32 by omega]

/-- What the stores leave: the block. -/
theorem stored_block (m : Mem) (q : Addr) (x y : BitVec 64) :
    blockAt (writeBytes m q (beBytes 4 x ++ beBytes 4 y)) q = encodeBlock (lo x) (lo y) := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [encodeBlock_getD _ _ hi]
  simp only [writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    List.length_append, beBytes_length, show i < 4 + 4 by omega, ite_true]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [beBytes_length]; exact h4)]
    simp only [beBytes, List.getElem?_map, List.getElem?_range h4, Option.map_some, Option.getD_some]
    rw [shr_lo _ (by omega)]
  · rw [ite_eq_right h4, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [beBytes_length]; omega), beBytes_length]
    simp only [beBytes, List.getElem?_map, List.getElem?_range (show i - 4 < 4 by omega), Option.map_some,
      Option.getD_some]
    rw [shr_lo _ (by omega)]
    congr 2; omega

theorem stored_frame (m : Mem) (q : Addr) (x y : BitVec 64) :
    Frame [⟨q, 8⟩] m (writeBytes m q (beBytes 4 x ++ beBytes 4 y)) :=
  WriteBytes.writeBytes_frame _ _ _ (by
    simp only [List.length_append, beBytes_length]
    exact Region.contains_self q 8)

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The registers the loop writes. -/
def loopRegs : List Reg := [.a1, .a2, .a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6,
  .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

/-- The loop's fixed facts, about the state `s₀` before it: the schedule at
`S` (the frame) and the `n` blocks at `D`. -/
structure LoopEnv (S D : Addr) (n : Nat) (s₀ : State) : Prop where
  a7 : s₀.gpr .a7 = S
  al : S.toNat % 4 = 0
  al8 : S.toNat % 8 = 0
  key : ∀ o, o % 4 = 0 → o + 4 ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 o) 4
  key8 : ∀ o, o % 8 = 0 → o + 8 ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 o) 8
  data : (⟨D, 8 * n⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 4168⟩ : Region).Disjoint ⟨D, 8 * n⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ n
  ptr : u.gpr .a1 = wAt D k
  cnt : u.gpr .a2 = BitVec.ofNat 64 (n - k)
  keep : Keep loopRegs s₀ u
  done : ∀ b < k, blockAt u.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < n → blockAt u.mem (wAt D b) = blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * n⟩] s₀.mem u.mem

theorem ecb_step {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) {k : Nat}
    (hk : k < n) {u : State} (I : EInv S D n up s₀ k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u
      (fun u' => EInv S D n up s₀ (k + 1) u' ∧ u'.gpr .a2 = BitVec.ofNat 64 (n - (k + 1))) := by
  have fit := L.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.keep.2.2]; exact L.data
  have inD : InRegions u.wr (wAt D k) 8 :=
    ⟨_, dR, Offset.contains_base D (by omega) (by omega)⟩
  have inD' : InRegions (u.rd ++ u.wr) (wAt D k) 8 :=
    let ⟨r, hr, hc⟩ := inD; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  refine WP.mono (loadBlock_run u I.ptr inD') fun u₁ ⟨l₁, h₁, k₁, m₁⟩ => ?_
  have hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have Ku₁ : Keep loopRegs s₀ u₁ := (I.keep.trans k₁).mono (by decide)
  have E : LookEnv u₁ := by
    refine ⟨fun o ha ho => ?_, fun o ha ho => ?_, by rw [Ku₁.gpr (by decide), L.a7]; exact L.al,
      by rw [Ku₁.gpr (by decide), L.a7]; exact L.al8⟩
    · rw [Ku₁.gpr (by decide), L.a7, Ku₁.2.1, Ku₁.2.2]
      exact L.key o ha ho
    · rw [Ku₁.gpr (by decide), L.a7, Ku₁.2.1, Ku₁.2.2]
      exact L.key8 o ha ho
  apply WP.seq
  refine WP.mono (cipher_run E up) fun u₂ ⟨c₂, k₂, m₂⟩ => ?_
  have Ku₂ : Keep loopRegs s₀ u₂ := (Ku₁.trans k₂).mono (by decide)
  have wr₂ : u₂.wr = u.wr := by rw [k₂.2.2, k₁.2.2]
  have p₂ : u₂.gpr .a1 = wAt D k := by rw [k₂.gpr (by decide), k₁.gpr (by decide), I.ptr]
  refine WP.mono (storeBlock_run u₂ p₂ (by rw [wr₂]; exact inD)) fun u₃ ⟨m₃, p₃, c₃, k₃⟩ => ?_
  have subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have hc₂ : u₂.gpr .a2 = BitVec.ofNat 64 (n - k) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), I.cnt]
  have other : ∀ b, b < n → b ≠ k → blockAt u₃.mem (wAt D b) = blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame (stored_frame _ _ _ _) fun r hr => ?_, m₂, m₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega) (by omega) (by omega)
  have c₃' : u₃.gpr .a2 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [c₃, hc₂]; apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨⟨by omega, ?_, c₃', (Ku₂.trans k₃).mono (by decide), fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃'⟩
  · rw [p₃, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, wAt, wAt, Offset.add_add]
    congr 2
  · by_cases hbk : b = k
    · subst hbk
      have e1 := congrArg Prod.fst c₂
      have e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      rw [m₃, stored_block, e1, e2, l₁, h₁, m₁, Ku₁.gpr (by decide), L.a7, hK, I.rest b (by omega) hk,
        blockOut_eq]
    · rw [other b (by omega) hbk]; exact I.done b (by omega)
  · rw [other b h2 (by omega)]; exact I.rest b (by omega) h2
  · rw [m₃]
    refine I.frame.trans ?_
    rw [← m₁, ← m₂]
    exact (stored_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subK⟩

/-! ## Two blocks -/

/-- The big-endian word at offset `o` of the block at `q + 8`. -/
theorem beWord_block8 (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    beWord m q (8 + o) = decodeWord (blockAt m (q + 8#64)) o := by
  refine word_ext fun b hb => ?_
  rw [beWord_byte _ _ _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega),
    show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    Offset.add_add_eq _ (show 8 + (o + (3 - b)) = 8 + o + (3 - b) by omega)]

/-- The block at `a1 + 8` into block B's halves. -/
theorem loadHalves2_run (u : State) {q : Addr} (hq : u.gpr .a1 = q)
    (r : InRegions (u.rd ++ u.wr) q 16) :
    WP isa (.block (loadBE32 xL2 tmp ptr 8 ++ loadBE32 xR2 tmp ptr 12)) u fun t =>
      lo (t.gpr .s1) = decodeWord (blockAt u.mem (q + 8#64)) 0 ∧
      lo (t.gpr .s2) = decodeWord (blockAt u.mem (q + 8#64)) 4 ∧
        Keep [.s1, .s2, .t4] u t ∧ t.mem = u.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (loadBE32_ok (d := .s1) (tmp := .t4) (n := .a1) (off := 8) (by decide) (by decide)
    (by decide) (by decide) (by rw [hq]; exact CallLay.inRegions_sub r (by decide) (by decide)))
    fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (loadBE32_ok (d := .s2) (tmp := .t4) (n := .a1) (off := 12) (by decide) (by decide)
    (by decide) (by decide) (by
      simp only [RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub r (by decide) (by decide))) fun u₂ e₂ => ?_
  subst e₂
  refine ⟨?_, ?_, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, hq,
      ← beWord_block8 _ _ (o := 0) (by decide)]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, lo_ext, RegUpd.mem_write, hq,
      ← beWord_block8 _ _ (o := 4) (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The two blocks at `a1` into the halves. -/
theorem loadBlock2_run (u : State) {q : Addr} (hq : u.gpr .a1 = q)
    (r : InRegions (u.rd ++ u.wr) q 16) :
    WP isa (.block loadBlock2) u fun t =>
      lo (t.gpr .a3) = decodeWord (blockAt u.mem q) 0 ∧ lo (t.gpr .a4) = decodeWord (blockAt u.mem q) 4 ∧
      lo (t.gpr .s1) = decodeWord (blockAt u.mem (q + 8#64)) 0 ∧
      lo (t.gpr .s2) = decodeWord (blockAt u.mem (q + 8#64)) 4 ∧
        Keep [.a3, .a4, .s1, .s2, .t4] u t ∧ t.mem = u.mem := by
  unfold loadBlock2
  rw [List.append_assoc, WP.block_append_iff]
  have r8 : InRegions (u.rd ++ u.wr) q 8 := by
    have h := CallLay.inRegions_sub (off := 0) (l := 8) r (by decide) (by decide)
    rwa [BitVec.add_zero] at h
  refine WP.mono (loadBlock_run u hq r8) fun u₁ ⟨l₁, h₁, k₁, m₁⟩ => ?_
  refine WP.mono (loadHalves2_run u₁ (q := q) (by rw [k₁.gpr (by decide), hq]) (by rw [keep_reads k₁]; exact r))
    fun t ⟨l₂, h₂, k₂, m₂⟩ => ?_
  refine ⟨?_, ?_, by rw [l₂, m₁], by rw [h₂, m₁], (k₁.trans k₂).mono (by decide), m₂.trans m₁⟩
  · rw [k₂.gpr (by decide), l₁]
  · rw [k₂.gpr (by decide), h₁]

/-- Block B's halves to the block at `a1 + 8`. -/
theorem storeHalves2_run (u : State) {q : Addr} (hq : u.gpr .a1 = q) (w : InRegions u.wr q 16) :
    WP isa (.block (storeBE 4 xL2 tmp ptr 8 ++ storeBE 4 xR2 tmp ptr 12)) u fun t =>
      t.mem = writeBytes u.mem (q + 8#64) (beBytes 4 (u.gpr .s1) ++ beBytes 4 (u.gpr .s2)) ∧
      Keep [.t4] u t := by
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (v := .s1) (tmp := .t4) (n := .a1) (off := 8) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [hq]; exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeBE_ok (v := .s2) (tmp := .t4) (n := .a1) (off := 12) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      simp only [RegUpd.gpr_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₂ e₂ => ?_
  subst e₂
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · have h := WriteBytes.writeBytes_append u.mem (q + BitVec.ofNat 64 8) (beBytes 4 (u.gpr .s1))
      (beBytes 4 (u.gpr .s2)) (by simp only [beBytes_length]; decide)
    rw [beBytes_length, Offset.add_add] at h
    simp only [RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_false, hq]
    exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-- The halves to the two blocks at `a1`, the next pair's pointer, and the
counter less two. -/
theorem storeBlock2_run (u : State) {q : Addr} (hq : u.gpr .a1 = q) (w : InRegions u.wr q 16) :
    WP isa (.block storeBlock2) u fun t =>
      t.mem = writeBytes (writeBytes u.mem q (beBytes 4 (u.gpr .a3) ++ beBytes 4 (u.gpr .a4))) (q + 8#64)
        (beBytes 4 (u.gpr .s1) ++ beBytes 4 (u.gpr .s2)) ∧
      t.gpr .a1 = q + 16#64 ∧ t.gpr .a2 = u.gpr .a2 - 2#64 ∧ Keep [.t4, .a1, .a2] u t := by
  unfold storeBlock2
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (storeBE_ok (v := .a3) (tmp := .t4) (n := .a1) (off := 0) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      rw [hq]; exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeBE_ok (v := .a4) (tmp := .t4) (n := .a1) (off := 4) (w := 4) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun j hj => by
      simp only [RegUpd.gpr_write, RegUpd.wr_write, reduceCtorEq, ite_false, hq]
      exact CallLay.inRegions_sub w (by omega) (by decide)) fun u₂ e₂ => ?_
  subst e₂
  have hA := WriteBytes.writeBytes_append u.mem q (beBytes 4 (u.gpr .a3)) (beBytes 4 (u.gpr .a4)) (by
    simp only [beBytes_length]; decide)
  rw [beBytes_length] at hA
  rw [← List.append_assoc, WP.block_append_iff]
  let v := { { u with mem := writeBytes u.mem (u.gpr .a1 + BitVec.ofNat 64 0) (beBytes 4 (u.gpr .a3)) }.write
      .t4 (u.gpr .a3) with
    mem := writeBytes (writeBytes u.mem (u.gpr .a1 + BitVec.ofNat 64 0) (beBytes 4 (u.gpr .a3)))
      (u.gpr .a1 + BitVec.ofNat 64 4) (beBytes 4 (u.gpr .a4)) }.write .t4 (u.gpr .a4)
  have vm : v.mem = writeBytes u.mem q (beBytes 4 (u.gpr .a3) ++ beBytes 4 (u.gpr .a4)) := by
    simp only [v, RegUpd.mem_write, hq, BitVec.add_zero]; exact hA
  have vg : ∀ r, r ≠ .t4 → v.gpr r = u.gpr r := fun r hr => by
    simp only [v, RegUpd.gpr_write, hr, ite_false]
  refine WP.mono (storeHalves2_run v (q := q) (by rw [vg _ (by decide), hq]) (by
    simp only [v, RegUpd.wr_write]; exact w)) fun x ⟨xm, xk⟩ => ?_
  have x1 : x.gpr .a1 = q := by rw [xk.gpr (by decide), vg _ (by decide), hq]
  refine WP.mono (WP.keep [.a1, .a2] (Q := fun t => t.gpr .a1 = q + 16#64 ∧ t.gpr .a2 = x.gpr .a2 - 2#64 ∧
      t.mem = x.mem) (by brun [x1]) (by decide) rfl) fun t ⟨⟨t1, t2, tm⟩, tk⟩ => ⟨?_, t1, ?_, ?_⟩
  · rw [tm, xm, vm, vg _ (by decide), vg _ (by decide)]
  · rw [t2, xk.gpr (by decide), vg _ (by decide)]
  · refine ⟨fun r hr => ?_, tk.2.1.trans (xk.2.1.trans ?_), tk.2.2.trans (xk.2.2.trans ?_)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [tk.gpr (by simp [hr.2.1, hr.2.2]), xk.gpr (by simp [hr.1]), vg _ hr.1]
    · simp only [v, RegUpd.rd_write]
    · simp only [v, RegUpd.wr_write]

/-- `t1 := cnt >> 1`, the pairs left. -/
theorem pairsLeft_run (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr .a2 = BitVec.ofNat 64 k) :
    WP isa (.block [pairsLeft]) u fun t => t.gpr .t1 = BitVec.ofNat 64 (k / 2) ∧ t.mem = u.mem := by
  have e : BitVec.ofNat 64 k >>> 1 = BitVec.ofNat 64 (k / 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  unfold pairsLeft
  brun [h, e]

/-- The body of the pairs' loop. -/
abbrev pairBody (up : Bool) : Prog isa :=
  .seq (.block loadBlock2) (.seq (cipher2 up) (.block (storeBlock2 ++ [pairsLeft])))

theorem pair_step {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) {k : Nat}
    (hk : k + 2 ≤ n) {u : State} (I : EInv S D n up s₀ k u) :
    WP isa (pairBody up) u
      (fun u' => EInv S D n up s₀ (k + 2) u' ∧ u'.gpr .t1 = BitVec.ofNat 64 ((n - (k + 2)) / 2)) := by
  have fit := L.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.keep.2.2]; exact L.data
  have inD : InRegions u.wr (wAt D k) 16 :=
    ⟨_, dR, Offset.contains_base D (by omega) (by omega)⟩
  have inD' : InRegions (u.rd ++ u.wr) (wAt D k) 16 :=
    let ⟨r, hr, hc⟩ := inD; ⟨r, List.mem_append_right _ hr, hc⟩
  have e8 : wAt D k + 8#64 = wAt D (k + 1) := by
    rw [wAt, wAt, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; congr 2
  apply WP.seq
  refine WP.mono (loadBlock2_run u I.ptr inD') fun u₁ ⟨l₁, h₁, l₁', h₁', k₁, m₁⟩ => ?_
  have hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have Ku₁ : Keep loopRegs s₀ u₁ := (I.keep.trans k₁).mono (by decide)
  have E : LookEnv u₁ := by
    refine ⟨fun o ha ho => ?_, fun o ha ho => ?_, by rw [Ku₁.gpr (by decide), L.a7]; exact L.al,
      by rw [Ku₁.gpr (by decide), L.a7]; exact L.al8⟩
    · rw [Ku₁.gpr (by decide), L.a7, Ku₁.2.1, Ku₁.2.2]
      exact L.key o ha ho
    · rw [Ku₁.gpr (by decide), L.a7, Ku₁.2.1, Ku₁.2.2]
      exact L.key8 o ha ho
  apply WP.seq
  refine WP.mono (cipher2_run E up) fun u₂ ⟨c₂, c₂', k₂, m₂⟩ => ?_
  have Ku₂ : Keep loopRegs s₀ u₂ := (Ku₁.trans k₂).mono (by decide)
  have wr₂ : u₂.wr = u.wr := by rw [k₂.2.2, k₁.2.2]
  have p₂ : u₂.gpr .a1 = wAt D k := by rw [k₂.gpr (by decide), k₁.gpr (by decide), I.ptr]
  rw [WP.block_append_iff]
  refine WP.mono (storeBlock2_run u₂ p₂ (by rw [wr₂]; exact inD)) fun u₃ ⟨m₃, p₃, c₃, k₃⟩ => ?_
  have hc₂ : u₂.gpr .a2 = BitVec.ofNat 64 (n - k) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), I.cnt]
  have c₃' : u₃.gpr .a2 = BitVec.ofNat 64 (n - (k + 2)) := by
    rw [c₃, hc₂]; apply BitVec.eq_of_toNat_eq; simp; omega
  refine WP.mono (WP.keep [.t1] (pairsLeft_run u₃ (by omega) c₃') (by decide) rfl)
    fun u₄ ⟨⟨t₄, m₄⟩, k₄⟩ => ?_
  -- The memory after the stores.
  let M₁ := writeBytes u₂.mem (wAt D k) (beBytes 4 (u₂.gpr .a3) ++ beBytes 4 (u₂.gpr .a4))
  have f₁ := stored_frame u₂.mem (wAt D k) (u₂.gpr .a3) (u₂.gpr .a4)
  have f₂ := stored_frame M₁ (wAt D k + 8#64) (u₂.gpr .s1) (u₂.gpr .s2)
  have mem₄ : u₄.mem = writeBytes M₁ (wAt D k + 8#64) (beBytes 4 (u₂.gpr .s1) ++ beBytes 4 (u₂.gpr .s2)) := by
    rw [m₄, m₃]
  have subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have subK' : Region.Sub ⟨wAt D k + 8#64, 8⟩ ⟨D, 8 * n⟩ := by rw [e8]; exact Offset.sub_base D (by omega)
  have other : ∀ b, b < n → b ≠ k → b ≠ k + 1 → blockAt u₄.mem (wAt D b) = blockAt u.mem (wAt D b) :=
    fun b hb hne hne' => by
      rw [mem₄, blockAt_frame f₂ fun r hr => ?_, blockAt_frame f₁ fun r hr => ?_, m₂, m₁]
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (by omega) (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        rw [e8]; exact Offset.disjoint D (by omega) (by omega) (by omega)
  have Ku₄ : Keep loopRegs s₀ u₄ := ((Ku₂.trans k₃).trans k₄).mono (by decide)
  refine ⟨⟨by omega, ?_, by rw [k₄.gpr (by decide), c₃'], Ku₄, fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, t₄⟩
  · rw [k₄.gpr (by decide), p₃, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, wAt, wAt,
      Offset.add_add]
    congr 2
  · have e0 : u₁.gpr .a7 = S := by rw [Ku₁.gpr (by decide), L.a7]
    by_cases hbk : b = k
    · subst hbk
      have e1 := congrArg Prod.fst c₂
      have e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      rw [mem₄, blockAt_frame f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [e8]; exact Offset.disjoint D (by omega) (by omega) (by omega),
        stored_block, e1, e2, l₁, h₁, m₁, e0, hK, I.rest b (by omega) (by omega), blockOut_eq]
    · by_cases hbk' : b = k + 1
      · subst hbk'
        have e1 := congrArg Prod.fst c₂'
        have e2 := congrArg Prod.snd c₂'
        simp only at e1 e2
        rw [mem₄, ← e8, stored_block, e1, e2, l₁', h₁', m₁, e0, hK, e8, I.rest (k + 1) (by omega) (by omega),
          blockOut_eq]
      · rw [other b (by omega) hbk hbk']; exact I.done b (by omega)
  · rw [other b h2 (by omega) (by omega)]; exact I.rest b (by omega) h2
  · rw [mem₄]
    refine I.frame.trans ?_
    rw [← m₁, ← m₂]
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subK⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subK'⟩

/-- The pairs, while two blocks are left. -/
theorem pairs_run {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀)
    {u : State} (I : EInv S D n up s₀ 0 u) (h1 : u.gpr .t1 = BitVec.ofNat 64 (n / 2)) :
    WP isa (.ite (.zero .t1) (.block []) (.loop (pairBody up) (.nonzero .t1))) u
      (fun v => ∃ k, n - k < 2 ∧ EInv S D n up s₀ k v) := by
  have hn64 : n < 2 ^ 64 := by have := L.fit; omega
  refine WP.ite (u.gpr .t1 == 0) (by rw [Steps.eval_zero]) (fun hz => WP.block_nil ⟨0, ?_, I⟩) (fun hz => ?_)
  · rw [h1, Steps.ofNat_beq_zero (by omega)] at hz
    have := of_decide_eq_true hz
    omega
  rw [h1, Steps.ofNat_beq_zero (by omega)] at hz
  have hz' := of_decide_eq_false hz
  refine WP.loop (M := isa) (Q := fun v => ∃ k, n - k < 2 ∧ EInv S D n up s₀ k v)
    (fun m v => ∃ k, k + 2 ≤ n ∧ m = (n - k) / 2 ∧ EInv S D n up s₀ k v) ?_ (n / 2) u
    ⟨0, by omega, by omega, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (pair_step L hk J) fun v' ⟨J', hz⟩ => ?_
  rw [Steps.eval_nonzero, hz, ofNat_bne_zero' (by omega)]
  by_cases e : (n - (k + 2)) / 2 = 0
  · left
    exact ⟨by simp [e], k + 2, by omega, J'⟩
  · right
    exact ⟨by simp [e], (n - (k + 2)) / 2, by omega, k + 2, by omega, rfl, J'⟩

/-- The last block, if one is left. -/
theorem last_run {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) {k : Nat}
    (hk : n - k < 2) {u : State} (I : EInv S D n up s₀ k u) :
    WP isa (.ite (.zero cnt) (.block []) (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock)))) u
      (EInv S D n up s₀ n) := by
  have hn64 : n < 2 ^ 64 := by have := L.fit; omega
  refine WP.ite (u.gpr .a2 == 0) (by rw [cnt, Steps.eval_zero]) (fun hz => WP.block_nil ?_) (fun hz => ?_)
  · rw [I.cnt, Steps.ofNat_beq_zero (by omega)] at hz
    have := of_decide_eq_true hz
    have e : k = n := by have := I.le; omega
    exact e ▸ I
  · rw [I.cnt, Steps.ofNat_beq_zero (by omega)] at hz
    have := of_decide_eq_false hz
    have e : k + 1 = n := by have := I.le; omega
    exact WP.mono (ecb_step L (by omega) I) fun v ⟨J, _⟩ => e ▸ J

/-! ## The frame holding the schedule -/

/-- A schedule copied byte for byte. -/
theorem scheduleAt_copy {m m' : Mem} {p q : Addr}
    (h : ∀ i < 4168, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    scheduleAt m' q = scheduleAt m p := by
  apply Vector.ext; intro i hi
  simp only [scheduleAt, Vector.getElem_ofFn]
  split
  · rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
  · rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- `Region.Disjoint` as `Mem.Sep`. -/
theorem sep_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) : Mem.Sep r₁.base r₁.len r₂.base r₂.len :=
  fun x hx hy => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- What the frame's body may assume: the schedule readable, the `n` blocks
writable, apart from each other and from the 4176 bytes below the stack
pointer, the blocks not wrapping around. -/
structure MainPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 4168⟩]
  wr : (⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩ : Region) ∈ s.wr
  keyData : (⟨s.gpr .a0, 4168⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 4176 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a0, 4168⟩
  stackData : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

/-- The schedule's length, as `slli` builds it. -/
theorem shl_4168 : BitVec.ofNat 64 1042 <<< 2 = BitVec.ofNat 64 4168 := by decide

theorem main_wp (up : Bool) {s : State} (h : MainPre s) (hn : 0 < (s.gpr .a2).toNat) :
    WP isa (inFrame (ecbMain up)) s fun s' => (∀ b < (s.gpr .a2).toNat,
      blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockOut (scheduleAt s.mem (s.gpr .a0)) up (blockAt s.mem (wAt (s.gpr .a1) b))) ∧
      Frame [⟨s.sp - 4176, 4176⟩, ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩] s.mem s'.mem := by
  have fit := h.fit
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  have hF : (frameBase s) = s.sp - 4176 := frameBase_eq s
  have hFal : (frameBase s).toNat % 16 = 0 := frameBase_al s h.al h.sp
  refine inFrame_wp h.sp ?_
  unfold ecbMain
  -- The frame, and the schedule's length.
  apply WP.seq
  refine WP.mono (WP.keep [.a7, .t0, .t4] (Q := fun t => t.gpr .a7 = (frameBase s) ∧ t.gpr .t0 = (frameBase s) ∧
      t.gpr .t4 = BitVec.ofNat 64 4168 ∧ t.mem = s.mem) (by
    unfold li4168
    brun [inner_sp, inner_mem, shl_4168]
    all_goals rfl) (by decide) rfl) fun a ⟨⟨a7, a0, a4, am⟩, ak⟩ => ?_
  have ag : ∀ r, r ∉ [Reg.a7, .t0, .t4] → a.gpr r = s.gpr r := fun r hr => ak.gpr hr
  have ard : a.rd = s.rd := ak.2.1
  have awr : a.wr = (inner s).wr := ak.2.2
  -- The schedule copied into the frame.
  apply WP.seq
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .a0) (dst := .t0) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) a (N := 4168) (by decide) (by decide) a4
    (fun i hi => ⟨⟨s.gpr .a0, 4168⟩, by rw [ard, h.rd]; simp,
      by rw [ag _ (by decide)]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [awr, a0]; exact frame_in s (by omega) (by omega))
    (by
      rw [a0, ag _ (by decide)]
      intro x hx hy
      have hx' : (x - (s.sp - BitVec.ofNat 64 4176)).toNat < 4176 := by rw [← frameBase_eq]; omega
      exact sep_of_disjoint h.stackKey x hx' hy))
    fun c ⟨cc, cf, ck⟩ => ?_
  rw [a0, ag .a0 (by decide), am] at cc
  rw [a0, am] at cf
  have cg : ∀ r, r ∉ [Reg.t1, .a0, .t0, .t4] → r ∉ [Reg.a7, .t0, .t4] → c.gpr r = s.gpr r :=
    fun r h1 h2 => (ck.gpr h1).trans (ag r h2)
  have c7 : c.gpr .a7 = (frameBase s) := (ck.gpr (by decide)).trans a7
  have cwr : c.wr = (inner s).wr := ck.2.2.trans awr
  have hdata : ∀ b < n, blockAt c.mem (wAt D b) = blockAt s.mem (wAt D b) := fun b hb =>
    blockAt_frame cf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.stackData.sub_left (r₁' := ⟨(frameBase s), 4168⟩) (by rw [hF]; exact Region.sub_prefix (by decide))).sub_right
        (r₂' := ⟨wAt D b, 8⟩) (Offset.sub_base _ (by omega))).symm
  have hK : scheduleAt c.mem (frameBase s) = scheduleAt s.mem (s.gpr .a0) := scheduleAt_copy cc
  -- The blocks.
  have L : LoopEnv (frameBase s) D n c := by
    refine ⟨c7, by omega, by omega, fun o ha ho => ?_, fun o ha ho => ?_, ?_, ?_, fit⟩
    · obtain ⟨r, hr, hc⟩ := frame_in s (o := o) (n := 4) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ (by rw [cwr]; exact hr), hc⟩
    · obtain ⟨r, hr, hc⟩ := frame_in s (o := o) (n := 8) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ (by rw [cwr]; exact hr), hc⟩
    · rw [cwr, inner_wr]; simp only [List.mem_cons]; exact .inr (.inr (.inr h.wr))
    · rw [hF]; exact h.stackData.sub_left (Region.sub_prefix (by decide))
  have I0 : EInv (frameBase s) D n up c 0 c :=
    ⟨by omega, by rw [cg .a1 (by decide) (by decide)]; simp [wAt, D],
      by rw [cg .a2 (by decide) (by decide)]; simp [n], Keep.refl _ _,
      fun b hb => absurd hb (by omega), fun _ _ _ => rfl, Frame.refl _ _⟩
  have hn64 : n < 2 ^ 64 := by omega
  apply WP.seq
  refine WP.mono (WP.keep [.t1] (pairsLeft_run c hn64 (by rw [cg .a2 (by decide) (by decide)]; simp [n]))
    (by decide) rfl) fun c' ⟨⟨c1, cm⟩, ck'⟩ => ?_
  have L' : LoopEnv (frameBase s) D n c' := by
    refine ⟨by rw [ck'.gpr (by decide), c7], L.al, L.al8, ?_, ?_, ?_, L.keyData, fit⟩
    · rw [keep_reads ck']; exact L.key
    · rw [keep_reads ck']; exact L.key8
    · rw [ck'.2.2]; exact L.data
  have I0' : EInv (frameBase s) D n up c' 0 c' :=
    ⟨by omega, by rw [ck'.gpr (by decide)]; exact I0.ptr, by rw [ck'.gpr (by decide)]; exact I0.cnt,
      Keep.refl _ _, fun b hb => absurd hb (by omega), fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (pairs_run L' I0' c1) fun d ⟨k, hk, J⟩ => ?_
  apply WP.seq
  refine WP.mono (last_run L' hk J) fun e E => ?_
  -- The frame zeroed.
  have e7 : e.gpr .a7 = (frameBase s) := (E.keep.gpr (by decide)).trans (by rw [ck'.gpr (by decide), c7])
  have ewr : e.wr = (inner s).wr := E.keep.2.2.trans (ck'.2.2.trans cwr)
  unfold wipe
  apply WP.seq
  refine WP.mono (WP.keep [.t1, .t0, .t4] (Q := fun t => t.gpr .t0 = (frameBase s) ∧ t.gpr .t4 = BitVec.ofNat 64 522 ∧
      t.gpr .t1 = 0#64 ∧ t.mem = e.mem) (by brun [e7]) (by decide) rfl) fun f ⟨⟨f0, f4, f1, fm⟩, fk⟩ => ?_
  refine WP.mono (fillLoop_ok (v := .t1) (ptr := .t0) (cnt := .t4) (by decide) (by decide) (by decide) f
    (N := 522) (by decide) (by decide) f4 (by rw [f0]; omega)
    (fun i hi => by rw [fk.2.2, ewr, f0]; exact frame_in s (by omega) (by omega)))
    fun t ⟨_, tf, _⟩ => ⟨fun b hb => ?_, ?_⟩
  · rw [f0, fm] at tf
    show blockAt t.mem (wAt D b) = _
    rw [blockAt_frame tf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((h.stackData.sub_left (r₁' := ⟨(frameBase s), 8 * 522⟩) (by rw [hF]; exact Region.sub_prefix (by decide))).sub_right
          (r₂' := ⟨wAt D b, 8⟩) (Offset.sub_base _ (by omega))).symm,
      E.done b hb, cm, hK, hdata b hb]
  · rw [f0, fm] at tf
    rw [← cm] at cf
    show Frame _ s.mem t.mem
    refine ((cf.sub fun r hr => ?_).trans (E.frame.sub fun r hr => ?_)).trans (tf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by rw [← hF]; exact Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun x hx => hx⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by rw [← hF]; exact Region.sub_prefix (by decide)⟩

/-! ## The function -/

/-- What ECB may assume: the schedule readable, the `n` blocks writable,
apart from each other and from the 4256 bytes below the stack pointer (the
saved registers' frame and the schedule's), the blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 4168⟩]
  wr : s.wr = [⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩]
  keyData : (⟨s.gpr .a0, 4168⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 4256 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 4256, 4256⟩ : Region).Disjoint ⟨s.gpr .a0, 4168⟩
  stackData : (⟨s.sp - 4256, 4256⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

theorem save_eq : (Instr.addSp rowPtr 0 :: saved.map fun (r, d) => Instr.store .d r rowPtr d) =
    ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved := rfl

theorem restore_eq : (Instr.addSp rowPtr 0 :: saved.map fun (r, d) => Instr.load .d r rowPtr d) =
    ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 saved := rfl

theorem saved_ok : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide
theorem saved_in : ∀ p ∈ saved, 0 ≤ p.2 ∧ p.2 + 8 ≤ 0 + 80 := by decide
theorem saved_t0 : ∀ p ∈ saved, p.1 ≠ .t0 := by decide

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Blowfish.RISCV64.ecb up) s fun s' => (∀ b < (s.gpr .a2).toNat,
      blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockOut (scheduleAt s.mem (s.gpr .a0)) up (blockAt s.mem (wAt (s.gpr .a1) b))) ∧
      ∀ p ∈ saved, s'.gpr p.1 = s.gpr p.1 := by
  have fit := h.fit
  have hsp := h.sp
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  unfold Impl.Blowfish.RISCV64.ecb
  refine WP.ite (s.gpr .a2 == 0) (by rw [cnt, Steps.eval_zero]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .a2).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨fun b hb => absurd hb (by omega), fun _ _ => rfl⟩
  have hn : 0 < n := by
    have : s.gpr .a2 ≠ 0 := by simpa using hz
    have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  -- The saved registers' frame, at `B`, above the schedule's, at `P`.
  let B := s.sp - BitVec.ofNat 64 80
  let P := s.sp - BitVec.ofNat 64 4256
  have hB : B.toNat = s.sp.toNat - 80 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  have eB : B = P + BitVec.ofNat 64 4176 := by
    apply BitVec.eq_of_toNat_eq
    simp only [B, P, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have eP : B - (4176 : BitVec 64) = P := by
    show B - BitVec.ofNat 64 4176 = P; rw [eB, BitVec.add_sub_cancel]
  have sB : Region.Sub ⟨B, 80⟩ ⟨P, 4256⟩ := by rw [eB]; exact Offset.sub_base P (by omega)
  have dB : (⟨B, 80⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * n⟩ := h.stackData.sub_left sB
  have dK : (⟨B, 80⟩ : Region).Disjoint ⟨s.gpr .a0, 4168⟩ := h.stackKey.sub_left sB
  refine WP.alloc (n := savedBytes) (by decide) (by unfold savedBytes; omega) ?_
  -- The registers saved.
  apply WP.seq
  rw [save_eq, WP.block_append_iff]
  have asp : (allocd savedBytes s).sp = B := rfl
  have amem : (allocd savedBytes s).mem = s.mem := rfl
  refine WP.mono (WP.rdwr (WP.keep [.t0] (Q := fun t => t.gpr .t0 = B ∧ t.mem = s.mem) (by
    brun [asp, amem]) (by decide) rfl)) fun a ⟨⟨⟨a0, am⟩, ak⟩, ard, awr, asp'⟩ => ?_
  have ag : ∀ r, r ≠ .t0 → a.gpr r = s.gpr r := fun r hr => ak.gpr (by simp [hr])
  have awr' : a.wr = ⟨B, 80⟩ :: s.wr := awr
  have hBal : B.toNat % 16 = 0 := by rw [hB]; have := h.al; omega
  refine Spill.save_ok (b := .t0) (by rw [a0]; omega) saved_ok (fun p hp => ?_) ?_
  · have := saved_in p hp
    rw [awr', a0]
    exact ⟨_, List.mem_cons_self, Offset.contains_base B (by omega) (by omega)⟩
  rw [a0]
  let Ms := Spill.saveMem a.mem B a.gpr saved
  have fs : Frame [⟨B, 80⟩] s.mem Ms := by
    rw [← am]
    exact Spill.saveMem_frame_base (fun p hp => (saved_in p hp).2) (by decide) _ _ _
  let b : State := { a with mem := Ms }
  have bg : ∀ r, r ≠ .t0 → b.gpr r = s.gpr r := ag
  have hb : MainPre b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show a.rd = _; rw [ard, bg _ (by decide)]; exact h.rd
    · show _ ∈ a.wr
      rw [awr', bg _ (by decide), bg _ (by decide), h.wr]; simp
    · rw [bg _ (by decide), bg _ (by decide), bg _ (by decide)]; exact h.keyData
    · rw [bg _ (by decide), bg _ (by decide)]; exact fit
    · show a.sp.toNat % 16 = 0; rw [asp', asp]; exact hBal
    · show 4176 ≤ a.sp.toNat; rw [asp', asp, hB]; omega
    · show (⟨a.sp - _, _⟩ : Region).Disjoint _
      rw [asp', asp, eP, bg _ (by decide)]; exact h.stackKey.sub_left (Region.sub_prefix (by decide))
    · show (⟨a.sp - _, _⟩ : Region).Disjoint _
      rw [asp', asp, eP, bg _ (by decide), bg _ (by decide)]; exact h.stackData.sub_left (Region.sub_prefix (by decide))
  have hbn : 0 < (b.gpr .a2).toNat := by rw [bg _ (by decide)]; exact hn
  refine WP.block_nil ?_
  apply WP.seq
  refine WP.mono (WP.rdwr (main_wp up hb hbn)) fun e ⟨⟨eblk, efr⟩, erd, ewr, esp⟩ => ?_
  -- The registers restored.
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = e.sp ∧ t.mem = e.mem) (by brun) (by decide) rfl)
    fun e₁ ⟨⟨e0, em⟩, ek⟩ => ?_
  have eB' : e.sp = B := by rw [esp]; exact asp'.trans asp
  have hsv : Spill.Saved B a.gpr saved e₁.mem := by
    rw [em]
    refine (Spill.saveMem_saved (by decide) a.mem B a.gpr).frame_in saved_in efr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · show (⟨B + BitVec.ofNat 64 0, 80⟩ : Region).Disjoint ⟨a.sp - _, _⟩
      rw [asp', asp, eP, BitVec.add_zero, eB]
      exact Offset.disjoint_base P (by decide) (by have := P.isLt; omega)
    · rw [BitVec.add_zero, bg _ (by decide), bg _ (by decide)]; exact dB
  refine WP.mono (Spill.restore_wp (B := B) (by omega) (by rw [e0, eB']) saved_ok (by decide) (fun p hp => ?_)
    hsv) fun t R => ⟨fun i hi => ?_, fun p hp => ?_⟩
  · have := saved_in p hp
    rw [ek.2.1, ek.2.2, ewr]
    exact ⟨_, List.mem_append_right _ (by show _ ∈ a.wr; rw [awr']; exact List.mem_cons_self),
      Offset.contains_base B (by omega) (by omega)⟩
  · show blockAt t.mem _ = _
    have := eblk i (by rw [bg _ (by decide)]; exact hi)
    rw [bg _ (by decide), bg _ (by decide)] at this
    rw [R.mem, em, this]
    show blockOut (scheduleAt Ms _) up (blockAt Ms _) = _
    rw [scheduleAt_eq_of_frame _ fs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dK.symm,
      blockAt_frame fs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dB.sub_right (r₂' := ⟨wAt D i, 8⟩) (Offset.sub_base _ (by omega))).symm]
  · show t.gpr p.1 = _
    rw [R.gpr p hp, ag _ (saved_t0 p hp)]

end VG.Proof.Blowfish.RISCV64
