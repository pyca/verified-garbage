module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbLoops
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbKernel
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Divstep.WordBasic

/-!
# The batched inverse on PPC64LE: its operations on arrays

In the key operations' working space (`Ws`), with `n` and the batches left
`c` in `r10` (`Ctx`): each operation of `Impl/Rsa/PPC64LE/InvBatch.lean` on
`n + 1` (or `n + 2`) digits of arrays, signed numbers read by `sv` (the low
digits and a signed top digit).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop subBody selBody copyBody seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (loopRegs Ahead)

/-! ## The context -/

/-- The working space, and `n` and the count `c` in `r10`. -/
structure Ctx (s : State) (B : Addr) (Z w N n c : Nat) : Prop where
  ws : Ws s B Z w N
  r10 : s.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * c)
  npos : 1 ≤ n
  nw : n ≤ w
  room : 15 ≤ N
  cb : c < 2 ^ 40
  wbig : 10 ≤ w

theorem Ctx.of_keep {s t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c)
    (k : Keep kRegs s t) : Ctx t B Z w N n c :=
  ⟨h.ws.of_keep k, (k.gpr _ (by decide)).trans h.r10, h.npos, h.nw, h.room, h.cb, h.wbig⟩

theorem Ctx.nlt {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) : n < 2 ^ 15 := by
  have := h.nw; have := h.ws.wle; omega

theorem cnt_eq {n c : Nat} (hn : n < 2 ^ 15) :
    (BitVec.ofNat 64 (n + 2 ^ 15 * c) <<< 49) >>> 49 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem Ctx.cnt {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) :
    (s.gpr .r10 <<< 49) >>> 49 = BitVec.ofNat 64 n := by
  rw [h.r10]; exact cnt_eq h.nlt

/-- An array's address, as `ptr` computes it. -/
theorem Ctx.ptr {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) (j : Nat) :
    BitVec.ofNat 64 j * s.gpr .r30 + s.gpr .r31 + BitVec.ofNat 64 KeyWorkspace.hdr = off B (arr w j) := by
  rw [h.ws.r30, h.ws.r31]; exact ptr_val _ _ _

/-! ## Signed numbers -/

/-- `k + 1` digits at `d`, the top one signed. -/
def sv (m : Mem) (B : Addr) (d k : Nat) : Int :=
  (val32 m B d k : Int) + 2 ^ (32 * k) * (m.readW (off B (d + 4 * k)) 32).toInt

theorem toInt_cond (x : BitVec 32) : (x.toInt : Int) = x.toNat - if 2 ^ 31 ≤ x.toNat then 2 ^ 32 else 0 := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> split <;> omega

/-- The digits read unsigned. -/
theorem val_sv (m : Mem) (B : Addr) (d k : Nat) :
    (val32 m B d (k + 1) : Int) = sv m B d k +
      2 ^ (32 * (k + 1)) * (if 2 ^ 31 ≤ w32 m B (d + 4 * k) then 1 else 0) := by
  rw [sv, val32_succ, toInt_cond, show 32 * (k + 1) = 32 * k + 32 by omega, Int.pow_add]
  push_cast
  split <;> grind

theorem sv_range (m : Mem) (B : Addr) (d k : Nat) :
    -2 ^ (32 * k + 31) ≤ sv m B d k ∧ sv m B d k < 2 ^ (32 * k + 31) := by
  have hv := val32_lt m B d k
  have ht1 := (m.readW (off B (d + 4 * k)) 32).toInt_le
  have ht2 := (m.readW (off B (d + 4 * k)) 32).le_toInt
  rw [sv, Int.pow_add]
  generalize (m.readW (off B (d + 4 * k)) 32).toInt = T at ht1 ht2 ⊢
  have hP : (0 : Int) < 2 ^ (32 * k) := by exact_mod_cast Nat.two_pow_pos _
  have hv' : (val32 m B d k : Int) < 2 ^ (32 * k) := by exact_mod_cast hv
  generalize (2 : Int) ^ (32 * k) = P at hP hv' ⊢
  have ht1' : T ≤ 2 ^ 31 - 1 := by simpa using ht1
  have ht2' : -2 ^ 31 ≤ T := by simpa using ht2
  constructor
  · have := Int.mul_le_mul_of_nonneg_left ht2' (Int.le_of_lt hP); grind
  · have := Int.mul_le_mul_of_nonneg_left ht1' (Int.le_of_lt hP); grind

/-- A multiple of `H > 0` strictly between `-H` and `H` is zero. -/
theorem mul_small {H d : Int} (hH : 0 < H) (h1 : -H < H * d) (h2 : H * d < H) : d = 0 := by
  rcases Int.lt_trichotomy d 0 with hd | hd | hd
  · have := Int.mul_le_mul_of_nonneg_left (show d ≤ -1 by omega) (Int.le_of_lt hH); omega
  · exact hd
  · have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ d by omega) (Int.le_of_lt hH); omega

/-- A signed number from the unsigned digits of it, plus a multiple of
`2^(32 (k + 1))`. -/
theorem sv_of_eq {m : Mem} {B : Addr} {d k : Nat} {z q : Int}
    (h : (val32 m B d (k + 1) : Int) = z + 2 ^ (32 * (k + 1)) * q)
    (hz1 : -2 ^ (32 * k + 31) ≤ z) (hz2 : z < 2 ^ (32 * k + 31)) : sv m B d k = z := by
  have e := val_sv m B d k
  have r := sv_range m B d k
  rw [e] at h
  have eP : (2 : Int) ^ (32 * (k + 1)) = 2 * 2 ^ (32 * k + 31) := by
    rw [show 32 * (k + 1) = (32 * k + 31) + 1 by omega, Int.pow_succ, Int.mul_comm]
  have hH : (0 : Int) < 2 ^ (32 * k + 31) := by exact_mod_cast Nat.two_pow_pos _
  rw [eP] at h
  generalize (2 : Int) ^ (32 * k + 31) = H at h hz1 hz2 r hH
  generalize sv m B d k = x at h r ⊢
  generalize (if 2 ^ 31 ≤ w32 m B (d + 4 * k) then (1 : Int) else 0) = b at h
  have h0 : (2 * H) * (b - q) = z - x := by grind
  have := mul_small (H := 2 * H) (d := b - q) (by omega) (by omega) (by omega)
  rw [this, Int.mul_zero] at h0
  omega

/-! ## Blocks -/

/-- `ldW r o`: `r` := the window's 64-bit word at `o`. -/
theorem ldW_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {r : Reg} (hr : r ≠ .r0)
    (h30 : r ≠ .r30) (h31 : r ≠ .r31) {o : Nat} (ho : o + 8 ≤ 48) (ho4 : o % 4 = 0) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (s.mem.readW (off B (arr w aW + o)) 64)) Q) :
    WP isa (.block (ldW r o ++ rest)) s Q := by
  have fit := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega)
  have hS : S w = 4 * (w + 2) := rfl
  have := h.ws.wpos
  have := h.wbig
  rw [ldW, List.append_assoc]
  refine ptr_ok h.ws hr h30 h31 (by decide) ?_
  rw [WP.block_append_iff]
  have hl : InRegions ((s.write r (off B (arr w aW))).rd ++ (s.write r (off B (arr w aW))).wr)
      ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o) 8 := by
    simp only [gpr_write, ↓reduceIte, rd_write, wr_write, off_add]
    exact h.ws.scr.ld (d := arr w aW + o) (n := 8) (by omega)
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d hr ⟨by omega, ho4⟩ hl,
    gpr_write, ↓reduceIte, off_add, mem_write, Option.some.injEq, exists_eq_left', write_write]
  exact k

/-- A digit outside the bytes that changed, read as a bit vector. -/
theorem Outside.readW32 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun _ _ => h _ (by rw [ofs_off base (by omega)]; omega)

/-! ## `lin` -/

theorem toInt_low {q : Int} (h1 : -2 ^ 31 ≤ q) (h2 : q < 2 ^ 31) :
    ((BitVec.ofInt 64 q).setWidth 32).toInt = q := by
  have e := Divstep.toNat_ofInt64 q
  rw [toInt_cond, BitVec.toNat_setWidth]
  have := (BitVec.ofInt 64 q).isLt
  split <;> omega

/-- The top digit of `u [a] + v [b]`, both signed, and the carry after it. -/
theorem linTop_ok {s : State} {B : Addr} {Z dO dA dB : Nat} (hs : Scr s B Z) {u v c : Int}
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h9 : s.gpr .r9 = BitVec.ofInt 64 c) (h11 : s.gpr .r11 = BitVec.ofInt 64 u)
    (h12 : s.gpr .r12 = BitVec.ofInt 64 v) (huv : u.natAbs + v.natAbs ≤ 2 ^ 30)
    (hc1 : -2 ^ 31 ≤ c) (hc2 : c ≤ 2 ^ 31) (hO : dO + 8 ≤ Z) (hA : dA + 4 ≤ Z) (hB : dB + 4 ≤ Z) :
    WP isa (.block linTop) s fun t =>
      ((∃ q : Int, -2 ^ 31 ≤ q ∧ q < 2 ^ 31 ∧
        (w32 t.mem B dO : Int) + 2 ^ 32 * q =
          u * (s.mem.readW (off B dA) 32).toInt + v * (s.mem.readW (off B dB) 32).toInt + c ∧
        (t.mem.readW (off B (dO + 4)) 32).toInt = q) ∧ Outside B dO 8 s.mem t.mem) ∧
      Keep [.r0, .r3, .r4, .r9] s t := by
  have hnw := hs.nowrap
  refine WP.keep _ ?_ (by decide)
  prun [linTop, h5, h6, h7, h9, h11, h12, hs.ld (show dA + 4 ≤ Z by omega), hs.ld (show dB + 4 ≤ Z by omega),
    hs.st (show dO + 4 ≤ Z by omega), hs.st (show dO + 4 + 4 ≤ Z by omega), sext_arith]
  have xa1 := (s.mem.readW (off B dA) 32).toInt_le
  have xa2 := (s.mem.readW (off B dA) 32).le_toInt
  have xb1 := (s.mem.readW (off B dB) 32).toInt_le
  have xb2 := (s.mem.readW (off B dB) 32).le_toInt
  generalize (s.mem.readW (off B dA) 32).toInt = X at xa1 xa2 ⊢
  generalize (s.mem.readW (off B dB) 32).toInt = Y at xb1 xb2 ⊢
  obtain ⟨e1, e2, -, -⟩ := lin_arith u v c X Y huv hc1 hc2 (by omega) (by omega) (by omega) (by omega)
  have a : (u * X).natAbs ≤ u.natAbs * 2 ^ 31 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (by omega)
  have b : (v * Y).natAbs ≤ v.natAbs * 2 ^ 31 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (by omega)
  rw [e1]
  refine ⟨⟨(u * X + v * Y + c) / 2 ^ 32, by omega, by omega, ?_, ?_⟩, ?_⟩
  · rw [(writeW32_outside _ B (d := dO + 4) _ (by omega)).w32 (by omega) (by omega), w32_write_self]
    exact e2
  · rw [Mem.readW_writeW_self32]
    exact toInt_low (by omega) (by omega)
  · exact ((writeW32_outside _ B (d := dO) _ (by omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ B (d := dO + 4) _ (by omega)).mono (by omega) (by omega))

/-- Arrays apart are each ahead of the other, for `k ≤ w + 2` digits. -/
theorem ahead_k {w o a k : Nat} (h : o ≠ a) (hk : k ≤ w + 2) : Ahead (arr w o) (arr w a) k := by
  have := arr_disj (w := w) h
  simp only [S] at this
  unfold Ahead; omega

/-- `[o] = c₁ [a] + c₂ [b]` (`lin`), the coefficients `u`, `v` the window's
words at `c₁`, `c₂`. -/
theorem lin_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {c1 c2 o a b : Nat}
    {u v : Int} (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hc1 : c1 + 8 ≤ 48) (hc1' : c1 % 4 = 0) (hc2 : c2 + 8 ≤ 48) (hc2' : c2 % 4 = 0)
    (hu : s.mem.readW (off B (arr w aW + c1)) 64 = BitVec.ofInt 64 u)
    (hv : s.mem.readW (off B (arr w aW + c2)) 64 = BitVec.ofInt 64 v)
    (huv : u.natAbs + v.natAbs ≤ 2 ^ 30) :
    WP isa (lin c1 c2 o a b) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      sv t.mem B (arr w o) (n + 1) = u * sv s.mem B (arr w a) n + v * sv s.mem B (arr w b) n ∧
      Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  rw [lin]; simp only [seqs]; rw [WP.seq_iff]
  -- The pointers, the coefficients, the count and no carry.
  have hb1 : WP isa (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ ldW .r11 c1 ++ ldW .r12 c2 ++ cntN ++
      ([.li .r9 0] : List Instr))) s fun t => Ctx t B Z w N n c ∧ t.mem = s.mem ∧
      t.gpr .r5 = off B (arr w o) ∧ t.gpr .r6 = off B (arr w a) ∧ t.gpr .r7 = off B (arr w b) ∧
      t.gpr .r8 = BitVec.ofNat 64 n ∧ t.gpr .r9 = BitVec.ofInt 64 0 ∧ t.gpr .r11 = BitVec.ofInt 64 u ∧
      t.gpr .r12 = BitVec.ofInt 64 v ∧ Keep kRegs s t := by
    rw [show ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ ldW .r11 c1 ++ ldW .r12 c2 ++ cntN ++
      ([.li .r9 0] : List Instr) = ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++
        (ldW .r11 c1 ++ (ldW .r12 c2 ++ (cntN ++ ([.li .r9 0] : List Instr)))) by simp only [List.append_assoc]]
    refine ptr3_ok h.ws (by omega) (by omega) (by omega) fun t p5 p6 p7 kt mt => ?_
    have ht := h.of_keep (kt.mono (by decide))
    refine ldW_ok ht (by decide) (by decide) (by decide) hc1 hc1' ?_
    refine ldW_ok (ht.of_keep ((Keep.write _ .r11 _).mono (rs' := kRegs) (by decide))) (by decide) (by decide)
      (by decide) hc2 hc2' ?_
    have hc := ht.cnt
    refine WP.mono (WP.keep [.r8, .r9] (Q := fun x => x.gpr .r8 = BitVec.ofNat 64 n ∧
      x.gpr .r9 = BitVec.ofInt 64 0 ∧ x.mem = t.mem) ?_ (by decide)) fun x ⟨⟨x8, x9, xm⟩, kx⟩ => ?_
    · prun [cntN, hc]
      rfl
    have k0 : Keep kRegs s x :=
      (((kt.trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans kx).mono (by decide)
    refine ⟨h.of_keep k0, xm.trans mt, ?_, ?_, ?_, x8, x9, ?_, ?_, k0⟩
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p5
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p6
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact p7
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte, mt]; exact hu
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, ↓reduceIte, mem_write, mt]; exact hv
  refine WP.mono hb1 fun t1 ⟨h1, m1, p5, p6, p7, p8, p9, p11, p12, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (linLoop_ok h1.ws.scr p5 p6 p7 p8 p9 p11 p12 huv (by decide) (by decide) h.npos (by omega)
    (by omega) (by omega) (by omega) (ahead_k hoa (by omega)) (ahead_k hob (by omega)))
    fun t2 ⟨⟨c', hc1', hc2', q9, qeq⟩, q5, q6, q7, out2, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  refine WP.mono (linTop_ok h2.ws.scr q5 q6 q7 q9 ((k2.gpr _ (by decide)).trans p11)
    ((k2.gpr _ (by decide)).trans p12) huv hc1' hc2' (by omega) (by omega) (by omega))
    fun t3 ⟨⟨⟨q, hq1, hq2, qe, qt⟩, out3⟩, k3⟩ => ?_
  have k : Keep kRegs s t3 := (k1.trans' (k2.mono (by decide))).trans' (k3.mono (by decide))
  rw [m1] at qeq out2
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · exact (KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega) (by simp)).trans
      (KeyWorkspace.Keep.of_arr (d := 4 * n) out3 (by omega) (by simp))
  · have da := (arr_disj (w := w) hoa)
    have db := (arr_disj (w := w) hob)
    have xa : t2.mem.readW (off B (arr w a + 4 * n)) 32 = s.mem.readW (off B (arr w a + 4 * n)) 32 :=
      Outside.readW32 out2 (by omega) (by omega)
    have xb : t2.mem.readW (off B (arr w b + 4 * n)) 32 = s.mem.readW (off B (arr w b + 4 * n)) 32 :=
      Outside.readW32 out2 (by omega) (by omega)
    have vo : val32 t3.mem B (arr w o) n = val32 t2.mem B (arr w o) n := out3.val32 (by omega) (by omega)
    rw [xa, xb] at qe
    unfold sv
    rw [show arr w o + 4 * (n + 1) = arr w o + 4 * n + 4 by omega, qt, val32_succ, vo]
    have eP : (2 : Int) ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by
      rw [show 32 * (n + 1) = 32 * n + 32 by omega, Int.pow_add, Int.mul_comm]
    rw [eP]
    push_cast
    generalize (2 : Int) ^ (32 * n) = P at qeq ⊢
    grind

end VG.Proof.Rsa.PPC64LE.InvBatch
