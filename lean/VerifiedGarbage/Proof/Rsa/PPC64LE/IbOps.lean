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

/-- The first `k ≤ w + 2` digits of an array outside a frame. -/
theorem keep_val {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j k : Nat} (hk : k ≤ w + 2) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    val32 m' B (arr w j) k = val32 m B (arr w j) k := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega)
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; simp only [S] at *; omega
  · have := hd d hd'; have : KeyWorkspace.hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- A word of `≤ 8` bytes inside an array outside a frame. -/
theorem keep_word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j o b : Nat} (hb : o + b / 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    m'.readW (off B (arr w j + o)) b = m.readW (off B (arr w j + o)) b := by
  refine Mem.readW_congr fun i hi => h _ fun r hr => ?_
  rw [ofs_off B (by omega)]
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; omega
  · have := hd d hd'; have : KeyWorkspace.hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega

/-- A signed number of `k + 1 ≤ w + 2` digits in an array outside a frame. -/
theorem keep_sv {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j k : Nat} (hk : k + 1 ≤ w + 2) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    sv m' B (arr w j) k = sv m B (arr w j) k := by
  unfold sv
  rw [keep_val h (by omega) hj hd fit, keep_word h (o := 4 * k) (b := 32) (by simp only [S]; omega) hj hd fit]

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

/-! ## `shr` -/

theorem ofNat_succ (n : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) :=
  (BitVec.ofNat_add n 1).symm

/-- `[o] = [a] / 2^30` (`shr`), `n + 1` digits, for `[a]` (`n + 2` digits) a
multiple of `2^30`. -/
theorem shr_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o a : Nat}
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) {z : Int}
    (hy : sv s.mem B (arr w a) (n + 1) = 2 ^ 30 * z) (hz1 : -2 ^ (32 * n + 31) ≤ z)
    (hz2 : z < 2 ^ (32 * n + 31)) :
    WP isa (shr o a) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      sv t.mem B (arr w o) n = z ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have da := arr_disj (w := w) hoa
  rw [shr, WP.seq_iff]
  have hb1 : WP isa (.block (ptr .r5 o ++ ptr .r6 a ++ cntN1)) s fun t => Ctx t B Z w N n c ∧
      t.mem = s.mem ∧ t.gpr .r5 = off B (arr w o) ∧ t.gpr .r6 = off B (arr w a) ∧
      t.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧ Keep kRegs s t := by
    rw [List.append_assoc]
    refine ptr_ok h.ws (by decide) (by decide) (by decide) (by omega) ?_
    refine ptr_ok (h.ws.of_keep (Keep.write _ .r5 _)) (by decide) (by decide) (by decide) (by omega) ?_
    refine WP.mono (WP.keep [.r8] (Q := fun x => x.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧ x.mem = s.mem) ?_
      (by decide)) fun x ⟨⟨x8, xm⟩, kx⟩ => ?_
    · prun [cntN1, cntN, h.cnt, ofNat_succ]
    have k0 : Keep kRegs s x := (((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).trans kx).mono (by decide)
    refine ⟨h.of_keep k0, xm, ?_, ?_, x8, k0⟩
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, reduceCtorEq, ↓reduceIte]
    · rw [kx.gpr _ (by decide)]; simp only [gpr_write, ↓reduceIte]
  refine WP.mono hb1 fun t1 ⟨h1, m1, p5, p6, p8, k1⟩ => ?_
  refine WP.mono (shrLoop_ok h1.ws.scr p5 p6 p8 (by omega) (by omega) (by omega) (by omega) (by omega))
    fun t2 ⟨veq, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := k1.trans' (k2.mono (by decide))
  rw [m1] at veq out2
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega) (by simp), ?_, k⟩
  have e := val_sv s.mem B (arr w a) (n + 1)
  rw [hy] at e
  have hd := congrArg (fun x : Nat => (x : Int)) veq
  push_cast at hd
  rw [e] at hd
  refine sv_of_eq (q := 4 * (if 2 ^ 31 ≤ w32 s.mem B (arr w a + 4 * (n + 1)) then 1 else 0) -
    ((w32 s.mem B (arr w a + 4 * (n + 1)) / 2 ^ 30 : Nat) : Int)) ?_ hz1 hz2
  have e1 : (2 : Int) ^ (32 * (n + 1 + 1)) = 2 ^ 30 * (4 * 2 ^ (32 * (n + 1))) := by
    rw [show 32 * (n + 1 + 1) = 30 + (2 + 32 * (n + 1)) by omega, Int.pow_add, Int.pow_add]; rfl
  rw [e1, Int.mul_assoc, ← Int.mul_add, show (1073741824 : Int) = 2 ^ 30 from rfl,
    Int.mul_ediv_cancel_left _ (by decide)] at hd
  generalize (2 : Int) ^ (32 * (n + 1)) = P at hd ⊢
  push_cast at hd
  grind

/-! ## Counts -/

theorem cntN_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n c) :
    WP isa (.block cntN) t fun x => (x.gpr .r8 = BitVec.ofNat 64 n ∧ x.mem = t.mem) ∧ Keep [.r8] t x := by
  refine WP.keep _ ?_ (by decide)
  prun [cntN, h.cnt]

theorem cntN1_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n c) :
    WP isa (.block cntN1) t fun x => (x.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧ x.mem = t.mem) ∧ Keep [.r8] t x := by
  refine WP.keep _ ?_ (by decide)
  prun [cntN1, cntN, h.cnt, ofNat_succ]

/-- Arrays equal or apart: `o` is ahead of `a`, for `k ≤ w + 2` digits. -/
theorem ahead_any (w o a k : Nat) (hk : k ≤ w + 2) : Ahead (arr w o) (arr w a) k := by
  by_cases e : o = a
  · subst e; exact .inl (Nat.le_refl _)
  · exact ahead_k e hk

/-- The pointers of three arrays, a count and no carry. -/
theorem setup_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n c → WP isa (.block cnt) t fun x =>
      (x.gpr .r8 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.r8] t x)
    (ho : o < 2 ^ 15) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) :
    WP isa (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cnt ++ ([.li .r9 0] : List Instr))) s fun t =>
      Ctx t B Z w N n c ∧ t.mem = s.mem ∧ t.gpr .r5 = off B (arr w o) ∧ t.gpr .r6 = off B (arr w a) ∧
      t.gpr .r7 = off B (arr w b) ∧ t.gpr .r8 = BitVec.ofNat 64 K ∧ t.gpr .r9 = 0 ∧
      Keep [.r5, .r6, .r7, .r8, .r9] s t := by
  rw [show ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cnt ++ ([.li .r9 0] : List Instr) =
    ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ (cnt ++ ([.li .r9 0] : List Instr)) by simp only [List.append_assoc]]
  refine ptr3_ok h.ws ho ha hb fun t p5 p6 p7 kt mt => ?_
  have ht := h.of_keep (kt.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (hcnt t ht) fun x ⟨⟨x8, xm⟩, kx⟩ => ?_
  refine WP.mono (WP.keep [.r9] (Q := fun y => y.gpr .r9 = 0 ∧ y.mem = x.mem) (by prun; rfl) (by decide))
    fun y ⟨⟨y9, ym⟩, ky⟩ => ?_
  have k0 : Keep [.r5, .r6, .r7, .r8, .r9] s y := ((kt.trans kx).trans ky).mono (by decide)
  refine ⟨h.of_keep (k0.mono (by decide)), ym.trans (xm.trans mt), ?_, ?_, ?_, ?_, y9, k0⟩
  · rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; exact p5
  · rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; exact p6
  · rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; exact p7
  · rw [ky.gpr _ (by decide)]; exact x8

/-! ## `mac` -/

/-- `[o] = [a] + k [b]` (`mac`), `K` digits, `k < 2^32` in `r11`; `o` equal to
`a` and to `b`, or apart from them. -/
theorem mac_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n c → WP isa (.block cnt) t fun x =>
      (x.gpr .r8 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.r8] t x)
    (hK1 : 1 ≤ K) (hK : K ≤ n + 1) (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256)
    (hk : (s.gpr .r11).toNat < 2 ^ 32) :
    WP isa (mac o a b cnt) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      val32 t.mem B (arr w o) K + 2 ^ (32 * K) * (t.gpr .r9).toNat =
        val32 s.mem B (arr w a) K + (s.gpr .r11).toNat * val32 s.mem B (arr w b) K ∧
      (t.gpr .r9).toNat < 2 ^ 32 ∧ t.gpr .r5 = off B (arr w o + 4 * K) ∧ t.gpr .r11 = s.gpr .r11 ∧
      Outside B (arr w o) (4 * K) s.mem t.mem ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.ws.wle
  rw [mac, macSetup, WP.seq_iff]
  refine WP.mono (setup_ok h hcnt (by omega) (by omega) (by omega)) fun t1 ⟨h1, m1, p5, p6, p7, p8, p9, k1⟩ => ?_
  have k11 : t1.gpr .r11 = s.gpr .r11 := k1.gpr _ (by decide)
  refine WP.mono (macLoop_ok h1.ws.scr p5 p6 p7 p8 (by rw [p9]; decide) (by rw [k11]; exact hk) hK1 (by omega)
    (by omega) (by omega) (by omega) (ahead_any w o a K (by omega)) (ahead_any w o b K (by omega)))
    fun t2 ⟨q9, qeq, q5, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := (k1.mono (by decide)).trans' (k2.mono (by decide))
  rw [m1, k11, p9] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega) (by simp), by simpa using qeq, q9, q5, (k2.gpr _ (by decide)).trans k11, out2, k⟩

/-! ## `csub` -/

/-- `[o] = [x] - m` where it does not borrow, else `[x]` (`csub`), `n + 1`
digits, through `[sc]`. -/
theorem csub_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o x sc : Nat}
    (ho : o < N) (hx : x < N) (hsc : sc < N) (hm : aMz < N) (hN : N ≤ 256) (hsx : sc ≠ x)
    (hsm : sc ≠ aMz) (hos : o ≠ sc) {p X : Nat} (hp : val32 s.mem B (arr w aMz) (n + 1) = p)
    (hX : val32 s.mem B (arr w x) (n + 1) = X) :
    WP isa (csub o x sc) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o, sc] [] s.mem t.mem ∧
      val32 t.mem B (arr w o) (n + 1) = (if p ≤ X then X - p else X) ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fx := h.ws.arr_fit hx
  have fs := h.ws.arr_fit hsc
  have fm := h.ws.arr_fit hm
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nw
  have := h.npos
  have := h.ws.wle
  have hnw := h.ws.nowrap
  rw [csub]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (setup_ok h (fun t ht => cntN1_ok ht) (by omega) (by omega) (by omega))
    fun t1 ⟨h1, m1, p5, p6, p7, p8, p9, k1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.subLoop_ok h1.ws.scr p5 p6 p7 p8 (by rw [p9]; decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (ahead_k hsx (by omega)) (ahead_k hsm (by omega)))
    fun t2 ⟨b9, veq, out2, k2⟩ => ?_
  have h2 := h1.of_keep (k2.mono (by decide))
  rw [m1, p9, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at veq
  rw [m1] at out2
  rw [WP.seq_iff]
  -- The mask of the borrow.
  have hb2 : WP isa (.block (ptr .r5 o ++ ptr .r6 sc ++ ptr .r7 x ++ cntN1 ++
      ([.li .r0 0, .sub .r9 .r0 .r9] : List Instr))) t2 fun t => Ctx t B Z w N n c ∧ t.mem = t2.mem ∧
      t.gpr .r5 = off B (arr w o) ∧ t.gpr .r6 = off B (arr w sc) ∧ t.gpr .r7 = off B (arr w x) ∧
      t.gpr .r8 = BitVec.ofNat 64 (n + 1) ∧ t.gpr .r9 = 0#64 - t2.gpr .r9 ∧ Keep kRegs t2 t := by
    rw [show ptr .r5 o ++ ptr .r6 sc ++ ptr .r7 x ++ cntN1 ++ ([.li .r0 0, .sub .r9 .r0 .r9] : List Instr) =
      ptr .r5 o ++ ptr .r6 sc ++ ptr .r7 x ++ (cntN1 ++ ([.li .r0 0, .sub .r9 .r0 .r9] : List Instr)) by
        simp only [List.append_assoc]]
    refine ptr3_ok h2.ws (by omega) (by omega) (by omega) fun t q5 q6 q7 kt mt => ?_
    have ht := h2.of_keep (kt.mono (by decide))
    rw [WP.block_append_iff]
    refine WP.mono (cntN1_ok ht) fun y ⟨⟨y8, ym⟩, ky⟩ => ?_
    have y9 : y.gpr .r9 = t2.gpr .r9 := (ky.gpr _ (by decide)).trans (kt.gpr _ (by decide))
    refine WP.mono (WP.keep [.r0, .r9] (Q := fun z => z.gpr .r9 = 0#64 - t2.gpr .r9 ∧ z.mem = y.mem)
      (by prun [y9]) (by decide)) fun z ⟨⟨z9, zm⟩, kz⟩ => ?_
    have k0 : Keep kRegs t2 z := ((kt.trans ky).trans kz).mono (by decide)
    refine ⟨h2.of_keep k0, zm.trans (ym.trans mt), ?_, ?_, ?_, ?_, z9, k0⟩
    · rw [kz.gpr _ (by decide), ky.gpr _ (by decide)]; exact q5
    · rw [kz.gpr _ (by decide), ky.gpr _ (by decide)]; exact q6
    · rw [kz.gpr _ (by decide), ky.gpr _ (by decide)]; exact q7
    · rw [kz.gpr _ (by decide)]; exact y8
  refine WP.mono hb2 fun t3 ⟨h3, m3, r5, r6, r7, r8, r9, k3⟩ => ?_
  have e9 : ∀ y : BitVec 64, y.toNat ≤ 1 →
      0#64 - y = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if decide (y.toNat = 1) then 1 else 0) := by
    intro y hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with e | e
    · have : y = 0#64 := BitVec.eq_of_toNat_eq e
      subst this; rfl
    · have : y = 1#64 := BitVec.eq_of_toNat_eq e
      subst this; rfl
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.selLoop_ok (b := decide ((t2.gpr .r9).toNat = 1)) h3.ws.scr
    r5 r6 r7 r8 (by rw [r9]; exact e9 _ b9) (by omega) (by omega) (by omega) (by omega) (by omega)
    (ahead_k hos (by omega)) (ahead_any w o x (n + 1) (by omega))) fun t4 ⟨seq, out4, k4⟩ => ?_
  have k : Keep kRegs s t4 :=
    (((k1.mono (by decide)).trans' (k2.mono (by decide))).trans' k3).trans' (k4.mono (by decide))
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · rw [m3] at out4
    exact (KeyWorkspace.Keep.of_arr (o := sc) (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega)
      (by simp)).trans (KeyWorkspace.Keep.of_arr (o := o) (d := 0) (by simpa only [Nat.add_zero] using out4)
        (by omega) (by simp))
  · have vx : val32 t2.mem B (arr w x) (n + 1) = X := by
      rw [out2.val32 (by have := arr_disj (w := w) hsx; omega) (by omega)]; exact hX
    rw [seq, m3, vx]
    have hpR := val32_lt s.mem B (arr w aMz) (n + 1)
    have hXR := val32_lt s.mem B (arr w x) (n + 1)
    have hSR := val32_lt t2.mem B (arr w sc) (n + 1)
    rw [hp] at hpR veq
    rw [hX] at hXR veq
    generalize 2 ^ (32 * (n + 1)) = R at hpR hXR hSR veq
    by_cases e : (t2.gpr .r9).toNat = 1
    · rw [e] at veq; simp only [e, decide_true, ↓reduceIte]
      have : ¬ p ≤ X := by omega
      simp only [this, ↓reduceIte]
    · have e0 : (t2.gpr .r9).toNat = 0 := by omega
      rw [e0] at veq; simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      have : p ≤ X := by omega
      simp only [this, ↓reduceIte]; omega

end VG.Proof.Rsa.PPC64LE.InvBatch
