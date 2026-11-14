module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Divstep.WordDef
import VerifiedGarbage.Proof.Divstep.Word
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Loops
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbLoops
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Divstep.WordBasic
import VerifiedGarbage.Proof.Divstep.WordArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Framework.Block

/-! # The batched inverse on PPC64LE: the divsteps

`wstepCode_ok`: one divstep's code leaves in `r3`–`r9` the words of
`Proof/Divstep/WordDef.lean`'s `wstep` of their values; `wsteps_ok`: `k` of
them, `wsteps k`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Divstep (WSt wstep)

/-- The words of a divstep: `d f g u v q r` in `r3`–`r9`. -/
def regsW (s : State) : WSt :=
  ⟨s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r6, s.gpr .r7, s.gpr .r8, s.gpr .r9⟩

/-- The registers the divsteps change. -/
abbrev kRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r11, .r12]

theorem low_bit (x : BitVec 64) : (x <<< 63) >>> 63 = x &&& 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have := x.isLt
  omega_using []

theorem wstepCode_ok (s : State) :
    WP isa (.block wstepCode) s fun t => (regsW t = wstep (regsW s) ∧ t.mem = s.mem) ∧ Keep kRegs s t := by
  refine WP.keep _ ?_ (by decide)
  prun [wstepCode, regsW]
  simp only [wstep, low_bit, Divstep.shl1]
  rfl

/-- `k` divsteps, unrolled. -/
theorem wsteps_ok (k : Nat) (s : State) :
    WP isa (.block (wsteps k)) s fun t =>
      (regsW t = Divstep.wsteps k (regsW s) ∧ t.mem = s.mem) ∧ Keep kRegs s t := by
  induction k generalizing s with
  | zero => exact WP.block_nil ⟨⟨rfl, rfl⟩, Keep.refl _ _⟩
  | succ k ih =>
    rw [wsteps, List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    refine WP.mono (wstepCode_ok s) fun t ⟨⟨e, m⟩, k₁⟩ => WP.mono (ih t) fun u ⟨⟨e₂, m₂⟩, k₂⟩ =>
      ⟨⟨by rw [e₂, e]; rfl, m₂.trans m⟩, k₁.trans' k₂⟩

end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE: its digit loops

Over `n` digits of 32 bits at byte offsets of the working space, pointers in
`r5`–`r7` and the count in `r8`, as `Loops.lean`'s:

* `macLoop_ok`: `[o] := [a] + k [b]`, `k < 2^32` in `r11`, the carry in `r9`;
* `shrLoop_ok`: `[o] := [a] >> 30`, reading one digit more;
* `linLoop_ok`: `[o] := u [a] + v [b]` for signed `u`, `v` in `r11`, `r12`,
  the signed carry in `r9`.
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.InvBatch (macBody)
open VG.Proof.Rsa.PPC64LE.Loops (loopRegs Ahead Ahead.outside)

/-! ## `mac` -/

/-- A digit of `a + k m + c`, on bit vectors: below `2^64`. -/
theorem mac_arith (k : BitVec 64) (m a : BitVec 32) (c : BitVec 64) (hk : k.toNat < 2 ^ 32)
    (hc : c.toNat < 2 ^ 32) :
    let S := k * m.setWidth 64 + a.setWidth 64 + c
    (S >>> 32).toNat < 2 ^ 32 ∧
      (S.setWidth 32).toNat + 2 ^ 32 * (S >>> 32).toNat = a.toNat + k.toNat * m.toNat + c.toNat := by
  intro S
  have hm := m.isLt
  have ha := a.isLt
  have hkm : k.toNat * m.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega_using [hk]) (by omega_using [])
  have vS : S.toNat = ((k.toNat * m.toNat % 2 ^ 64 + a.toNat) % 2 ^ 64 + c.toNat) % 2 ^ 64 := by
    simp only [S, BitVec.toNat_add, BitVec.toNat_mul, toNat_ext32]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, vS]
  generalize k.toNat * m.toNat = P at hkm ⊢
  omega_using [hc, hkm]

/-- `[o] := [a] + k [m]` over `n` digits (`countLoop .r8 macBody`), from the
carry `c` in `r9`: the sum and the carry out. -/
theorem macLoop_ok {s : State} {B : Addr} {Z dO dA dM n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dO) (h6 : s.gpr .r6 = off B dA) (h7 : s.gpr .r7 = off B dM)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 n) (h9 : (s.gpr .r9).toNat < 2 ^ 32)
    (h11 : (s.gpr .r11).toNat < 2 ^ 32) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (hO : dO + 4 * n ≤ Z) (hA : dA + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (aA : Ahead dO dA n) (aM : Ahead dO dM n) :
    WP isa (countLoop .r8 macBody) s fun t =>
      (t.gpr .r9).toNat < 2 ^ 32 ∧
      val32 t.mem B dO n + 2 ^ (32 * n) * (t.gpr .r9).toNat =
        val32 s.mem B dA n + (s.gpr .r11).toNat * val32 s.mem B dM n + (s.gpr .r9).toNat ∧
      t.gpr .r5 = off B (dO + 4 * n) ∧ Outside B dO (4 * n) s.mem t.mem ∧ Keep loopRegs s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r5 = off B (dO + 4 * i) ∧ t.gpr .r6 = off B (dA + 4 * i) ∧ t.gpr .r7 = off B (dM + 4 * i) ∧
      (t.gpr .r9).toNat < 2 ^ 32 ∧ Outside B dO (4 * i) s.mem t.mem ∧
      val32 t.mem B dO i + 2 ^ (32 * i) * (t.gpr .r9).toNat =
        val32 s.mem B dA i + (s.gpr .r11).toNat * val32 s.mem B dM i + (s.gpr .r9).toNat ∧
      Keep loopRegs s t
  refine WP.mono (wp_countdown (body := .block (macBody ++ ([.subi .r8 .r8 1] : List Instr)))
    (cnt := .r8) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, j7, j9, jout, jeq, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; rfl, h9, Outside.refl _ _ _ _,
      by simp [val32], Keep.refl _ _⟩ h8)
    fun t ⟨j5, _, _, j9, jout, jeq, jk⟩ => ⟨j9, jeq, j5, jout, jk⟩
  have k11 : t.gpr .r11 = s.gpr .r11 := jk.gpr _ (by decide)
  have hst := (show WP isa (.block (macBody ++ ([.subi .r8 .r8 1] : List Instr))) t fun t' =>
      let S := t.gpr .r11 * (t.mem.readW (off B (dM + 4 * i)) 32).setWidth 64 +
        (t.mem.readW (off B (dA + 4 * i)) 32).setWidth 64 + t.gpr .r9
      (t'.gpr .r5 = off B (dO + 4 * i + 4) ∧ t'.gpr .r6 = off B (dA + 4 * i + 4) ∧
        t'.gpr .r7 = off B (dM + 4 * i + 4) ∧ t'.gpr .r9 = S >>> 32 ∧
        t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off B (dO + 4 * i)) (S.setWidth 32)) ∧ Keep loopRegs t t' from by
    refine WP.keep _ ?_ (by decide)
    prun [macBody, j5, j6, j7, (hs.congr jk.wr).ld (show dA + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).ld (show dM + 4 * i + 4 ≤ Z by omega_arith),
      (hs.congr jk.wr).st (show dO + 4 * i + 4 ≤ Z by omega_arith)])
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l9, l8, lm⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, jk.trans' lk⟩, l8⟩
  · rw [l5, show dO + 4 * i + 4 = dO + 4 * (i + 1) by omega_arith]
  · rw [l6, show dA + 4 * i + 4 = dA + 4 * (i + 1) by omega_arith]
  · rw [l7, show dM + 4 * i + 4 = dM + 4 * (i + 1) by omega_arith]
  · rw [l9]; exact (mac_arith _ _ _ _ (by rw [k11]; exact h11) j9).1
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ B (d := dO + 4 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have wa : w32 t.mem B (dA + 4 * i) = w32 s.mem B (dA + 4 * i) :=
      jout.w32 (by have := aA.outside hi; omega_arith) (by omega_arith)
    have wm : w32 t.mem B (dM + 4 * i) = w32 s.mem B (dM + 4 * i) :=
      jout.w32 (by have := aM.outside hi; omega_arith) (by omega_arith)
    have k : _ = w32 t.mem B (dA + 4 * i) + (t.gpr .r11).toNat * w32 t.mem B (dM + 4 * i) + (t.gpr .r9).toNat :=
      (mac_arith (t.gpr .r11) (t.mem.readW (off B (dM + 4 * i)) 32)
        (t.mem.readW (off B (dA + 4 * i)) 32) _ (by rw [k11]; exact h11) j9).2
    rw [lm, l9, val32_write_top _ _ _ _ _ (by omega_arith), val32_succ s.mem B dM i, val32_succ s.mem B dA i,
      ← pow32_mul i, ← wa, ← wm, ← k11]
    rw [k11] at k
    grind


end VG.Proof.Rsa.PPC64LE.InvBatch

/-!
# The batched inverse on PPC64LE: its operations on arrays

In the key operations' working space (`Ws`), with `n` and the batches left
`c` in `r10` (`Ctx`): each operation of `Impl/Rsa/PPC64LE/InvBatch.lean` on
`n + 1` (or `n + 2`) digits of arrays, signed numbers read by `sv` (the low
digits and a signed top digit).
-/

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (ptr countLoop subBody selBody copyBody seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num slot arr_disj)
open VG.Proof.Rsa.PPC64LE.Loops (loopRegs Ahead AheadW macRegs acc macWLoop_ok
  subWLoop_ok selWLoop_ok copyWLoop_ok eqWLoop_ok)

/-! ## The context -/

/-- The working space, and `n` and the count `c` in `r10`; the `ν = ⌈n / 2⌉`
words fit in an array with room for one more (`2 ν ≤ w`). -/
structure Ctx (s : State) (B : Addr) (Z w N n c : Nat) : Prop where
  ws : Ws s B Z w N
  r10 : s.gpr .r10 = BitVec.ofNat 64 (n + 2 ^ 15 * c)
  npos : 1 ≤ n
  nw : n ≤ w
  room : 15 ≤ N
  cb : c < 2 ^ 40
  wbig : 10 ≤ w
  fit : n + n % 2 ≤ w

theorem Ctx.of_keep {s t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c)
    (k : Keep kRegs s t) : Ctx t B Z w N n c :=
  ⟨h.ws.of_keep k, (k.gpr _ (by decide)).trans h.r10, h.npos, h.nw, h.room, h.cb, h.wbig, h.fit⟩

theorem Ctx.nlt {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) : n < 2 ^ 15 := by
  have := h.nw; have := h.ws.wle; omega_arith

theorem cnt_eq {n c : Nat} (hn : n < 2 ^ 15) :
    (BitVec.ofNat 64 (n + 2 ^ 15 * c) <<< 49) >>> 49 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_using [hn]

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
  split <;> split <;> omega_arith

/-- The digits read unsigned. -/
theorem val_sv (m : Mem) (B : Addr) (d k : Nat) :
    (val32 m B d (k + 1) : Int) = sv m B d k +
      2 ^ (32 * (k + 1)) * (if 2 ^ 31 ≤ w32 m B (d + 4 * k) then 1 else 0) := by
  rw [sv, val32_succ, toInt_cond, show 32 * (k + 1) = 32 * k + 32 by omega_using [], Int.pow_add]
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
  · have := Int.mul_le_mul_of_nonneg_left (show d ≤ -1 by omega_using [hd]) (Int.le_of_lt hH); omega_using [h1, this]
  · exact hd
  · have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ d by omega_using [hd]) (Int.le_of_lt hH); omega_using [h2, this]

/-- A signed number from the unsigned digits of it, plus a multiple of
`2^(32 (k + 1))`. -/
theorem sv_of_eq {m : Mem} {B : Addr} {d k : Nat} {z q : Int}
    (h : (val32 m B d (k + 1) : Int) = z + 2 ^ (32 * (k + 1)) * q)
    (hz1 : -2 ^ (32 * k + 31) ≤ z) (hz2 : z < 2 ^ (32 * k + 31)) : sv m B d k = z := by
  have e := val_sv m B d k
  have r := sv_range m B d k
  rw [e] at h
  have eP : (2 : Int) ^ (32 * (k + 1)) = 2 * 2 ^ (32 * k + 31) := by
    rw [show 32 * (k + 1) = (32 * k + 31) + 1 by omega_using [], Int.pow_succ, Int.mul_comm]
  have hH : (0 : Int) < 2 ^ (32 * k + 31) := by exact_mod_cast Nat.two_pow_pos _
  rw [eP] at h
  generalize (2 : Int) ^ (32 * k + 31) = H at h hz1 hz2 r hH
  generalize sv m B d k = x at h r ⊢
  generalize (if 2 ^ 31 ≤ w32 m B (d + 4 * k) then (1 : Int) else 0) = b at h
  have h0 : (2 * H) * (b - q) = z - x := by grind
  have := mul_small (H := 2 * H) (d := b - q) (by omega_using [hz1, hz2]) (by omega_using [hz1, r, h0]) (by omega_using [hz2, r, h0])
  rw [this, Int.mul_zero] at h0
  omega_using [h0]

/-- The first `k ≤ w + 2` digits of an array outside a frame. -/
theorem keep_val {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j k : Nat} (hk : k ≤ w + 2) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    val32 m' B (arr w j) k = val32 m B (arr w j) k := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega_using [hk, fit])
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; simp only [S] at *; omega_using [hk, this]
  · have := hd d hd'; have : KeyWorkspace.hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith

/-- A word of `≤ 8` bytes inside an array outside a frame. -/
theorem keep_word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j o b : Nat} (hb : o + b / 8 ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    m'.readW (off B (arr w j + o)) b = m.readW (off B (arr w j + o)) b := by
  refine Mem.readW_congr fun i hi => h _ fun r hr => ?_
  rw [ofs_off B (by omega_using [hb, fit, hi])]
  simp only [KeyWorkspace.ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨x, hx, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (hj x hx); dsimp only; omega_using [hb, hi, this]
  · have := hd d hd'; have : KeyWorkspace.hdr ≤ arr w j := Nat.le_add_right _ _; dsimp only; omega_arith

/-- The first `k` words (`8 k ≤ S w`) of an array outside a frame. -/
theorem keep_wv {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j k : Nat} (hk : 8 * k ≤ S w) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    wordsVal m' B (arr w j) k = wordsVal m B (arr w j) k := by
  suffices e : ∀ k o, o + 8 * k ≤ S w → wordsVal m' B (arr w j + o) k = wordsVal m B (arr w j + o) k by
    simpa using e k 0 (by omega_using [hk])
  intro k
  induction k with
  | zero => intro o _; rfl
  | succ k ih =>
    intro o ho
    simp only [wordsVal]
    rw [show arr w j + o + 8 = arr w j + (o + 8) by omega_using [], ih (o + 8) (by omega_using [ho])]
    unfold Mont.word
    rw [keep_word h (o := o) (b := 64) (by omega_using [ho]) hj hd fit]

/-- A signed number of `k + 1 ≤ w + 2` digits in an array outside a frame. -/
theorem keep_sv {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : KeyWorkspace.Keep B w js ds m m') {j k : Nat} (hk : k + 1 ≤ w + 2) (hj : ∀ x ∈ js, x ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    sv m' B (arr w j) k = sv m B (arr w j) k := by
  unfold sv
  rw [keep_val h (by omega_using [hk]) hj hd fit, keep_word h (o := 4 * k) (b := 32) (by simp only [S]; omega_using [hk]) hj hd fit]

/-! ## Blocks -/

/-- `ldW r o`: `r` := the window's 64-bit word at `o`. -/
theorem ldW_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {r : Reg} (hr : r ≠ .r0)
    (h30 : r ≠ .r30) (h31 : r ≠ .r31) {o : Nat} (ho : o + 8 ≤ 48) (ho4 : o % 4 = 0) {rest : List Instr}
    {Q : State → Prop} (k : WP isa (.block rest) (s.write r (s.mem.readW (off B (arr w aW + o)) 64)) Q) :
    WP isa (.block (ldW r o ++ rest)) s Q := by
  have fit := h.ws.arr_fit (j := aW) (by have := h.room; unfold aW; omega_using [this])
  have hS : S w = 4 * (w + 2) := rfl
  have := h.ws.wpos
  have := h.wbig
  rw [ldW, List.append_assoc]
  refine ptr_ok h.ws hr h30 h31 (by decide) ?_
  rw [WP.block_append_iff]
  have hl : InRegions ((s.write r (off B (arr w aW))).rd ++ (s.write r (off B (arr w aW))).wr)
      ((s.write r (off B (arr w aW))).gpr r + BitVec.ofNat 64 o) 8 := by
    simp only [gpr_write, ↓reduceIte, rd_write, wr_write, off_add]
    exact h.ws.scr.ld (d := arr w aW + o) (n := 8) (by omega_using [ho, fit, hS, this])
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d hr ⟨by omega_using [ho], ho4⟩ hl,
    gpr_write, ↓reduceIte, off_add, mem_write, Option.some.injEq, exists_eq_left', write_write]
  exact k

/-- A digit outside the bytes that changed, read as a bit vector. -/
theorem Outside.readW32 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun _ _ => h _ (by rw [ofs_off base (by omega_arith)]; omega_arith)

/-! ## Words -/

/-- The words the inverse works on, `⌈n / 2⌉`. -/
abbrev nu (n : Nat) : Nat := (n + 1) / 2

theorem Ctx.nu1 {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) : 1 ≤ nu n := by
  have := h.npos; unfold nu; omega_using [this]

theorem Ctx.nuw {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) : 2 * nu n ≤ w := by
  have := h.fit; unfold nu; omega_using [this]

/-- `n` digits fit in `ν` words. -/
theorem pow_nu (n : Nat) : 2 ^ (32 * n) ≤ 2 ^ (64 * nu n) :=
  Nat.pow_le_pow_right (by decide) (by unfold nu; omega_using [])

/-- Arrays apart are each ahead of the other, for `k` words (`8 k ≤ S w`). -/
theorem aheadW_k {w o a k : Nat} (h : o ≠ a) (hk : 8 * k ≤ S w) : AheadW (arr w o) (arr w a) k := by
  have := arr_disj (w := w) h
  unfold AheadW; omega_using [hk, this]

/-- Arrays equal or apart: `o` is ahead of `a`, for `k` words (`8 k ≤ S w`). -/
theorem aheadW_any (w o a k : Nat) (hk : 8 * k ≤ S w) : AheadW (arr w o) (arr w a) k := by
  by_cases e : o = a
  · subst e; exact .inl (Nat.le_refl _)
  · exact aheadW_k e hk

theorem ofNat_succ (n : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) :=
  (BitVec.ofNat_add n 1).symm

theorem ofNat_half {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [h])]

/-! ## Counts -/

theorem cntN_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n c) :
    WP isa (.block cntN) t fun x => (x.gpr .r8 = BitVec.ofNat 64 (nu n) ∧ x.mem = t.mem) ∧ Keep [.r8] t x := by
  have := h.nlt
  refine WP.keep _ ?_ (by decide)
  prun [cntN, h.cnt, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega_using [this])]

theorem cntN1_ok {t : State} {B : Addr} {Z w N n c : Nat} (h : Ctx t B Z w N n c) :
    WP isa (.block cntN1) t fun x =>
      (x.gpr .r8 = BitVec.ofNat 64 (nu n + 1) ∧ x.mem = t.mem) ∧ Keep [.r8] t x := by
  have := h.nlt
  refine WP.keep _ ?_ (by decide)
  prun [cntN1, cntN, h.cnt, ofNat_succ, ofNat_half (show n + 1 < 2 ^ 64 by omega_using [this])]

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

/-- `[o] = [a] + k [b]` (`mac`), `K` words, `k` in `r11`; `o` equal to `a`
and to `b`, or apart from them. -/
theorem mac_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o a b K : Nat}
    {cnt : List Instr} (hcnt : ∀ t, Ctx t B Z w N n c → WP isa (.block cnt) t fun x =>
      (x.gpr .r8 = BitVec.ofNat 64 K ∧ x.mem = t.mem) ∧ Keep [.r8] t x)
    (hK1 : 1 ≤ K) (hK : 8 * K ≤ S w) (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) :
    WP isa (mac o a b cnt) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) K + 2 ^ (64 * K) * (t.gpr .r9).toNat =
        wordsVal s.mem B (arr w a) K + (s.gpr .r11).toNat * wordsVal s.mem B (arr w b) K ∧
      t.gpr .r5 = off B (arr w o + 8 * K) ∧ t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r4 = s.gpr .r4 ∧
      Outside B (arr w o) (8 * K) s.mem t.mem ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.ws.wle
  rw [mac, WP.seq_iff]
  refine WP.mono (setup_ok h hcnt (by omega_using [ho, hN]) (by omega_using [ha, hN]) (by omega_using [hb, hN])) fun t1 ⟨h1, m1, p5, p6, p7, p8, p9, k1⟩ => ?_
  have k11 : t1.gpr .r11 = s.gpr .r11 := k1.gpr _ (by decide)
  refine WP.mono (macWLoop_ok h1.ws.scr p5 p6 p7 p8 hK1 (by omega_using [hK, hS, this])
    (by omega_using [hK, fo]) (by omega_using [hK, fa]) (by omega_using [hK, fb]) (aheadW_any w o a K (by omega_using [hK])) (aheadW_any w o b K (by omega_using [hK])))
    fun t2 ⟨qeq, q5, out2, k2⟩ => ?_
  have k : Keep kRegs s t2 := (k1.mono (by decide)).trans' (k2.mono (by decide))
  rw [m1, k11, p9] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2)
    (by omega_using [hK]) (by simp), by simpa using qeq, q5, (k2.gpr _ (by decide)).trans k11,
    (k2.gpr _ (by decide)).trans (k1.gpr _ (by decide)), out2, k⟩

theorem ofNat_shl3 {k : Nat} (h : 8 * k < 2 ^ 64) : BitVec.ofNat 64 k <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [h])]
  omega_using [h]

/-- `topOf j`: `r6` holds the address of word `ν` of array `j`. -/
theorem topOf_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {j : Nat} (hj : j < N)
    (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ctx t B Z w N n c → t.mem = s.mem → t.gpr .r6 = off B (arr w j + 8 * nu n) → Keep kRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (topOf j ++ rest)) s Q := by
  have := h.nuw
  have := h.ws.wle
  have hnw := h.ws.nowrap
  have fj := h.ws.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  rw [topOf, List.append_assoc, List.append_assoc]
  refine ptr_ok h.ws (by decide) (by decide) (by decide) (by omega_using [hj, hN]) ?_
  have h1 := h.of_keep ((Keep.write s .r6 (off B (arr w j))).mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (cntN_ok h1) fun x ⟨⟨x8, xm⟩, kx⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r6, .r8] (Q := fun y => y.gpr .r6 = off B (arr w j + 8 * nu n) ∧ y.mem = x.mem)
    ?_ (by decide)) fun y ⟨⟨y6, ym⟩, ky⟩ => ?_
  · have x6 : x.gpr .r6 = off B (arr w j) := by
      rw [kx.gpr _ (by decide)]; simp only [gpr_write, ↓reduceIte]
    prun [x8, x6, ofNat_shl3 (show 8 * nu n < 2 ^ 64 by omega_arith), off_add]
  have k0 : Keep kRegs s y := (((Keep.write s .r6 _).trans kx).trans ky).mono (by decide)
  exact k y (h.of_keep k0) (ym.trans xm) y6 k0

/-! ## The shift by 59 -/

/-- The arithmetic shift by 59 as the code computes it, unsigned: the top
bits, and the sign's ones above them. -/
theorem sshr59_toNat (x : BitVec 64) :
    (x >>> 59 - (x >>> 63) <<< 5).toNat =
      if 2 ^ 63 ≤ x.toNat then x.toNat / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 else x.toNat / 2 ^ 59 := by
  have hx := x.isLt
  have e1 : (x >>> 59).toNat = x.toNat / 2 ^ 59 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have e2 : ((x >>> 63) <<< 5).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 5 else 0 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    split <;> omega_arith
  rw [BitVec.toNat_sub, e1, e2]
  split <;> omega_using []

/-- The shift by 59: the low words and the top word's arithmetic
shift are `shr_nat`'s `(V + 2 H (2^64 - 1 if V ≥ H)) / 2^59 mod 2 H`. -/
theorem shr_arith64 {L Vlo M : Nat} (x : BitVec 64) (hVlo : Vlo < M)
    (hL : L + M * (x.toNat / 2 ^ 59) = (Vlo + M * x.toNat) / 2 ^ 59) (hLM : L < M) :
    L + M * (x >>> 59 - (x >>> 63) <<< 5).toNat =
      (Vlo + M * x.toNat + 2 * (M * 2 ^ 63) * (if M * 2 ^ 63 ≤ Vlo + M * x.toNat then 2 ^ 64 - 1 else 0)) /
        2 ^ 59 % (2 * (M * 2 ^ 63)) :=
  Divstep.WordArith.shr_arith x.isLt hVlo (sshr59_toNat x) hL hLM

/-! ## `subW` and `csub` -/

/-- `[o] = [a] - [b]` (`subW`), `ν + 1` words, the carry bit set where it does
not borrow. -/
theorem subW_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o a b : Nat}
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) :
    WP isa (subW o a b) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) (nu n + 1) + wordsVal s.mem B (arr w b) (nu n + 1) =
        wordsVal s.mem B (arr w a) (nu n + 1) + 2 ^ (64 * (nu n + 1)) * (1 - t.ca.toNat) ∧
      Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  rw [subW, WP.seq_iff]
  have hb1 : WP isa (.block (ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cntN1 ++ ([.subc .r0 .r8 .r8] : List Instr)))
      s fun t => Ctx t B Z w N n c ∧ t.mem = s.mem ∧ t.gpr .r5 = off B (arr w o) ∧
      t.gpr .r6 = off B (arr w a) ∧ t.gpr .r7 = off B (arr w b) ∧ t.gpr .r8 = BitVec.ofNat 64 (nu n + 1) ∧
      t.ca = true ∧ Keep kRegs s t := by
    rw [show ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ cntN1 ++ ([.subc .r0 .r8 .r8] : List Instr) =
      ptr .r5 o ++ ptr .r6 a ++ ptr .r7 b ++ (cntN1 ++ ([.subc .r0 .r8 .r8] : List Instr)) by
        simp only [List.append_assoc]]
    refine ptr3_ok h.ws (by omega_using [ho, hN]) (by omega_using [ha, hN]) (by omega_using [hb, hN]) fun t p5 p6 p7 kt mt => ?_
    have ht := h.of_keep (kt.mono (by decide))
    rw [WP.block_append_iff]
    refine WP.mono (cntN1_ok ht) fun x ⟨⟨x8, xm⟩, kx⟩ => ?_
    refine WP.mono (WP.keep [.r0] (Q := fun y => y.ca = true ∧ y.mem = x.mem) ?_ (by decide))
      fun y ⟨⟨yc, ym⟩, ky⟩ => ?_
    · have := (x.gpr .r8).isLt
      mcrun []
      simp only [decide_eq_true_eq]
      omega_using []
    have k0 : Keep kRegs s y := ((kt.trans kx).trans ky).mono (by decide)
    refine ⟨h.of_keep k0, ym.trans (xm.trans mt), ?_, ?_, ?_, ?_, yc, k0⟩
    · rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; exact p5
    · rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; exact p6
    · rw [ky.gpr _ (by decide), kx.gpr _ (by decide)]; exact p7
    · rw [ky.gpr _ (by decide)]; exact x8
  refine WP.mono hb1 fun t1 ⟨h1, m1, p5, p6, p7, p8, pc, k1⟩ => ?_
  refine WP.mono (subWLoop_ok h1.ws.scr p5 p6 p7 p8 (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (aheadW_any w o a _ (by omega_arith)) (aheadW_any w o b _ (by omega_arith)))
    fun t2 ⟨qeq, out2, k2, _, _, _⟩ => ?_
  have k : Keep kRegs s t2 := k1.trans' (k2.mono (by decide))
  rw [m1, pc] at qeq
  rw [m1] at out2
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega_arith)
    (by simp), by simpa using qeq, k⟩

/-- The selection mask of a borrow from the carry bit: `CA - 1`. -/
theorem mask_of_ca (b : Bool) :
    BitVec.ofNat 64 (b.toNat) - BitVec.ofNat 64 1 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if !b then 1 else 0) := by
  cases b <;> rfl

/-- `[o] = [x] - m` where it does not borrow, else `[x]` (`csub`), `ν + 1`
words, through `[sc]`. -/
theorem csub_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {o x sc : Nat}
    (ho : o < N) (hx : x < N) (hsc : sc < N) (hN : N ≤ 256) (hsx : sc ≠ x)
    (hsm : sc ≠ aMz) (hos : o ≠ sc) {p X : Nat} (hp : wordsVal s.mem B (arr w aMz) (nu n + 1) = p)
    (hX : wordsVal s.mem B (arr w x) (nu n + 1) = X) :
    WP isa (csub o x sc) s fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o, sc] [] s.mem t.mem ∧
      wordsVal t.mem B (arr w o) (nu n + 1) = (if p ≤ X then X - p else X) ∧ Keep kRegs s t := by
  have hm : aMz < N := by have := h.room; unfold aMz; omega_using [this]
  have fo := h.ws.arr_fit ho
  have fx := h.ws.arr_fit hx
  have fs := h.ws.arr_fit hsc
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.nu1
  have := h.ws.wle
  rw [csub]; simp only [seqs]; rw [WP.seq_iff]
  refine WP.mono (subW_ok h hsc hx hm hN) fun t1 ⟨h1, f1, e1, k1⟩ => ?_
  have xp : wordsVal t1.mem B (arr w x) (nu n + 1) = X := by
    rw [← hX]; exact keep_wv f1 (by omega_arith) (by simpa using hsx) (by simp) (h.ws.fit64 hx)
  have mp : wordsVal t1.mem B (arr w aMz) (nu n + 1) = p := by
    rw [← hp]; exact keep_wv f1 (by omega_arith) (by simpa using hsm) (by simp) (h.ws.fit64 hm)
  rw [hp, hX] at e1
  rw [WP.seq_iff]
  -- The mask, then the pointers and the count.
  have hb2 : WP isa (.block ([.li .r9 0, .adde .r9 .r9 .r9, .subi .r9 .r9 1] ++ ptr .r5 o ++ ptr .r6 sc ++
      ptr .r7 x ++ cntN1)) t1 fun t => Ctx t B Z w N n c ∧ t.mem = t1.mem ∧ t.gpr .r5 = off B (arr w o) ∧
      t.gpr .r6 = off B (arr w sc) ∧ t.gpr .r7 = off B (arr w x) ∧ t.gpr .r8 = BitVec.ofNat 64 (nu n + 1) ∧
      t.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if !t1.ca then 1 else 0) ∧ Keep kRegs t1 t := by
    rw [show ([.li .r9 0, .adde .r9 .r9 .r9, .subi .r9 .r9 1] ++ ptr .r5 o ++ ptr .r6 sc ++ ptr .r7 x ++ cntN1 :
        List Instr) = [.li .r9 0, .adde .r9 .r9 .r9, .subi .r9 .r9 1] ++ (ptr .r5 o ++ ptr .r6 sc ++ ptr .r7 x ++
          cntN1) by simp only [List.append_assoc], WP.block_append_iff]
    refine WP.mono (WP.keep [.r9] (Q := fun y => y.gpr .r9 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if !t1.ca then 1 else 0) ∧ y.mem = t1.mem) ?_ (by decide)) fun y ⟨⟨y9, ym⟩, ky⟩ => ?_
    · mcrun [exec_adde]
      rw [← mask_of_ca]
      cases t1.ca <;> rfl
    have hy := h1.of_keep (ky.mono (by decide))
    refine ptr3_ok hy.ws (by omega_using [ho, hN]) (by omega_using [hsc, hN]) (by omega_using [hx, hN]) fun t p5 p6 p7 kt mt => ?_
    refine WP.mono (cntN1_ok (hy.of_keep (kt.mono (by decide)))) fun z ⟨⟨z8, zm⟩, kz⟩ => ?_
    have k0 : Keep kRegs t1 z := ((ky.trans kt).trans kz).mono (by decide)
    refine ⟨h1.of_keep k0, zm.trans (mt.trans ym), ?_, ?_, ?_, z8, ?_, k0⟩
    · rw [kz.gpr _ (by decide)]; exact p5
    · rw [kz.gpr _ (by decide)]; exact p6
    · rw [kz.gpr _ (by decide)]; exact p7
    · rw [kz.gpr _ (by decide), kt.gpr _ (by decide)]; exact y9
  refine WP.mono hb2 fun t2 ⟨h2, m2, p5, p6, p7, p8, p9, k2⟩ => ?_
  refine WP.mono (selWLoop_ok h2.ws.scr p5 p6 p7 p8 p9 (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (aheadW_k hos (by omega_arith)) (aheadW_any w o x _ (by omega_arith))) fun t3 ⟨qeq, out3, k3, _, _, _⟩ => ?_
  have k : Keep kRegs s t3 := (k1.trans' k2).trans' (k3.mono (by decide))
  rw [m2] at qeq out3
  refine ⟨h.of_keep k, ?_, ?_, k⟩
  · exact (f1.mono (by simp)).trans (KeyWorkspace.Keep.of_arr (d := 0)
      (by simpa only [Nat.add_zero] using out3) (by omega_arith) (by simp))
  · rw [qeq, xp]
    have hD := wordsVal_lt t1.mem B (arr w sc) (nu n + 1)
    have hXl : X < 2 ^ (64 * (nu n + 1)) := by rw [← hX]; exact wordsVal_lt _ _ _ _
    have hpl : p < 2 ^ (64 * (nu n + 1)) := by rw [← hp]; exact wordsVal_lt _ _ _ _
    generalize wordsVal t1.mem B (arr w sc) (nu n + 1) = D at hD e1 ⊢
    generalize 2 ^ (64 * (nu n + 1)) = K at hD hXl hpl e1 ⊢
    cases hc : t1.ca
    · simp only [hc, Bool.toNat_false, Nat.sub_zero, Nat.mul_one] at e1
      have hlt : ¬ p ≤ X := by omega_using [hD, e1]
      simp only [Bool.not_false, ↓reduceIte, hlt]
    · simp only [hc, Bool.toNat_true, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at e1
      have hle : p ≤ X := by omega_using [e1]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hle]
      omega_using [e1]

/-! ## Sign masks -/

/-- The sign mask `0 - x >> 63` of a word, unsigned. -/
theorem signMask_toNat (x : BitVec 64) :
    (BitVec.ofNat 64 0 - x >>> 63).toNat = if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0 := by
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  split <;> omega_arith

/-! ## Selection by a sign -/

theorem ushr63_ofNat (x : BitVec 64) :
    x >>> 63 = BitVec.ofNat 64 (if decide (2 ^ 63 ≤ x.toNat) then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  by_cases hx : 2 ^ 63 ≤ x.toNat
  · rw [decide_eq_true hx]; simp only [↓reduceIte]; omega_using [hx]
  · rw [decide_eq_false hx]; simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [hx]

/-- `signOf j`: the mask of `[j]`'s sign, its word `ν`'s top bit, into `r9`. -/
theorem signOf_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {j : Nat} (hj : j < N)
    (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ctx t B Z w N n c → t.mem = s.mem → t.gpr .r9 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat) then 1 else 0) →
      Keep kRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (signOf j ++ rest)) s Q := by
  have fj := h.ws.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  have hnw := h.ws.nowrap
  rw [signOf, List.append_assoc]
  refine topOf_ok h hj hN fun x hx xm x6 kx => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r9] (Q := fun y => y.gpr .r9 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat) then 1 else 0) ∧
      y.mem = x.mem) ?_ (by decide)) fun y ⟨⟨y9, ym⟩, ky⟩ => ?_
  · prun [x6, xm, exec_load_d, word, hx.ws.scr.ld (show arr w j + 8 * nu n + 8 ≤ Z by omega_arith), ushr63_ofNat]
  have k0 : Keep kRegs s y := kx.trans' (ky.mono (by decide))
  exact k y (h.of_keep k0) (ym.trans xm) y9 k0

/-- `[o] := [b]` if `[j] < 0` (its word `ν`'s top bit), else `[a]`, `ν + 1` words (`signSel`). -/
theorem signSel_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {j o a b : Nat}
    (hj : j < N) (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hob : o ≠ b) :
    WP isa (signSel j o a b) s
      fun t => Ctx t B Z w N n c ∧ KeyWorkspace.Keep B w [o] [] s.mem t.mem ∧
        wordsVal t.mem B (arr w o) (nu n + 1) =
          (if 2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat then wordsVal s.mem B (arr w b) (nu n + 1)
            else wordsVal s.mem B (arr w a) (nu n + 1)) ∧
        Outside B (arr w o) (8 * (nu n + 1)) s.mem t.mem ∧ Keep kRegs s t := by
  have fo := h.ws.arr_fit ho
  have fa := h.ws.arr_fit ha
  have fb := h.ws.arr_fit hb
  have hS : S w = 4 * (w + 2) := rfl
  have := h.nuw
  have := h.ws.wle
  rw [signSel, WP.seq_iff, List.append_assoc, List.append_assoc, List.append_assoc]
  have hb1 : WP isa (.block (signOf j ++ (ptr .r5 o ++ (ptr .r6 a ++ (ptr .r7 b ++ cntN1))))) s fun t =>
      Ctx t B Z w N n c ∧ t.mem = s.mem ∧ t.gpr .r5 = off B (arr w o) ∧ t.gpr .r6 = off B (arr w a) ∧
      t.gpr .r7 = off B (arr w b) ∧ t.gpr .r8 = BitVec.ofNat 64 (nu n + 1) ∧ t.gpr .r9 = BitVec.ofNat 64 0 -
        BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (word s.mem B (arr w j + 8 * nu n)).toNat) then 1 else 0) ∧
      Keep kRegs s t := by
    refine signOf_ok h hj hN fun x hx xm x9 kx => ?_
    rw [← List.append_assoc, ← List.append_assoc]
    refine ptr3_ok hx.ws (by omega_using [ho, hN]) (by omega_using [ha, hN]) (by omega_using [hb, hN]) fun t p5 p6 p7 kt mt => ?_
    refine WP.mono (cntN1_ok (hx.of_keep (kt.mono (by decide)))) fun z ⟨⟨z8, zm⟩, kz⟩ => ?_
    have k0 : Keep kRegs s z := kx.trans' ((kt.trans kz).mono (by decide))
    refine ⟨h.of_keep k0, zm.trans (mt.trans xm), ?_, ?_, ?_, z8, ?_, k0⟩
    · rw [kz.gpr _ (by decide)]; exact p5
    · rw [kz.gpr _ (by decide)]; exact p6
    · rw [kz.gpr _ (by decide)]; exact p7
    · rw [kz.gpr _ (by decide), kt.gpr _ (by decide)]; exact x9
  refine WP.mono hb1 fun t1 ⟨h1, m1, p5, p6, p7, p8, p9, k1⟩ => ?_
  refine WP.mono (selWLoop_ok h1.ws.scr p5 p6 p7 p8 p9 (by omega_using []) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (aheadW_any w o a _ (by omega_arith)) (aheadW_k hob (by omega_arith))) fun t2 ⟨v2, out2, k2, _, _, _⟩ => ?_
  have k : Keep kRegs s t2 := k1.trans' (k2.mono (by decide))
  rw [m1] at v2 out2
  refine ⟨h.of_keep k, KeyWorkspace.Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using out2) (by omega_arith)
    (by simp), ?_, out2, k⟩
  rw [v2]
  simp only [decide_eq_true_eq]

/-! ## Zeroing -/

theorem val32_zero {m : Mem} {B : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ i < k, w32 m B (d + 4 * i) = 0) → val32 m B d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_zero (fun i hi => h i (by omega_using [hi])), h k (by omega_using []), Nat.mul_zero]

theorem ofNat_add2 (n : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 2 = BitVec.ofNat 64 (n + 2) :=
  (BitVec.ofNat_add n 2).symm

/-- `zeroW j`: `[j]`'s `w + 2` digits zeroed. -/
theorem zeroW_ws_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 256) :
    WP isa (zeroW j) s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w [j] [] s.mem t.mem ∧
      Outside B (arr w j) (4 * (w + 2)) s.mem t.mem ∧ (∀ i < w + 2, w32 t.mem B (arr w j + 4 * i) = 0) ∧
      Keep [.r0, .r5, .r8] s t := by
  have fj := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wle
  rw [zeroW, WP.seq_iff]
  refine ptr_ok h (by decide) (by decide) (by decide) (by omega_using [hj, hN]) ?_
  refine WP.mono (WP.keep [.r0, .r8] (Q := fun u => u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.ofNat 64 (w + 2) ∧
    u.gpr .r5 = off B (arr w j) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u0, u8, u5, um⟩, ku⟩ => ?_
  · prun [h.r29, ofNat_add2]
    rfl
  have k1 : Keep [.r0, .r5, .r8] s u := ((Keep.write _ .r5 _).trans ku).mono (by decide)
  refine WP.mono (VG.Proof.Rsa.PPC64LE.Loops.zeroLoop_ok (h.of_keep k1).scr u5 u8 u0 (by omega_using []) (by omega_using [this])
    (by omega_using [fj, hS])) fun t ⟨z, out, kt⟩ => ?_
  rw [um] at out
  exact ⟨h.of_keep (k1.trans' (kt.mono (by decide))), KeyWorkspace.Keep.of_arr (d := 0)
    (by simpa only [Nat.add_zero] using out) (by omega_using [hS]) (by simp), out, z, k1.trans' (kt.mono (by decide))⟩

open VG.PPC64LE.RegUpd
open VG.Proof.Rsa.KeyWorkspace (arr_end)
open VG.Proof.Rsa.PPC64LE.Loops (sgn tlo thi lo2 hi2 FGAcc ABAcc macC acc_two lin_inv_step)

/-! ## The borrowed registers -/

theorem Ctx.of_keep' {s t : State} {B : Addr} {Z w N n c : Nat} {rs : List Reg} (h : Ctx s B Z w N n c)
    (k : Keep rs s t) (h10 : .r10 ∉ rs := by decide) (h29 : .r29 ∉ rs := by decide)
    (h30 : .r30 ∉ rs := by decide) (h31 : .r31 ∉ rs := by decide) : Ctx t B Z w N n c :=
  ⟨h.ws.of_keep k h29 h30 h31, (k.gpr _ h10).trans h.r10, h.npos, h.nw, h.room, h.cb, h.wbig, h.fit⟩

/-- `stRegs rs o`: the registers `rs` stored to the words from offset `o` of
`r3`'s address. -/
theorem stRegs_ok {B : Addr} {Z d : Nat} :
    ∀ (rs : List Reg) (o : Nat) (s : State), Scr s B Z → s.gpr .r3 = off B d → o % 4 = 0 →
      d + o + 8 * rs.length ≤ Z → o + 8 * rs.length < 2 ^ 15 →
      WP isa (.block (stRegs rs o)) s fun u => Keep [] s u ∧ Outside B (d + o) (8 * rs.length) s.mem u.mem ∧
        ∀ i (hi : i < rs.length), word u.mem B (d + o + 8 * i) = s.gpr rs[i]
  | [], _, _, _, _, _, _, _ => WP.block_nil ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun i hi => absurd hi (by simp)⟩
  | r :: rs, o, s, hs, h3, ho4, hZ, ho => by
    have hnw := hs.nowrap
    simp only [List.length_cons] at hZ ho ⊢
    rw [stRegs, show (Instr.store .d r .r3 o :: stRegs rs (o + 8)) = [Instr.store .d r .r3 o] ++ stRegs rs (o + 8)
      from rfl, WP.block_append_iff]
    have hst : WP isa (.block [Instr.store .d r .r3 o]) s fun u =>
        u.mem = s.mem.writeW (off B (d + o)) (s.gpr r) ∧ Keep [] s u := by
      have hr : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 o) 8 := by
        rw [h3, off_add]; exact hs.st (by omega_using [hZ])
      refine WP.of_runBlock ?_
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_store_d (by decide) ⟨by omega_using [ho], ho4⟩ hr,
        Option.some.injEq, exists_eq_left', h3, off_add]
      exact ⟨trivial, Keep.mem _ _⟩
    refine WP.mono hst fun u ⟨mu, ku⟩ => ?_
    have h3' : u.gpr .r3 = off B d := (ku.gpr _ (by simp)).trans h3
    refine WP.mono (stRegs_ok rs (o + 8) u (hs.congr ku.wr) h3' (by omega_using [ho4]) (by omega_using [hZ]) (by omega_using [ho]))
      fun v ⟨kv, ov, rv⟩ => ⟨ku.trans kv, ?_, fun i hi => ?_⟩
    · rw [mu] at ov
      exact ((writeW_outside _ B _ (d := d + o) (by omega_using [hZ, hnw])).mono (by omega_using []) (by omega_using [])).trans
        (ov.mono (by omega_using []) (by omega_using []))
    · cases i with
      | zero =>
        rw [Nat.mul_zero, Nat.add_zero, ov.word (by omega_using []) (by omega_using [hZ, hnw]), mu, word_writeW_self]; rfl
      | succ j =>
        rw [show d + o + 8 * (j + 1) = d + (o + 8) + 8 * j by omega_using [], rv j (by simp at hi; omega_using [hi]),
          List.getElem_cons_succ]
        exact ku.gpr _ (by simp)

/-- `ldRegs rs o`: the registers `rs` (distinct, not `r3`) loaded from the
words from offset `o` of `r3`'s address. -/
theorem ldRegs_ok {B : Addr} {Z d : Nat} :
    ∀ (rs : List Reg) (o : Nat) (s : State), Scr s B Z → s.gpr .r3 = off B d → .r3 ∉ rs → rs.Nodup →
      o % 4 = 0 → d + o + 8 * rs.length ≤ Z → o + 8 * rs.length < 2 ^ 15 →
      WP isa (.block (ldRegs rs o)) s fun u => Keep rs s u ∧ u.mem = s.mem ∧
        ∀ i (hi : i < rs.length), u.gpr rs[i] = word s.mem B (d + o + 8 * i)
  | [], _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨Keep.refl _ _, rfl, fun i hi => absurd hi (by simp)⟩
  | r :: rs, o, s, hs, h3, ht3, hnd, ho4, hZ, ho => by
    have hnw := hs.nowrap
    simp only [List.length_cons] at hZ ho ⊢
    simp only [List.mem_cons, not_or] at ht3
    rw [List.nodup_cons] at hnd
    rw [ldRegs, show (Instr.load .d r .r3 o :: ldRegs rs (o + 8)) = [Instr.load .d r .r3 o] ++ ldRegs rs (o + 8)
      from rfl, WP.block_append_iff]
    have hl : WP isa (.block [Instr.load .d r .r3 o]) s fun u =>
        u.gpr r = word s.mem B (d + o) ∧ u.mem = s.mem ∧ Keep [r] s u := by
      have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 o) 8 := by
        rw [h3, off_add]; exact hs.ld (by omega_using [hZ])
      refine WP.of_runBlock ?_
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (by decide) ⟨by omega_using [ho], ho4⟩ hr,
        Option.some.injEq, exists_eq_left']
      exact ⟨by simp only [gpr_write, ↓reduceIte, h3, off_add], rfl, Keep.write _ _ _⟩
    refine WP.mono hl fun u ⟨ur, mu, ku⟩ => ?_
    have h3' : u.gpr .r3 = off B d := (ku.gpr _ (by simpa [eq_comm] using ht3.1)).trans h3
    refine WP.mono (ldRegs_ok rs (o + 8) u (hs.congr ku.wr) h3' ht3.2 hnd.2 (by omega_using [ho4]) (by omega_using [hZ]) (by omega_using [ho]))
      fun v ⟨kv, mv, rv⟩ => ⟨(ku.trans kv).mono (by simp), mv.trans mu, fun i hi => ?_⟩
    · cases i with
      | zero => rw [List.getElem_cons_zero, kv.gpr _ hnd.1, ur, Nat.mul_zero, Nat.add_zero]
      | succ j =>
        rw [List.getElem_cons_succ, rv j (by simp at hi; omega_using [hi]), mu,
          show d + (o + 8) + 8 * j = d + o + 8 * (j + 1) by omega_using []]

/-- `ptr r3 j` and `stRegs rs 0`: the registers `rs` to the first words of array `j`. -/
theorem stArr_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hj15 : j < 2 ^ 15)
    (hw : 12 ≤ w + 2) {rs : List Reg} (hl : rs.length ≤ 6) (h3 : .r3 ∉ rs) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep [.r3] s u → Outside B (arr w j) (8 * rs.length) s.mem u.mem →
      (∀ i (hi : i < rs.length), word u.mem B (arr w j + 8 * i) = s.gpr rs[i]) → WP isa (.block rest) u Q) :
    WP isa (.block (ptr .r3 j ++ stRegs rs 0 ++ rest)) s Q := by
  have fj := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) hj15 ?_
  rw [WP.block_append_iff]
  refine WP.mono (stRegs_ok (d := arr w j) rs 0 _ (h.scr.congr rfl) (by simp [gpr_write]) rfl (by omega_using [hw, hl, fj, hS]) (by omega_using [hl]))
    fun u ⟨ku, ou, ru⟩ => k u (((Keep.write _ .r3 _).trans ku).mono (by simp)) (by simpa [mem_write] using ou)
      fun i hi => ?_
  rw [show arr w j + 8 * i = arr w j + 0 + 8 * i by omega_using [], ru i hi, gpr_write]
  have : rs[i] ≠ .r3 := fun e => h3 (e ▸ List.getElem_mem hi)
  simp only [this, ↓reduceIte]

/-- `ptr r3 j` and `ldRegs rs 0`: the registers `rs` from the first words of array `j`. -/
theorem ldArr_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) (hj15 : j < 2 ^ 15)
    (hw : 12 ≤ w + 2) {rs : List Reg} (hl : rs.length ≤ 6) (h3 : .r3 ∉ rs) (hnd : rs.Nodup) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Keep (.r3 :: rs) s u → u.mem = s.mem →
      (∀ i (hi : i < rs.length), u.gpr rs[i] = word s.mem B (arr w j + 8 * i)) → WP isa (.block rest) u Q) :
    WP isa (.block (ptr .r3 j ++ ldRegs rs 0 ++ rest)) s Q := by
  have fj := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by decide) (by decide) hj15 ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldRegs_ok (d := arr w j) rs 0 _ (h.scr.congr rfl) (by simp [gpr_write]) h3 hnd rfl (by omega_using [hw, hl, fj, hS])
    (by omega_using [hl])) fun u ⟨ku, mu, ru⟩ => k u (((Keep.write _ .r3 _).trans ku).mono (by simp)) (by simpa [mem_write] using mu)
      fun i hi => ?_
  rw [ru i hi, mem_write, Nat.add_zero]

/-- `spill`: the borrowed registers to the first words of arrays 11–13. -/
theorem spill_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) :
    WP isa (.block spill) s fun u => Keep [.r3] s u ∧ KeyWorkspace.Keep B w [aT1, aT2, aT3] [] s.mem u.mem ∧
      (∀ i (hi : i < spill1.length), word u.mem B (arr w aT1 + 8 * i) = s.gpr spill1[i]) ∧
      (∀ i (hi : i < spill2.length), word u.mem B (arr w aT2 + 8 * i) = s.gpr spill2[i]) ∧
      ∀ i (hi : i < spill3.length), word u.mem B (arr w aT3 + 8 * i) = s.gpr spill3[i] := by
  have r1 : aT1 < N := by have := h.room; unfold aT1; omega_using [this]
  have r2 : aT2 < N := by have := h.room; unfold aT2; omega_using [this]
  have r3 : aT3 < N := by have := h.room; unfold aT3; omega_using [this]
  have f1 := h.ws.fit64 r1
  have f2 := h.ws.fit64 r2
  have f3 := h.ws.fit64 r3
  have hS : S w = 4 * (w + 2) := rfl
  have := h.wbig
  have d12 := arr_disj (w := w) (show aT1 ≠ aT2 by decide)
  have d13 := arr_disj (w := w) (show aT1 ≠ aT3 by decide)
  have d23 := arr_disj (w := w) (show aT2 ≠ aT3 by decide)
  rw [spill, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    ← List.append_assoc (ptr .r3 aT1), ← List.append_assoc (ptr .r3 aT2), ← List.append_nil (ptr .r3 aT3 ++ _)]
  refine stArr_ok h.ws r1 (by decide) (by omega_using [this]) (by decide) (by decide) fun u ku ou ru => ?_
  have hu := h.ws.of_keep ku
  refine stArr_ok hu r2 (by decide) (by omega_using [this]) (by decide) (by decide) fun v kv ov rv => ?_
  have hv := hu.of_keep kv
  refine stArr_ok hv r3 (by decide) (by omega_using [this]) (by decide) (by decide) fun x kx ox rx => WP.block_nil ?_
  simp only [spill1, spill2, spill3, List.length_cons, List.length_nil] at ou ov ox
  refine ⟨(ku.trans' kv).trans' kx, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · exact ((KeyWorkspace.Keep.of_arr (d := 0) (by simpa [mem_write] using ou) (by omega_using [hS, this]) (by simp)).trans
      (KeyWorkspace.Keep.of_arr (d := 0) (by simpa using ov) (by omega_using [hS, this]) (by simp))).trans
      (KeyWorkspace.Keep.of_arr (d := 0) (by simpa using ox) (by omega_using [hS, this]) (by simp))
  · have : i < 6 := by simpa [spill1] using hi
    rw [ox.word (by omega_arith) (by omega_arith), ov.word (by omega_arith) (by omega_arith), ru i hi]
  · have : i < 6 := by simpa [spill2] using hi
    rw [ox.word (by omega_arith) (by omega_arith), rv i hi, ku.gpr _ ?_]
    have := List.getElem_mem hi; revert this; generalize spill2[i] = r; revert r; decide
  · rw [rx i hi, kv.gpr _ ?_, ku.gpr _ ?_] <;>
    · have := List.getElem_mem hi; revert this; generalize spill3[i] = r; revert r; decide

/-- `restore`: the borrowed registers back from the first words of arrays 11–13. -/
theorem restore_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) :
    WP isa (.block restore) s fun u => Keep (.r3 :: (spill1 ++ spill2 ++ spill3)) s u ∧ u.mem = s.mem ∧
      (∀ i (hi : i < spill1.length), u.gpr spill1[i] = word s.mem B (arr w aT1 + 8 * i)) ∧
      (∀ i (hi : i < spill2.length), u.gpr spill2[i] = word s.mem B (arr w aT2 + 8 * i)) ∧
      ∀ i (hi : i < spill3.length), u.gpr spill3[i] = word s.mem B (arr w aT3 + 8 * i) := by
  have r1 : aT1 < N := by have := h.room; unfold aT1; omega_using [this]
  have r2 : aT2 < N := by have := h.room; unfold aT2; omega_using [this]
  have r3 : aT3 < N := by have := h.room; unfold aT3; omega_using [this]
  have := h.wbig
  rw [restore, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    ← List.append_assoc (ptr .r3 aT1), ← List.append_assoc (ptr .r3 aT2), ← List.append_nil (ptr .r3 aT3 ++ _)]
  refine ldArr_ok h.ws r1 (by decide) (by omega_using [this]) (by decide) (by decide) (by decide) fun u ku mu ru => ?_
  have hu := h.ws.of_keep ku
  refine ldArr_ok hu r2 (by decide) (by omega_using [this]) (by decide) (by decide) (by decide) fun v kv mv rv => ?_
  have hv := hu.of_keep kv
  refine ldArr_ok hv r3 (by decide) (by omega_using [this]) (by decide) (by decide) (by decide) fun x kx mx rx =>
    WP.block_nil ⟨((ku.trans kv).trans kx).mono (by decide), by rw [mx, mv, mu], fun i hi => ?_, fun i hi => ?_,
      fun i hi => ?_⟩
  · rw [kx.gpr _ ?_, kv.gpr _ ?_, ru i hi] <;>
    · have := List.getElem_mem hi; revert this; generalize spill1[i] = r; revert r; decide
  · rw [kx.gpr _ ?_, rv i hi, mu]
    have := List.getElem_mem hi; revert this; generalize spill2[i] = r; revert r; decide
  · rw [rx i hi, mv, mu]

/-- The borrowed registers back where they were: what changes only `rs`, and
the borrowed registers, between a spill and a restore that keep the words
spilled, changes only `rs` and `r3`. -/
theorem spill_restore {s u v x : State} {B : Addr} {w : Nat} {rs : List Reg}
    (k1 : Keep [.r3] s u)
    (r1 : ∀ i (hi : i < spill1.length), word u.mem B (arr w aT1 + 8 * i) = s.gpr spill1[i])
    (r2 : ∀ i (hi : i < spill2.length), word u.mem B (arr w aT2 + 8 * i) = s.gpr spill2[i])
    (r3 : ∀ i (hi : i < spill3.length), word u.mem B (arr w aT3 + 8 * i) = s.gpr spill3[i])
    (k2 : Keep (rs ++ (spill1 ++ spill2 ++ spill3)) u v)
    (w1 : ∀ i < 6, word v.mem B (arr w aT1 + 8 * i) = word u.mem B (arr w aT1 + 8 * i))
    (w2 : ∀ i < 6, word v.mem B (arr w aT2 + 8 * i) = word u.mem B (arr w aT2 + 8 * i))
    (w3 : ∀ i < 3, word v.mem B (arr w aT3 + 8 * i) = word u.mem B (arr w aT3 + 8 * i))
    (k3 : Keep (.r3 :: (spill1 ++ spill2 ++ spill3)) v x)
    (l1 : ∀ i (hi : i < spill1.length), x.gpr spill1[i] = word v.mem B (arr w aT1 + 8 * i))
    (l2 : ∀ i (hi : i < spill2.length), x.gpr spill2[i] = word v.mem B (arr w aT2 + 8 * i))
    (l3 : ∀ i (hi : i < spill3.length), x.gpr spill3[i] = word v.mem B (arr w aT3 + 8 * i)) :
    Keep (.r3 :: rs) s x := by
  refine ⟨fun r hr => ?_, k3.rd.trans (k2.rd.trans k1.rd), k3.wr.trans (k2.wr.trans k1.wr),
    k3.sp.trans (k2.sp.trans k1.sp), k3.lr.trans (k2.lr.trans k1.lr)⟩
  simp only [List.mem_cons, not_or] at hr
  by_cases h1 : r ∈ spill1
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h1
    rw [l1 i hi, w1 i (by simpa [spill1] using hi), r1 i hi]
  by_cases h2 : r ∈ spill2
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h2
    rw [l2 i hi, w2 i (by simpa [spill2] using hi), r2 i hi]
  by_cases h3 : r ∈ spill3
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h3
    rw [l3 i hi, w3 i (by simpa [spill3] using hi), r3 i hi]
  rw [k3.gpr _ (by simp only [List.mem_cons, List.mem_append, not_or]; exact ⟨hr.1, ⟨h1, h2⟩, h3⟩),
    k2.gpr _ (by simp only [List.mem_append, not_or]; exact ⟨hr.2, ⟨h1, h2⟩, h3⟩), k1.gpr _ (by simp [hr.1])]

/-! ## The passes' blocks -/

/-- The registers `fsetup` writes. -/
abbrev fsRegs : List Reg := [.r0, .r5, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25]

/-- `fsetup a b`: the matrix from the window, its masks, the pointers at
arrays `a` and `b`, and the accumulators zero. -/
theorem fsetup_ok {s : State} {B : Addr} {Z w N n c : Nat} (h : Ctx s B Z w N n c) {a b : Nat}
    (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) :
    WP isa (.block (fsetup a b)) s fun t => Ctx t B Z w N n c ∧ t.mem = s.mem ∧
      t.gpr .r14 = s.mem.readW (off B (arr w aW + wU)) 64 ∧ t.gpr .r15 = s.mem.readW (off B (arr w aW + wV)) 64 ∧
      t.gpr .r16 = s.mem.readW (off B (arr w aW + wQ)) 64 ∧ t.gpr .r17 = s.mem.readW (off B (arr w aW + wR)) 64 ∧
      t.gpr .r18 = sgn (t.gpr .r14) ∧ t.gpr .r19 = sgn (t.gpr .r15) ∧
      t.gpr .r20 = sgn (t.gpr .r16) ∧ t.gpr .r21 = sgn (t.gpr .r17) ∧
      t.gpr .r5 = off B (arr w a) ∧ t.gpr .r6 = off B (arr w b) ∧
      t.gpr .r22 = 0#64 ∧ t.gpr .r23 = 0#64 ∧ t.gpr .r24 = 0#64 ∧ t.gpr .r25 = 0#64 ∧ Keep fsRegs s t := by
  rw [fsetup]
  simp only [List.append_assoc]
  refine ldW_ok h (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  have h1 := h.of_keep' (Keep.write s .r14 (s.mem.readW (off B (arr w aW + wU)) 64))
  refine ldW_ok h1 (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  have h2 := h1.of_keep' (Keep.write _ .r15 (s.mem.readW (off B (arr w aW + wV)) 64))
  refine ldW_ok h2 (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  have h3 := h2.of_keep' (Keep.write _ .r16 (s.mem.readW (off B (arr w aW + wQ)) 64))
  refine ldW_ok h3 (by decide) (by decide) (by decide) (by decide) (by decide) ?_
  have h4 := h3.of_keep' (Keep.write _ .r17 (s.mem.readW (off B (arr w aW + wR)) 64))
  simp only [mem_write] at h1 h2 h3 h4 ⊢
  generalize hs4 : (((s.write .r14 (s.mem.readW (off B (arr w aW + wU)) 64)).write .r15
    (s.mem.readW (off B (arr w aW + wV)) 64)).write .r16 (s.mem.readW (off B (arr w aW + wQ)) 64)).write .r17
    (s.mem.readW (off B (arr w aW + wR)) 64) = s4 at h4
  have k4 : Keep [.r14, .r15, .r16, .r17] s s4 := by
    rw [← hs4]
    exact ((((Keep.write s .r14 _).trans (Keep.write _ .r15 _)).trans (Keep.write _ .r16 _)).trans
      (Keep.write _ .r17 _)).mono (by decide)
  have e4 : s4.mem = s.mem := by rw [← hs4]; simp only [mem_write]
  have g14 : s4.gpr .r14 = s.mem.readW (off B (arr w aW + wU)) 64 := by rw [← hs4]; simp [gpr_write]
  have g15 : s4.gpr .r15 = s.mem.readW (off B (arr w aW + wV)) 64 := by rw [← hs4]; simp [gpr_write]
  have g16 : s4.gpr .r16 = s.mem.readW (off B (arr w aW + wQ)) 64 := by rw [← hs4]; simp [gpr_write]
  have g17 : s4.gpr .r17 = s.mem.readW (off B (arr w aW + wR)) 64 := by rw [← hs4]; simp [gpr_write]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r18, .r19, .r20, .r21] (Q := fun t => t.gpr .r0 = 0#64 ∧
      t.gpr .r18 = sgn (s4.gpr .r14) ∧ t.gpr .r19 = sgn (s4.gpr .r15) ∧ t.gpr .r20 = sgn (s4.gpr .r16) ∧
      t.gpr .r21 = sgn (s4.gpr .r17) ∧ t.mem = s4.mem) (by prun [sgn]) (by decide))
    fun t5 ⟨⟨z0, m18, m19, m20, m21, e5⟩, k5⟩ => ?_
  have h5 := h4.of_keep' k5
  refine ptr_ok h5.ws (by decide) (by decide) (by decide) ha ?_
  refine ptr_ok (h5.ws.of_keep (Keep.write _ _ _)) (by decide) (by decide) (by decide) hb ?_
  refine WP.mono (WP.keep [.r22, .r23, .r24, .r25] (Q := fun t => t.gpr .r22 = 0#64 ∧ t.gpr .r23 = 0#64 ∧
      t.gpr .r24 = 0#64 ∧ t.gpr .r25 = 0#64 ∧ t.mem = t5.mem) (by prun) (by decide))
    fun t ⟨⟨z22, z23, z24, z25, et⟩, kt⟩ => ?_
  have k6 : Keep [.r5, .r6] t5 ((t5.write .r5 (off B (arr w a))).write .r6 (off B (arr w b))) :=
    ((Keep.write _ .r5 _).trans (Keep.write _ .r6 _)).mono (by decide)
  have kall : Keep fsRegs s t := (((k4.trans k5).trans k6).trans kt).mono (by decide)
  have g : ∀ r, r ∉ [Reg.r22, .r23, .r24, .r25] → r ≠ .r5 → r ≠ .r6 → t.gpr r = t5.gpr r := fun r h1 h2 h3 => by
    rw [kt.gpr _ h1]; simp [gpr_write, h2, h3]
  refine ⟨h.of_keep' kall, by rw [et]; simp only [e5, e4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    z22, z23, z24, z25, kall⟩
  · rw [g _ (by decide) (by decide) (by decide), k5.gpr _ (by decide), g14]
  · rw [g _ (by decide) (by decide) (by decide), k5.gpr _ (by decide), g15]
  · rw [g _ (by decide) (by decide) (by decide), k5.gpr _ (by decide), g16]
  · rw [g _ (by decide) (by decide) (by decide), k5.gpr _ (by decide), g17]
  · rw [g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide), m18, k5.gpr _ (by decide)]
  · rw [g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide), m19, k5.gpr _ (by decide)]
  · rw [g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide), m20, k5.gpr _ (by decide)]
  · rw [g _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide), m21, k5.gpr _ (by decide)]
  · rw [kt.gpr _ (by decide)]; simp [gpr_write]
  · rw [kt.gpr _ (by decide)]; simp [gpr_write]

/-- Word 0 of the pass over `f` and `g` (at `dF`, `dG`): both accumulators'
terms, and their low words' top bits. -/
theorem fgFirst_ok {t : State} {B : Addr} {Z dF dG : Nat} (hs : Scr t B Z)
    (p5 : t.gpr .r5 = off B dF) (p6 : t.gpr .r6 = off B dG) (hF : dF + 8 ≤ Z) (hG : dG + 8 ≤ Z)
    (m18 : t.gpr .r18 = sgn (t.gpr .r14)) (m19 : t.gpr .r19 = sgn (t.gpr .r15))
    (m20 : t.gpr .r20 = sgn (t.gpr .r16)) (m21 : t.gpr .r21 = sgn (t.gpr .r17)) :
    WP isa (.block (fterms 0 ++ ([.lsr .d .r28 .r22 59, .lsr .d .r12 .r24 59] : List Instr) ++
      fshift .r22 .r23 ++ fshift .r24 .r25)) t fun u =>
      let x := word t.mem B dF
      let y := word t.mem B dG
      (u.gpr .r22 = hi2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) ∧
        u.gpr .r23 = 0#64 - hi2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) >>> 63 ∧
        u.gpr .r28 = lo2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22) >>> 59 ∧
        u.gpr .r24 = hi2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) ∧
        u.gpr .r25 = 0#64 - hi2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) >>> 63 ∧
        u.gpr .r12 = lo2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24) >>> 59 ∧ u.mem = t.mem) ∧
      Keep [.r0, .r3, .r12, .r22, .r23, .r24, .r25, .r26, .r27, .r28] t u := by
  refine WP.keep _ ?_ (by decide)
  mcrun [fterms, fterm, fshift, hi2, lo2, tlo, thi, sgn, exec_adde, word, BitVec.add_zero, p5, p6, m18, m19, m20,
    m21, hs.ld (show dF + 8 ≤ Z by omega_using [hF]), hs.ld (show dG + 8 ≤ Z by omega_using [hG])]

/-- The top words of the new `f` and `g`: the last five bits, sign-extended. -/
theorem fgTop_ok {t : State} {B : Addr} {Z dF dG : Nat} (hs : Scr t B Z)
    (p5 : t.gpr .r5 = off B dF) (p6 : t.gpr .r6 = off B dG) (hF : dF + 8 ≤ Z) (hG : dG + 8 ≤ Z) :
    WP isa (.block fgTop) t fun u =>
      u.mem = (t.mem.writeW (off B dF) (t.gpr .r28 - (t.gpr .r28 >>> 4) <<< 5)).writeW (off B dG)
        (t.gpr .r12 - (t.gpr .r12 >>> 4) <<< 5) ∧ Keep [.r0] t u := by
  refine WP.keep _ ?_ (by decide)
  prun [fgTop, p5, p6, hs.st (show dF + 8 ≤ Z by omega_using [hF]), hs.st (show dG + 8 ≤ Z by omega_using [hG])]

theorem ushr59_4 (x : BitVec 64) : x >>> 59 >>> 4 = x >>> 63 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

/-- The end of the pass over `f` and `g`: the stored words with the top
word are `shr_nat`'s shift of the low words `V ≡ u F + v G`. -/
theorem fg_end {u v : Int} {F G k R : Nat} {lo hi prev : BitVec 64} (h : FGAcc u v F G k R lo hi prev)
    (hR : R < 2 ^ (64 * k)) :
    ∃ V : Nat, V < 2 ^ (64 * (k + 1)) ∧ (V : Int) % 2 ^ (64 * (k + 1)) = (u * F + v * G) % 2 ^ (64 * (k + 1)) ∧
      R + 2 ^ (64 * k) * (prev - (prev >>> 4) <<< 5).toNat =
        (V + 2 * (2 ^ (64 * k) * 2 ^ 63) * (if 2 ^ (64 * k) * 2 ^ 63 ≤ V then 2 ^ 64 - 1 else 0)) / 2 ^ 59 %
          (2 * (2 ^ (64 * k) * 2 ^ 63)) := by
  obtain ⟨A, last, hA, hp, hlin, hshr, -, -⟩ := h
  have hl := last.isLt
  refine ⟨A + 2 ^ (64 * k) * last.toNat, ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * k)) (show last.toNat + 1 ≤ 2 ^ 64 by omega_using [])
    rw [Nat.mul_add_one] at this
    rw [Nat.mul_succ, Nat.pow_add]; omega_using [hA, this]
  · rw [← hlin, Int.add_mul_emod_self_left]
  · rw [hp, ushr59_4]
    exact shr_arith64 last hA hshr hR

/-- Word 0 of the pass over `a` and `b` (at `dA`, `dB`, `m` at `dM`), `iv` in
`r4`: both accumulators' terms, `k₁ = t₀ iv` and `k₂`, and `k m₀` added with
no carry. -/
theorem abFirst_ok {t : State} {B : Addr} {Z dA dB dM : Nat} (hs : Scr t B Z)
    (p5 : t.gpr .r5 = off B dA) (p6 : t.gpr .r6 = off B dB) (p7 : t.gpr .r7 = off B dM)
    (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z)
    (m18 : t.gpr .r18 = sgn (t.gpr .r14)) (m19 : t.gpr .r19 = sgn (t.gpr .r15))
    (m20 : t.gpr .r20 = sgn (t.gpr .r16)) (m21 : t.gpr .r21 = sgn (t.gpr .r17)) :
    WP isa (.block abFirst) t fun u =>
      let x := word t.mem B dA
      let y := word t.mem B dB
      let mw := word t.mem B dM
      let l1 := lo2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22)
      let l2 := lo2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24)
      (u.gpr .r28 = l1 * t.gpr .r4 ∧ u.gpr .r12 = l2 * t.gpr .r4 ∧
        u.gpr .r22 = hi2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) ∧
        u.gpr .r23 = 0#64 - hi2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22) (t.gpr .r23) >>> 63 ∧
        u.gpr .r9 = macC (l1 * t.gpr .r4) mw l1 0#64 ∧
        u.gpr .r24 = hi2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) ∧
        u.gpr .r25 = 0#64 - hi2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24) (t.gpr .r25) >>> 63 ∧
        u.gpr .r11 = macC (l2 * t.gpr .r4) mw l2 0#64 ∧ u.mem = t.mem) ∧
      Keep [.r0, .r3, .r4, .r9, .r11, .r12, .r22, .r23, .r24, .r25, .r26, .r27, .r28] t u := by
  refine WP.keep _ ?_ (by decide)
  mcrun [abFirst, fterms, fterm, fmac, fshift, hi2, lo2, tlo, thi, sgn, macC, exec_adde, word, BitVec.add_zero,
    p5, p6, p7, m18, m19, m20, m21, hs.ld (show dA + 8 ≤ Z by omega_using [hA]), hs.ld (show dB + 8 ≤ Z by omega_using [hB]),
    hs.ld (show dM + 8 ≤ Z by omega_using [hM])]

/-- Word `ν - 1` of the new `a` or `b`: the low word with the carry. -/
abbrev lastLo (l c : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (l.toNat + c.toNat)

/-- Word `ν`: the low word's sign with the carry out. -/
abbrev lastHi (l c : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((0#64 - l >>> 63).toNat + (decide (2 ^ 64 ≤ l.toNat + c.toNat)).toNat)

/-- Word `ν` of the pass over `a` and `b` (pointers at word `ν - 1`, at `dA`,
`dB`): both accumulators' terms; the low words with the carries are words
`ν - 1`, and the low words' signs with the carries out words `ν`. -/
theorem abLast_ok {t : State} {B : Addr} {Z dA dB : Nat} (hs : Scr t B Z)
    (p5 : t.gpr .r5 = off B dA) (p6 : t.gpr .r6 = off B dB) (hA : dA + 16 ≤ Z) (hB : dB + 16 ≤ Z)
    (m18 : t.gpr .r18 = sgn (t.gpr .r14)) (m19 : t.gpr .r19 = sgn (t.gpr .r15))
    (m20 : t.gpr .r20 = sgn (t.gpr .r16)) (m21 : t.gpr .r21 = sgn (t.gpr .r17)) :
    WP isa (.block abLast) t fun u =>
      let x := word t.mem B (dA + 8)
      let y := word t.mem B (dB + 8)
      let l1 := lo2 (t.gpr .r14) (t.gpr .r15) x y (t.gpr .r22)
      let l2 := lo2 (t.gpr .r16) (t.gpr .r17) x y (t.gpr .r24)
      u.mem = (((t.mem.writeW (off B dA) (lastLo l1 (t.gpr .r9))).writeW (off B (dA + 8)) (lastHi l1 (t.gpr .r9))).writeW
        (off B dB) (lastLo l2 (t.gpr .r11))).writeW (off B (dB + 8)) (lastHi l2 (t.gpr .r11)) ∧
      Keep [.r3, .r4, .r22, .r23, .r24, .r25, .r26, .r27] t u := by
  refine WP.keep _ ?_ (by decide)
  mcrun [abLast, fterms, fterm, hi2, lo2, tlo, thi, sgn, lastLo, lastHi, exec_adde, word, p5, p6, m18, m19, m20,
    m21, hs.ld (show dA + 8 + 8 ≤ Z by omega_using [hA]), hs.ld (show dB + 8 + 8 ≤ Z by omega_using [hB]),
    hs.st (show dA + 8 ≤ Z by omega_using [hA]), hs.st (show dB + 8 ≤ Z by omega_using [hB]),
    hs.st (show dA + 8 + 8 ≤ Z by omega_using [hA]), hs.st (show dB + 8 + 8 ≤ Z by omega_using [hB])]

/-- The end of the pass over `a` and `b`, at word `n + 1 = ν` where `m`'s is
zero: the stored words with the last two are `mredRaw_nat`'s `E / 2^64` for
the low words `W ≡ u Da + v Db`. -/
theorem ab_end {c1 c2 : BitVec 64} {k w0 Da Db P n R : Nat} {lo hi c : BitVec 64} (x y : BitVec 64)
    (h1 : -2 ^ 61 ≤ c1.toInt) (h2 : c1.toInt ≤ 2 ^ 61) (h3 : -2 ^ 61 ≤ c2.toInt) (h4 : c2.toInt ≤ 2 ^ 61)
    (h : ABAcc c1.toInt c2.toInt k w0 Da Db P n R lo hi c) (hR : R < 2 ^ (64 * n)) :
    ∃ W : Nat, W < 2 ^ (64 * (n + 2)) ∧ W % 2 ^ 64 = w0 ∧
      (W : Int) % 2 ^ (64 * (n + 2)) = (c1.toInt * ((Da + 2 ^ (64 * (n + 1)) * x.toNat : Nat) : Int) +
        c2.toInt * ((Db + 2 ^ (64 * (n + 1)) * y.toNat : Nat) : Int)) % 2 ^ (64 * (n + 2)) ∧
      R + 2 ^ (64 * n) * (lastLo (lo2 c1 c2 x y lo) c).toNat +
          2 ^ (64 * (n + 1)) * (lastHi (lo2 c1 c2 x y lo) c).toNat =
        (W + 2 ^ (64 * (n + 1)) * 2 ^ 64 * (if 2 ^ (64 * (n + 1)) * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) + k * P) %
          (2 ^ (64 * (n + 1)) * 2 ^ 64 * 2 ^ 64) / 2 ^ 64 := by
  obtain ⟨A, hA, hw0, hlin, hmac, hb1, hb2⟩ := h
  have e := acc_two c1 c2 x y lo hi h1 h2 h3 h4 hb1 hb2
  have hl := (lo2 c1 c2 x y lo).isLt
  have hc := c.isLt
  have eM : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
  refine ⟨A + 2 ^ (64 * (n + 1)) * (lo2 c1 c2 x y lo).toNat, ?_, ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * (n + 1))) (show (lo2 c1 c2 x y lo).toNat + 1 ≤ 2 ^ 64 by omega_using [])
    rw [Nat.mul_add_one] at this
    rw [show 64 * (n + 2) = 64 * (n + 1) + 64 by omega_using [], Nat.pow_add]; omega_using [hA, this]
  · rw [eM, Nat.mul_assoc, Nat.add_mul_mod_self_left]; exact hw0
  · have := lin_inv_step (u := c1.toInt) (v := c2.toInt) (S0 := 0) (W := A) (by rw [Int.add_zero]; exact hlin) e
    rw [Int.add_zero, show 64 * (n + 1) + 64 = 64 * (n + 2) by omega_using []] at this
    rw [← this, Int.add_mul_emod_self_left]
  · generalize hL : lo2 c1 c2 x y lo = L at *
    have hlo : (lastLo L c).toNat = (L.toNat + c.toNat) % 2 ^ 64 := by simp only [lastLo, BitVec.toNat_ofNat]
    have hhi : (lastHi L c).toNat =
        ((if 2 ^ 63 ≤ L.toNat then 2 ^ 64 - 1 else 0) + (L.toNat + c.toNat) / 2 ^ 64) % 2 ^ 64 := by
      have hd : (decide (2 ^ 64 ≤ L.toNat + c.toNat)).toNat = (L.toNat + c.toNat) / 2 ^ 64 := by
        by_cases hc2 : 2 ^ 64 ≤ L.toNat + c.toNat
        · rw [decide_eq_true hc2, Bool.toNat_true]; omega_using [hc2]
        · rw [decide_eq_false hc2, Bool.toNat_false]; omega_using [hc2]
      rw [lastHi, BitVec.toNat_ofNat, hd, show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, signMask_toNat]
    have m := Divstep.WordArith.mred_arith (L := 2 ^ 64 * R) (Wlo := A) (P := P) (k := k) (A := 2 ^ (64 * (n + 1)))
      L.isLt hc hA (by rw [eM]; exact Nat.mul_lt_mul_of_pos_left hR (Nat.two_pow_pos 64))
      (by rw [eM, Nat.mul_assoc, ← Nat.mul_add]; exact hmac) hlo hhi
    rw [← m, eM]
    have : 2 ^ 64 * R + 2 ^ 64 * 2 ^ (64 * n) * (lastLo L c).toNat + 2 ^ 64 * 2 ^ (64 * n) * 2 ^ 64 *
        (lastHi L c).toNat = 2 ^ 64 * (R + 2 ^ (64 * n) * (lastLo L c).toNat + 2 ^ 64 * 2 ^ (64 * n) *
          (lastHi L c).toNat) := by
      rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [this, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64)]

end VG.Proof.Rsa.PPC64LE.InvBatch
