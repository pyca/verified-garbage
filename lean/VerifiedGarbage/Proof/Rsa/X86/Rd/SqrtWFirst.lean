module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.SqrtWBase
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Add
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.RecoverDetWords
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Loop
import VerifiedGarbage.Proof.Rsa.X86.Rd.Move
import VerifiedGarbage.Proof.Mont.WriteWord32
import VerifiedGarbage.Proof.Bignum.SqrtRem

-- separate module: the first digit's bit-pair loop is the square root's longest symbolic run

/-! # The square root by words on i686: the first digit

`firstX`: the root `s₀` of the normalized radicand's top two words by bit
pairs (`isqBody`, 32 runs), its remainder in their place, `2 s₀` at word
`W' - 1` of `sqD`, and `d = s₀` with its reciprocal in the header.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot aM
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Impl.Rsa.X86.Recover (aN)
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Mont.X86 (at_ sc)
open VG.Proof.Mont.X86.Rt (PtrAt)
open VG.Proof.Bignum.X86.R2Words (hdr_read)

theorem quad_toNat (x : BitVec 32) : (x + x + (x + x)).toNat = 4 * x.toNat % 2 ^ 32 := by
  simp only [BitVec.toNat_add]; omega

theorem quad_shr (x y : BitVec 32) :
    (x + x + (x + x) + y >>> 30).toNat = (4 * x.toNat + y.toNat / 2 ^ 30) % 2 ^ 32 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

/-! ## The bit-pair loop's body, in pieces between its header stores -/

abbrev isq1 : List Instr := [
  .mov .eax (.reg .ecx), .shift .shr .eax 30, .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi),
  .alu .add .esi (.reg .eax),
  .mov .eax (.reg .ebp), .shift .shr .eax 30, .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
  .alu .add .ecx (.reg .eax),
  .mov .edx (.mem (sc hTl)), .mov .eax (.reg .edx), .shift .shr .eax 30, .alu .add .ebp (.reg .ebp),
  .alu .add .ebp (.reg .ebp), .alu .add .ebp (.reg .eax), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx)]

theorem isq1_ok {s : State} {B : Addr} {bytes : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (di : PtrAt s B .edi 0) (hb : hTl + 4 ≤ bytes) :
    WP isa (.block isq1) s fun t => t.mem = s.mem ∧
      (t.gpr .esi).toNat = (4 * (s.gpr .esi).toNat + (s.gpr .ecx).toNat / 2 ^ 30) % 2 ^ 32 ∧
      (t.gpr .ecx).toNat = (4 * (s.gpr .ecx).toNat + (s.gpr .ebp).toNat / 2 ^ 30) % 2 ^ 32 ∧
      (t.gpr .ebp).toNat = (4 * (s.gpr .ebp).toNat + w32 s.mem B hTl / 2 ^ 30) % 2 ^ 32 ∧
      (t.gpr .edx).toNat = 4 * w32 s.mem B hTl % 2 ^ 32 ∧ t.gpr .ebx = s.gpr .ebx := by
  obtain ⟨hdi, aT, rT⟩ := hdr_read (o := hTl) ws di hb
  xrun [hdi, aT, rT, sc]
  simp only [Nat.zero_add, quad_shr, quad_toNat, w32]
  exact ⟨trivial, trivial, trivial, trivial⟩

abbrev isq2 : List Instr :=
  [.mov .eax (.reg .ebx), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .or .eax (.imm 1)]

theorem or_one_of_even {x : Nat} (h : x % 2 = 0) : x ||| 1 = x + 1 := by
  have e := Nat.shiftLeft_add_eq_or_of_lt (a := x / 2) (i := 1) (b := 1) (by decide)
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)] at e
  exact e.symm

theorem isq2_ok {s : State} :
    WP isa (.block isq2) s fun t => t.mem = s.mem ∧ (t.gpr .eax).toNat = 4 * (s.gpr .ebx).toNat % 2 ^ 32 + 1 := by
  xrun
  simp only [BitVec.toNat_or, BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
  rw [or_one_of_even (by omega)]
  omega

abbrev isq3 : List Instr := [.mov .edx (.reg .ebx), .shift .shr .edx 30]

theorem isq3_ok {s : State} :
    WP isa (.block isq3) s fun t => t.mem = s.mem ∧ (t.gpr .edx).toNat = (s.gpr .ebx).toNat / 2 ^ 30 := by
  xrun
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

open VG.Proof.Bignum.X86.R2Words (bmask and_bmask sbb_bmask)

theorem bmask_xor (c : Bool) : 0#32 - (BitVec.ofBool c).setWidth 32 ^^^ (-1) = bmask (!c) := by
  cases c <;> decide

abbrev isq4 : List Instr := [.alu .cmp .ecx (.reg .eax), .mov .eax (.reg .esi), .alu .sbb .eax (.reg .edx),
  .alu .sbb .eax (.reg .eax), .alu .xor .eax (.imm (-1)), .mov .edx (.mem (sc hTa)), .alu .and .edx (.reg .eax)]

theorem isq4_ok {s : State} {B : Addr} {bytes : Nat} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (di : PtrAt s B .edi 0) (hb : hTa + 4 ≤ bytes) :
    WP isa (.block isq4) s fun t => t.mem = s.mem ∧ t.gpr .ecx = s.gpr .ecx ∧
      t.gpr .eax = bmask (!decide ((s.gpr .esi).toNat <
        (s.gpr .edx).toNat + (decide ((s.gpr .ecx).toNat < (s.gpr .eax).toNat)).toNat)) ∧
      (t.gpr .edx).toNat = (if !decide ((s.gpr .esi).toNat <
        (s.gpr .edx).toNat + (decide ((s.gpr .ecx).toNat < (s.gpr .eax).toNat)).toNat) then w32 s.mem B hTa else 0) := by
  obtain ⟨hdi, aT, rT⟩ := hdr_read (o := hTa) ws di hb
  xrun [hdi, aT, rT, sc]
  simp only [bmask_xor, and_bmask, w32, Nat.zero_add, true_and]

abbrev isq5 : List Instr := [.mov .edx (.mem (sc hTb)), .alu .and .edx (.reg .eax), .alu .and .eax (.imm 1),
  .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .eax), .mov .eax (.mem (sc hTa)), .alu .sub .ecx (.reg .eax),
  .alu .sbb .esi (.reg .edx), .mov .eax (.mem (sc hCnt)), .alu .sub .eax (.imm 1)]

theorem sub32_toNat (a b : BitVec 32) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 32 * (decide (a.toNat < b.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

theorem bmask_and_one (c : Bool) : (bmask c &&& 1).toNat = c.toNat := by cases c <;> decide

theorem isq5_ok {s : State} {B : Addr} {bytes : Nat} {c : Bool} (ws : VG.Proof.Mont.X86.Rt.Ws s B bytes)
    (di : PtrAt s B .edi 0) (hb : hCnt + 4 ≤ bytes) (hax : s.gpr .eax = bmask c) :
    WP isa (.block isq5) s fun t => t.mem = s.mem ∧
      (t.gpr .ebx).toNat = (2 * (s.gpr .ebx).toNat + c.toNat) % 2 ^ 32 ∧
      (∃ c0 < 2, (t.gpr .ecx).toNat + w32 s.mem B hTa = (s.gpr .ecx).toNat + 2 ^ 32 * c0 ∧
        (t.gpr .esi).toNat + (if c then w32 s.mem B hTb else 0) + c0 = (s.gpr .esi).toNat + 2 ^ 32 *
          (decide ((s.gpr .esi).toNat < (if c then w32 s.mem B hTb else 0) + c0)).toNat) ∧
      t.zf = some (s.mem.readW (off B hCnt) 32 - 1 == 0) ∧
      t.gpr .eax = s.mem.readW (off B hCnt) 32 - 1 := by
  obtain ⟨hdi, aB, rB⟩ := hdr_read (o := hTb) ws di (by simp only [hTb, hCnt] at hb ⊢; omega)
  obtain ⟨-, aA, rA⟩ := hdr_read (o := hTa) ws di (by simp only [hTa, hCnt] at hb ⊢; omega)
  obtain ⟨-, aC, rC⟩ := hdr_read (o := hCnt) ws di hb
  xrun [hdi, aB, rB, aA, rA, aC, rC, sc, hax]
  simp only [Nat.zero_add, w32, and_true]
  refine ⟨?_, _, Bool.toNat_lt (decide ((s.gpr .ecx).toNat < (s.mem.readW (off B hTa) 32).toNat)),
    sub32_toNat _ _, ?_⟩
  · simp only [BitVec.toNat_add, bmask_and_one]; omega
  · have e := VG.Proof.Bignum.X86.R2Words.sbb32_toNat (s.gpr .esi) (s.mem.readW (off B hTb) 32 &&& bmask c)
      (decide ((s.gpr .ecx).toNat < (s.mem.readW (off B hTa) 32).toNat))
    rw [and_bmask] at e
    rw [← e]

/-! ## The arithmetic of a bit pair -/

/-- The pairs of `T` from pair `31 - i` on: four times those from `32 - i` on, and the pair at
the top of `T 4^i mod 2^64`. -/
theorem pair_top (T : Nat) {i : Nat} (hi : i < 32) :
    T / 4 ^ (32 - (i + 1)) = 4 * (T / 4 ^ (32 - i)) + T * 4 ^ i % 2 ^ 64 / 2 ^ 62 := by
  have e := VG.Proof.Rsa.RecoverDet.pair_succ T (31 - i)
  rw [show 31 - i + 1 = 32 - i by omega, show 31 - i = 32 - (i + 1) by omega] at e
  rw [e]
  congr 1
  have h64 : (2 : Nat) ^ 64 = 4 ^ i * (4 ^ (32 - (i + 1)) * 4) := by
    rw [← Nat.pow_succ, ← Nat.pow_add, show (2 : Nat) ^ 64 = 4 ^ 32 by decide]; congr 1; omega
  have h62 : (2 : Nat) ^ 62 = 4 ^ i * 4 ^ (32 - (i + 1)) := by
    rw [← Nat.pow_add, show (2 : Nat) ^ 62 = 4 ^ 31 by decide]; congr 1; omega
  rw [h64, h62, Nat.mul_comm T, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ (Nat.pow_pos (by decide)),
    Nat.mod_mul_right_div_self]

/-- A bit pair's step: from `y² + R = N`, `R ≤ 2 y`, the root `2 y + c` and remainder of `4 N + p`. -/
theorem isq_step {N p y R : Nat} (hp : p < 4) (hyR : y * y + R = N) (hRy : R ≤ 2 * y) :
    (2 * y + (decide (4 * y + 1 ≤ 4 * R + p)).toNat) * (2 * y + (decide (4 * y + 1 ≤ 4 * R + p)).toNat) +
        (4 * R + p - (decide (4 * y + 1 ≤ 4 * R + p)).toNat * (4 * y + 1)) = 4 * N + p ∧
      4 * R + p - (decide (4 * y + 1 ≤ 4 * R + p)).toNat * (4 * y + 1) ≤
        2 * (2 * y + (decide (4 * y + 1 ≤ 4 * R + p)).toNat) := by
  have e0 : (2 * y) * (2 * y) = 4 * (y * y) := by grind
  have e1 : (2 * y + 1) * (2 * y + 1) = 4 * (y * y) + 4 * y + 1 := by grind
  by_cases hc : 4 * y + 1 ≤ 4 * R + p
  · simp only [hc, decide_true, Bool.toNat_true, Nat.one_mul]
    rw [e1]; omega
  · simp only [hc, decide_false, Bool.toNat_false, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    rw [e0]; omega

theorem root_lt {T i y R : Nat} (hT : T < 2 ^ 64) (hi : i ≤ 32) (hyR : y * y + R = T / 4 ^ (32 - i)) :
    y < 2 ^ i := by
  have hN : T / 4 ^ (32 - i) < 2 ^ i * 2 ^ i := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.mul_pow,
      show 2 * 2 = 4 from rfl, ← Nat.pow_add, show i + (32 - i) = 32 by omega]
    exact Nat.lt_of_lt_of_le hT (by decide)
  refine Nat.lt_of_not_le fun c => ?_
  have := Nat.mul_le_mul c c
  omega

/-- The remainder brought down a pair, and whether it is at least `4 y + 1`, from the registers. -/
theorem isq_regs {e0 c0 Th y R : Nat} (hc0 : c0 < 2 ^ 32) (hTh : Th < 2 ^ 32)
    (hR : e0 * 2 ^ 32 + c0 = R) (hRy : R ≤ 2 * y) (hy : y < 2 ^ 31) :
    (4 * e0 + c0 / 2 ^ 30) % 2 ^ 32 * 2 ^ 32 + (4 * c0 + Th / 2 ^ 30) % 2 ^ 32 = 4 * R + Th / 2 ^ 30 ∧
    (!decide ((4 * e0 + c0 / 2 ^ 30) % 2 ^ 32 < y / 2 ^ 30 +
        (decide ((4 * c0 + Th / 2 ^ 30) % 2 ^ 32 < 4 * y % 2 ^ 32 + 1)).toNat)) =
      decide (4 * y + 1 ≤ 4 * R + Th / 2 ^ 30) := by
  have he : e0 = 0 := by omega
  subst he
  have hp : Th / 2 ^ 30 < 4 := by omega
  generalize Th / 2 ^ 30 = p at *
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add] at hR ⊢
  subst hR
  have h4 : c0 / 2 ^ 30 % 2 ^ 32 = c0 / 2 ^ 30 := by omega
  rw [h4]
  have e : c0 / 2 ^ 30 * 2 ^ 32 + (4 * c0 + p) % 2 ^ 32 = 4 * c0 + p := by omega
  refine ⟨e, ?_⟩
  have key : (c0 / 2 ^ 30 < y / 2 ^ 30 + (decide ((4 * c0 + p) % 2 ^ 32 < 4 * y % 2 ^ 32 + 1)).toNat) ↔
      4 * c0 + p < 4 * y + 1 := by
    by_cases h1 : (4 * c0 + p) % 2 ^ 32 < 4 * y % 2 ^ 32 + 1
    · rw [decide_eq_true h1, Bool.toNat_true]; omega
    · rw [decide_eq_false h1, Bool.toNat_false]; omega
  by_cases h2 : 4 * y + 1 ≤ 4 * c0 + p
  · rw [decide_eq_true h2, decide_eq_false (by rw [key]; omega)]; rfl
  · rw [decide_eq_false h2, decide_eq_true (by rw [key]; omega)]; rfl

/-- The subtraction of `4 y + 1` where the mask is set. -/
theorem isq_sub {e1 c1 e9 c9 y k0 : Nat} (cb : Bool) (he9 : e9 < 2 ^ 32) (hc9 : c9 < 2 ^ 32)
    (hc1 : c1 < 2 ^ 32) (hcb : cb = decide (4 * y + 1 ≤ e1 * 2 ^ 32 + c1))
    (h1 : c9 + (if cb then 4 * y % 2 ^ 32 + 1 else 0) = c1 + 2 ^ 32 * k0)
    (h2 : e9 + (if cb then y / 2 ^ 30 else 0) + k0 =
      e1 + 2 ^ 32 * (decide (e1 < (if cb then y / 2 ^ 30 else 0) + k0)).toNat) :
    e9 * 2 ^ 32 + c9 = e1 * 2 ^ 32 + c1 - cb.toNat * (4 * y + 1) := by
  cases cb with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero, Bool.toNat_false, Nat.zero_mul, Nat.sub_zero] at h1 h2 ⊢
    have : k0 = 0 := by omega
    subst this
    simp at h2; omega
  | true =>
    simp only [ite_true, Bool.toNat_true, Nat.one_mul] at h1 h2 hcb ⊢
    have hc := of_decide_eq_true hcb.symm
    by_cases h3 : e1 < y / 2 ^ 30 + k0
    · exfalso
      simp only [h3, decide_true, Bool.toNat_true] at h2
      have : k0 ≤ 1 := by omega
      omega
    · simp only [h3, decide_false, Bool.toNat_false] at h2; omega

theorem quad_mod (T i : Nat) : T * 4 ^ (i + 1) % 2 ^ 64 = 4 * (T * 4 ^ i % 2 ^ 64) % 2 ^ 64 := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 4, Nat.mul_mod, Nat.mod_eq_of_lt (show 4 < 2 ^ 64 by decide)]

theorem dec_toNat {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 32) : (BitVec.ofNat 32 k - 1).toNat = k - 1 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2, show (1 : BitVec 32).toNat = 1 from rfl]; omega

theorem dec_beq {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 32) : (BitVec.ofNat 32 k - 1 == 0) = decide (k = 1) := by
  by_cases hk : k = 1
  · subst hk; decide
  · have : BitVec.ofNat 32 k - 1 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [dec_toNat h1 h2] at this; simp at this; omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [hk]

/-! ## A run of the loop -/

theorem isqBody_eq : isqBody = isq1 ++ (([.store (sc hTl) .edx] : List Instr) ++ (isq2 ++
    (([.store (sc hTa) .eax] : List Instr) ++ (isq3 ++ (([.store (sc hTb) .edx] : List Instr) ++ (isq4 ++
    (([.store (sc hTa) .edx] : List Instr) ++ (isq5 ++ ([.store (sc hCnt) .eax] : List Instr))))))))) := rfl

/-- After `i` runs of `isqBody` on the top two words `T`: the root `y` of `T`'s top `i` pairs in
`ebx`, its remainder `R ≤ 2 y` in `esi:ecx`, `T 4^i mod 2^64` in `ebp:hTl`, `32 - i` in `hCnt`. -/
def IsqI (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat) (liveW : List Nat)
    (V0 : Nat → Nat) (T i : Nat) (u : State) : Prop :=
  ∃ V y R, KS g s0 A live AW liveW V (hTl :: hCnt :: lsN) u ∧ (∀ d ∈ lsN, V d = V0 d) ∧
    V hTl = T * 4 ^ i % 2 ^ 64 % 2 ^ 32 ∧ V hCnt = 32 - i ∧
    (u.gpr .ebp).toNat = T * 4 ^ i % 2 ^ 64 / 2 ^ 32 ∧
    (u.gpr .esi).toNat * 2 ^ 32 + (u.gpr .ecx).toNat = R ∧ (u.gpr .ebx).toNat = y ∧
    y * y + R = T / 4 ^ (32 - i) ∧ R ≤ 2 * y

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem KS.hdrAcc (h : KS g s0 A live AW liveW V ls s) :
    VG.Proof.Mont.X86.Rt.Ws s g.B g.Z ∧ PtrAt s g.B .edi 0 ∧ 160 ≤ g.Z := by
  have ws := h.rt.rt
  have nw := ws.nowrap
  have hz : 160 ≤ g.Z := by have := h.ws.hdr_le; simpa [hdr] using this
  refine ⟨ws, ?_, hz⟩
  rw [PtrAt, h.rt.edi, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

theorem lsN_slots : ∀ d ∈ lsN, d ≠ hTl ∧ d ≠ hTa ∧ d ≠ hTb ∧ d ≠ hCnt := by decide

theorem isqIter_ok {V0 : Nat → Nat} {T i : Nat} (hi : i < 32) (hT : T < 2 ^ 64)
    (I : IsqI g s0 A live AW liveW V0 T i s) :
    WP isa (.block isqBody) s fun t => t.zf = some (decide (i + 1 = 32)) ∧
      IsqI g s0 A live AW liveW V0 T (i + 1) t := by
  obtain ⟨V, y, R, h, hV, hVt, hVc, hbp, hR, hy, hyR, hRy⟩ := I
  have yl := root_lt hT (by omega) hyR
  have p31 : 2 ^ i ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨ws, di, hz⟩ := h.hdrAcc
  rw [isqBody_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.eax, .ecx, .edx, .esi, .ebp] (isq1_ok ws di (by simp only [hTl]; omega)) rfl)
    fun u₁ ⟨⟨m₁, si₁, cx₁, bp₁, dx₁, bx₁⟩, K₁⟩ => ?_
  have h₁ := h.of_rest K₁ (by decide) m₁
  rw [WP.block_append_iff]
  refine WP.mono (h₁.storeSlot (d := hTl) (by decide) .edx) fun u₂ ⟨h₂, _, K₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.eax] isq2_ok rfl) fun u₃ ⟨⟨m₃, ax₃⟩, K₃⟩ => ?_
  have h₃ := h₂.of_rest K₃ (by decide) m₃
  rw [WP.block_append_iff]
  refine WP.mono (h₃.storeSlot (d := hTa) (by decide) .eax) fun u₄ ⟨h₄, _, K₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.edx] isq3_ok rfl) fun u₅ ⟨⟨m₅, dx₅⟩, K₅⟩ => ?_
  have h₅ := h₄.of_rest K₅ (by decide) m₅
  rw [WP.block_append_iff]
  refine WP.mono (h₅.storeSlot (d := hTb) (by decide) .edx) fun u₆ ⟨h₆, _, K₆⟩ => ?_
  obtain ⟨ws₆, di₆, -⟩ := h₆.hdrAcc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.eax, .ecx, .edx] (isq4_ok ws₆ di₆ (by simp only [hTa]; omega)) rfl)
    fun u₇ ⟨⟨m₇, cx₇, ax₇, dx₇⟩, K₇⟩ => ?_
  have h₇ := h₆.of_rest K₇ (by decide) m₇
  rw [WP.block_append_iff]
  refine WP.mono (h₇.storeSlot (d := hTa) (by decide) .edx) fun u₈ ⟨h₈, _, K₈⟩ => ?_
  obtain ⟨ws₈, di₈, -⟩ := h₈.hdrAcc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86.R2Words.WP.keeps [.eax, .ebx, .ecx, .edx, .esi] (isq5_ok ws₈ di₈ (by simp only [hCnt]; omega)
    ((K₈.1 .eax (by decide)).trans ax₇)) rfl) fun u₉ ⟨⟨m₉, bx₉, ⟨c0, c0l, cx₉, si₉⟩, zf₉, ax₉⟩, K₉⟩ => ?_
  have h₉ := h₈.of_rest K₉ (by decide) m₉
  refine WP.mono (h₉.storeSlot (d := hCnt) (by decide) .eax) fun t ⟨ht, zt, Kt⟩ => ?_
  -- The header words read back.
  have eTl : w32 s.mem g.B hTl = T * 4 ^ i % 2 ^ 64 % 2 ^ 32 := (h.sl hTl (by simp)).trans hVt
  have eTa6 : w32 u₆.mem g.B hTa = (u₃.gpr .eax).toNat := (h₆.sl hTa (by simp)).trans (by simp [upd, hTa, hTb])
  have eTa8 : w32 u₈.mem g.B hTa = (u₇.gpr .edx).toNat := (h₈.sl hTa (by simp)).trans (by simp [upd, hTa])
  have eTb8 : w32 u₈.mem g.B hTb = (u₅.gpr .edx).toNat := (h₈.sl hTb (by simp)).trans (by simp [upd, hTa, hTb])
  have eC8 : u₈.mem.readW (off g.B hCnt) 32 = BitVec.ofNat 32 (32 - i) := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact (h₈.sl hCnt (by simp)).trans (by simp [upd, hTa, hTb, hTl, hCnt]; exact hVc))
  -- The registers through the stores.
  have bx₂ : u₂.gpr .ebx = s.gpr .ebx := by rw [K₂.1 _ (by decide), bx₁]
  have bx₈ : u₈.gpr .ebx = s.gpr .ebx := by
    rw [K₈.1 _ (by decide), K₇.1 _ (by decide), K₆.1 _ (by decide), K₅.1 _ (by decide), K₄.1 _ (by decide),
      K₃.1 _ (by decide), bx₂]
  have si₆ : u₆.gpr .esi = u₁.gpr .esi := by
    rw [K₆.1 _ (by decide), K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]
  have cx₆ : u₆.gpr .ecx = u₁.gpr .ecx := by
    rw [K₆.1 _ (by decide), K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]
  have dx₆ : u₆.gpr .edx = u₅.gpr .edx := K₆.1 _ (by decide)
  have ax₆ : u₆.gpr .eax = u₃.gpr .eax := by rw [K₆.1 _ (by decide), K₅.1 _ (by decide), K₄.1 _ (by decide)]
  have si₈ : u₈.gpr .esi = u₁.gpr .esi := by rw [K₈.1 _ (by decide), K₇.1 _ (by decide), si₆]
  have cx₈ : u₈.gpr .ecx = u₁.gpr .ecx := by rw [K₈.1 _ (by decide), cx₇, cx₆]
  have bpt : t.gpr .ebp = u₁.gpr .ebp := by
    rw [Kt.1 _ (by decide), K₉.1 _ (by decide), K₈.1 _ (by decide), K₇.1 _ (by decide), K₆.1 _ (by decide),
      K₅.1 _ (by decide), K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]
  -- The numbers.
  generalize hcb : (!decide ((u₆.gpr .esi).toNat < (u₆.gpr .edx).toNat +
    (decide ((u₆.gpr .ecx).toNat < (u₆.gpr .eax).toNat)).toNat)) = cb at ax₇ dx₇ si₉ bx₉
  rw [si₆, cx₆, dx₆, ax₆] at hcb
  rw [eTa6] at dx₇
  rw [eTa8, cx₈] at cx₉
  rw [eTb8, si₈] at si₉
  rw [bx₈, hy] at bx₉
  rw [eC8, dec_beq (by omega) (by omega)] at zf₉
  rw [eC8] at ax₉
  rw [eTl] at bp₁ dx₁
  rw [hbp] at cx₁ bp₁
  rw [bx₂, hy] at ax₃
  rw [K₄.1 _ (by decide), K₃.1 _ (by decide), bx₂, hy] at dx₅
  rw [ax₃] at dx₇
  rw [dx₇] at cx₉
  rw [dx₅] at si₉
  have hp := pair_top T hi
  generalize hTq : T * 4 ^ i % 2 ^ 64 = Tq at hbp eTl bp₁ dx₁ cx₁ hp
  have hTq64 : Tq < 2 ^ 64 := hTq ▸ Nat.mod_lt _ (by decide)
  have hRl := (s.gpr .ecx).isLt
  obtain ⟨eR, eB⟩ := isq_regs (e0 := (s.gpr .esi).toNat) (Th := Tq / 2 ^ 32) (y := y) hRl
    (by omega) hR hRy (by omega)
  rw [← si₁, ← cx₁, ← ax₃, ← dx₅, hcb] at eB
  have p62 : Tq / 2 ^ 62 = Tq / 2 ^ 32 / 2 ^ 30 := by omega
  rw [← p62] at eB
  have eR' : (u₁.gpr .esi).toNat * 2 ^ 32 + (u₁.gpr .ecx).toNat = 4 * R + Tq / 2 ^ 62 := by
    rw [si₁, cx₁, p62]; exact eR
  have hcb' : cb = decide (4 * y + 1 ≤ (u₁.gpr .esi).toNat * 2 ^ 32 + (u₁.gpr .ecx).toNat) := by
    rw [eR']; exact eB
  have eS := isq_sub cb (u₉.gpr .esi).isLt (u₉.gpr .ecx).isLt (u₁.gpr .ecx).isLt hcb' cx₉ si₉
  rw [eR'] at eS
  obtain ⟨yS, rS⟩ := isq_step (N := T / 4 ^ (32 - i)) (p := Tq / 2 ^ 62) (by omega) hyR hRy
  rw [← eB] at yS rS
  have sub : ∀ d ∈ hTl :: hCnt :: lsN, d ∈ hCnt :: hTa :: hTb :: hTa :: hTl :: hTl :: hCnt :: lsN := by decide
  have cb1 := Bool.toNat_le cb
  refine ⟨by rw [zt, zf₉]; exact congrArg some (decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩), _, 2 * y + cb.toNat,
    4 * R + Tq / 2 ^ 62 - cb.toNat * (4 * y + 1),
    ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨sub d hd, rfl⟩),
    fun d hd => ?_, ?_, ?_, ?_, ?_, ?_, by rw [hp]; exact yS, rS⟩
  · obtain ⟨n1, n2, n3, n4⟩ := lsN_slots d hd
    rw [upd_ne _ _ n4, upd_ne _ _ n2, upd_ne _ _ n3, upd_ne _ _ n2, upd_ne _ _ n1]; exact hV d hd
  · simp only [upd, hTa, hTb, hTl, hCnt, ↓reduceIte, Nat.reduceEqDiff]
    rw [dx₁, quad_mod, hTq]; omega_using []
  · simp only [upd, hCnt, ↓reduceIte]
    rw [ax₉, dec_toNat (by omega) (by omega)]; omega_using []
  · rw [bpt, bp₁, quad_mod, hTq]; omega_using [hTq64]
  · rw [Kt.1 _ (by decide), Kt.1 _ (by decide)]; exact eS
  · rw [Kt.1 _ (by decide), bx₉, Nat.mod_eq_of_lt (by omega_using [yl, p31, cb1])]
  

theorem isqLoop_ok {V0 : Nat → Nat} {T : Nat} (hT : T < 2 ^ 64)
    (I : IsqI g s0 A live AW liveW V0 T 0 s) :
    WP isa (.loop (.block isqBody) .ne) s (IsqI g s0 A live AW liveW V0 T 32) := by
  refine WP.loop (M := isa) (Q := IsqI g s0 A live AW liveW V0 T 32)
    (fun n v => ∃ i, n = 32 - i ∧ i < 32 ∧ IsqI g s0 A live AW liveW V0 T i v) ?_ (32 - 0) s
    ⟨0, rfl, by decide, I⟩
  rintro n v ⟨i, rfl, hi, J⟩
  refine WP.mono (isqIter_ok hi hT J) fun v' ⟨z, J'⟩ => ?_
  by_cases e : i + 1 = 32
  · exact .inl ⟨by simp only [eval, z, e, decide_true, Option.map_some, Bool.not_true], e ▸ J'⟩
  · exact .inr ⟨by simp only [eval, z, e, decide_false, Option.map_some, Bool.not_false], 32 - (i + 1),
      by omega, i + 1, rfl, by omega, J'⟩

end

/-! ## Pointers at the radicand's top words, and two words written -/

open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)

/-- `topH r j i t`: `r` at word `2 W' - i` of the wide array `j`, for `W' = wq a`. -/
theorem topH_ok {s : State} {is : List Instr} {Q : State → Prop} {B : Addr} {Z len N : Nat}
    (h : RtWs wid s B Z len N) {a j i : Nat} {r t : Reg} (hm : MLen s B Z nl a) (hj : j < N)
    (hrt : r ≠ t) (hte : t ≠ .edi) (hrs : r ≠ .esp) (hts : t ≠ .esp) (hi : i ≤ 2 * wq a)
    (hw : 2 * wq a ≤ kw len + 2)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (arr (kw len) j + 8 * wq a - 4 * i) →
      WP isa (.block is) u Q) :
    WP isa (.block (topH r j i t ++ is)) s Q := by
  have fit := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  simp only [topH, List.append_assoc, List.cons_append, List.nil_append]
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi hrt hte (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  have hm₁ : MLen u₁ B Z nl a :=
    hm.keep K₁ (by simp [hrs.symm, hts.symm]) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine VG.Proof.Rsa.X86.WordRt.width4_ok hm₁ fun u₂ K₂ m₂ e₂ => wp_addS rfl fun u₃ U₃ _ =>
    wp_addS rfl fun u₄ U₄ _ => wp_subS rfl fun u₅ U₅ _ => ?_
  have K : Keeps [r, t] s u₅ := (K₁.trans (K₂.mono (by simp))).trans
    ((U₃.keeps.mono (by simp)).trans ((U₄.keeps.mono (by simp)).trans (U₅.keeps.mono (by simp))))
  refine kk u₅ K (by rw [U₅.mem, U₄.mem, U₃.mem, m₂, m₁]) ?_
  have hp₂ : PtrAt u₂ B r (arr (kw len) j) := by rw [PtrAt, K₂.1 _ (by simp [hrt])]; exact p₁
  have et₃ : u₃.gpr t = u₂.gpr t := U₃.other _ hrt.symm
  rw [PtrAt, U₅.gpr, U₄.gpr, U₃.gpr, et₃, e₂]
  have h4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
  have hi4 : (BitVec.ofNat 32 (4 * i)).toNat = 4 * i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, hp₂, h4, hi4]
  have := B.isLt
  omega

/-- Words `k` and `k + 1` of a number written, `k + 1` first, its words from `k + 2` on zero. -/
theorem val32_write_two (m : Mem) (B : Addr) {d k n : Nat} (lo hi : BitVec 32) (hk : k + 2 ≤ n)
    (fit : d + 4 * n ≤ 2 ^ 64) (hz : val32 m B (d + 4 * (k + 2)) (n - (k + 2)) = 0) :
    val32 ((m.writeW (off B (d + 4 * (k + 1))) hi).writeW (off B (d + 4 * k)) lo) B d n =
      val32 m B d k + 2 ^ (32 * k) * (lo.toNat + 2 ^ 32 * hi.toNat) := by
  have o1 := writeW32_outside m B (d := d + 4 * (k + 1)) hi (by omega)
  have o2 := writeW32_outside (m.writeW (off B (d + 4 * (k + 1))) hi) B (d := d + 4 * k) lo (by omega)
  obtain ⟨r, rfl⟩ : ∃ r, n = k + (2 + r) := ⟨n - (k + 2), by omega⟩
  rw [show k + (2 + r) - (k + 2) = r by omega] at hz
  generalize hm' : (m.writeW (off B (d + 4 * (k + 1))) hi).writeW (off B (d + 4 * k)) lo = m' at o2
  have e1 : val32 m' B d k = val32 m B d k := by
    rw [o2.val32 (.inl (by omega)) (by omega), o1.val32 (.inl (by omega)) (by omega)]
  have e2 : val32 m' B (d + 4 * k + 4 * 2) r = 0 := by
    rw [o2.val32 (.inr (by omega)) (by omega), o1.val32 (.inr (by omega)) (by omega),
      show d + 4 * k + 4 * 2 = d + 4 * (k + 2) by omega, hz]
  have e3 : w32 m' B (d + 4 * k) = lo.toNat := by rw [← hm', w32_write_self]
  have e4 : w32 m' B (d + 4 * k + 4) = hi.toNat := by
    rw [o2.w32 (.inr (by omega)) (by omega), show d + 4 * k + 4 = d + 4 * (k + 1) by omega, w32_write_self]
  rw [val32_append, val32_append _ _ (d + 4 * k), e1, e2]
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [e3, e4]

/-- The top two words of a number of `2 W'` words. -/
theorem top2_split {X W' : Nat} (hW : 1 ≤ W') (hX : X < 2 ^ (64 * W')) :
    X / 2 ^ (32 * (2 * W' - 1)) % 2 ^ 32 = X / 2 ^ (64 * (W' - 1)) / 2 ^ 32 ∧
      X / 2 ^ (32 * (2 * W' - 2)) % 2 ^ 32 = X / 2 ^ (64 * (W' - 1)) % 2 ^ 32 ∧
      X / 2 ^ (64 * (W' - 1)) < 2 ^ 64 := by
  have hT : X / 2 ^ (64 * (W' - 1)) < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 + 64 * (W' - 1) = 64 * W' by omega]
    exact hX
  refine ⟨?_, ?_, hT⟩
  · rw [show 32 * (2 * W' - 1) = 64 * (W' - 1) + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [show 32 * (2 * W' - 2) = 64 * (W' - 1) by omega]

section
variable {g : Geo} {s0 : State} {A : Nat → Nat} {live : List Nat} {liveW : List Nat}

theorem kwW2 (g : Geo) : kw (16 * g.n + 24) = 2 * g.w + 2 := by rw [kw_wid]; rfl

open VG.Proof.Mont.X86.Rt (readSrc_ptr ptr_sub)

/-- The loop's set-up: the radicand's top two words `T` in `ebp` and `hTl`, the root and remainder
zero, the count 32. -/
theorem firstSetup_ok {u : State} {AW V : Nat → Nat} {X a : Nat}
    (h : KS g s0 A live AW liveW V lsN u) (hR : wR ∈ liveW) (hX : AW wR = X)
    (hm : MLen u g.B g.Z nl a) (ha0 : 1 ≤ a) (haw : wq a ≤ g.w) (hXa : X < 2 ^ (64 * wq a)) :
    WP isa (.block (topH .eax sqZ 1 .edx ++ ([.mov .ebp (.mem (at_ .eax 0)), .alu .sub .eax (.imm 4),
      .mov .edx (.mem (at_ .eax 0)), .store (sc hTl) .edx, .mov .ebx (.imm 0), .mov .ecx (.imm 0),
      .mov .esi (.imm 0), .mov .eax (.imm 32), .store (sc hCnt) .eax] : List Instr))) u
      (IsqI g s0 A live AW liveW V (X / 2 ^ (64 * (wq a - 1))) 0) := by
  have hr := h.rtW
  have eW := kwW2 g
  have wl : wq a ≥ 1 := by simp only [wq]; omega
  have fit := h.wsW.arr_fit (h.liveW_lt wR hR)
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  rw [show g.W = 2 * g.w + 2 from rfl] at fit
  refine topH_ok hr hm (h.liveW_lt wR hR) (r := .eax) (t := .edx) (j := sqZ) (i := 1) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega) fun u₁ K₁ m₁ p₁ => ?_
  rw [eW] at p₁
  have h₁ := h.of_rest (K₁.mono (by decide) : Keeps [.eax, .edx] u u₁) (by decide) m₁
  obtain ⟨ws₁, -, -⟩ := h₁.hdrAcc
  have aW : arr g.W wR = arr (2 * g.w + 2) wR := rfl
  refine wp_movS (readSrc_ptr ws₁ p₁ (d := 0) (by rw [show sqZ = wR from rfl]; omega)) fun u₂ U₂ _ => ?_
  refine wp_subS rfl fun u₃ U₃ _ => ?_
  have p₃ : PtrAt u₃ g.B .eax (arr (2 * g.w + 2) sqZ + 8 * wq a - 4 * 1 - 4) := by
    rw [PtrAt, U₃.gpr, U₂.other _ (by decide), ptr_sub p₁ _ (by simp; omega)]; simp
  have ws₃ := ws₁.of_wr (U₃.wr.trans U₂.wr)
  refine wp_movS (readSrc_ptr ws₃ p₃ (d := 0) (by rw [show sqZ = wR from rfl]; omega)) fun u₄ U₄ _ => ?_
  have K₄ : Keeps [.ebp, .eax, .edx] u₁ u₄ :=
    (U₂.keeps.mono (by decide)).trans ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))
  have h₄ := h₁.of_rest K₄ (by decide) (by rw [U₄.mem, U₃.mem, U₂.mem])
  refine storeHdr h₄.ws (d := hTl) (by decide) .edx fun u₅ K₅ e₅ k₅ _ _ => ?_
  have h₅ := h₄.slot1 K₅ (by decide) (k₅.mono (by decide)) e₅
  refine wp_movS rfl fun u₆ U₆ _ => wp_movS rfl fun u₇ U₇ _ => wp_movS rfl fun u₈ U₈ _ =>
    wp_movS rfl fun u₉ U₉ _ => ?_
  have K₉ : Keeps [.ebx, .ecx, .esi, .eax] u₅ u₉ := (U₆.keeps.mono (by decide)).trans
    ((U₇.keeps.mono (by decide)).trans ((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide))))
  have h₉ := h₅.of_rest K₉ (by decide) (by rw [U₉.mem, U₈.mem, U₇.mem, U₆.mem])
  refine storeHdr h₉.ws (d := hCnt) (by decide) .eax fun t Kt et kt _ _ => WP.block_nil ?_
  have ht := h₉.slot1 Kt (by decide) (kt.mono (by decide)) et
  -- The top two words.
  obtain ⟨e1, e2, hT⟩ := top2_split wl hXa
  have num_u : val32 u.mem g.B (arr (2 * g.w + 2) wR) (2 * g.w + 2) = X := (h.arrsW wR hR).trans hX
  have w1 := VG.Proof.Rsa.X86.WordRt.w32_of_val32 u.mem g.B (d := arr (2 * g.w + 2) wR) (n := 2 * g.w + 2)
    (k := 2 * wq a - 1) (by omega)
  have w2 := VG.Proof.Rsa.X86.WordRt.w32_of_val32 u.mem g.B (d := arr (2 * g.w + 2) wR) (n := 2 * g.w + 2)
    (k := 2 * wq a - 2) (by omega)
  rw [num_u, e1] at w1
  rw [num_u, e2] at w2
  have sub : ∀ d ∈ hTl :: hCnt :: lsN, d ∈ hCnt :: hTl :: lsN := by decide
  refine ⟨_, 0, 0, ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨sub d hd, rfl⟩),
    fun d hd => ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.le_refl _⟩
  · obtain ⟨n1, -, -, n4⟩ := lsN_slots d hd
    rw [upd_ne _ _ n4, upd_ne _ _ n1]
  · rw [upd_ne _ _ (by decide), upd_self, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT]
    rw [U₄.gpr, U₃.mem, U₂.mem, m₁, show arr (2 * g.w + 2) sqZ + 8 * wq a - 4 * 1 - 4 + 0 =
      arr (2 * g.w + 2) wR + 4 * (2 * wq a - 2) by rw [show sqZ = wR from rfl]; omega]
    exact w2
  · rw [upd_self, U₉.gpr]; rfl
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT, kt.1 _ (by decide), U₉.other _ (by decide),
      U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide), k₅.1 _ (by decide),
      U₄.other _ (by decide), U₃.other _ (by decide), U₂.gpr, m₁, show arr (2 * g.w + 2) sqZ + 8 * wq a - 4 * 1 + 0 =
      arr (2 * g.w + 2) wR + 4 * (2 * wq a - 1) by rw [show sqZ = wR from rfl]; omega]
    exact w1
  · rw [kt.1 .esi (by decide), kt.1 .ecx (by decide), U₉.other .esi (by decide), U₉.other .ecx (by decide),
      U₈.gpr, U₈.other .ecx (by decide), U₇.gpr]; rfl
  · rw [kt.1 _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide), U₆.gpr]; rfl
  · rw [Nat.div_eq_of_lt (by rw [Nat.sub_zero, show (4 : Nat) ^ 32 = 2 ^ 64 by decide]; exact hT)]

open VG.Proof.Mont.X86.Rt (ea_ptr ws_write)

/-- A number below `2^(32 k)` of `n ≥ k` words: its words from `k` on are zero. -/
theorem val32_high_zero {m : Mem} {B : Addr} {d k n : Nat} (hk : k ≤ n) (h : val32 m B d n < 2 ^ (32 * k)) :
    val32 m B (d + 4 * k) (n - k) = 0 := by
  rw [show n = k + (n - k) by omega, val32_append] at h
  rw [show n - k = k + (n - k) - k by omega]
  have := Nat.two_pow_pos (32 * k)
  rcases Nat.eq_zero_or_pos (val32 m B (d + 4 * k) (k + (n - k) - k)) with e | e
  · exact e
  · exfalso
    rw [show k + (n - k) - k = n - k by omega] at e
    have := Nat.le_mul_of_pos_right (2 ^ (32 * k)) e
    omega

/-- The remainder `esi:ecx` into the radicand's words `H - 2` and `H - 1`. -/
theorem postZ_ok {u : State} {AW V : Nat → Nat} {ls : List Nat} {X a r : Nat}
    (h : KS g s0 A live AW liveW V ls u) (hR : wR ∈ liveW) (hX : AW wR = X)
    (hm : MLen u g.B g.Z nl a) (ha0 : 1 ≤ a) (haw : wq a ≤ g.w) (hXa : X < 2 ^ (64 * wq a))
    (hl : ∀ j ∈ live, j / 2 ≠ wR) (hr : (u.gpr .esi).toNat * 2 ^ 32 + (u.gpr .ecx).toNat = r) :
    WP isa (.block (topH .eax sqZ 1 .edx ++ ([.store (at_ .eax 0) .esi, .alu .sub .eax (.imm 4),
      .store (at_ .eax 0) .ecx] : List Instr))) u fun v =>
      KS g s0 A live (upd AW wR (r * 2 ^ (64 * (wq a - 1)) + X % 2 ^ (64 * (wq a - 1)))) (wR :: liveW) V ls v ∧
      Keeps [.eax, .edx] u v := by
  have hr' := h.rtW
  have eW := kwW2 g
  have wl : wq a ≥ 1 := by simp only [wq]; omega
  have fit := h.wsW.arr_fit (h.liveW_lt wR hR)
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  rw [show g.W = 2 * g.w + 2 from rfl] at fit
  refine topH_ok hr' hm (h.liveW_lt wR hR) (r := .eax) (t := .edx) (j := sqZ) (i := 1) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega) fun u₁ K₁ m₁ p₁ => ?_
  rw [eW, show sqZ = wR from rfl] at p₁
  have ws₁ := hr'.rt.of_keeps K₁
  refine wp_storeS (ea_ptr ws₁ p₁ (d := 0) (by omega)) (ws_write ws₁ (by omega)) fun u₂ M₂ => ?_
  refine wp_subS rfl fun u₃ U₃ _ => ?_
  have p₃ : PtrAt u₃ g.B .eax (arr (2 * g.w + 2) wR + 8 * wq a - 4 * 1 - 4) := by
    rw [PtrAt, U₃.gpr, M₂.gpr, VG.Proof.Mont.X86.Rt.ptr_sub p₁ _ (by simp; omega)]; simp
  have ws₃ := ws₁.of_wr (U₃.wr.trans M₂.wr)
  refine wp_storeS (ea_ptr ws₃ p₃ (d := 0) (by omega)) (ws_write ws₃ (by omega)) fun u₄ M₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .edx] u u₄ := (K₁.trans (((M₂.keeps _).trans (U₃.keeps.mono (by decide))).trans
    (M₄.keeps _)))
  -- The memory: two words written.
  obtain ⟨k, hk⟩ : ∃ k, k = 2 * wq a - 2 := ⟨_, rfl⟩
  have ea1 : arr (2 * g.w + 2) wR + 8 * wq a - 4 * 1 + 0 = arr (2 * g.w + 2) wR + 4 * (k + 1) := by omega
  have ea2 : arr (2 * g.w + 2) wR + 8 * wq a - 4 * 1 - 4 + 0 = arr (2 * g.w + 2) wR + 4 * k := by omega
  have mem₄ : u₄.mem = (u.mem.writeW (off g.B (arr (2 * g.w + 2) wR + 4 * (k + 1))) (u.gpr .esi)).writeW
      (off g.B (arr (2 * g.w + 2) wR + 4 * k)) (u.gpr .ecx) := by
    rw [M₄.mem, U₃.mem, M₂.mem, m₁, U₃.other _ (by decide), M₂.gpr, K₁.1 _ (by decide), K₁.1 _ (by decide),
      ea1, ea2]
  have o1 := writeW32_outside u.mem g.B (d := arr (2 * g.w + 2) wR + 4 * (k + 1)) (u.gpr .esi) (by omega)
  have o2 := writeW32_outside (u.mem.writeW (off g.B (arr (2 * g.w + 2) wR + 4 * (k + 1))) (u.gpr .esi)) g.B
    (d := arr (2 * g.w + 2) wR + 4 * k) (u.gpr .ecx) (by omega)
  rw [← mem₄] at o2
  have O : Outside g.B (arr (2 * g.w + 2) wR + 4 * k) 8 u.mem u₄.mem :=
    (o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))
  have keep : Keep g.B g.W [wR] [] u.mem u₄.mem :=
    Keep.of_arr (d := 4 * k) O (by simp only [S, show g.W = 2 * g.w + 2 from rfl]; omega) (by simp)
  have num_u : val32 u.mem g.B (arr (2 * g.w + 2) wR) (2 * g.w + 2) = X := (h.arrsW wR hR).trans hX
  have hz := val32_high_zero (k := k + 2) (by omega) (num_u ▸ (show X < 2 ^ (32 * (k + 2)) by
    rw [show 32 * (k + 2) = 64 * wq a by omega]; exact hXa))
  have val := val32_write_two u.mem g.B (d := arr (2 * g.w + 2) wR) (n := 2 * g.w + 2) (u.gpr .ecx) (u.gpr .esi)
    (by omega) (by omega) hz
  rw [← mem₄] at val
  have low : val32 u.mem g.B (arr (2 * g.w + 2) wR) k = X % 2 ^ (64 * (wq a - 1)) := by
    have e := val32_mod u.mem (B := g.B) (arr (2 * g.w + 2) wR) k (2 * g.w + 2 - k)
    rw [show k + (2 * g.w + 2 - k) = 2 * g.w + 2 by omega, num_u] at e
    rw [← e, show 64 * (wq a - 1) = 32 * k by omega]
  refine ⟨h.write_W keep (h.liveW_lt wR hR) (by simp) (K₄.mono (by decide)) ?_ hl (by simp), K₄⟩
  change val32 u₄.mem g.B (arr (2 * g.w + 2) wR) (2 * g.w + 2) = _
  rw [val, low, show 32 * k = 64 * (wq a - 1) by omega, ← hr]
  grind

/-- `2 s₀` into `sqD`'s words `W' - 1` and `W'`, `sqD` zero before. -/
theorem postD_ok {u : State} {AW V : Nat → Nat} {ls : List Nat} {a y : Nat}
    (h : KS g s0 A live AW liveW V ls u) (hD : sqD ∈ liveW) (hD0 : AW sqD = 0)
    (hm : MLen u g.B g.Z nl a) (ha0 : 1 ≤ a) (haw : wq a ≤ g.w)
    (hl : ∀ j ∈ live, j / 2 ≠ sqD) (hy : (u.gpr .ebx).toNat = y) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.topPtr wid nl .eax sqD 1 .edx ++ ([.mov .edx (.reg .ebx),
      .alu .add .edx (.reg .edx), .store (at_ .eax 0) .edx, .mov .edx (.reg .ebx), .shift .shr .edx 31,
      .store (at_ .eax 4) .edx] : List Instr))) u fun v =>
      KS g s0 A live (upd AW sqD (2 * y * 2 ^ (32 * (wq a - 1)))) (sqD :: liveW) V ls v ∧ Keeps [.eax, .edx] u v := by
  have hr' := h.rtW
  have eW := kwW2 g
  have wl : wq a ≥ 1 := by simp only [wq]; omega
  have fit := h.wsW.arr_fit (h.liveW_lt sqD hD)
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  rw [show g.W = 2 * g.w + 2 from rfl] at fit
  refine VG.Proof.Rsa.X86.WordRt.topPtr_ok hr' hm (h.liveW_lt sqD hD) (r := .eax) (t := .edx) (i := 1)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  rw [eW] at p₁
  have ws₁ := hr'.rt.of_keeps K₁
  refine wp_movS rfl fun u₂ U₂ _ => wp_addS rfl fun u₃ U₃ _ => ?_
  have p₃ : PtrAt u₃ g.B .eax (arr (2 * g.w + 2) sqD + 4 * wq a - 4 * 1) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.other _ (by decide)]; exact p₁
  have ws₃ := ws₁.of_wr (U₃.wr.trans U₂.wr)
  refine wp_storeS (ea_ptr ws₃ p₃ (d := 0) (by omega)) (ws_write ws₃ (by omega)) fun u₄ M₄ => ?_
  refine wp_movS rfl fun u₅ U₅ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₆ U₆ => ?_
  have p₆ : PtrAt u₆ g.B .eax (arr (2 * g.w + 2) sqD + 4 * wq a - 4 * 1) := by
    rw [PtrAt, U₆.other _ (by decide), U₅.other _ (by decide), M₄.gpr]; exact p₃
  have ws₆ := ws₃.of_wr ((U₆.wr.trans U₅.wr).trans M₄.wr)
  refine wp_storeS (ea_ptr ws₆ p₆ (d := 4) (by omega)) (ws_write ws₆ (by omega)) fun t M₇ => WP.block_nil ?_
  have Kt : Keeps [.eax, .edx] u t := K₁.trans ((U₂.keeps.mono (by decide)).trans ((U₃.keeps.mono (by decide)).trans
    ((M₄.keeps _).trans ((U₅.keeps.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans (M₇.keeps _))))))
  have bx₂ : u₂.gpr .ebx = u.gpr .ebx := by rw [U₂.other _ (by decide), K₁.1 _ (by decide)]
  have lo : (u₃.gpr .edx).toNat = 2 * y % 2 ^ 32 := by
    rw [U₃.gpr, BitVec.toNat_add, U₂.gpr, K₁.1 .ebx (by decide), hy]; omega
  have hi : (u₆.gpr .edx).toNat = y / 2 ^ 31 := by
    rw [U₆.gpr, U₅.gpr, M₄.gpr, U₃.other _ (by decide), bx₂, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hy]
  have hy32 : y < 2 ^ 32 := hy ▸ (u.gpr .ebx).isLt
  -- The memory: two words written.
  obtain ⟨k, hk⟩ : ∃ k, k = wq a - 1 := ⟨_, rfl⟩
  have ea1 : arr (2 * g.w + 2) sqD + 4 * wq a - 4 * 1 + 0 = arr (2 * g.w + 2) sqD + 4 * k := by omega
  have ea2 : arr (2 * g.w + 2) sqD + 4 * wq a - 4 * 1 + 4 = arr (2 * g.w + 2) sqD + 4 * (k + 1) := by omega
  have memt : t.mem = (u.mem.writeW (off g.B (arr (2 * g.w + 2) sqD + 4 * k)) (u₃.gpr .edx)).writeW
      (off g.B (arr (2 * g.w + 2) sqD + 4 * (k + 1))) (u₆.gpr .edx) := by
    rw [M₇.mem, U₆.mem, U₅.mem, M₄.mem, U₃.mem, U₂.mem, m₁, ea1, ea2]
  have o1 := writeW32_outside u.mem g.B (d := arr (2 * g.w + 2) sqD + 4 * k) (u₃.gpr .edx) (by omega)
  have o2 := writeW32_outside (u.mem.writeW (off g.B (arr (2 * g.w + 2) sqD + 4 * k)) (u₃.gpr .edx)) g.B
    (d := arr (2 * g.w + 2) sqD + 4 * (k + 1)) (u₆.gpr .edx) (by omega)
  rw [← memt] at o2
  have O : Outside g.B (arr (2 * g.w + 2) sqD + 4 * k) 8 u.mem t.mem :=
    (o1.mono (by omega) (by omega)).trans (o2.mono (by omega) (by omega))
  have keep : Keep g.B g.W [sqD] [] u.mem t.mem :=
    Keep.of_arr (d := 4 * k) O (by simp only [S, show g.W = 2 * g.w + 2 from rfl]; omega) (by simp)
  have z : val32 u.mem g.B (arr (2 * g.w + 2) sqD) (2 * g.w + 2) = 0 := (h.arrsW sqD hD).trans hD0
  have v1 := val32_write_word u.mem g.B (d := arr (2 * g.w + 2) sqD) (i := k) (k := 2 * g.w + 2) (u₃.gpr .edx)
    (by omega) (by omega) (by rw [z]; exact Nat.two_pow_pos _)
  rw [z, Nat.zero_add] at v1
  have v2 := val32_write_word (u.mem.writeW (off g.B (arr (2 * g.w + 2) sqD + 4 * k)) (u₃.gpr .edx)) g.B
    (d := arr (2 * g.w + 2) sqD) (i := k + 1) (k := 2 * g.w + 2) (u₆.gpr .edx) (by omega) (by omega) (by
      rw [v1, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_left (BitVec.isLt _) (Nat.two_pow_pos _))
  rw [← memt, v1, lo, hi] at v2
  refine ⟨h.write_W keep (h.liveW_lt sqD hD) (by simp) (Kt.mono (by decide)) ?_ hl (by simp), Kt⟩
  change val32 t.mem g.B (arr (2 * g.w + 2) sqD) (2 * g.w + 2) = _
  rw [v2, ← hk, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
  have e : 2 * y = 2 * y % 2 ^ 32 + 2 ^ 32 * (y / 2 ^ 31) := by omega
  conv => rhs; rw [e]
  grind

end

/-- The first digit's root is normalized: `T ≥ 2^62` gives `s₀ ≥ 2^31`. -/
theorem root_ge {T y R : Nat} (hT : 2 ^ 62 ≤ T) (hyR : y * y + R = T) (hRy : R ≤ 2 * y) : 2 ^ 31 ≤ y := by
  refine Nat.le_of_not_lt fun c => ?_
  have := Nat.mul_le_mul (show y ≤ 2 ^ 31 - 1 by omega) (show y ≤ 2 ^ 31 - 1 by omega)
  omega

theorem top_ge {X W' : Nat} (hW : 1 ≤ W') (hXn : 2 ^ 30 * 2 ^ (64 * W' - 32) ≤ X) :
    2 ^ 62 ≤ X / 2 ^ (64 * (W' - 1)) := by
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
  rw [← Nat.pow_add] at hXn
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hXn

theorem post_split (a b c : List Instr) (x y z w : Instr) :
    a ++ [x, y, z, w] ++ b ++ c = (a ++ [x, y, z]) ++ ([w] ++ (b ++ c)) := by simp

open VG.Proof.Rsa.X86.WordRt (wq MLen)
open VG.Impl.Rsa.X86.WordModRt (oD oV)

theorem firstX_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {X a : Nat}
    (h : KS g s0 A [aD, aZero] AW [wR] V lsN u) (hX : AW wR = X)
    (ha : g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a) (hal : a ≤ 1024) (ha0 : 1 ≤ a)
    (haw : wq a ≤ g.w) (hXa : X < 2 ^ (64 * wq a)) (hXn : 2 ^ 30 * 2 ^ (64 * wq a - 32) ≤ X) :
    WP isa firstX u fun v => ∃ AW' V' s r, KS g s0 A [aD, aZero] AW' [wR, sqD] V' (oD :: oV :: lsN) v ∧
      (∀ d ∈ lsN, V' d = V d) ∧ SqR a X (wq a - 1) s r AW' V' := by
  have wl : wq a ≥ 1 := by simp only [wq]; omega
  obtain ⟨-, -, hT⟩ := top2_split wl hXa
  have hTn := top_ge wl hXn
  unfold firstX
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (h.zeroWide_W (j := sqD) (by decide) (by decide)) fun u₁ ⟨h₁, _⟩ => ?_)
  refine WP.seq (WP.mono (firstSetup_ok h₁ (by simp) (by rw [upd_ne _ _ (by decide)]; exact hX)
    (h₁.mlen ha hal) ha0 haw hXa) fun u₂ I₂ => ?_)
  refine WP.seq (WP.mono (isqLoop_ok hT I₂) fun u₃ I₃ => ?_)
  obtain ⟨V₃, y, R, h₃, hV₃, -, -, -, hR, hy, hyR, hRy⟩ := I₃
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hyR
  have y32 := root_lt (by omega) (Nat.le_refl _) (show y * y + R = X / 2 ^ (64 * (wq a - 1)) / 4 ^ (32 - 32) by
    rw [Nat.sub_self, Nat.pow_zero, Nat.div_one]; exact hyR)
  have y31 := root_ge hTn hyR hRy
  refine WP.seq ?_
  rw [post_split, WP.block_append_iff]
  refine WP.mono (postZ_ok h₃ (by simp) (by rw [upd_ne _ _ (by decide)]; exact hX) (h₃.mlen ha hal) ha0 haw hXa
    (by decide) hR) fun u₄ ⟨h₄, K₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (h₄.storeSlot (d := oD) (by decide) .ebx) fun u₅ ⟨h₅, _, K₅⟩ => ?_
  have hy₅ : (u₅.gpr .ebx).toNat = y := by rw [K₅.1 _ (by decide), K₄.1 _ (by decide), hy]
  refine WP.mono (postD_ok h₅ (by simp) (by rw [upd_ne _ _ (by decide), upd_self]) (h₅.mlen ha hal) ha0 haw (by decide) hy₅)
    fun u₆ ⟨h₆, K₆⟩ => ?_
  have hr₆ := h₆.rtW
  have sD : slot u₆.mem g.B oD = y := by
    rw [h₆.sl oD (by simp), upd_self, K₄.1 _ (by decide), hy]
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.recip_ok hr₆ sD y31 y32) fun v ⟨_, kv, ev, rv⟩ => ?_
  have hv := h₆.slot1 kv (by decide) (rv.mono (by decide)) ev
  have sub : ∀ d ∈ oD :: oV :: lsN, d ∈ oV :: oD :: hTl :: hCnt :: lsN := by decide
  refine ⟨_, _, y, R, hv.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩)
    (fun d hd => ⟨sub d hd, rfl⟩), fun d hd => ?_, ?_⟩
  · have n1 : d ≠ oV := by revert d; decide
    have n2 : d ≠ oD := by revert d; decide
    rw [upd_ne _ _ n1, upd_ne _ _ n2, hV₃ d hd]
  · have eoD : upd (upd V₃ oD (u₄.gpr .ebx).toNat) oV ((2 ^ 64 - 1) / y - 2 ^ 32) oD = y := by
      rw [upd_ne _ _ (by decide), upd_self, K₄.1 _ (by decide), hy]
    refine ⟨upd_self _ _ _, by rw [upd_ne _ _ (by decide), upd_self], hyR, hRy, ?_, ?_, ?_, ?_⟩
    · rw [eoD, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    · rw [eoD]; exact y31
    · rw [show wq a - (wq a - 1) = 1 by omega]; exact y32
    · rw [eoD, upd_self]

end VG.Proof.Rsa.X86.Recover
