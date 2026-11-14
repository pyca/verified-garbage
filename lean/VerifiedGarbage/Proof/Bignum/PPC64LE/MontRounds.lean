module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# Montgomery multiplication on PPC64LE: the rounds

A round (`round_ok`) replaces the accumulator `T` (`w + 1` words) with `(T +
aᵢ b + u m) / 2⁶⁴`: its start (`roundStart_ok`: the pointers from `r10` and
`8 w = r16 - r10`, `m'` and the counts), word 0 (`head_ok`: `u`, and the
values left pending for word 1), words `1` to `w - 1` in blocks
(`Wd`, the words done and pending after word 0, which a block extends,
`Wd.step`; `remBlock_ok`, one block of `(w - 1) mod 4` words, and
`quadLoop_ok`, blocks of four, counted by `r17`'s low half), and word `w`
(`top_ok`). The `w` rounds (`rounds_ok`, counted by `r17`'s high half) leave
`T < 2m` with `T 2^(64 w) ≡ a b (mod m)`, and the bases and `2 w` that the
rounds used as pointers and counts back in `r7`–`r9` and `r11`
(`roundsFini_ok`).

The kernel's round (`round8_ok`) is the same but for its blocks: one of
`(w - 1) mod 4` words, one of four if bit 2 of `w - 1` is set (`quadBlock_ok`,
the bit in `r27`), then blocks of eight (`octLoop_ok`). The rounds' proof is
generic in the round (`RoundSpec`, `roundsWith_ok`), and gives both `rounds_ok`
and `rounds8_ok`.

## Blocks

A block of `k ≤ 8` words (`block`; only the kernel's rounds have blocks of
more than four) holds the words in `sreg 0`, …, `sreg (k - 1)` and adds `x p` to them twice (`half`), each time in two carry chains:
the low words of the products (`lo_ok`, one `loStep` per word) and their
high words, one word up (`hi_ok`, one `hiStep` per word). `half_ok` puts the
two together with the pending values a chain leaves for the next block (a
carry kept as `CA - 1`, `cenc`, and a high word), and `block_ok` the whole
block: loads, two halves, stores.

Each instruction is run by a rule that hands the continuation the next state
as `W1` (one register written), so that the registers are variables (`sreg
i` for any `i`, and the halves' registers) and the proofs never unfold
`State.write`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Mont4

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum.PPC64LE (Scr Keep off_add gpr_write)

/-! ## One instruction at a time -/

/-- `t` is `s` with at most register `d` (and CA) written. -/
structure W1 (s t : State) (d : Reg) : Prop where
  gpr : ∀ r, r ≠ d → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  lr : t.lr = s.lr

theorem W1.keep {s t : State} {d : Reg} (h : W1 s t d) : Keep [d] s t :=
  ⟨fun r hr => h.gpr r (by simpa using hr), h.rd, h.wr, h.sp, h.lr⟩

theorem W1.write (s : State) (d : Reg) (v : BitVec 64) : W1 s (s.write d v) d :=
  ⟨fun r hr => by rw [gpr_write, ite_eq_right hr], rfl, rfl, rfl, rfl, rfl⟩

theorem W1.writeCarry (s : State) (d : Reg) (v : Nat) : W1 s (s.writeCarry d v) d :=
  ⟨fun r hr => by rw [gpr_writeCarry, ite_eq_right hr], rfl, rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld {d n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ t, W1 s t d → t.gpr d = s.mem.readW a 64 → t.ca = s.ca → WP isa (.block is) t Q) :
    WP isa (.block (.load .d d n off :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, exec_load_d hn ho (by rw [ha]; exact hin), ?_⟩
  rw [ha]
  exact k _ (W1.write _ _ _) (by rw [gpr_write, ite_eq_left rfl]) rfl

/-- A store: every register kept, and the memory written. -/
theorem wp_st {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ t', Keep [] s t' → t'.mem = s.mem.writeW a (s.gpr t) → t'.ca = s.ca → WP isa (.block is) t' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, exec_store_d hn ho (by rw [ha]; exact hout), ?_⟩
  rw [ha]
  exact k _ ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ rfl rfl

/-- An instruction that writes one register and not CA. -/
theorem wp_write {i : Instr} {d : Reg} {v : BitVec 64} (he : exec i s = some (s.write d v))
    (k : ∀ t, W1 s t d → t.gpr d = v → t.ca = s.ca → WP isa (.block is) t Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, he, k _ (W1.write _ _ _) (by rw [gpr_write, ite_eq_left rfl]) rfl⟩

theorem wp_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ t, W1 s t d → t.gpr d = s.gpr n + BitVec.ofNat 64 imm → t.ca = s.ca → WP isa (.block is) t Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, exec_addi hn h, k _ (W1.write _ _ _) (by rw [gpr_write, ite_eq_left rfl]) rfl⟩

theorem wp_mul {d n m : Reg}
    (k : ∀ t, W1 s t d → t.gpr d = s.gpr n * s.gpr m → t.ca = s.ca → WP isa (.block is) t Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, exec_mul, k _ (W1.write _ _ _) (by rw [gpr_write, ite_eq_left rfl]) rfl⟩

theorem wp_mulhu {d n m : Reg}
    (k : ∀ t, W1 s t d → (t.gpr d).toNat = (s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64 → t.ca = s.ca →
      WP isa (.block is) t Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, exec_mulhu, k _ (W1.write _ _ _) ?_ rfl⟩
  rw [gpr_write, ite_eq_left rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have hn := (s.gpr n).isLt
  have hm := (s.gpr m).isLt
  exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_le hn (Nat.le_of_lt hm) (by decide))

/-- A carrying write of a sum below `2⁶⁵`. -/
theorem wp_carry {d : Reg} {i : Instr} {v : Nat} (hv : v < 2 ^ 65)
    (he : exec i s = some (s.writeCarry d v))
    (k : ∀ t, W1 s t d → (t.gpr d).toNat + 2 ^ 64 * t.ca.toNat = v → WP isa (.block is) t Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨_, he, k _ (W1.writeCarry _ _ _) (toNat_add_ca s hv)⟩

theorem wp_adde {d n m : Reg}
    (k : ∀ t, W1 s t d → (t.gpr d).toNat + 2 ^ 64 * t.ca.toNat =
      (s.gpr n).toNat + (s.gpr m).toNat + s.ca.toNat → WP isa (.block is) t Q) :
    WP isa (.block (.adde d n m :: is)) s Q := by
  have hn := (s.gpr n).isLt
  have hm := (s.gpr m).isLt
  have hc : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact wp_carry (by omega_using [hc]) exec_adde k

theorem wp_addc {d n m : Reg}
    (k : ∀ t, W1 s t d → (t.gpr d).toNat + 2 ^ 64 * t.ca.toNat = (s.gpr n).toNat + (s.gpr m).toNat →
      WP isa (.block is) t Q) :
    WP isa (.block (.addc d n m :: is)) s Q := by
  have hn := (s.gpr n).isLt
  have hm := (s.gpr m).isLt
  exact wp_carry (by omega_using []) exec_addc k

theorem wp_addze {d n : Reg}
    (k : ∀ t, W1 s t d → (t.gpr d).toNat + 2 ^ 64 * t.ca.toNat = (s.gpr n).toNat + s.ca.toNat →
      WP isa (.block is) t Q) :
    WP isa (.block (.addze d n :: is)) s Q := by
  have hn := (s.gpr n).isLt
  have hc : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact wp_carry (by omega_using [hc]) exec_addze k

end

/-! ## Kept carries -/

/-- A carry `b` kept in a register as `CA - 1`: 0 or all ones. -/
def cenc (b : Bool) : BitVec 64 := BitVec.ofNat 64 (2 ^ 64 - 1 + b.toNat)

/-- `subfe c, c, c` keeps CA in `c`. -/
theorem wp_save {c : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ t, W1 s t c → t.gpr c = cenc s.ca → WP isa (.block is) t Q) :
    WP isa (.block (.sube c c c :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, exec_sube, k _ (W1.writeCarry _ _ _) ?_⟩
  rw [gpr_writeCarry, ite_eq_left rfl, cenc]
  congr 1
  have := (s.gpr c).isLt
  omega_using []

/-- `subfc c, r10, c` sets CA to the carry kept in `c`, for `r10` not all ones. -/
theorem wp_restore {c : Reg} {b : Bool} {is : List Instr} {s : State} {Q : State → Prop}
    (hc : s.gpr c = cenc b) (h10 : (s.gpr .r10).toNat < 2 ^ 64 - 1)
    (k : ∀ t, W1 s t c → t.ca = b → WP isa (.block is) t Q) :
    WP isa (.block (.subc c .r10 c :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, exec_subc, k _ (W1.writeCarry _ _ _) ?_⟩
  rw [ca_writeCarry, hc, cenc]
  cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, BitVec.toNat_ofNat] <;> simp only [decide_eq_true_eq,
    decide_eq_false_iff_not] <;> omega_arith

/-! ## The words of a block -/

theorem sreg_mem (i : Nat) : sreg i ∈ [Reg.r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31] := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [sreg]

theorem sreg_inj : ∀ i < 8, ∀ j < 8, sreg i = sreg j → i = j := by decide

/-- The registers the chains write, but the halves' own. -/
def blkRegs : List Reg := [.r0, .r9, .r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31]

theorem sreg_ne {r : Reg} (hr : r ∉ [Reg.r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31]) (i : Nat) : sreg i ≠ r := fun e => hr (e ▸ sreg_mem i)

theorem sreg_blk (i : Nat) : sreg i ∈ blkRegs := by
  have := sreg_mem i
  simp only [blkRegs, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  rcases this with h | h | h | h | h | h | h | h <;> simp [h]

theorem keep_step {s t : State} {r₁ r₂ : Reg} {i : Nat} (h : Keep [r₁, r₂, sreg i] s t)
    (h₁ : r₁ ∈ blkRegs := by decide) (h₂ : r₂ ∈ blkRegs := by decide) : Keep blkRegs s t :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h₁, h₂, sreg_blk i]

/-- `sreg j` is not written by a step of word `i ≠ j`. -/
theorem sreg_notin {i j : Nat} (hi : i < 8) (hj : j < 8) (h : j ≠ i) {r₁ r₂ : Reg}
    (h₁ : r₁ ∉ [Reg.r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31] := by decide) (h₂ : r₂ ∉ [Reg.r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31] := by decide) :
    sreg j ∉ [r₁, r₂, sreg i] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨sreg_ne h₁ j, sreg_ne h₂ j, fun e => h (sreg_inj j hj i hi e)⟩


/-- The sum of `f j 2^(64 j)` for `j < i`. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => psum f i + 2 ^ (64 * i) * f i

theorem psum_congr {f g : Nat → Nat} : ∀ {i : Nat}, (∀ j < i, f j = g j) → psum f i = psum g i
  | 0, _ => rfl
  | i + 1, h => by
    rw [psum, psum, psum_congr (fun j hj => h j (by omega_using [hj])), h i (by omega_using [])]

/-- Register `sreg (j + o)`'s value. -/
abbrev sv (s : State) (o j : Nat) : Nat := (s.gpr (sreg (j + o))).toNat

theorem keep_blk {s t : State} {rs : List Reg} (h : Keep rs s t) {r : Reg} (hn : r ∉ blkRegs)
    (hr : ∀ r ∈ rs, r ∈ blkRegs := by decide) : t.gpr r = s.gpr r := h.gpr r fun h' => hn (hr r h')

/-- The low word of a product and its high word. -/
theorem lo_hi (x y : BitVec 64) : (x * y).toNat + 2 ^ 64 * (x.toNat * y.toNat / 2 ^ 64) = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul]; exact Nat.mod_add_div _ _

/-- A high word of a product is at most `2⁶⁴ - 2`. -/
theorem hi_le (x y : BitVec 64) : x.toNat * y.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
  have hx := x.isLt
  have hy := y.isLt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_using []) (by omega_using [])
  exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [this]))

theorem chain_step {P₁ P₀ L c₀ c₁ Q S' c' S l : Nat} (h₁ : P₁ + Q * c₁ = P₀ + L + c₀)
    (h₂ : S' + 2 ^ 64 * c' = S + l + c₁) : P₁ + Q * S' + 2 ^ 64 * Q * c' = P₀ + Q * S + (L + Q * l) + c₀ := by
  have e : Q * S' + 2 ^ 64 * Q * c' = Q * (S + l + c₁) := by rw [← h₂, Nat.mul_add]; grind
  grind

/-! ## The chain of low words -/

/-- Word `i` of the low chain: `S i += lo(x pᵢ) + CA`, `pᵢ` left in `r9`. -/
theorem loStep_ok {s : State} {B : Addr} {Z d i : Nat} {x p : Reg} (hs : Scr s B Z)
    (hp : s.gpr p = off B d) (hpr : p ≠ .r0) (hi : i < 8) (hd : d + 8 * i + 8 ≤ Z) (hx : x ∉ blkRegs) :
    WP isa (.block (loStep x p i)) s fun t =>
      (sv t 0 i + 2 ^ 64 * t.ca.toNat = sv s 0 i + (s.gpr x * word s.mem B (d + 8 * i)).toNat + s.ca.toNat ∧
        t.gpr .r9 = word s.mem B (d + 8 * i) ∧ t.mem = s.mem) ∧ Keep [.r9, .r0, sreg i] s t := by
  have hs0 := sreg_ne (r := .r0) (by decide) i
  have hs9 := sreg_ne (r := .r9) (by decide) i
  have hx9 : x ≠ .r9 := fun e => hx (by simp [e, blkRegs])
  unfold loStep
  refine wp_ld hpr ⟨by omega_using [hi], by omega_using []⟩ (by rw [hp, off_add]) (hs.ld (by omega_using [hd])) fun t₁ w₁ e₁ c₁ => ?_
  refine wp_mul fun t₂ w₂ e₂ c₂ => ?_
  refine wp_adde fun t₃ w₃ e₃ => WP.block_nil ⟨⟨?_, ?_, ?_⟩, (w₁.keep.trans (w₂.keep.trans w₃.keep)).mono fun r hr => by simpa using hr⟩
  · simp only [sv, Nat.add_zero]
    rw [e₃, w₂.gpr _ hs0, w₁.gpr _ hs9, e₂, w₁.gpr _ hx9, e₁, c₂, c₁]
  · rw [w₃.gpr _ (Ne.symm hs9), w₂.gpr _ (by decide), e₁]
  · rw [w₃.mem, w₂.mem, w₁.mem]

theorem loSteps_succ (x p : Reg) (i : Nat) :
    (List.range (i + 1)).flatMap (loStep x p) = (List.range i).flatMap (loStep x p) ++ loStep x p i := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low chain over `i ≤ 8` words. -/
theorem lo_ok {B : Addr} {Z d : Nat} {x p : Reg} (hpr : p ≠ .r0) (hx : x ∉ blkRegs) (hp' : p ∉ blkRegs) :
    ∀ (i : Nat) {s : State}, Scr s B Z → s.gpr p = off B d → i ≤ 8 → d + 8 * i ≤ Z →
    WP isa (.block ((List.range i).flatMap (loStep x p))) s fun t =>
      (psum (sv t 0) i + 2 ^ (64 * i) * t.ca.toNat =
          psum (sv s 0) i + psum (fun j => (s.gpr x * word s.mem B (d + 8 * j)).toNat) i + s.ca.toNat ∧
        (0 < i → t.gpr .r9 = word s.mem B (d + 8 * (i - 1))) ∧
        (∀ j, i ≤ j → j < 8 → t.gpr (sreg j) = s.gpr (sreg j)) ∧ t.mem = s.mem) ∧ Keep blkRegs s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨by simp [psum], fun h => absurd h (by decide), fun _ _ _ => rfl, rfl⟩,
      Keep.refl _ _⟩
  | i + 1, s, hs, hp, hi, hd => by
    rw [loSteps_succ, WP.block_append_iff]
    refine WP.mono (lo_ok hpr hx hp' i hs hp (by omega_using [hi]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, _, f₁, m₁⟩, k₁⟩ => ?_
    refine WP.mono (loStep_ok (i := i) (d := d) (hs.congr k₁.wr) (by rw [keep_blk k₁ hp', hp]) hpr (by omega_using [hi]) (by omega_using [hd]) hx)
      fun t ⟨⟨e, h9, m⟩, k⟩ => ⟨⟨?_, fun _ => ?_, fun j hj hj4 => ?_, ?_⟩, k₁.trans' (keep_step k)⟩
    · have pt : psum (sv t 0) i = psum (sv t₁ 0) i := psum_congr fun j hj => by
        simp only [sv, Nat.add_zero]
        rw [k.gpr _ (by simpa using sreg_notin (i := i) (j := j) (by omega_using [hi]) (by omega_using [hi, hj]) (by omega_using [hj]))]
      simp only [sv, Nat.add_zero] at e
      rw [m₁, keep_blk k₁ hx, f₁ i (Nat.le_refl _) (by omega_using [hi])] at e
      simp only [psum, pow64_succ]
      rw [pt]
      have := chain_step e₁ e
      simp only [sv, Nat.add_zero] at this ⊢
      omega_using [this]
    · rw [h9, m₁]; rfl
    · rw [k.gpr _ (by simpa using sreg_notin (i := i) (j := j) (by omega_using [hi]) hj4 (by omega_using [hj])), f₁ j (by omega_using [hj]) hj4]
    · rw [m, m₁]

/-! ## The chain of high words -/

/-- The high word of a product. -/
abbrev hiw (x y : BitVec 64) : Nat := x.toNat * y.toNat / 2 ^ 64

/-- Word `i + 1` of the high chain: `S (i + 1) += hi(x pᵢ) + CA`. -/
theorem hiStep_ok {s : State} {B : Addr} {Z d i : Nat} {x p : Reg} (hs : Scr s B Z)
    (hp : s.gpr p = off B d) (hpr : p ≠ .r0) (hi : i < 7) (hd : d + 8 * i + 8 ≤ Z) (hx : x ∉ blkRegs) :
    WP isa (.block (hiStep x p i)) s fun t =>
      (sv t 1 i + 2 ^ 64 * t.ca.toNat = sv s 1 i + hiw (s.gpr x) (word s.mem B (d + 8 * i)) + s.ca.toNat ∧
        t.mem = s.mem) ∧ Keep [.r0, .r0, sreg (i + 1)] s t := by
  have hs0 := sreg_ne (r := .r0) (by decide) (i + 1)
  have hx0 : x ≠ .r0 := fun e => hx (by simp [e, blkRegs])
  unfold hiStep
  refine wp_ld hpr ⟨by omega_using [hi], by omega_using []⟩ (by rw [hp, off_add]) (hs.ld (by omega_using [hd])) fun t₁ w₁ e₁ c₁ => ?_
  refine wp_mulhu fun t₂ w₂ e₂ c₂ => ?_
  refine wp_adde fun t₃ w₃ e₃ => WP.block_nil ⟨⟨?_, ?_⟩, (w₁.keep.trans (w₂.keep.trans w₃.keep)).mono fun r hr => by simpa using hr⟩
  · simp only [sv]
    rw [e₃, w₂.gpr _ hs0, w₁.gpr _ hs0, e₂, w₁.gpr _ hx0, e₁, c₂, c₁]
  · rw [w₃.mem, w₂.mem, w₁.mem]

theorem hiSteps_succ (x p : Reg) (i : Nat) :
    (List.range (i + 1)).flatMap (hiStep x p) = (List.range i).flatMap (hiStep x p) ++ hiStep x p i := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The high chain over words `1` to `i ≤ 7`, of the products of words `0` to
`i - 1`. -/
theorem hi_ok {B : Addr} {Z d : Nat} {x p : Reg} (hpr : p ≠ .r0) (hx : x ∉ blkRegs) (hp' : p ∉ blkRegs) :
    ∀ (i : Nat) {s : State}, Scr s B Z → s.gpr p = off B d → i ≤ 7 → d + 8 * i ≤ Z →
    WP isa (.block ((List.range i).flatMap (hiStep x p))) s fun t =>
      (psum (sv t 1) i + 2 ^ (64 * i) * t.ca.toNat =
          psum (sv s 1) i + psum (fun j => hiw (s.gpr x) (word s.mem B (d + 8 * j))) i + s.ca.toNat ∧
        t.gpr .r9 = s.gpr .r9 ∧ (∀ j, (j = 0 ∨ i < j) → j < 8 → t.gpr (sreg j) = s.gpr (sreg j)) ∧
        t.mem = s.mem) ∧ Keep blkRegs s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨by simp [psum], rfl, fun _ _ _ => rfl, rfl⟩, Keep.refl _ _⟩
  | i + 1, s, hs, hp, hi, hd => by
    rw [hiSteps_succ, WP.block_append_iff]
    refine WP.mono (hi_ok hpr hx hp' i hs hp (by omega_using [hi]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, r₁, f₁, m₁⟩, k₁⟩ => ?_
    refine WP.mono (hiStep_ok (i := i) (d := d) (hs.congr k₁.wr) (by rw [keep_blk k₁ hp', hp]) hpr (by omega_using [hi])
      (by omega_using [hd]) hx) fun t ⟨⟨e, m⟩, k⟩ => ⟨⟨?_, ?_, fun j hj hj4 => ?_, ?_⟩, k₁.trans' (keep_step k)⟩
    · have pt : psum (sv t 1) i = psum (sv t₁ 1) i := psum_congr fun j hj => by
        simp only [sv]
        have := sreg_notin (i := i + 1) (j := j + 1) (r₁ := .r0) (r₂ := .r0) (by omega_using [hi]) (by omega_using [hi, hj]) (by omega_using [hj])
        rw [k.gpr _ (by simpa using this)]
      simp only [sv] at e
      rw [m₁, keep_blk k₁ hx, f₁ (i + 1) (.inr (by omega_using [])) (by omega_using [hi])] at e
      simp only [psum, pow64_succ]
      rw [pt]
      have := chain_step e₁ e
      simp only [sv] at this ⊢
      omega_using [this]
    · rw [k.gpr _ (by simpa using Ne.symm (sreg_ne (r := .r9) (by decide) (i + 1))), r₁]
    · rw [k.gpr _ (by simpa using sreg_notin (i := i + 1) (j := j) (r₁ := .r0) (r₂ := .r0) (by omega_using [hi]) hj4 (by omega_using [hj])),
        f₁ j (by omega_using [hj]) hj4]
    · rw [m, m₁]

/-! ## Half a block -/

theorem psum_shift (f : Nat → Nat) : ∀ n, psum f (n + 1) = f 0 + 2 ^ 64 * psum (fun j => f (j + 1)) n
  | 0 => by simp [psum]
  | n + 1 => by
    rw [psum, psum_shift f n, psum, pow64_succ]
    grind

/-- The low and the high words of the products of `x` with `k` words. -/
theorem psum_lohi (x : BitVec 64) (m : Mem) (B : Addr) (d : Nat) : ∀ k,
    psum (fun j => (x * word m B (d + 8 * j)).toNat) k + 2 ^ 64 * psum (fun j => hiw x (word m B (d + 8 * j))) k =
      x.toNat * wordsVal m B d k
  | 0 => by simp [psum, wordsVal]
  | k + 1 => by
    have ih := psum_lohi x m B d k
    have hl := congrArg (2 ^ (64 * k) * ·) (lo_hi x (word m B (d + 8 * k)))
    rw [psum, psum, wordsVal_succ_top]
    grind

theorem half_arith {P₀ P₂ L b c₂ s₂ R₂ h₀ s₅ c₅ R₆ Q c₆ H hn h₇ : Nat}
    (hA : P₂ + 2 ^ 64 * Q * c₂ = P₀ + L + b) (hP₂ : P₂ = s₂ + 2 ^ 64 * R₂) (hB : s₅ + 2 ^ 64 * c₅ = s₂ + h₀)
    (hC : R₆ + Q * c₆ = R₂ + H + c₅) (hD : h₇ = hn + c₆) :
    s₅ + 2 ^ 64 * R₆ + 2 ^ 64 * Q * (c₂ + h₇) = P₀ + b + h₀ + (L + 2 ^ 64 * (H + Q * hn)) := by
  subst hP₂ hD
  grind

/-- The registers `half` writes. -/
def halfRegs (c h : Reg) : List Reg := c :: h :: blkRegs

/-- Half a block of `k` words (`half c x p h k`), the words at `p`: `S + 2^(64 k)
(c + h) = S + c + h + x p` for the carry `c` (kept as `cenc`) and the pending
high word `h` on entry and on exit. -/
theorem half_ok {s : State} {B : Addr} {Z d k : Nat} {c x p h : Reg} {b : Bool} (hs : Scr s B Z)
    (hp : s.gpr p = off B d) (hk : 1 ≤ k) (hk4 : k ≤ 8) (hd : d + 8 * k ≤ Z)
    (hc : s.gpr c = cenc b) (h10 : (s.gpr .r10).toNat < 2 ^ 64 - 1)
    (hcb : c ∉ blkRegs) (hxb : x ∉ blkRegs) (hpb : p ∉ blkRegs) (hhb : h ∉ blkRegs)
    (hcx : c ≠ x) (hcp : c ≠ p) (hch : c ≠ h) (hpr : p ≠ .r0) :
    WP isa (.block (half c x p h k)) s fun t =>
      (∃ b' : Bool, t.gpr c = cenc b' ∧
        psum (sv t 0) k + 2 ^ (64 * k) * (b'.toNat + (t.gpr h).toNat) =
          psum (sv s 0) k + b.toNat + (s.gpr h).toNat + (s.gpr x).toNat * wordsVal s.mem B d k) ∧
        (∀ j, k ≤ j → j < 8 → t.gpr (sreg j) = s.gpr (sreg j)) ∧ t.mem = s.mem ∧ Keep (halfRegs c h) s t := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega_using [hk]⟩
  have hs3 : ∀ {r : Reg}, r ∉ blkRegs → Reg.r3 ≠ r := fun hr e => hr (by simp [← e, blkRegs])
  have hs9 : ∀ {r : Reg}, r ∉ blkRegs → Reg.r9 ≠ r := fun hr e => hr (by simp [← e, blkRegs])
  simp only [half, List.append_assoc, List.cons_append, List.nil_append, Nat.add_sub_cancel]
  -- CA from `c`.
  refine wp_restore hc h10 fun t₁ w₁ c₁ => ?_
  have g₁ : ∀ {r}, r ≠ c → t₁.gpr r = s.gpr r := fun h => w₁.gpr _ h
  -- The low chain.
  rw [WP.block_append_iff]
  refine WP.mono (lo_ok hpr hxb hpb (n + 1) (hs.congr w₁.wr) (by rw [g₁ (Ne.symm hcp), hp]) hk4 hd)
    fun t₂ ⟨⟨e₂, r₂, f₂, m₂⟩, k₂⟩ => ?_
  have hb₂ : ∀ {r}, r ∉ blkRegs → t₂.gpr r = t₁.gpr r := fun h => keep_blk k₂ h
  -- The last high word, and CA into `c`.
  refine wp_mulhu fun t₃ w₃ e₃ c₃ => ?_
  refine wp_save fun t₄ w₄ e₄ => ?_
  -- The high chain, from `h`.
  refine wp_addc fun t₅ w₅ e₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hi_ok (d := d) hpr hxb hpb n (hs.congr (w₅.wr.trans (w₄.wr.trans (w₃.wr.trans (k₂.wr.trans w₁.wr)))))
    (by rw [w₅.gpr _ (hs3 hpb).symm, w₄.gpr _ (Ne.symm hcp), w₃.gpr _ (hs9 hpb).symm, hb₂ hpb, g₁ (Ne.symm hcp), hp])
    (by omega_using [hk4]) (by omega_using [hd])) fun t₆ ⟨⟨e₆, r₆, f₆, m₆⟩, k₆⟩ => ?_
  refine wp_addze fun t₇ w₇ e₇ => WP.block_nil ⟨⟨t₂.ca, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [w₇.gpr _ hch, keep_blk k₆ hcb, w₅.gpr _ (hs3 hcb).symm, e₄, c₃]
  · -- What each piece read is what it was on entry.
    have sx : t₅.gpr x = s.gpr x := by
      rw [w₅.gpr _ (hs3 hxb).symm, w₄.gpr _ hcx.symm, w₃.gpr _ (hs9 hxb).symm, hb₂ hxb, g₁ hcx.symm]
    have sm : t₅.mem = s.mem := by rw [w₅.mem, w₄.mem, w₃.mem, m₂, w₁.mem]
    have p₁ : psum (sv t₁ 0) (n + 1) = psum (sv s 0) (n + 1) :=
      psum_congr fun j _ => by simp only [sv]; rw [g₁ (sreg_ne (r := c) (fun h => hcb (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        simp [blkRegs, h])) (j + 0))]
    rw [p₁, c₁, w₁.mem, g₁ hcx.symm] at e₂
    have p₅ : psum (sv t₅ 1) n = psum (fun j => sv t₂ 0 (j + 1)) n := psum_congr fun j hj => by
      have h3 : sreg (j + 1) ≠ .r3 := fun e => absurd (sreg_inj (j + 1) (by omega_using [hk4, hj]) 0 (by decide) e) (by omega_using [])
      simp only [sv, Nat.add_zero]
      rw [w₅.gpr _ h3, w₄.gpr _ (sreg_ne (fun h => hcb (by simp_all [blkRegs])) _),
        w₃.gpr _ (sreg_ne (r := .r9) (by decide) _)]
    rw [p₅, sx, sm] at e₆
    have s₂₄ : ∀ {r}, r ≠ .r3 → r ≠ c → r ≠ .r9 → t₄.gpr r = t₂.gpr r := fun h1 h2 h3 => by
      rw [w₄.gpr _ h2, w₃.gpr _ h3]
    rw [s₂₄ (Ne.symm (hs3 hhb)) (Ne.symm hch) (Ne.symm (hs9 hhb)), hb₂ hhb, g₁ (Ne.symm hch),
      w₄.gpr _ (fun e => hcb (by simp [← e, blkRegs])), w₃.gpr _ (by decide)] at e₅
    have r9 : (t₆.gpr .r9).toNat = hiw (s.gpr x) (word s.mem B (d + 8 * n)) := by
      rw [r₆, w₅.gpr _ (by decide), w₄.gpr _ (hs9 hcb), e₃, hb₂ hxb, g₁ hcx.symm, r₂ (by omega_using []),
        w₁.mem, Nat.add_sub_cancel]
    have hle : hiw (s.gpr x) (word s.mem B (d + 8 * n)) ≤ 2 ^ 64 - 2 := hi_le _ _
    have h7lt := (t₇.gpr h).isLt
    have c6 : t₆.ca.toNat ≤ 1 := Bool.toNat_le _
    rw [r9] at e₇
    have e₇' : (t₇.gpr h).toNat = hiw (s.gpr x) (word s.mem B (d + 8 * n)) + t₆.ca.toNat := by
      have : t₇.ca.toNat ≤ 1 := Bool.toNat_le _
      omega_using [e₇, hle, c6]
    have p₇ : psum (sv t₇ 0) (n + 1) = (t₅.gpr .r3).toNat + 2 ^ 64 * psum (sv t₆ 1) n := by
      rw [psum_shift]
      congr 1
      · show (t₇.gpr .r3).toNat = _
        rw [w₇.gpr _ (hs3 hhb)]
        exact congrArg BitVec.toNat (f₆ 0 (.inl rfl) (by decide))
      · refine congrArg _ (psum_congr fun j _ => ?_)
        simp only [sv]
        rw [w₇.gpr _ (sreg_ne (fun h' => hhb (by simp_all [blkRegs])) _)]
    rw [pow64_succ] at e₂
    have H := half_arith e₂ (psum_shift (sv t₂ 0) n) e₅ e₆ e₇'
    rw [p₇, pow64_succ, H, ← psum_lohi (s.gpr x) s.mem B d (n + 1)]
    rfl
  · intro j hj hj4
    have h3 : sreg j ≠ .r3 := fun e => absurd (sreg_inj j hj4 0 (by decide) e) (by omega_using [hj])
    rw [w₇.gpr _ (sreg_ne (fun h' => hhb (by simp_all [blkRegs])) _), f₆ j (.inr (by omega_using [hj])) hj4, w₅.gpr _ h3,
      w₄.gpr _ (sreg_ne (fun h' => hcb (by simp_all [blkRegs])) _), w₃.gpr _ (sreg_ne (r := .r9) (by decide) _),
      f₂ j hj hj4, g₁ (sreg_ne (fun h' => hcb (by simp_all [blkRegs])) _)]
  · rw [w₇.mem, m₆, w₅.mem, w₄.mem, w₃.mem, m₂, w₁.mem]
  · exact ((((((w₁.keep.trans k₂).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans k₆).trans w₇.keep).mono
      (fun r hr => by simp only [halfRegs, blkRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind)

/-! ## A block -/

theorem map_succ {α : Type} (f : Nat → α) (i : Nat) :
    (List.range (i + 1)).map f = (List.range i).map f ++ [f i] := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- The words of a block, loaded from `r14 + 8` on. -/
theorem loads_ok {B : Addr} {Z dT : Nat} : ∀ (i : Nat) {s : State}, Scr s B Z → s.gpr .r14 = off B dT → i ≤ 8 →
    dT + 8 * i + 8 ≤ Z →
    WP isa (.block ((List.range i).map fun j => .load .d (sreg j) .r14 (8 * j + 8))) s fun t =>
      (psum (sv t 0) i = wordsVal s.mem B (dT + 8) i ∧ t.mem = s.mem) ∧ Keep [.r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31] s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨rfl, rfl⟩, Keep.refl _ _⟩
  | i + 1, s, hs, h14, hi, hd => by
    rw [map_succ, WP.block_append_iff]
    refine WP.mono (loads_ok i hs h14 (by omega_using [hi]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, m₁⟩, k₁⟩ => ?_
    have h14' : t₁.gpr .r14 = off B dT := (k₁.gpr _ (by decide)).trans h14
    refine wp_ld (by decide) ⟨by omega_using [hi], by omega_using []⟩ (by rw [h14', off_add]) ((hs.congr k₁.wr).ld (by omega_using [hd]))
      fun t w e c => WP.block_nil ⟨⟨?_, by rw [w.mem, m₁]⟩, k₁.trans' (w.keep.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sreg_mem i)⟩
    have pt : psum (sv t 0) i = psum (sv t₁ 0) i := psum_congr fun j hj => by
      simp only [sv, Nat.add_zero]
      rw [w.gpr _ fun h => absurd (sreg_inj j (by omega_using [hi, hj]) i (by omega_using [hi]) h) (by omega_using [hj])]
    rw [psum, pt, e₁, wordsVal_succ_top]
    simp only [sv, Nat.add_zero]
    rw [e, m₁, show dT + (8 * i + 8) = dT + 8 + 8 * i by omega_using []]

/-- The words of a block, stored from `r14` on. -/
theorem stores_ok {B : Addr} {Z dT : Nat} : ∀ (i : Nat) {s : State}, Scr s B Z → s.gpr .r14 = off B dT → i ≤ 8 →
    dT + 8 * i ≤ Z →
    WP isa (.block ((List.range i).map fun j => .store .d (sreg j) .r14 (8 * j))) s fun t =>
      (wordsVal t.mem B dT i = psum (sv s 0) i ∧ Outside B dT (8 * i) s.mem t.mem) ∧ Keep [] s t
  | 0, s, _, _, _, _ => WP.block_nil ⟨⟨rfl, Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | i + 1, s, hs, h14, hi, hd => by
    have hnw := hs.nowrap
    rw [map_succ, WP.block_append_iff]
    refine WP.mono (stores_ok i hs h14 (by omega_using [hi]) (by omega_using [hd])) fun t₁ ⟨⟨e₁, o₁⟩, k₁⟩ => ?_
    have h14' : t₁.gpr .r14 = off B dT := (k₁.gpr _ (by simp)).trans h14
    refine wp_st (by decide) ⟨by omega_using [hi], by omega_using []⟩ (by rw [h14', off_add]) ((hs.congr k₁.wr).st (by omega_using [hd]))
      fun t w wm _ => WP.block_nil ⟨⟨?_, ?_⟩, k₁.trans' w⟩
    · rw [wm, wordsVal_succ_top, (writeW_outside _ B _ (by omega_using [hd, hnw])).wordsVal (by omega_using []) (by omega_using [hd, hnw]),
        word_writeW_self, e₁, psum, k₁.gpr _ (by simp)]
      rfl
    · rw [wm]
      exact (o₁.mono (Nat.le_refl _) (by omega_using [])).trans ((writeW_outside _ B _ (by omega_using [hd, hnw])).mono (by omega_using []) (by omega_using []))

/-- What the chains leave pending at the end of a block (and at its start):
the carries of the two low chains, kept in `r12` and `r11`, and the high
words of the two high chains, with their carries, in `r20` and `r22`; their
sum is `C`, of weight the block's next word. -/
def Pend (s : State) (C : Nat) : Prop :=
  ∃ bA bC : Bool, s.gpr .r12 = cenc bA ∧ s.gpr .r11 = cenc bC ∧
    C = bA.toNat + (s.gpr .r20).toNat + bC.toNat + (s.gpr .r22).toNat

/-- The registers a block writes. -/
def blockRegs : List Reg := [.r0, .r9, .r3, .r4, .r7, .r8, .r28, .r29, .r30, .r31, .r11, .r12, .r20, .r22, .r14, .r15, .r16]

theorem block_arith {T P₀ P₁ P₂ W Q a b u m bA hA bC hC bA' hA' bC' hC' : Nat} (hT : P₀ = T)
    (eA : P₁ + Q * (bA' + hA') = P₀ + bA + hA + a * b) (eC : P₂ + Q * (bC' + hC') = P₁ + bC + hC + u * m)
    (hW : W = P₂) : W + Q * (bA' + hA' + bC' + hC') = T + a * b + u * m + (bA + hA + bC + hC) := by
  subst hT hW
  grind

/-- A block of `k` words (`block k`), `r14` at `dT` (word `j - 1` of `T`) and `r15`,
`r16` at `dB`, `dM` (word `j` of `b` and `m`): the `k` words stored from
`dT` and the values pending after it make up `T + aᵢ b + u m` plus the values
pending before it, for the `k` words of `T`, `b` and `m` from `dT + 8`,
`dB` and `dM`, `aᵢ` in `r18` and `u` in `r19`; the pointers advanced. -/
theorem block_ok {s : State} {B : Addr} {Z dT dB dM k C : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B dT) (h15 : s.gpr .r15 = off B dB) (h16 : s.gpr .r16 = off B dM)
    (hk : 1 ≤ k) (hk4 : k ≤ 8) (hT : dT + 8 * k + 8 ≤ Z) (hB : dB + 8 * k ≤ Z) (hM : dM + 8 * k ≤ Z)
    (h10 : (s.gpr .r10).toNat < 2 ^ 64 - 1) (hC : Pend s C) :
    WP isa (.block (block k)) s fun t =>
      ((∃ C', Pend t C' ∧ wordsVal t.mem B dT k + 2 ^ (64 * k) * C' =
          wordsVal s.mem B (dT + 8) k + (s.gpr .r18).toNat * wordsVal s.mem B dB k +
            (s.gpr .r19).toNat * wordsVal s.mem B dM k + C) ∧
        Outside B dT (8 * k) s.mem t.mem ∧ t.gpr .r14 = off B (dT + 8 * k) ∧ t.gpr .r15 = off B (dB + 8 * k) ∧
        t.gpr .r16 = off B (dM + 8 * k)) ∧ Keep blockRegs s t := by
  obtain ⟨bA, bC, hA, hC', rfl⟩ := hC
  unfold block
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- The words of `T`.
  refine WP.mono (loads_ok k hs h14 hk4 hT) fun t₁ ⟨⟨e₁, m₁⟩, k₁⟩ => ?_
  have g₁ : ∀ r ∈ [Reg.r10, .r11, .r12, .r14, .r15, .r16, .r18, .r19, .r20, .r22], t₁.gpr r = s.gpr r :=
    fun r hr => k₁.gpr r (by revert r hr; decide)
  -- `aᵢ b`.
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (c := .r12) (x := .r18) (p := .r15) (h := .r20) (d := dB) (b := bA) (hs.congr k₁.wr)
    (by rw [g₁ _ (by decide), h15]) hk hk4 hB (by rw [g₁ _ (by decide), hA]) (by rw [g₁ _ (by decide)]; exact h10)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t₂ ⟨⟨bA', c₂, e₂⟩, _, m₂, k₂⟩ => ?_
  have g₂ : ∀ r ∈ [Reg.r10, .r11, .r14, .r16, .r19, .r22], t₂.gpr r = t₁.gpr r :=
    fun r hr => k₂.gpr r (by revert r hr; decide)
  -- `u m`.
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (c := .r11) (x := .r19) (p := .r16) (h := .r22) (d := dM) (b := bC) (hs.congr (k₂.wr.trans k₁.wr))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h16]) hk hk4 hM (by rw [g₂ _ (by decide), g₁ _ (by decide), hC'])
    (by rw [g₂ _ (by decide), g₁ _ (by decide)]; exact h10)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t₃ ⟨⟨bC', c₃, e₃⟩, _, m₃, k₃⟩ => ?_
  have g₃ : ∀ r ∈ [Reg.r12, .r14, .r15, .r16, .r20], t₃.gpr r = t₂.gpr r :=
    fun r hr => k₃.gpr r (by revert r hr; decide)
  -- The stores, and the pointers.
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok (dT := dT) k (hs.congr (k₃.wr.trans (k₂.wr.trans k₁.wr)))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h14]) hk4 (by omega_using [hT])) fun t₄ ⟨⟨e₄, o₄⟩, k₄⟩ => ?_
  have g₄ : ∀ r ∈ [Reg.r14, .r15, .r16, .r18, .r19], t₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (by simp), k₃.gpr r (by revert r hr; decide), k₂.gpr r (by revert r hr; decide),
      k₁.gpr r (by revert r hr; decide)]
  refine wp_addi (by decide) (by omega_using [hk4]) fun t₅ w₅ e₅ _ => ?_
  refine wp_addi (by decide) (by omega_using [hk4]) fun t₆ w₆ e₆ _ => ?_
  refine wp_addi (by decide) (by omega_using [hk4]) fun t w e _ => WP.block_nil
    ⟨⟨⟨_, ⟨bA', bC', ?_, ?_, rfl⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [w.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), k₄.gpr _ (by simp), g₃ _ (by decide), c₂]
  · rw [w.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), k₄.gpr _ (by simp), c₃]
  · have r20 : t.gpr .r20 = t₂.gpr .r20 := by
      rw [w.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), k₄.gpr _ (by simp), g₃ _ (by decide)]
    have r22 : t.gpr .r22 = t₃.gpr .r22 := by
      rw [w.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), k₄.gpr _ (by simp)]
    rw [g₂ _ (by decide), g₂ _ (by decide), m₂, g₁ _ (by decide), g₁ _ (by decide), m₁] at e₃
    rw [g₁ _ (by decide), g₁ _ (by decide), m₁] at e₂
    rw [r20, r22, w.mem, w₆.mem, w₅.mem]
    exact block_arith e₁ e₂ e₃ e₄
  · rw [w.mem, w₆.mem, w₅.mem, ← m₁, ← m₂, ← m₃]
    exact o₄
  · rw [w.gpr _ (by decide), w₆.gpr _ (by decide), e₅, g₄ _ (by decide), h14, off_add]
  · rw [w.gpr _ (by decide), e₆, w₅.gpr _ (by decide), g₄ _ (by decide), h15, off_add]
  · rw [e, w₆.gpr _ (by decide), w₅.gpr _ (by decide), g₄ _ (by decide), h16, off_add]
  · exact ((((((k₁.trans k₂).trans k₃).trans k₄).trans w₅.keep).trans w₆.keep).trans w.keep).mono
      (by simp only [halfRegs, blkRegs, blockRegs]; decide)



theorem shr3_8 (w : Nat) (hw : 8 * w < 2 ^ 64) : BitVec.ofNat 64 (8 * w) >>> 3 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hw]

/-- The start of a round (`roundStart`), `r16` and `r15` at word `w` of `m` and
`b`. -/
theorem roundStart_ok {s : State} {B : Addr} {Z dA dB dM w R : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B dM) (h15 : s.gpr .r15 = off B (dB + 8 * w)) (h16 : s.gpr .r16 = off B (dM + 8 * w))
    (h17 : s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32)) (hlay : dA = dM + 16 * (w + 2))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 2) ≤ Z) :
    WP isa (.block roundStart) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 64 ((w - 1) % 4) ∧ t.gpr .r14 = off B dA ∧ t.gpr .r15 = off B dB ∧
        t.gpr .r16 = off B dM ∧ t.gpr .r19 = word s.mem B (dA + 8 * (w + 1)) ∧
        t.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (w - 1) / 4) ∧ t.mem = s.mem) ∧
      Keep [.r9, .r16, .r15, .r3, .r14, .r4, .r19, .r7, .r8, .r17] s t := by
  have hnw := hs.nowrap
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  unfold roundStart
  have e9 : off B (dM + 8 * w) - off B dM = BitVec.ofNat 64 (8 * w) := by
    rw [VG.Offset.add_sub_add _ (by omega_using []), Nat.add_sub_cancel_left]
  have e3 : BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 (8 * w) + off B dM = off B (dM + 16 * w) := by
    rw [BitVec.ofNat_add_ofNat, BitVec.add_comm, off_add]; congr 2; omega_using []
  have e17 : BitVec.ofNat 64 (R * 4294967296) + BitVec.ofNat 64 ((w - 1) / 4) =
      BitVec.ofNat 64 (R * 4294967296 + (w - 1) / 4) := BitVec.ofNat_add_ofNat _ _
  have e15 : off B (dB + 8 * w) - BitVec.ofNat 64 (8 * w) = off B dB := by
    rw [VG.Offset.add_ofNat_sub _ (by omega_using []), Nat.add_sub_cancel]
  prun [h10, h15, h16, h17, e9, e3, e15, exec_lsr_d, shr3_8 w (by omega_using [hw']), ofNat_sub_one hw (by omega_using [hw']),
    fios_quot (w - 1) (by omega_using [hw']), fios_rem (w - 1), e17,
    hs.ld (show dM + 16 * w + 8 * w + 40 + 8 ≤ Z by omega_using [hlay, hA])]
  subst hlay
  rw [show dM + 16 * w + 32 = dM + 16 * (w + 2) by omega_using [],
    show dM + 16 * w + 8 * w + 40 = dM + 16 * (w + 2) + 8 * (w + 1) by omega_using []]
  exact ⟨rfl, rfl⟩

theorem head_arith {t₀ l₁ hA s₀ c₁ l₂ hC c₂ ab um : Nat} (e₁ : s₀ + 2 ^ 64 * c₁ = t₀ + l₁)
    (eab : l₁ + 2 ^ 64 * hA = ab) (eum : l₂ + 2 ^ 64 * hC = um) (e₂ : 2 ^ 64 * c₂ = s₀ + l₂) :
    2 ^ 64 * (c₁ + hA + c₂ + hC) = t₀ + ab + um := by
  omega_using [e₁, eab, eum, e₂]

/-- Word 0 of a round (`head`), for `aᵢ` at `da` (`r6`), `T`, `b` and `m` at `r14`,
`r15`, `r16` and `m'` in `r19`: `aᵢ` in `r18`, `u` in `r19` and the values pending
for word 1 such that `2⁶⁴ C = t₀ + aᵢ b₀ + u m₀`; `b`'s and `m`'s pointers at word 1. -/
theorem head_ok {s : State} {B : Addr} {Z da dA dB dM : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h14 : s.gpr .r14 = off B dA) (h15 : s.gpr .r15 = off B dB)
    (h16 : s.gpr .r16 = off B dM) (hm : ((word s.mem B dM).toNat * (s.gpr .r19).toNat + 1) % 2 ^ 64 = 0)
    (ha : da + 8 ≤ Z) (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z) :
    WP isa (.block head) s fun t =>
      ((∃ C, Pend t C ∧ 2 ^ 64 * C = (word s.mem B dA).toNat + (word s.mem B da).toNat * (word s.mem B dB).toNat +
          (t.gpr .r19).toNat * (word s.mem B dM).toNat) ∧
        t.gpr .r18 = word s.mem B da ∧ t.gpr .r6 = off B (da + 8) ∧ t.gpr .r14 = off B dA ∧
        t.gpr .r15 = off B (dB + 8) ∧ t.gpr .r16 = off B (dM + 8) ∧ t.mem = s.mem) ∧
      Keep [.r18, .r6, .r3, .r0, .r20, .r12, .r19, .r22, .r11, .r15, .r16] s t := by
  unfold head
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [h6, off_add, Nat.add_zero]) (hs.ld ha) fun t₁ w₁ e₁ _ => ?_
  refine wp_addi (by decide) (by decide) fun t₂ w₂ e₂ _ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [w₂.gpr _ (by decide), w₁.gpr _ (by decide), h14, off_add, Nat.add_zero])
    ((hs.congr (w₂.wr.trans w₁.wr)).ld hA) fun t₃ w₃ e₃ _ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide),
    w₁.gpr _ (by decide), h15, off_add, Nat.add_zero]) ((hs.congr (w₃.wr.trans (w₂.wr.trans w₁.wr))).ld hB) fun t₄ w₄ e₄ _ => ?_
  refine wp_mulhu fun t₅ w₅ e₅ _ => ?_
  refine wp_mul fun t₆ w₆ e₆ _ => ?_
  refine wp_addc fun t₇ w₇ e₇ => ?_
  refine wp_save fun t₈ w₈ e₈ => ?_
  refine wp_mul fun t₉ w₉ e₉ _ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by
      rw [w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide),
        w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide),
        h16, off_add, Nat.add_zero])
    ((hs.congr (w₉.wr.trans (w₈.wr.trans (w₇.wr.trans (w₆.wr.trans (w₅.wr.trans (w₄.wr.trans (w₃.wr.trans
      (w₂.wr.trans w₁.wr))))))))).ld hM) fun t₁₀ w₁₀ e₁₀ _ => ?_
  refine wp_mulhu fun t₁₁ w₁₁ e₁₁ _ => ?_
  refine wp_mul fun t₁₂ w₁₂ e₁₂ _ => ?_
  refine wp_addc fun t₁₃ w₁₃ e₁₃ => ?_
  refine wp_save fun t₁₄ w₁₄ e₁₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₁₅ w₁₅ e₁₅ _ => ?_
  refine wp_addi (by decide) (by decide) fun t w e _ => WP.block_nil ⟨⟨⟨_, ⟨t₇.ca, t₁₃.ca, ?_, ?_, rfl⟩, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals simp (disch := decide) only [w.gpr, w₁₅.gpr, w₁₄.gpr, w₁₃.gpr, w₁₂.gpr, w₁₁.gpr, w₁₀.gpr, w₉.gpr,
    w₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, w₄.gpr, w₃.gpr, w₂.gpr, w₁.gpr, w.mem, w₁₅.mem, w₁₄.mem, w₁₃.mem, w₁₂.mem,
    w₁₁.mem, w₁₀.mem, w₉.mem, w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem] at *
  · exact e₈
  · exact e₁₄
  · -- the arithmetic
    rw [e₁, e₄] at e₅ e₆
    rw [e₆, e₃] at e₇
    rw [e₁₀] at e₁₁ e₁₂
    rw [e₁₂] at e₁₃
    show 2 ^ 64 * _ = (s.mem.readW (off B dA) 64).toNat +
      (s.mem.readW (off B da) 64).toNat * (s.mem.readW (off B dB) 64).toNat +
      (t₉.gpr .r19).toNat * (s.mem.readW (off B dM) 64).toNat
    have eab := lo_hi (s.mem.readW (off B da) 64) (s.mem.readW (off B dB) 64)
    have eum := lo_hi (t₉.gpr .r19) (s.mem.readW (off B dM) 64)
    have mt : ((t₇.gpr .r3).toNat + (t₉.gpr .r19 * s.mem.readW (off B dM) 64).toNat) % 2 ^ 64 = 0 := by
      rw [e₉, BitVec.toNat_mul, BitVec.toNat_mul, Nat.mul_comm (s.gpr .r19).toNat, Nat.add_mod, Nat.mod_mod,
        ← Nat.add_mod]
      exact mont_low _ _ _ hm
    have := (t₁₃.gpr .r3).isLt
    omega_using [e₅, e₇, e₁₁, e₁₃, eab, eum, mt]
  · exact e₁
  · rw [e₂, h6, off_add]
  · exact h14
  · rw [e₁₅, h15, off_add]
  · rw [e, h16, off_add]
  · exact (((((((((((((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).trans
      w₇.keep).trans w₈.keep).trans w₉.keep).trans w₁₀.keep).trans w₁₁.keep).trans w₁₂.keep).trans w₁₃.keep).trans
      w₁₄.keep).trans w₁₅.keep).trans w.keep).mono

/-! ## The words of a round -/

/-- After word 0 (`s₁`, which leaves `C₀` pending) and `j` more words: the
pointers at word `j` (`T`'s one down), the `j` words stored from `dA` and the
values pending after them make up `T + aᵢ b + u m` over those words plus `C₀`. -/
def Wd (B : Addr) (dA dB dM C₀ : Nat) (s₁ : State) (j : Nat) (t : State) : Prop :=
  t.gpr .r14 = off B (dA + 8 * j) ∧ t.gpr .r15 = off B (dB + 8 + 8 * j) ∧ t.gpr .r16 = off B (dM + 8 + 8 * j) ∧
    Outside B dA (8 * j) s₁.mem t.mem ∧
    (∃ C, Pend t C ∧ wordsVal t.mem B dA j + 2 ^ (64 * j) * C =
      wordsVal s₁.mem B (dA + 8) j + (s₁.gpr .r18).toNat * wordsVal s₁.mem B (dB + 8) j +
        (s₁.gpr .r19).toNat * wordsVal s₁.mem B (dM + 8) j + C₀) ∧
    Keep (.r17 :: blockRegs) s₁ t

theorem Wd.zero {B : Addr} {dA dB dM C₀ : Nat} {s₁ : State} (h14 : s₁.gpr .r14 = off B dA)
    (h15 : s₁.gpr .r15 = off B (dB + 8)) (h16 : s₁.gpr .r16 = off B (dM + 8)) (hC : Pend s₁ C₀) :
    Wd B dA dB dM C₀ s₁ 0 s₁ :=
  ⟨by rw [h14]; rfl, by rw [h15], by rw [h16], Outside.refl _ _ _ _,
    ⟨C₀, hC, by simp [wordsVal]⟩, Keep.refl _ _⟩

/-- A block of `k` words after `j` words. -/
theorem Wd.step {B : Addr} {Z dA dB dM C₀ w j k : Nat} {s₁ t : State} (hs : Scr s₁ B Z)
    (hW : Wd B dA dB dM C₀ s₁ j t) (hk : 1 ≤ k) (hk4 : k ≤ 8) (hjk : j + k + 1 ≤ w)
    (h10 : (s₁.gpr .r10).toNat < 2 ^ 64 - 1)
    (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa (.block (block k)) t fun u => Wd B dA dB dM C₀ s₁ (j + k) u ∧ u.gpr .r17 = t.gpr .r17 := by
  have hnw := hs.nowrap
  obtain ⟨h14, h15, h16, o, ⟨C, hC, e⟩, kt⟩ := hW
  have g : ∀ r ∈ [Reg.r10, .r18, .r19], t.gpr r = s₁.gpr r := fun r hr => kt.gpr r (by revert r hr; decide)
  refine WP.mono (block_ok (hs.congr kt.wr) h14 h15 h16 hk hk4 (by omega_using [hjk, hA]) (by omega_using [hjk, hB]) (by omega_using [hjk, hM])
    (by rw [g _ (by decide)]; exact h10) hC) fun t' ⟨⟨⟨C', hC', e'⟩, o', p14, p15, p16⟩, k'⟩ => ?_
  refine ⟨⟨by rw [p14, Nat.add_assoc, ← Nat.mul_add], by rw [p15, Nat.add_assoc (dB + 8), ← Nat.mul_add],
    by rw [p16, Nat.add_assoc (dM + 8), ← Nat.mul_add], ?_, ⟨C', hC', ?_⟩, kt.trans' (k'.mono (by decide))⟩,
    k'.gpr _ (by decide)⟩
  · exact (o.mono (Nat.le_refl _) (by omega_using [])).trans (o'.mono (by omega_using []) (by omega_using []))
  · -- The words the block read are those after word 0.
    have rd : ∀ d, (d + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ d ∨ d = dA) → d + 8 * w ≤ Z →
        wordsVal t.mem B (d + 8 + 8 * j) k = wordsVal s₁.mem B (d + 8 + 8 * j) k := fun d hd hdZ =>
      o.wordsVal (by omega_using [hjk, hd]) (by omega_using [hjk, hnw, hdZ])
    rw [show dA + 8 * j + 8 = dA + 8 + 8 * j by omega_using [], rd dA (.inr (.inr rfl)) (by omega_using [hA]), rd dB (by omega_using [dBA]) hB,
      rd dM (by omega_using [dMA]) hM, g _ (by decide), g _ (by decide)] at e'
    rw [fios_wordsVal_append, fios_wordsVal_append s₁.mem B (dA + 8), fios_wordsVal_append s₁.mem B (dB + 8),
      fios_wordsVal_append s₁.mem B (dM + 8), show 64 * (j + k) = 64 * j + 64 * k by omega_using [], Nat.pow_add,
      show wordsVal t'.mem B dA j = wordsVal t.mem B dA j from o'.wordsVal (by omega_using []) (by omega_using [hjk, hA, hnw])]
    exact fios_sum_group e e' rfl

theorem Wd.write {B : Addr} {dA dB dM C₀ j : Nat} {s₁ t : State} (h : Wd B dA dB dM C₀ s₁ j t) {r : Reg}
    (v : BitVec 64) (h₁ : r ∈ Reg.r17 :: blockRegs := by decide)
    (h₂ : r ∉ [Reg.r14, .r15, .r16, .r11, .r12, .r20, .r22] := by decide) :
    Wd B dA dB dM C₀ s₁ j (t.write r v) := by
  obtain ⟨h14, h15, h16, o, ⟨C, ⟨bA, bC, e12, e11, eC⟩, e⟩, kt⟩ := h
  have g : ∀ r' ∈ [Reg.r14, .r15, .r16, .r11, .r12, .r20, .r22], (t.write r v).gpr r' = t.gpr r' := fun r' hr' => by
    rw [gpr_write, ite_eq_right fun (e : r' = r) => h₂ (e ▸ hr')]
  exact ⟨by rw [g _ (by decide)]; exact h14, by rw [g _ (by decide)]; exact h15, by rw [g _ (by decide)]; exact h16, o,
    ⟨C, ⟨bA, bC, by rw [g _ (by decide)]; exact e12, by rw [g _ (by decide)]; exact e11,
      by rw [g _ (by decide), g _ (by decide)]; exact eC⟩, e⟩,
    kt.trans' ((Keep.write t r v).mono fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact h₁)⟩

/-- Words `1` to `N` (`N = (w - 1) mod 4`, in `r9`), one block of `N` words. -/
theorem remBlock_ok {B : Addr} {Z dA dB dM C₀ w N : Nat} {s₁ t : State} (hs : Scr s₁ B Z)
    (hW : Wd B dA dB dM C₀ s₁ 0 t) (h9 : t.gpr .r9 = BitVec.ofNat 64 N) (hN : N < 4) (hNw : N + 1 ≤ w)
    (h10 : (s₁.gpr .r10).toNat < 2 ^ 64 - 1)
    (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa remBlock t fun u => Wd B dA dB dM C₀ s₁ N u ∧ u.gpr .r17 = t.gpr .r17 := by
  have step := fun {j k : Nat} {t' : State} (h : Wd B dA dB dM C₀ s₁ j t') (e : t'.gpr .r17 = t.gpr .r17)
    (hk : 1 ≤ k) (hk4 : k ≤ 8) (hjk : j + k + 1 ≤ w) =>
    WP.mono (Wd.step hs h hk hk4 hjk h10 hA hB hM dBA dMA) fun _ h => And.intro h.1 (h.2.trans e)
  unfold remBlock
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_using [hN]) h9) (fun hz => ?_) (fun hz => ?_)
  · have : N = 0 := of_decide_eq_true hz
    subst this
    exact WP.block_nil ⟨hW, rfl⟩
  have hN0 : N ≠ 0 := of_decide_eq_false hz
  refine WP.seq (WP.mono (subi_ok t .r9 (by decide)) fun t₁ e₁ => ?_)
  subst e₁
  have h9₁ : (t.write .r9 (t.gpr .r9 - BitVec.ofNat 64 1)).gpr .r9 = BitVec.ofNat 64 (N - 1) := by
    rw [gpr_write, ite_eq_left rfl, h9, ofNat_sub_one (by omega_using [hN0]) (by omega_using [hN])]
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_using [hN]) h9₁) (fun hz => ?_) (fun hz => ?_)
  · have : N = 1 := by have := of_decide_eq_true hz; omega_using [hN0, this]
    subst this
    exact step (hW.write _) (by rw [gpr_write]; rfl) (by decide) (by decide) (by omega_using [hNw])
  have hN1 : N - 1 ≠ 0 := of_decide_eq_false hz
  refine WP.seq (WP.mono (subi_ok _ .r9 (by decide)) fun t₂ e₂ => ?_)
  subst e₂
  have h9₂ : ((t.write .r9 (t.gpr .r9 - BitVec.ofNat 64 1)).write .r9 (BitVec.ofNat 64 (N - 1) - BitVec.ofNat 64 1)).gpr
      .r9 = BitVec.ofNat 64 (N - 2) := by
    rw [gpr_write, ite_eq_left rfl, ofNat_sub_one (by omega_using [hN1]) (by omega_using [hN])]; rfl
  rw [h9₁]
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_using [hN]) h9₂) (fun hz => ?_) (fun hz => ?_)
  · have : N = 2 := by have := of_decide_eq_true hz; omega_using [hN1, this]
    subst this
    exact step ((hW.write _).write _) (by rw [gpr_write, gpr_write]; rfl) (by decide) (by decide) (by omega_using [hNw])
  · have : N = 3 := by have := of_decide_eq_false hz; omega_using [hN, this]
    subst this
    exact step ((hW.write _).write _) (by rw [gpr_write, gpr_write]; rfl) (by decide) (by decide) (by omega_using [hNw])

/-- `r17`, `R` rounds in its high half and `n` in its low half, compared with 0
as a word: its low half. -/
theorem eval_w17 {s : State} {R n : Nat} (h : s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + n)) (hn : n < 2 ^ 32) :
    isa.eval (.zero .w .r17) s = some (decide (n = 0)) ∧ isa.eval (.nonzero .w .r17) s = some (decide (n ≠ 0)) := by
  have e : s.read .w .r17 = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [State.read, h, Size.bits, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []
  have z : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
    rw [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl]
    by_cases hz : n = 0
    · simp [hz]
    · simp only [hz, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_ofNat] at this
      omega_using [hn, hz, this]
  refine ⟨?_, ?_⟩
  · change VG.PPC64LE.eval (.zero .w .r17) s = _
    simp only [VG.PPC64LE.eval, e, z]
  · change VG.PPC64LE.eval (.nonzero .w .r17) s = _
    simp only [VG.PPC64LE.eval, e, bne, z, decide_not]

/-- The blocks of four words: `N` of them, counted by `r17`'s low half, after `j`
words. -/
theorem quadLoop_ok {B : Addr} {Z dA dB dM C₀ w R j N : Nat} {s₁ t : State} (hs : Scr s₁ B Z)
    (hW : Wd B dA dB dM C₀ s₁ j t) (h17 : t.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + N)) (hR : R < 2 ^ 31)
    (hN : N < 2 ^ 31) (hjN : j + 4 * N + 1 ≤ w) (h10 : (s₁.gpr .r10).toNat < 2 ^ 64 - 1)
    (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa quadLoop t fun t' => Wd B dA dB dM C₀ s₁ (j + 4 * N) t' ∧ t'.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32) := by
  unfold quadLoop
  refine WP.ite _ (eval_w17 h17 (by omega_using [hN])).1 (fun hz => ?_) (fun hz => ?_)
  · have : N = 0 := of_decide_eq_true hz
    subst this
    exact WP.block_nil ⟨hW, by rw [h17, Nat.add_zero]⟩
  have hN0 : N ≠ 0 := of_decide_eq_false hz
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => ∃ i, m = N - i ∧ i < N ∧ Wd B dA dB dM C₀ s₁ (j + 4 * i) s ∧
      s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (N - i))) (fun (m : Nat) (s : State) ⟨i, hm, hi, hW', h17'⟩ => ?_) N t
    ⟨0, by omega_using [], by omega_using [hN0], hW, by rw [h17, Nat.sub_zero]⟩
  rw [WP.block_append_iff]
  refine WP.mono (Wd.step (k := 4) hs hW' (by decide) (by decide) (by omega_using [hjN, hi]) h10 hA hB hM dBA dMA)
    fun u ⟨hu, u17'⟩ => ?_
  have u17 : u.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (N - i)) := u17'.trans h17'
  refine WP.mono (subi_ok u .r17 (by decide)) fun u' e => ?_
  subst e
  have e17 : (u.write .r17 (u.gpr .r17 - BitVec.ofNat 64 1)).gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (N - (i + 1))) := by
    rw [gpr_write, ite_eq_left rfl, u17, ofNat_sub_one (by omega_using [hi]) (by omega_using [hR, hN])]
    congr 1; omega_using [hi]
  have hW₂ := hu.write (r := .r17) (u.gpr .r17 - BitVec.ofNat 64 1)
  rw [show j + 4 * i + 4 = j + 4 * (i + 1) by omega_using []] at hW₂
  by_cases hl : i + 1 = N
  · refine .inl ⟨by rw [(eval_w17 e17 (by omega_using [hN])).2, decide_eq_false (by omega_using [hl])], ?_, ?_⟩
    · rw [← hl]; exact hW₂
    · rw [e17, hl, Nat.sub_self, Nat.add_zero]
  · exact .inr ⟨by rw [(eval_w17 e17 (by omega_using [hN])).2, decide_eq_true (by omega_using [hi, hl])], N - (i + 1), by omega_using [hm, hi], i + 1, rfl,
      by omega_using [hi, hl], hW₂, e17⟩

theorem round_dec {R : Nat} (hR : 1 ≤ R) (hR' : R < 2 ^ 31) :
    BitVec.ofNat 64 (R * 2 ^ 32) - BitVec.ofNat 64 1 <<< 32 = BitVec.ofNat 64 ((R - 1) * 2 ^ 32) ∧
      BitVec.ofNat 64 ((R - 1) * 2 ^ 32) >>> 32 = BitVec.ofNat 64 (R - 1) := by
  constructor <;> apply BitVec.eq_of_toNat_eq
  · rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.sub_mul, Nat.one_mul]
    omega_using [hR]
  · simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_using [hR']

/-- Word `w` (`top`), `r14` at `dT` (word `w - 1`): the word at `dT + 8` plus the
values pending, stored as two words at `dT`; one round less in `r17`'s high
half, and the rounds left in `r9`. -/
theorem top_ok {s : State} {B : Addr} {Z dT C R : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B dT)
    (hT : dT + 16 ≤ Z) (hC : Pend s C) (h10 : (s.gpr .r10).toNat < 2 ^ 64 - 1)
    (h17 : s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32)) (hR : 1 ≤ R) (hR' : R < 2 ^ 31) :
    WP isa (.block top) s fun t =>
      ((∃ x y : BitVec 64, t.mem = (s.mem.writeW (off B dT) x).writeW (off B (dT + 8)) y ∧
        x.toNat + 2 ^ 64 * y.toNat = (word s.mem B (dT + 8)).toNat + C) ∧
        t.gpr .r17 = BitVec.ofNat 64 ((R - 1) * 2 ^ 32) ∧ t.gpr .r9 = BitVec.ofNat 64 (R - 1)) ∧
      Keep [.r3, .r4, .r12, .r11, .r9, .r17] s t := by
  obtain ⟨bA, bC, eA, eC, rfl⟩ := hC
  unfold top
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [h14, off_add]) (hs.ld (by omega_using [hT])) fun t₁ w₁ e₁ _ => ?_
  refine wp_write (exec_li (d := .r4) (imm := 0) (by decide)) fun t₂ w₂ e₂ _ => ?_
  refine wp_restore (b := bA) (by rw [w₂.gpr _ (by decide), w₁.gpr _ (by decide), eA])
    (by rw [w₂.gpr _ (by decide), w₁.gpr _ (by decide)]; exact h10) fun t₃ w₃ c₃ => ?_
  refine wp_adde fun t₄ w₄ e₄ => ?_
  refine wp_addze fun t₅ w₅ e₅ => ?_
  refine wp_restore (b := bC) (by simp (disch := decide) only [w₅.gpr, w₄.gpr, w₃.gpr, w₂.gpr, w₁.gpr]; exact eC)
    (by simp (disch := decide) only [w₅.gpr, w₄.gpr, w₃.gpr, w₂.gpr, w₁.gpr]; exact h10) fun t₆ w₆ c₆ => ?_
  refine wp_adde fun t₇ w₇ e₇ => ?_
  refine wp_addze fun t₈ w₈ e₈ => ?_
  have h14₈ : t₈.gpr .r14 = off B dT := by
    simp (disch := decide) only [w₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, w₄.gpr, w₃.gpr, w₂.gpr, w₁.gpr]; exact h14
  have wr₈ : t₈.wr = s.wr := by
    rw [w₈.wr, w₇.wr, w₆.wr, w₅.wr, w₄.wr, w₃.wr, w₂.wr, w₁.wr]
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [h14₈, off_add, Nat.add_zero])
    (by rw [wr₈]; exact hs.st (by omega_using [hT])) fun t₉ k₉ m₉ _ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [k₉.gpr _ (by simp), h14₈, off_add])
    (by rw [k₉.wr, wr₈]; exact hs.st (by omega_using [hT])) fun t₁₀ k₁₀ m₁₀ _ => ?_
  refine wp_write (exec_li (d := .r9) (imm := 1) (by decide)) fun t₁₁ w₁₁ e₁₁ _ => ?_
  refine wp_write (exec_lsl (d := .r9) (n := .r9) (sh := 32) (by decide)) fun t₁₂ w₁₂ e₁₂ _ => ?_
  refine wp_write (exec_sub (d := .r17) (n := .r17) (m := .r9)) fun t₁₃ w₁₃ e₁₃ _ => ?_
  have h17t : t₁₃.gpr .r17 = BitVec.ofNat 64 ((R - 1) * 2 ^ 32) := by
    rw [e₁₃, w₁₂.gpr _ (by decide), e₁₂, e₁₁, w₁₁.gpr _ (by decide), k₁₀.gpr _ (by simp), k₉.gpr _ (by simp)]
    simp (disch := decide) only [w₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, w₄.gpr, w₃.gpr, w₂.gpr, w₁.gpr]
    rw [h17, (round_dec hR hR').1]
  refine wp_write (exec_lsr_d (d := .r9) (n := .r17) (sh := 32) (by decide)) fun t w e _ =>
    WP.block_nil ⟨⟨⟨t₈.gpr .r3, t₈.gpr .r4, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [w.mem, w₁₃.mem, w₁₂.mem, w₁₁.mem, m₁₀, m₉, k₉.gpr _ (by simp), w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem,
      w₃.mem, w₂.mem, w₁.mem]
  · simp (disch := decide) only [w₈.gpr, w₇.gpr, w₆.gpr, w₅.gpr, w₄.gpr, w₃.gpr, w₂.gpr, w₁.gpr] at e₄ e₅ e₇ e₈ ⊢
    rw [c₃, e₁] at e₄
    rw [e₂] at e₅
    rw [c₆] at e₇
    have := (t₈.gpr .r3).isLt
    have := (t₈.gpr .r4).isLt
    have := (t₅.gpr .r4).isLt
    have := (t₇.gpr .r3).isLt
    have := (t₄.gpr .r3).isLt
    have := Bool.toNat_le t₄.ca
    have := Bool.toNat_le t₅.ca
    have := Bool.toNat_le t₇.ca
    have := Bool.toNat_le t₈.ca
    have := Bool.toNat_le bA
    have := Bool.toNat_le bC
    simp only [BitVec.toNat_ofNat] at e₅
    show _ = (s.mem.readW (off B (dT + 8)) 64).toNat + _
    omega_arith
  · rw [w.gpr _ (by decide), h17t]
  · rw [e, h17t, (round_dec hR hR').2]
  · exact ((((((((((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).trans
      w₇.keep).trans w₈.keep).trans k₉).trans k₁₀).trans w₁₁.keep).trans w₁₂.keep).trans w₁₃.keep).trans w.keep
      |>.mono (by decide)

/-! ## A round -/

/-- The registers a round writes. -/
def roundRegs : List Reg :=
  [.r0, .r3, .r4, .r6, .r7, .r8, .r9, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r27, .r22, .r28, .r29,
    .r30, .r31]

/-- A round (`round`), for `aᵢ` at `da` (`r6`, advanced), `T` (`w + 1` words) at
`dA = dM + 16 (w + 2)`, `m'` above it, `b` and `m` (`w` words) at `dB` and `dM`,
`R` rounds left: `2⁶⁴ T' = T + aᵢ b + u m` for some `u < 2⁶⁴`, one round less. -/
theorem round_ok {s : State} {B : Addr} {Z da dA dB dM w R : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h10 : s.gpr .r10 = off B dM) (h15 : s.gpr .r15 = off B (dB + 8 * w))
    (h16 : s.gpr .r16 = off B (dM + 8 * w)) (h17 : s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32))
    (hlay : dA = dM + 16 * (w + 2))
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dA + 8 * (w + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hR : 1 ≤ R) (hR' : R < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) :
    WP isa round s fun t =>
      (t.gpr .r6 = off B (da + 8) ∧ t.gpr .r15 = off B (dB + 8 * w) ∧ t.gpr .r16 = off B (dM + 8 * w) ∧
        t.gpr .r17 = BitVec.ofNat 64 ((R - 1) * 2 ^ 32) ∧ t.gpr .r9 = BitVec.ofNat 64 (R - 1) ∧
        Outside B dA (8 * (w + 1)) s.mem t.mem ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal t.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w +
            u * wordsVal s.mem B dM w) ∧
      Keep roundRegs s t := by
  have hnw := hs.nowrap
  have h10' : (s.gpr .r10).toNat < 2 ^ 64 - 1 := by
    rw [h10, VG.Offset.toNat_add_ofNat]; omega_using [hw, hM, hnw]
  have dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM := .inl (by omega_using [hlay])
  have hK := Nat.mod_add_div (w - 1) 4
  generalize hN₁ : (w - 1) % 4 = N₁ at hK
  generalize hN₂ : (w - 1) / 4 = N₂ at hK
  have hN₁4 : N₁ < 4 := hN₁ ▸ Nat.mod_lt _ (by decide)
  unfold round
  rw [WP.seq_iff, WP.block_append_iff]
  -- The pointers and counts, then word 0.
  refine WP.mono (roundStart_ok hs h10 h15 h16 h17 hlay hw hw' hA) fun s₁ ⟨⟨i9, i14, i15, i16, i19, i17, im⟩, k₁⟩ => ?_
  refine WP.mono (head_ok (da := da) (dA := dA) (dB := dB) (dM := dM) (hs.congr k₁.wr) (by rw [k₁.gpr _ (by decide), h6]) i14
    i15 i16 (by rw [i19, im]; exact hm) ha (by omega_using [hA]) (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK]) (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK]))
    fun s₂ ⟨⟨⟨C₀, hC₀, e₀⟩, j18, j6, j14, j15, j16, jm⟩, k₂⟩ => ?_
  rw [hN₁] at i9
  have g₂ : ∀ r ∈ [Reg.r9, .r10, .r17], s₂.gpr r = s₁.gpr r := fun r hr => k₂.gpr r (by revert r hr; decide)
  have hs₂ : Scr s₂ B Z := hs.congr (k₂.wr.trans k₁.wr)
  have h10₂ : (s₂.gpr .r10).toNat < 2 ^ 64 - 1 := by rw [g₂ _ (by decide), k₁.gpr _ (by decide)]; exact h10'
  -- Words `1` to `N₁`, then `N₁ + 1` to `w - 1`, four at a time.
  refine WP.seq (WP.mono (remBlock_ok (w := w) hs₂ (Wd.zero j14 j15 j16 hC₀) (by rw [g₂ _ (by decide), i9]) hN₁4
    (by omega_using [hw, hN₁]) h10₂ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK]) hB hM dBA dMA) fun s₃ ⟨hW₃, e₃⟩ => ?_)
  refine WP.seq (WP.mono (quadLoop_ok (R := R) (N := N₂) hs₂ hW₃ (by rw [e₃, g₂ _ (by decide), i17, ← hN₂])
    (by omega_using [hR']) (by omega_using [hw', hN₂]) (by omega_using [hw, hN₁, hN₂]) h10₂ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK]) hB hM dBA dMA) fun s₄ ⟨hW₄, e₄⟩ => ?_)
  obtain ⟨n14, n15, n16, o₄, ⟨C, hC, eC⟩, k₄⟩ := hW₄
  rw [show N₁ + 4 * N₂ = w - 1 by omega_using [hN₁, hN₂]] at n14 n15 n16 o₄ eC
  -- Word `w`.
  refine WP.mono (top_ok (dT := dA + 8 * (w - 1)) (hs₂.congr k₄.wr) n14 (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK]) hC
    (by rw [k₄.gpr _ (by decide)]; exact h10₂) e₄ hR hR') fun t ⟨⟨⟨x, y, tm, txy⟩, t17, t9⟩, k₅⟩ => ?_
  have m₂ : s₂.mem = s.mem := jm.trans im
  have g₄ : ∀ r ∈ [Reg.r6, .r19], t.gpr r = s₂.gpr r := fun r hr => by
    rw [k₅.gpr r (by revert r hr; decide), k₄.gpr r (by revert r hr; decide)]
  have o₄' : Outside B dA (8 * (w - 1)) s.mem s₄.mem := m₂ ▸ o₄
  refine ⟨⟨by rw [g₄ _ (by decide), j6], by rw [k₅.gpr _ (by decide), n15, show dB + 8 + 8 * (w - 1) = dB + 8 * w by omega_using [hw]],
    by rw [k₅.gpr _ (by decide), n16, show dM + 8 + 8 * (w - 1) = dM + 8 * w by omega_using [hw]], t17, t9, ?_, (s₂.gpr .r19).toNat, (s₂.gpr .r19).isLt, ?_⟩,
    (((k₁.trans k₂).trans k₄).trans k₅).mono (by decide)⟩
  · rw [tm]
    exact (o₄'.mono (Nat.le_refl _) (by omega_using [])).trans
      (((writeW_outside _ B _ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK, hN₁4])).mono (by omega_using []) (by omega_using [])).trans
        ((writeW_outside _ B _ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK, hN₁4])).mono (by omega_using []) (by omega_using [hw])))
  · -- The words the blocks and the top read are those on entry.
    have tw : word s₄.mem B (dA + 8 * (w - 1) + 8) = word s.mem B (dA + 8 + 8 * (w - 1)) := by
      rw [o₄'.word (by omega_using []) (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK, hN₁4]), show dA + 8 * (w - 1) + 8 = dA + 8 + 8 * (w - 1) by omega_using []]
    rw [tw] at txy
    rw [m₂, j18, im] at eC
    rw [im] at e₀
    rw [tm, show w + 1 = w - 1 + 2 by omega_using [hw], fios_wordsVal_write2 _ _ _ _ _ _ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hN₂, hK, hN₁4]),
      fios_wordsVal_pred s.mem B dA (show 1 ≤ w - 1 + 2 by omega_using []), show w - 1 + 2 - 1 = w - 1 + 1 by omega_using [],
      wordsVal_succ_top s.mem B (dA + 8) (w - 1), fios_wordsVal_pred s.mem B dB hw, fios_wordsVal_pred s.mem B dM hw]
    exact fios_round_sum (c := C) (d := 0) (by rw [Nat.add_zero]; exact eC) e₀ (by rw [txy]; omega_using [])

/-! ## The kernel's round: blocks of eight words -/

theorem quot8 (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [h]

/-- Bit 2 of `n`, by shifts. -/
theorem bit2 (n : Nat) : BitVec.ofNat 64 n <<< 61 >>> 63 = BitVec.ofNat 64 (n / 4 % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega_using []

/-- The start of the kernel's round (`roundStart8`): `roundStart`, with `(w -
1) / 8` blocks in `r17`'s low half and bit 2 of `w - 1` in `r27`. -/
theorem roundStart8_ok {s : State} {B : Addr} {Z dA dB dM w R : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B dM) (h15 : s.gpr .r15 = off B (dB + 8 * w)) (h16 : s.gpr .r16 = off B (dM + 8 * w))
    (h17 : s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32)) (hlay : dA = dM + 16 * (w + 2))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 2) ≤ Z) :
    WP isa (.block roundStart8) s fun t =>
      (t.gpr .r9 = BitVec.ofNat 64 ((w - 1) % 4) ∧ t.gpr .r27 = BitVec.ofNat 64 ((w - 1) / 4 % 2) ∧
        t.gpr .r14 = off B dA ∧ t.gpr .r15 = off B dB ∧
        t.gpr .r16 = off B dM ∧ t.gpr .r19 = word s.mem B (dA + 8 * (w + 1)) ∧
        t.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (w - 1) / 8) ∧ t.mem = s.mem) ∧
      Keep [.r9, .r16, .r15, .r3, .r14, .r4, .r19, .r7, .r8, .r17, .r27] s t := by
  have hnw := hs.nowrap
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  unfold roundStart8
  have e9 : off B (dM + 8 * w) - off B dM = BitVec.ofNat 64 (8 * w) := by
    rw [VG.Offset.add_sub_add _ (by omega_using []), Nat.add_sub_cancel_left]
  have e3 : BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 (8 * w) + off B dM = off B (dM + 16 * w) := by
    rw [BitVec.ofNat_add_ofNat, BitVec.add_comm, off_add]; congr 2; omega_using []
  have e17 : BitVec.ofNat 64 (R * 4294967296) + BitVec.ofNat 64 ((w - 1) / 8) =
      BitVec.ofNat 64 (R * 4294967296 + (w - 1) / 8) := BitVec.ofNat_add_ofNat _ _
  have e15 : off B (dB + 8 * w) - BitVec.ofNat 64 (8 * w) = off B dB := by
    rw [VG.Offset.add_ofNat_sub _ (by omega_using []), Nat.add_sub_cancel]
  prun [h10, h15, h16, h17, e9, e3, e15, exec_lsr_d, shr3_8 w (by omega_using [hw']), ofNat_sub_one hw (by omega_using [hw']),
    quot8 (w - 1) (by omega_using [hw']), bit2 (w - 1), fios_rem (w - 1), e17,
    hs.ld (show dM + 16 * w + 8 * w + 40 + 8 ≤ Z by omega_using [hlay, hA])]
  subst hlay
  rw [show dM + 16 * w + 32 = dM + 16 * (w + 2) by omega_using [],
    show dM + 16 * w + 8 * w + 40 = dM + 16 * (w + 2) + 8 * (w + 1) by omega_using []]
  exact ⟨rfl, rfl⟩

/-- One block of four words if `r27` holds 1 (`quadBlock`), after `j` words. -/
theorem quadBlock_ok {B : Addr} {Z dA dB dM C₀ w j q : Nat} {s₁ t : State} (hs : Scr s₁ B Z)
    (hW : Wd B dA dB dM C₀ s₁ j t) (h21 : t.gpr .r27 = BitVec.ofNat 64 q) (hq : q < 2) (hjq : j + 4 * q + 1 ≤ w)
    (h10 : (s₁.gpr .r10).toNat < 2 ^ 64 - 1)
    (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa quadBlock t fun u => Wd B dA dB dM C₀ s₁ (j + 4 * q) u ∧ u.gpr .r17 = t.gpr .r17 := by
  unfold quadBlock
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_using [hq]) h21) (fun hz => ?_) (fun hz => ?_)
  · have : q = 0 := of_decide_eq_true hz
    subst this
    exact WP.block_nil ⟨hW, rfl⟩
  · have : q = 1 := by have := of_decide_eq_false hz; omega_using [hq, this]
    subst this
    exact Wd.step hs hW (by decide) (by decide) (by omega_using [hjq]) h10 hA hB hM dBA dMA

/-- The blocks of eight words: `N` of them, counted by `r17`'s low half, after `j`
words. -/
theorem octLoop_ok {B : Addr} {Z dA dB dM C₀ w R j N : Nat} {s₁ t : State} (hs : Scr s₁ B Z)
    (hW : Wd B dA dB dM C₀ s₁ j t) (h17 : t.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + N)) (hR : R < 2 ^ 31)
    (hN : N < 2 ^ 31) (hjN : j + 8 * N + 1 ≤ w) (h10 : (s₁.gpr .r10).toNat < 2 ^ 64 - 1)
    (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa octLoop t fun t' => Wd B dA dB dM C₀ s₁ (j + 8 * N) t' ∧ t'.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32) := by
  unfold octLoop
  refine WP.ite _ (eval_w17 h17 (by omega_using [hN])).1 (fun hz => ?_) (fun hz => ?_)
  · have : N = 0 := of_decide_eq_true hz
    subst this
    exact WP.block_nil ⟨hW, by rw [h17, Nat.add_zero]⟩
  have hN0 : N ≠ 0 := of_decide_eq_false hz
  refine WP.loop (M := isa) (fun (m : Nat) (s : State) => ∃ i, m = N - i ∧ i < N ∧ Wd B dA dB dM C₀ s₁ (j + 8 * i) s ∧
      s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (N - i))) (fun (m : Nat) (s : State) ⟨i, hm, hi, hW', h17'⟩ => ?_) N t
    ⟨0, by omega_using [], by omega_using [hN0], hW, by rw [h17, Nat.sub_zero]⟩
  rw [WP.block_append_iff]
  refine WP.mono (Wd.step (k := 8) hs hW' (by decide) (by decide) (by omega_using [hjN, hi]) h10 hA hB hM dBA dMA)
    fun u ⟨hu, u17'⟩ => ?_
  have u17 : u.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (N - i)) := u17'.trans h17'
  refine WP.mono (subi_ok u .r17 (by decide)) fun u' e => ?_
  subst e
  have e17 : (u.write .r17 (u.gpr .r17 - BitVec.ofNat 64 1)).gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32 + (N - (i + 1))) := by
    rw [gpr_write, ite_eq_left rfl, u17, ofNat_sub_one (by omega_using [hi]) (by omega_using [hR, hN])]
    congr 1; omega_using [hi]
  have hW₂ := hu.write (r := .r17) (u.gpr .r17 - BitVec.ofNat 64 1)
  rw [show j + 8 * i + 8 = j + 8 * (i + 1) by omega_using []] at hW₂
  by_cases hl : i + 1 = N
  · refine .inl ⟨by rw [(eval_w17 e17 (by omega_using [hN])).2, decide_eq_false (by omega_using [hl])], ?_, ?_⟩
    · rw [← hl]; exact hW₂
    · rw [e17, hl, Nat.sub_self, Nat.add_zero]
  · exact .inr ⟨by rw [(eval_w17 e17 (by omega_using [hN])).2, decide_eq_true (by omega_using [hi, hl])], N - (i + 1), by omega_using [hm, hi], i + 1, rfl,
      by omega_using [hi, hl], hW₂, e17⟩


/-- The kernel's round (`round8`): `round_ok`, with the words after word 0 in a
block of `(w - 1) mod 4`, a block of four if bit 2 of `w - 1` is set, and
blocks of eight. -/
theorem round8_ok {s : State} {B : Addr} {Z da dA dB dM w R : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h10 : s.gpr .r10 = off B dM) (h15 : s.gpr .r15 = off B (dB + 8 * w))
    (h16 : s.gpr .r16 = off B (dM + 8 * w)) (h17 : s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32))
    (hlay : dA = dM + 16 * (w + 2))
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dA + 8 * (w + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hR : 1 ≤ R) (hR' : R < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) :
    WP isa round8 s fun t =>
      (t.gpr .r6 = off B (da + 8) ∧ t.gpr .r15 = off B (dB + 8 * w) ∧ t.gpr .r16 = off B (dM + 8 * w) ∧
        t.gpr .r17 = BitVec.ofNat 64 ((R - 1) * 2 ^ 32) ∧ t.gpr .r9 = BitVec.ofNat 64 (R - 1) ∧
        Outside B dA (8 * (w + 1)) s.mem t.mem ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal t.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w +
            u * wordsVal s.mem B dM w) ∧
      Keep roundRegs s t := by
  have hnw := hs.nowrap
  have h10' : (s.gpr .r10).toNat < 2 ^ 64 - 1 := by
    rw [h10, VG.Offset.toNat_add_ofNat]; omega_using [hw, hM, hnw]
  have dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM := .inl (by omega_using [hlay])
  have hK : (w - 1) % 4 + 4 * ((w - 1) / 4 % 2) + 8 * ((w - 1) / 8) = w - 1 := by omega_using []
  generalize hN₁ : (w - 1) % 4 = N₁ at hK
  generalize hq : (w - 1) / 4 % 2 = q at hK
  generalize hN₂ : (w - 1) / 8 = N₂ at hK
  have hN₁4 : N₁ < 4 := hN₁ ▸ Nat.mod_lt _ (by decide)
  have hq2 : q < 2 := hq ▸ Nat.mod_lt _ (by decide)
  unfold round8
  rw [WP.seq_iff, WP.block_append_iff]
  -- The pointers and counts, then word 0.
  refine WP.mono (roundStart8_ok hs h10 h15 h16 h17 hlay hw hw' hA)
    fun s₁ ⟨⟨i9, i21, i14, i15, i16, i19, i17, im⟩, k₁⟩ => ?_
  refine WP.mono (head_ok (da := da) (dA := dA) (dB := dB) (dM := dM) (hs.congr k₁.wr) (by rw [k₁.gpr _ (by decide), h6]) i14
    i15 i16 (by rw [i19, im]; exact hm) ha (by omega_using [hA]) (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK]) (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK]))
    fun s₂ ⟨⟨⟨C₀, hC₀, e₀⟩, j18, j6, j14, j15, j16, jm⟩, k₂⟩ => ?_
  rw [hN₁] at i9
  rw [hq] at i21
  have g₂ : ∀ r ∈ [Reg.r9, .r10, .r17, .r27], s₂.gpr r = s₁.gpr r := fun r hr => k₂.gpr r (by revert r hr; decide)
  have hs₂ : Scr s₂ B Z := hs.congr (k₂.wr.trans k₁.wr)
  have h10₂ : (s₂.gpr .r10).toNat < 2 ^ 64 - 1 := by rw [g₂ _ (by decide), k₁.gpr _ (by decide)]; exact h10'
  -- Words `1` to `N₁`, then four words if `q` is 1, then the rest, eight at a time.
  refine WP.seq (WP.mono (remBlock_ok (w := w) hs₂ (Wd.zero j14 j15 j16 hC₀) (by rw [g₂ _ (by decide), i9]) hN₁4
    (by omega_using [hw, hN₁]) h10₂ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK]) hB hM dBA dMA) fun s₃ ⟨hW₃, e₃⟩ => ?_)
  have e21 : s₃.gpr .r27 = BitVec.ofNat 64 q := by
    rw [hW₃.2.2.2.2.2.gpr _ (by decide), g₂ _ (by decide), i21]
  refine WP.seq (WP.mono (quadBlock_ok (q := q) hs₂ hW₃ e21 hq2 (by omega_using [hw, hw', hA, hB, hM, dBA, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2]) h10₂ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK]) hB hM dBA dMA)
    fun s₃' ⟨hW₃', e₃'⟩ => ?_)
  refine WP.seq (WP.mono (octLoop_ok (R := R) (N := N₂) hs₂ hW₃' (by rw [e₃', e₃, g₂ _ (by decide), i17, ← hN₂])
    (by omega_using [hR']) (by omega_using [hw, hw', hA, hB, hM, dBA, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2]) (by omega_using [hw, hw', hA, hB, hM, dBA, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2]) h10₂ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK]) hB hM dBA dMA) fun s₄ ⟨hW₄, e₄⟩ => ?_)
  obtain ⟨n14, n15, n16, o₄, ⟨C, hC, eC⟩, k₄⟩ := hW₄
  rw [show N₁ + 4 * q + 8 * N₂ = w - 1 by omega_using [hw, hw', hA, hB, hM, dBA, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2]] at n14 n15 n16 o₄ eC
  -- Word `w`.
  refine WP.mono (top_ok (dT := dA + 8 * (w - 1)) (hs₂.congr k₄.wr) n14 (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK]) hC
    (by rw [k₄.gpr _ (by decide)]; exact h10₂) e₄ hR hR') fun t ⟨⟨⟨x, y, tm, txy⟩, t17, t9⟩, k₅⟩ => ?_
  have m₂ : s₂.mem = s.mem := jm.trans im
  have g₄ : ∀ r ∈ [Reg.r6, .r19], t.gpr r = s₂.gpr r := fun r hr => by
    rw [k₅.gpr r (by revert r hr; decide), k₄.gpr r (by revert r hr; decide)]
  have o₄' : Outside B dA (8 * (w - 1)) s.mem s₄.mem := m₂ ▸ o₄
  refine ⟨⟨by rw [g₄ _ (by decide), j6], by rw [k₅.gpr _ (by decide), n15, show dB + 8 + 8 * (w - 1) = dB + 8 * w by omega_using [hw]],
    by rw [k₅.gpr _ (by decide), n16, show dM + 8 + 8 * (w - 1) = dM + 8 * w by omega_using [hw]], t17, t9, ?_, (s₂.gpr .r19).toNat, (s₂.gpr .r19).isLt, ?_⟩,
    (((k₁.trans k₂).trans k₄).trans k₅).mono (by decide)⟩
  · rw [tm]
    exact (o₄'.mono (Nat.le_refl _) (by omega_using [])).trans
      (((writeW_outside _ B _ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2])).mono (by omega_using []) (by omega_using [])).trans
        ((writeW_outside _ B _ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2])).mono (by omega_using []) (by omega_using [hw])))
  · -- The words the blocks and the top read are those on entry.
    have tw : word s₄.mem B (dA + 8 * (w - 1) + 8) = word s.mem B (dA + 8 + 8 * (w - 1)) := by
      rw [o₄'.word (by omega_using []) (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2]), show dA + 8 * (w - 1) + 8 = dA + 8 + 8 * (w - 1) by omega_using []]
    rw [tw] at txy
    rw [m₂, j18, im] at eC
    rw [im] at e₀
    rw [tm, show w + 1 = w - 1 + 2 by omega_using [hw], fios_wordsVal_write2 _ _ _ _ _ _ (by omega_using [hlay, hw, hw', ha, hA, hB, hM, dBA, hnw, dMA, hN₁, hq, hN₂, hK, hN₁4, hq2]),
      fios_wordsVal_pred s.mem B dA (show 1 ≤ w - 1 + 2 by omega_using []), show w - 1 + 2 - 1 = w - 1 + 1 by omega_using [],
      wordsVal_succ_top s.mem B (dA + 8) (w - 1), fios_wordsVal_pred s.mem B dB hw, fios_wordsVal_pred s.mem B dM hw]
    exact fios_round_sum (c := C) (d := 0) (by rw [Nat.add_zero]; exact eC) e₀ (by rw [txy]; omega_using [])


/-- What a round does (`round_ok`), of any code `Rd`: so that the rounds'
proof (`roundsWith_ok`) serves both `round` and the kernel's `round8`. -/
def RoundSpec (Rd : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {Z da dA dB dM w R : Nat}, Scr s B Z →
    s.gpr .r6 = off B da → s.gpr .r10 = off B dM → s.gpr .r15 = off B (dB + 8 * w) →
    s.gpr .r16 = off B (dM + 8 * w) → s.gpr .r17 = BitVec.ofNat 64 (R * 2 ^ 32) → dA = dM + 16 * (w + 2) →
    ((word s.mem B dM).toNat * (word s.mem B (dA + 8 * (w + 1))).toNat + 1) % 2 ^ 64 = 0 →
    1 ≤ w → w < 2 ^ 31 → 1 ≤ R → R < 2 ^ 31 →
    da + 8 ≤ Z → dA + 8 * (w + 2) ≤ Z → dB + 8 * w ≤ Z → dM + 8 * w ≤ Z →
    (dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) →
    WP isa Rd s fun t =>
      (t.gpr .r6 = off B (da + 8) ∧ t.gpr .r15 = off B (dB + 8 * w) ∧ t.gpr .r16 = off B (dM + 8 * w) ∧
        t.gpr .r17 = BitVec.ofNat 64 ((R - 1) * 2 ^ 32) ∧ t.gpr .r9 = BitVec.ofNat 64 (R - 1) ∧
        Outside B dA (8 * (w + 1)) s.mem t.mem ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal t.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w +
            u * wordsVal s.mem B dM w) ∧
      Keep roundRegs s t

theorem round_spec : RoundSpec round := fun hs h6 h10 h15 h16 h17 hlay hm hw hw' hR hR' ha hA hB hM dBA =>
  round_ok hs h6 h10 h15 h16 h17 hlay hm hw hw' hR hR' ha hA hB hM dBA

theorem round8_spec : RoundSpec round8 := fun hs h6 h10 h15 h16 h17 hlay hm hw hw' hR hR' ha hA hB hM dBA =>
  round8_ok hs h6 h10 h15 h16 h17 hlay hm hw hw' hR hR' ha hA hB hM dBA

/-! ## The rounds -/

theorem shl2_8 (w : Nat) : BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

theorem shr2_8 (w : Nat) (hw : 8 * w < 2 ^ 64) : BitVec.ofNat 64 (8 * w) >>> 2 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hw]

theorem shl32 (w : Nat) : BitVec.ofNat 64 w <<< 32 = BitVec.ofNat 64 (w * 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- Before the rounds (`roundsInit`). -/
theorem roundsInit_ok {s : State} {B : Addr} {dB dM w : Nat}
    (h7 : s.gpr .r7 = off B dB) (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s.gpr .r4 = BitVec.ofNat 64 w) :
    WP isa (.block roundsInit) s fun t =>
      (t.gpr .r16 = off B (dM + 8 * w) ∧ t.gpr .r15 = off B (dB + 8 * w) ∧
        t.gpr .r17 = BitVec.ofNat 64 (w * 2 ^ 32) ∧ t.mem = s.mem) ∧ Keep [.r9, .r16, .r15, .r17] s t := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  unfold roundsInit
  have e16 : off B dM + BitVec.ofNat 64 (8 * w) = off B (dM + 8 * w) := off_add _ _ _
  have e15 : off B dB + BitVec.ofNat 64 (8 * w) = off B (dB + 8 * w) := off_add _ _ _
  prun [h7, h10, h11, h4, shl2_8 w, shl32 w, e16, e15]

/-- After the rounds (`roundsFini`), `r16` and `r15` at word `w` of `m` and `b`. -/
theorem roundsFini_ok {s : State} {B : Addr} {Z dA dB dM w : Nat} (hs : Scr s B Z)
    (h10 : s.gpr .r10 = off B dM) (h15 : s.gpr .r15 = off B (dB + 8 * w)) (h16 : s.gpr .r16 = off B (dM + 8 * w))
    (hlay : dA = dM + 16 * (w + 2)) (hw' : w < 2 ^ 31) (hA : dA + 8 * (w + 2) ≤ Z) :
    WP isa (.block roundsFini) s fun t =>
      (t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.gpr .r7 = off B dB ∧ t.gpr .r8 = off B dA ∧
        t.gpr .r9 = off B (dA + 8 * (w + 2)) ∧ t.gpr .r22 = word s.mem B (dA + 8 * (w + 1)) ∧ t.mem = s.mem) ∧
      Keep [.r3, .r11, .r7, .r8, .r9, .r4, .r22] s t := by
  have hnw := hs.nowrap
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  unfold roundsFini
  have e3 : off B (dM + 8 * w) - off B dM = BitVec.ofNat 64 (8 * w) := by
    rw [VG.Offset.add_sub_add _ (by omega_using []), Nat.add_sub_cancel_left]
  have e7 : off B (dB + 8 * w) - BitVec.ofNat 64 (8 * w) = off B dB := by
    rw [VG.Offset.add_ofNat_sub _ (by omega_using []), Nat.add_sub_cancel]
  have e8 : BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 (8 * w) + off B dM = off B (dM + 16 * w) := by
    rw [BitVec.ofNat_add_ofNat, BitVec.add_comm, off_add]; congr 2; omega_using []
  subst hlay
  prun [h10, h15, h16, e3, e7, e8, shr2_8 w (by omega_using [hw']), exec_lsr_d,
    hs.ld (show dM + 16 * w + 32 + 8 * w + 8 + 8 ≤ Z by omega_using [hA])]
  rw [show dM + 16 * w + 32 + 8 * w + 16 = dM + 16 * (w + 2) + 8 * (w + 2) by omega_using [],
    show dM + 16 * w + 32 + 8 * w + 8 = dM + 16 * (w + 2) + 8 * (w + 1) by omega_using [],
    show dM + 16 * w + 32 = dM + 16 * (w + 2) by omega_using []]
  exact ⟨rfl, rfl, rfl⟩


end VG.Proof.Bignum.PPC64LE.Mont4

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum (round_lt round_step)
open VG.Proof.Bignum.PPC64LE.Mont4 (roundsInit_ok roundsFini_ok)

/-- The registers the rounds write: those a round writes, but `r7`–`r9` and
`r11`, which they set back. -/
def roundsRegs : List Reg :=
  [.r0, .r3, .r4, .r6, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r27, .r22, .r28, .r29, .r30, .r31]

/-- The `w` rounds of any round `Rd` that does what a round does
(`RoundSpec`), over the words of `a` (at `da` of `B`, pointed to by `r6`),
from the accumulator 0 (at `dA = dM + 16 (w + 2)`, the temporary after it):
`T < 2m` and `T 2^(64 w) ≡ a b (mod m)`, for `b < m` (`w` words each, at `dB`
and `dM`), only the accumulator's `w + 2` words changed. -/
theorem roundsWith_ok {Rd : Prog isa} (hR : Mont4.RoundSpec Rd) {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h9 : s₀.gpr .r9 = off B (dA + 8 * (w + 2)))
    (h10 : s₀.gpr .r10 = off B dM) (h11 : s₀.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s₀.gpr .r4 = BitVec.ofNat 64 w)
    (hm : ((word s₀.mem B dM).toNat * (s₀.gpr .r22).toNat + 1) % 2 ^ 64 = 0)
    (h22 : s₀.gpr .r22 = word s₀.mem B (dA + 8 * (w + 1)))
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hlay : dA = dM + 16 * (w + 2))
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa (.seq (.block roundsInit) (.seq (.loop Rd (.nonzero .d .r9)) (.block roundsFini))) s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧ s.gpr .r22 = s₀.gpr .r22) ∧
      Keep roundsRegs s₀ s := by
  have hnw := hs.nowrap
  let M := wordsVal s₀.mem B dM w
  let Bv := wordsVal s₀.mem B dB w
  refine WP.seq (WP.mono (roundsInit_ok h7 h10 h11 h4) fun s₁ ⟨⟨i16, i15, i17, im⟩, k₁⟩ => ?_)
  let J : Nat → State → Prop := fun i s =>
    s.gpr .r6 = off B (da + 8 * i) ∧ s.gpr .r15 = off B (dB + 8 * w) ∧ s.gpr .r16 = off B (dM + 8 * w) ∧
    s.gpr .r17 = BitVec.ofNat 64 ((w - i) * 2 ^ 32) ∧ Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧
    wordsVal s.mem B dA (w + 1) < 2 * M ∧
    2 ^ (64 * i) * wordsVal s.mem B dA (w + 1) % M = wordsVal s₀.mem B da i * Bv % M ∧
    word s.mem B (dA + 8 * (w + 1)) = word s₀.mem B (dA + 8 * (w + 1)) ∧
    Keep Mont4.roundRegs s₀ s
  have hJ0 : J 0 s₁ := by
    refine ⟨by rw [k₁.gpr _ (by decide), h6]; rfl, i15, i16, by rw [i17, Nat.sub_zero], by rw [im]; exact Outside.refl _ _ _ _,
      by rw [im, hz]; omega, by rw [im, hz]; simp [wordsVal], by rw [im], k₁.mono (by decide)⟩
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.count_loop (cr := .r9) (n := w) (by omega_using [hw]) J
    (fun i hi s hJ => ?_) hJ0) fun s₂ hJ₂ => ?_)
  · obtain ⟨j6, j15, j16, j17, jout, jlt, jeq, jw, jk⟩ := hJ
    have g10 : s.gpr .r10 = off B dM := (jk.gpr _ (by decide)).trans h10
    have vM : wordsVal s.mem B dM w = M := jout.wordsVal (by omega_using [hlay]) (by omega_using [hlay, hA, hnw])
    have vB : wordsVal s.mem B dB w = Bv := jout.wordsVal (by omega_using [dBA]) (by omega_using [hB, hnw])
    have wM : word s.mem B dM = word s₀.mem B dM := jout.word (by omega_using [hlay]) (by omega_using [hw, hM, hnw])
    have wa : word s.mem B (da + 8 * i) = word s₀.mem B (da + 8 * i) := jout.word (by omega_using [daA, hi]) (by omega_using [ha, hnw, hi])
    refine WP.mono (hR (R := w - i) (da := da + 8 * i) (dA := dA) (dB := dB) (dM := dM) (w := w)
      (hs.congr jk.wr) j6 g10 j15 j16 j17 hlay (by rw [jw, wM, ← h22]; exact hm) (by omega_using [hw]) hw' (by omega_using [hi]) (by omega_using [hw'])
      (by omega_using [ha, hi]) hA hB hM (by omega_using [dBA])) fun s' ⟨⟨k6, k15, k16, k17, k9, kout, u, hu, keq⟩, k'⟩ => ⟨⟨?_, k15, k16, ?_, ?_, ?_, ?_,
        ?_, jk.trans' k'⟩, ?_⟩
    · rw [k6, Nat.mul_succ, Nat.add_assoc]
    · rw [k17, show w - i - 1 = w - (i + 1) by omega_using []]
    · exact jout.trans (kout.mono (Nat.le_refl _) (by omega_using []))
    · rw [vM, vB, wa] at keq
      have hM0 : 0 < M := by omega_using [jlt]
      exact round_lt keq jlt (s₀.mem.readW _ 64).isLt hb hu
    · rw [vM, vB, wa] at keq
      rw [wordsVal_succ_top s₀.mem B da i, Nat.mul_succ, Nat.pow_add]
      exact round_step keq jeq
    · rw [kout.word (by omega_using []) (by omega_using [hA, hnw]), jw]
    · rw [k9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hw'])]
      omega_using [hi]
  obtain ⟨j6, j15, j16, j17, jout, jlt, jeq, jw, jk⟩ := hJ₂
  refine WP.mono (roundsFini_ok (hs.congr jk.wr) ((jk.gpr _ (by decide)).trans h10) j15 j16 hlay hw' hA)
    fun t ⟨⟨t11, t7, t8, t9, t22, tm⟩, kt⟩ => ?_
  refine ⟨⟨by rw [tm]; exact jlt, by rw [tm]; exact jeq, by rw [tm]; exact jout, by rw [t22, jw, h22]⟩,
    ⟨fun r hr => ?_, kt.rd.trans jk.rd, kt.wr.trans jk.wr, kt.sp.trans jk.sp, kt.lr.trans jk.lr⟩⟩
  by_cases e7 : r = .r7
  · subst e7; rw [t7, h7]
  by_cases e8 : r = .r8
  · subst e8; rw [t8, h8]
  by_cases e9 : r = .r9
  · subst e9; rw [t9, h9]
  by_cases e11 : r = .r11
  · subst e11; rw [t11, h11]
  rw [kt.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; simp_all [roundsRegs]),
    jk.gpr r (by simp only [Mont4.roundRegs, List.mem_cons, List.not_mem_nil, or_false]; simp_all [roundsRegs])]

/-- The `w` rounds (`rounds`). -/
theorem rounds_ok {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h9 : s₀.gpr .r9 = off B (dA + 8 * (w + 2)))
    (h10 : s₀.gpr .r10 = off B dM) (h11 : s₀.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s₀.gpr .r4 = BitVec.ofNat 64 w)
    (hm : ((word s₀.mem B dM).toNat * (s₀.gpr .r22).toNat + 1) % 2 ^ 64 = 0)
    (h22 : s₀.gpr .r22 = word s₀.mem B (dA + 8 * (w + 1)))
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hlay : dA = dM + 16 * (w + 2))
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa rounds s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧ s.gpr .r22 = s₀.gpr .r22) ∧
      Keep roundsRegs s₀ s := by
  unfold rounds
  exact roundsWith_ok Mont4.round_spec hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb

/-- `rounds_ok`, of the kernel's rounds by blocks of up to eight words. -/
theorem rounds8_ok {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h9 : s₀.gpr .r9 = off B (dA + 8 * (w + 2)))
    (h10 : s₀.gpr .r10 = off B dM) (h11 : s₀.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h4 : s₀.gpr .r4 = BitVec.ofNat 64 w)
    (hm : ((word s₀.mem B dM).toNat * (s₀.gpr .r22).toNat + 1) % 2 ^ 64 = 0)
    (h22 : s₀.gpr .r22 = word s₀.mem B (dA + 8 * (w + 1)))
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hlay : dA = dM + 16 * (w + 2))
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa rounds8 s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧ s.gpr .r22 = s₀.gpr .r22) ∧
      Keep roundsRegs s₀ s := by
  unfold rounds8
  exact roundsWith_ok Mont4.round8_spec hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb

/-- What the rounds do (`rounds_ok`), of any code `R` that writes at most the
registers `rr`: so that `tail`'s proof serves both `tail` and the kernel's
`tail8`. -/
def RoundsSpecW (rr : List Reg) (R : Prog isa) : Prop :=
  ∀ {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat}, Scr s₀ B Z →
    s₀.gpr .r6 = off B da → s₀.gpr .r8 = off B dA → s₀.gpr .r7 = off B dB →
    s₀.gpr .r9 = off B (dA + 8 * (w + 2)) → s₀.gpr .r10 = off B dM → s₀.gpr .r11 = BitVec.ofNat 64 (2 * w) →
    s₀.gpr .r4 = BitVec.ofNat 64 w →
    ((word s₀.mem B dM).toNat * (s₀.gpr .r22).toNat + 1) % 2 ^ 64 = 0 →
    s₀.gpr .r22 = word s₀.mem B (dA + 8 * (w + 1)) →
    2 ≤ w → w < 2 ^ 31 → dA = dM + 16 * (w + 2) →
    da + 8 * w ≤ Z → dA + 8 * (w + 2) ≤ Z → dB + 8 * w ≤ Z → dM + 8 * w ≤ Z →
    (da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da) → (dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB) →
    wordsVal s₀.mem B dA (w + 1) = 0 → wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w →
    WP isa R s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧ s.gpr .r22 = s₀.gpr .r22) ∧
      Keep rr s₀ s

/-- `RoundsSpecW` of the rounds' registers (`roundsRegs`). -/
abbrev RoundsSpec (R : Prog isa) : Prop := RoundsSpecW roundsRegs R

theorem rounds_spec : RoundsSpec rounds := fun hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb =>
  rounds_ok hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb

theorem rounds8_spec : RoundsSpec rounds8 := fun hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb =>
  rounds8_ok hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb

end VG.Proof.Bignum.PPC64LE
