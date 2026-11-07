module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Search
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.Sieve
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Impl.Ffdh.RISCV64.Search
public meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public meta import VerifiedGarbage.Proof.Framework.RelCT
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# FFDH's prime search on RISC-V: the sieve, `montPrep` and the round's call

The proofs of `Impl/Ffdh/RISCV64/Search.lean`'s pieces, alongside those of
the shared ones (`Proof/MillerRabin/RISCV64/Search/`), as on PPC64LE
(`Proof/MillerRabin/PPC64LE/Search/`):

* `smallMod_ok`: `s0 := ` the number in the `w` words at `o` (`a7`) modulo
  `d` (in `s1`, from 2 to `2^62`), from the top bit: `r := 2 r + b`, less
  `d` when that is not below it (`modStep_ok`, by `sltu`'s mask: `sub_sel`);
* `sieve_ok`: `hBad` stays zero exactly when it was and no number of `ds`
  divides the candidate; `hBad` is the only word written;
* `montPrep_ok`: `montPrepWith_ok` with `r2Any` (`128 w` doublings, then
  Newton's iteration, `r2Any_ok`), for any odd `N ≥ 3`;
* `roundCall_ct`: two runs from the same prepared working space and witness
  (`RC`) leak the same: the witness into Montgomery form and the arguments
  from the working space's registers, the round as its contract makes it
  (`RelCT.call`), and the registers back.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Search

/-! ## The bit-serial remainder and the sieve -/

section

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Impl.Ffdh.RISCV64.Search
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (wv Frm word writeW_outside word_writeW_self)
open VG.Proof.Mont (off)

theorem rw_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.writeW a v).readW a 64 = v :=
  Mem.readW_writeW_self64 m a v

/-- A store at a covered offset keeps a change within the ranges. -/
theorem frm_writeW {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {a : Nat} (v : BitVec 64)
    (ha : ∃ r ∈ rs, r.1 ≤ a ∧ a + 8 ≤ r.1 + r.2) (ha' : a + 8 ≤ 2 ^ 64) :
    Frm B rs m (m'.writeW (B + BitVec.ofNat 64 a) v) :=
  h.trans ((Frm.of_outside (rs := [(a, 8)]) (writeW_outside m' B (d := a) v ha') (List.mem_singleton_self _)).widen
    fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact ha)

/-- `t` or `t − d` by `sltu`'s mask: `t mod d` for `t < 2 d`. -/
theorem sub_sel {t d : Nat} (ht : t < 2 ^ 63) (hd : d < 2 ^ 63) :
    BitVec.ofNat 64 t ^^^ ((BitVec.ofNat 64 t - BitVec.ofNat 64 d ^^^ BitVec.ofNat 64 t) &&&
        ((if BitVec.ofNat 64 t < BitVec.ofNat 64 d then (1 : BitVec 64) else 0) - BitVec.ofNat 64 1)) =
      BitVec.ofNat 64 (if d ≤ t then t - d else t) := by
  have hlt : (BitVec.ofNat 64 t < BitVec.ofNat 64 d) ↔ t < d := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  by_cases h : d ≤ t
  · have e : BitVec.ofNat 64 t - BitVec.ofNat 64 d = BitVec.ofNat 64 (t - d) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    rw [ite_eq_right_iff.mpr (fun e => absurd (hlt.mp e) (by omega_arith)), show (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide,
      e, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_comm (BitVec.ofNat 64 t), BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero, ite_eq_left h]
  · simp only [show BitVec.ofNat 64 t < BitVec.ofNat 64 d from hlt.mpr (by omega_arith), ↓reduceIte]
    rw [show (1 : BitVec 64) - BitVec.ofNat 64 1 = 0#64 by decide,
      BitVec.and_zero, BitVec.xor_zero, ite_eq_right h]

theorem mod_double_bit (c N b : Nat) : (2 * (c % N) + b) % N = (2 * c + b) % N := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- One step of the remainder: `s0 := (2 r + b) mod d` for `b` the top bit
of `s2`, which is shifted left. -/
theorem modStep_ok (u : State) {d r : Nat} (hd : 2 ≤ d) (hd' : d < 2 ^ 62) (h1 : u.gpr .s1 = BitVec.ofNat 64 d)
    (h0 : u.gpr .s0 = BitVec.ofNat 64 r) (hr : r < d) :
    WP isa (.block ([.shift .srl .d .s3 .s2 63, .shift .sll .d .s2 .s2 1, .add .s0 .s0 .s0, .add .s0 .s0 .s3,
        .sub .s3 .s0 .s1, .sltu .s4 .s0 .s1, .addi .s4 .s4 (-1), .logic .xor .s3 .s3 .s0,
        .logic .and .s3 .s3 .s4, .logic .xor .s0 .s0 .s3] : List Instr)) u fun u' =>
      (u'.gpr .s0 = BitVec.ofNat 64 ((2 * r + (u.gpr .s2 >>> 63).toNat) % d) ∧ u'.gpr .s2 = u.gpr .s2 <<< 1 ∧
        u'.mem = u.mem) ∧ Keep [.s0, .s2, .s3, .s4] u u' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have hb : (u.gpr .s2 >>> 63).toNat ≤ 1 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := (u.gpr .s2).isLt; omega_arith
  have et : BitVec.ofNat 64 r + BitVec.ofNat 64 r + u.gpr .s2 >>> 63 =
      BitVec.ofNat 64 (2 * r + (u.gpr .s2 >>> 63).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  brun [h0, h1]
  rw [et, sub_sel (by omega_arith) (by omega_arith)]
  congr 1
  generalize (u.gpr .s2 >>> 63).toNat = b at hb
  split
  · rw [Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  · rw [Nat.mod_eq_of_lt (by omega_arith)]

theorem top_bit (x : BitVec 64) {i : Nat} (hi : i < 64) :
    (BitVec.ofNat 64 (x.toNat * 2 ^ i % 2 ^ 64) >>> 63).toNat = x.toNat / 2 ^ (63 - i) % 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftRight_eq_div_pow]
  have e1 : (2 : Nat) ^ 64 = 2 ^ i * (2 ^ (63 - i) * 2) := by
    rw [← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega_arith
  have e2 : (2 : Nat) ^ 63 = 2 ^ i * 2 ^ (63 - i) := by rw [← Nat.pow_add]; congr 1; omega_arith
  rw [e1, e2, Nat.mul_comm x.toNat, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _),
    Nat.mod_mul_right_div_self]

theorem shl_step (x : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 (x.toNat * 2 ^ i % 2 ^ 64) <<< 1 = BitVec.ofNat 64 (x.toNat * 2 ^ (i + 1) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod, Nat.shiftLeft_eq,
    Nat.pow_succ 2 i, ← Nat.mul_assoc, Nat.pow_one, Nat.mod_mul_mod, Nat.mod_mod]

theorem div_step (x : Nat) {i : Nat} (hi : i < 64) : x / 2 ^ (63 - i) = 2 * (x / 2 ^ (64 - i)) + x / 2 ^ (63 - i) % 2 := by
  rw [show 64 - i = 63 - i + 1 by omega_arith, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega_arith

/-- The 64 steps over the word `x` in `s2`: `s0 := (2^64 v + x) mod d`. -/
theorem bits_ok {s : State} {d V : Nat} {x : BitVec 64} (hd : 2 ≤ d) (hd' : d < 2 ^ 62)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 d) (h0 : s.gpr .s0 = BitVec.ofNat 64 (V % d)) (h2 : s.gpr .s2 = x)
    (h5 : s.gpr .t5 = BitVec.ofNat 64 64) :
    WP isa (countLoop .t5 [.shift .srl .d .s3 .s2 63, .shift .sll .d .s2 .s2 1, .add .s0 .s0 .s0, .add .s0 .s0 .s3,
        .sub .s3 .s0 .s1, .sltu .s4 .s0 .s1, .addi .s4 .s4 (-1), .logic .xor .s3 .s3 .s0,
        .logic .and .s3 .s3 .s4, .logic .xor .s0 .s0 .s3]) s fun t =>
      (t.gpr .s0 = BitVec.ofNat 64 ((V * 2 ^ 64 + x.toNat) % d) ∧ t.mem = s.mem) ∧
        Keep [.s0, .s2, .s3, .s4, .t5] s t := by
  let Inv : Nat → State → Prop := fun i u =>
    (u.gpr .s0 = BitVec.ofNat 64 ((V * 2 ^ i + x.toNat / 2 ^ (64 - i)) % d) ∧
      u.gpr .s2 = BitVec.ofNat 64 (x.toNat * 2 ^ i % 2 ^ 64) ∧ u.mem = s.mem) ∧ Keep [.s0, .s2, .s3, .s4, .t5] s u
  refine WP.mono (wp_countdown (cnt := .t5) (N := 64) (by decide) (by decide) Inv
    (fun i hi u ⟨⟨u0, u2, um⟩, ku⟩ _ => ?_) ⟨⟨?_, ?_, rfl⟩, Keep.refl _ _⟩ h5) fun t ⟨⟨t0, _, tm⟩, kt⟩ => ?_
  · rw [WP.block_append_iff]
    have u1 : u.gpr .s1 = BitVec.ofNat 64 d := (ku.gpr (by decide)).trans h1
    refine WP.mono (modStep_ok u hd hd' u1 u0 (Nat.mod_lt _ (by omega_arith))) fun u₁ ⟨⟨a0, a2, am⟩, k1⟩ => ?_
    have hdec : WP isa (.block [.addi .t5 .t5 (-1)]) u₁ fun u₂ =>
        (u₂.gpr .t5 = u₁.gpr .t5 - BitVec.ofNat 64 1 ∧ u₂.mem = u₁.mem) ∧ Keep [.t5] u₁ u₂ := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun
    refine WP.mono hdec fun u₂ ⟨⟨b5, bm⟩, k2⟩ => ?_
    refine ⟨⟨⟨?_, ?_, by rw [bm, am, um]⟩, (ku.trans (k1.trans k2)).mono (by decide)⟩, ?_⟩
    · rw [k2.gpr (by decide), a0, u2, top_bit x hi, mod_double_bit]
      congr 2
      rw [Nat.pow_succ]
      have := div_step x.toNat hi
      have hf : V * (2 ^ i * 2) = 2 * (V * 2 ^ i) := by rw [Nat.mul_comm (2 ^ i) 2, Nat.mul_left_comm]
      rw [show 64 - (i + 1) = 63 - i by omega_arith, hf]
      omega_arith
    · rw [k2.gpr (by decide), a2, u2, shl_step]
    · rw [b5, k1.gpr (by decide)]
  · rw [h0, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (by have := x.isLt; omega_arith), Nat.add_zero]
  · rw [h2, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · refine ⟨⟨?_, tm⟩, kt⟩
    rw [t0, Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- The registers `smallMod` writes. -/
def smRegs : List Reg := [.s0, .s2, .s3, .s4, .t3, .t4, .t5]

theorem shl3_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `smallMod`: `s0 := ` the `w` words at `o` (`a7`) modulo `d` (in `s1`). -/
theorem smallMod_ok {s : State} {B : Addr} {Z o w d : Nat} (hs : Scr s B Z) (h7 : s.gpr .a7 = off B o)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h1 : s.gpr .s1 = BitVec.ofNat 64 d) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 8 = 0) (hd : 2 ≤ d) (hd' : d < 2 ^ 62) :
    WP isa smallMod s fun t => (t.gpr .s0 = BitVec.ofNat 64 (wv s.mem B o w % d) ∧ t.mem = s.mem) ∧
      Keep smRegs s t := by
  have hnw := hs.nowrap
  unfold smallMod
  refine WP.seq (WP.mono (WP.keep [.t3, .t4, .s0] (Q := fun u => u.gpr .t3 = off B (o + 8 * w) ∧
      u.gpr .t4 = BitVec.ofNat 64 w ∧ u.gpr .s0 = BitVec.ofNat 64 0 ∧ u.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨a3, a4, a0, am⟩, k1⟩ => ?_)
  · brun [h7, ht0, exec_li (show imm12 0 by decide), shl3_ofNat, BitVec.add_zero]
  let Inv : Nat → State → Prop := fun j t =>
    (t.gpr .s0 = BitVec.ofNat 64 (wv s.mem B (o + 8 * (w - j)) j % d) ∧ t.gpr .t3 = off B (o + 8 * (w - j)) ∧
      t.mem = s.mem) ∧ Keep smRegs s t
  refine WP.mono (wp_countdown (cnt := .t4) (N := w) (by omega_arith) (by omega_arith) Inv
    (fun j hj t ⟨⟨t0, t3, tm⟩, kt⟩ _ => ?_) ⟨⟨by rw [a0]; simp [wv], by rw [a3, Nat.sub_zero], am⟩,
      k1.mono (by decide)⟩ a4)
    fun t ⟨⟨t0, _, tm⟩, kt⟩ => ⟨⟨by rw [t0, Nat.sub_self, Nat.mul_zero, Nat.add_zero], tm⟩, kt⟩
  have ht : Scr t B Z := hs.congr kt.2.2
  have hrd : InRegions (t.rd ++ t.wr) (off B (o + 8 * (w - (j + 1)))) 8 := ht.ld (by omega_arith)
  have hal : (off B (o + 8 * (w - (j + 1)))).toNat % 8 = 0 := ht.al8 (by omega_arith) (by omega_arith)
  have e3 : off B (o + 8 * (w - j)) - BitVec.ofNat 64 8 = off B (o + 8 * (w - (j + 1))) := by
    rw [off_sub _ (by omega_arith)]; congr 1; omega_arith
  refine WP.seq (WP.mono (WP.keep [.t3, .s2, .t5] (Q := fun u => u.gpr .t3 = off B (o + 8 * (w - (j + 1))) ∧
      u.gpr .s2 = word s.mem B (o + 8 * (w - (j + 1))) ∧ u.gpr .t5 = BitVec.ofNat 64 64 ∧ u.mem = s.mem) ?_
    (by rfl) (by rfl)) fun u ⟨⟨u3, u2, u5, um⟩, ku⟩ => ?_)
  · brun [t3, e3, hrd, hal, BitVec.add_zero, tm, exec_li (show imm12 64 by decide)]
  refine WP.seq (WP.mono (bits_ok (V := wv s.mem B (o + 8 * (w - j)) j) hd hd'
    ((ku.gpr (by decide)).trans ((kt.gpr (by decide)).trans h1)) ((ku.gpr (by decide)).trans t0) u2 u5)
    fun v ⟨⟨v0, vm⟩, kv⟩ => ?_)
  have hdec : WP isa (.block [.addi .t4 .t4 (-1)]) v fun v₂ =>
      (v₂.gpr .t4 = v.gpr .t4 - BitVec.ofNat 64 1 ∧ v₂.mem = v.mem) ∧ Keep [.t4] v v₂ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun
  refine WP.mono hdec fun v₂ ⟨⟨b4, bm⟩, k2⟩ => ?_
  refine ⟨⟨⟨?_, ?_, by rw [bm, vm, um]⟩, ((kt.trans ku).trans (kv.trans k2)).mono (by decide)⟩, ?_⟩
  · rw [k2.gpr (by decide), v0]
    congr 2
    have e := VG.Proof.Bignum.wv_add s.mem B (o + 8 * (w - (j + 1))) 1 j
    rw [Nat.add_comm 1 j] at e
    rw [e, show o + 8 * (w - (j + 1)) + 8 * 1 = o + 8 * (w - j) by omega_arith]
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]
    rw [Nat.mul_comm _ (2 ^ 64), Nat.add_comm]
  · rw [k2.gpr (by decide), kv.gpr (by decide), u3]
  · rw [b4, kv.gpr (by decide), ku.gpr (by decide)]

theorem flag_eq {r : Nat} (hr : r < 2 ^ 64) :
    (if BitVec.ofNat 64 r < BitVec.ofInt 64 1 then (1 : BitVec 64) else 0) = 0#64 ↔ r ≠ 0 := by
  have : (BitVec.ofNat 64 r < BitVec.ofInt 64 1) ↔ r = 0 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, show (BitVec.ofInt 64 1).toNat = 1 from rfl]
    omega
  by_cases h : r = 0
  · simp only [this.mpr h, ↓reduceIte]; simp [h]
  · simp only [show ¬ BitVec.ofNat 64 r < BitVec.ofInt 64 1 from fun e => h (this.mp e), ↓reduceIte]; simp [h]

/-- `hBad` stored over `m`. -/
theorem bad_post {m : Mem} {B : Addr} {t : State} {v : BitVec 64} {P : Prop}
    (tm : t.mem = m.writeW (B + BitVec.ofNat 64 200) v) (hv : v = 0#64 ↔ P) :
    (word t.mem B (8 * hBad) = 0#64 ↔ P) ∧ Frm B [(8 * hBad, 8)] m t.mem := by
  refine ⟨?_, ?_⟩
  · simp only [word, VG.Proof.Bignum.off, hBad, Nat.reduceMul, tm, rw_self]; exact hv
  · rw [tm]
    exact frm_writeW (a := 200) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩ (by decide)

/-- The registers a trial division writes. -/
def trRegs : List Reg := .t2 :: .a4 :: .s1 :: smRegs

theorem trial_ok {s : State} {B : Addr} {Z o w x d : Nat} (hs : Scr s B Z) (h7 : s.gpr .a7 = off B o)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hx : wv s.mem B o w = x) (hw1 : 1 ≤ w)
    (hw : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 8 = 0) (hd2 : 2 ≤ d) (hd : d < 2 ^ 11) {P : Prop}
    (h4 : s.gpr .a4 = 0#64 ↔ P) :
    WP isa (trial d) s fun t => ((t.gpr .a4 = 0#64 ↔ P ∧ x % d ≠ 0) ∧ t.mem = s.mem) ∧ Keep trRegs s t := by
  unfold trial
  refine WP.seq (WP.mono (WP.keep [.s1] (Q := fun v => v.gpr .s1 = BitVec.ofNat 64 d ∧ v.mem = s.mem) ?_
    (by rfl) (by rfl)) fun v ⟨⟨v1, vm⟩, kv⟩ => ?_)
  · brun [exec_li (show imm12 (d : Int) by unfold imm12; omega)]
    exact BitVec.ofInt_natCast 64 d
  refine WP.seq (WP.mono (smallMod_ok (hs.congr kv.2.2) ((kv.gpr (by decide)).trans h7)
    ((kv.gpr (by decide)).trans ht0) v1 hw1 hw hZ ho hd2 (by omega)) fun t' ⟨⟨t0, tm'⟩, kt'⟩ => ?_)
  rw [vm, hx] at t0
  have k := kv.trans kt'
  have e4 : t'.gpr .a4 = s.gpr .a4 := k.gpr (by decide)
  refine WP.mono (WP.keep [.t2, .a4] (Q := fun t => t.gpr .a4 = t'.gpr .a4 |||
      (if BitVec.ofNat 64 (x % d) < BitVec.ofInt 64 1 then (1 : BitVec 64) else 0) ∧ t.mem = t'.mem)
      (by brun [t0, exec_li (show imm12 1 by decide)]) (by rfl) (by rfl))
    fun t ⟨⟨t4, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm, tm', vm]⟩, (k.trans kt).mono (by decide)⟩
  rw [t4, BitVec.or_eq_zero_iff, e4, h4, flag_eq (by have := Nat.mod_lt x (show 0 < d by omega); omega)]

theorem trials_ok {B : Addr} {Z o w x : Nat} (hw1 : 1 ≤ w) (hw : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 8 = 0)
    (hZ8 : 208 ≤ Z) :
    ∀ (ds : List Nat), (∀ d ∈ ds, 2 ≤ d ∧ d < 2 ^ 11) → ∀ {u : State} {P : Prop}, Scr u B Z →
      u.gpr .s6 = B → u.gpr .a7 = off B o → u.gpr .t0 = BitVec.ofNat 64 w → wv u.mem B o w = x →
      (u.gpr .a4 = 0#64 ↔ P) →
      WP isa (ds.foldr (fun d c => .seq (trial d) c) (.block [sth .a4 hBad])) u fun t =>
        ((word t.mem B (8 * hBad) = 0#64 ↔ P ∧ ∀ d ∈ ds, x % d ≠ 0) ∧ Frm B [(8 * hBad, 8)] u.mem t.mem) ∧
          Keep trRegs u t
  | [], _, u, P, hu, u6, _, _, _, h4 => by
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = u.mem.writeW (B + BitVec.ofNat 64 200) (u.gpr .a4)) ?_
      (by rfl) (by rfl)) fun t ⟨tm, kt⟩ => ⟨bad_post tm ?_, kt.mono (by decide)⟩
    · simp only [List.foldr_nil, sth, hBad]
      brun [u6, hu.st (d := 200) (n := 8) (by omega), hu.al8 (d := 200) (by omega) (by decide)]
    · simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true]; exact h4
  | d :: ds, hds, u, P, hu, u6, u7, ut0, ux, h4 => by
    have hd := hds d List.mem_cons_self
    refine WP.seq (WP.mono (trial_ok hu u7 ut0 ux hw1 hw hZ ho hd.1 hd.2 h4) fun t' ⟨⟨t4, tm'⟩, kt'⟩ => ?_)
    refine WP.mono (trials_ok (x := x) hw1 hw hZ ho hZ8 ds (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
      (hu.congr kt'.2.2) ((kt'.gpr (by decide)).trans u6) ((kt'.gpr (by decide)).trans u7)
      ((kt'.gpr (by decide)).trans ut0) (by rw [tm']; exact ux) t4)
      fun t ⟨⟨tb, tf⟩, kt⟩ => ⟨⟨?_, by rw [← tm']; exact tf⟩, (kt'.trans kt).mono (by decide)⟩
    rw [tb, List.forall_mem_cons]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

theorem oddPrimes256_bounds : ∀ d ∈ oddPrimes256, 2 ≤ d ∧ d < 2 ^ 11 := by decide

theorem sieve_ok {s : State} {B : Addr} {Z o w x : Nat} (ds : List Nat) (hds : ∀ d ∈ ds, 2 ≤ d ∧ d < 2 ^ 11)
    (hs : Scr s B Z) (h6 : s.gpr .s6 = B) (h7 : s.gpr .a7 = off B o)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hx : wv s.mem B o w = x) (hw1 : 1 ≤ w)
    (hw : w < 2 ^ 31) (hZ : o + 8 * w ≤ Z) (ho : o % 8 = 0) (hZ8 : 208 ≤ Z) :
    WP isa (sieve ds) s fun t =>
      ((word t.mem B (8 * hBad) = 0#64 ↔ word s.mem B (8 * hBad) = 0#64 ∧ ∀ d ∈ ds, x % d ≠ 0) ∧
        Frm B [(8 * hBad, 8)] s.mem t.mem) ∧ Keep trRegs s t := by
  unfold sieve
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = word s.mem B (8 * hBad) ∧ u.mem = s.mem)
    (by simp only [ldh, hBad, word, VG.Proof.Bignum.off]
        brun [h6, hs.ld (d := 200) (n := 8) (by omega), hs.al8 (d := 200) (by omega) (by decide)]) (by rfl) (by rfl))
    fun u ⟨⟨u4, um⟩, ku⟩ => ?_)
  refine WP.mono (trials_ok hw1 hw hZ ho hZ8 ds hds (hs.congr ku.2.2) ((ku.gpr (by decide)).trans h6)
    ((ku.gpr (by decide)).trans h7) ((ku.gpr (by decide)).trans ht0) (by rw [um]; exact hx)
    (P := word s.mem B (8 * hBad) = 0#64) (by rw [u4])) fun t ⟨⟨tb, tf⟩, kt⟩ =>
      ⟨⟨tb, by rw [← um]; exact tf⟩, (ku.trans kt).mono (by decide)⟩

end

/-! ## `R² mod N` and `−N⁻¹` by doublings -/

section

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.Ffdh.RISCV64.Search
open VG.Proof.Bignum.RISCV64
open VG.Proof.MillerRabin.RISCV64 (Env A MCtx expSetup_ok prepRegs copy_ok copyRegs slot_lt)
open VG.Proof.MillerRabin.RISCV64.Search
open VG.Proof.Bignum (slot Arrays)
open VG.Proof.RsaKeyGen (mrE mrA)
open VG.Impl.Bignum.RISCV64.PublicChecked (base montOp)

/-- `r2Any`: `x := 2^(128 w) mod N` in array 1 by `128 w` doublings of 1,
and `t1 := −N⁻¹ mod 2⁶⁴`: for any odd `N ≥ 3` in array 0. -/
theorem r2Any_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w ≤ 128) (hZ : slot w 8 ≤ Z)
    (hN3 : 3 ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa r2Any s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
        ((word s.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0) ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep r2Regs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hlow : (word s.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [fios_wordsVal_pred _ _ _ (show 1 ≤ w by omega)] at hodd
    omega
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN3 hodd ⊢
  unfold r2Any
  -- `x := 1`.
  have hb3 : WP isa (.block [.addi .t3 .a2 0]) s fun t =>
      (t.gpr .t3 = off B (slot w 1) ∧ t.mem = s.mem) ∧ Keep [.t3] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h2, BitVec.add_zero]
  refine WP.seq (WP.mono hb3 fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans ht0) (by omega) (by omega)
    (slot_al8 w 1) (by omega)) fun s₂ ⟨⟨_, z2, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hs₂ := hs.congr k12.2.2
  have hst : WP isa (.block [.li .s0 1, .store .d .s0 .a2 0, .shift .sll .d .a1 .t0 7]) s₂ fun t =>
      (t.mem = s₂.mem.writeW (off B (slot w 1)) (1 : BitVec 64) ∧ t.gpr .a1 = BitVec.ofNat 64 (128 * w)) ∧ Keep [.s0, .a1] s₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [exec_li (show imm12 1 by decide), (k12.gpr (by decide)).trans h2, (k12.gpr (by decide)).trans ht0,
      hs₂.st (show slot w 1 + 8 ≤ Z by omega), hs₂.al8 (show slot w 1 + 8 ≤ Z by omega) (slot_al8 w 1),
      BitVec.add_zero]
    refine ⟨rfl, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine WP.seq (WP.mono hst fun s₃ ⟨⟨m3, a1⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have hw1 : Outside B (slot w 1) 8 s₂.mem s₃.mem := by rw [m3]; exact writeW_outside _ _ _ (by omega)
  have o13 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₃.mem := by
    rw [← m1]; exact (o2.mono (o' := slot w 1) (n' := 24 * (w + 2)) (Nat.le_refl _) (by omega)).trans
      (hw1.mono (o' := slot w 1) (n' := 24 * (w + 2)) (Nat.le_refl _) (by omega))
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal o13 (by omega) (by omega), hNd]
  have w3 : word s₃.mem B (slot w 0) = word s.mem B (slot w 0) := Outside.word o13 (by omega) (by omega)
  have x3 : wordsVal s₃.mem B (slot w 1) w = 2 ^ 0 % N := by
    rw [Nat.pow_zero, Nat.mod_eq_of_lt (by omega), fios_wordsVal_pred _ _ _ (show 1 ≤ w by omega), m3,
      word_writeW_self, Outside.wordsVal (writeW_outside s₂.mem B (d := slot w 1) (1 : BitVec 64) (by omega))
        (d := slot w 1 + 8) (k := w - 1) (Or.inr (Nat.le_refl _)) (by omega)]
    have hz : wordsVal s₂.mem B (slot w 1 + 8) (w - 1) = 0 := by
      refine Pub.wsv_zero fun i hi => ?_
      rw [show slot w 1 + 8 + 8 * i = slot w 1 + 8 * (i + 1) by omega]; exact z2 (i + 1) (by omega)
    rw [hz]; rfl
  -- The doublings.
  have hs₃ := hs.congr k13.2.2
  refine WP.seq (WP.mono (r2Dbl_ok hs₃ ((k13.gpr (by decide)).trans h5) ((k13.gpr (by decide)).trans h6)
    ((k13.gpr (by decide)).trans h7) ((k13.gpr (by decide)).trans h2) ((k13.gpr (by decide)).trans ht0) (by omega)
    (by omega) (by omega) n3 (by omega) x3 a1 (by omega) (by omega)) fun s₄ ⟨x4, o4, k4⟩ => ?_)
  have k14 := k13.trans k4
  have o14 := o13.trans o4
  have w4 : word s₄.mem B (slot w 0) = word s.mem B (slot w 0) := Outside.word o14 (by omega) (by omega)
  -- `−N⁻¹`.
  refine WP.mono (minv_ok (hs.congr k14.2.2) ((k14.gpr (by decide)).trans h7) (slot_al8 w 0) (by omega)
    (by rw [w4]; exact hlow)) fun t ⟨⟨it, mt⟩, kt⟩ => ⟨⟨?_, by rw [← w4]; exact it⟩, by rw [mt]; exact o14,
      (k14.trans kt).mono (by decide)⟩
  rw [mt, x4, Nat.zero_add]

theorem r2Any_r2Ok : R2Ok r2Any fun _ _ => True := by
  intro s B Z w N h h2 h5 h6 hN hodd hN3 _
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ := h.hZ
  have hw := h.hw
  refine WP.mono (r2Any_ok h.hs h2 h5 h6 h.a7 h.t0 (by omega) h.hw' (by simp only [es] at hZ ⊢; omega)
    (by rw [show wordsVal s.mem B (slot w 0) w = A s.mem B w 0 from rfl, hN]; exact hN3)
    (by rw [show wordsVal s.mem B (slot w 0) w = A s.mem B w 0 from rfl, hN]; exact hodd))
    fun t ⟨⟨r, i⟩, o, k⟩ => ⟨⟨by rw [A, r, show wordsVal s.mem B (slot w 0) w = A s.mem B w 0 from rfl, hN], i⟩, o, k⟩

theorem montPrep_ok {s : State} {B : Addr} {Z w N : Nat} (h : Env s B Z w) (hn : A s.mem B w 0 = N)
    (hodd : N % 2 = 1) (hN3 : 3 ≤ N) :
    WP isa montPrep s fun t =>
      (Env t B Z w ∧ A t.mem B w 0 = N ∧
        ((word t.mem B (slot w 0)).toNat * (word t.mem B 56).toNat + 1) % 2 ^ 64 = 0 ∧
        ((word t.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
        A t.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧ A t.mem B w 9 = 2 ^ (64 * w) % N ∧
        A t.mem B w 10 = N - 2 ^ (64 * w) % N ∧ A t.mem B w aE = mrE N ∧
        t.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA N % 64) ∧
        Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t :=
  montPrepWith_ok r2Any_r2Ok h hn hodd hN3 trivial

end

/-! ## The round's call in constant time -/

section

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64 VG.Impl.MillerRabin.RISCV64.Search
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

theorem pins_RC : Pins RC [.a7, .s5, .t0, .s6] := by
  rintro d s₁ s₂ ⟨h₁, -⟩ ⟨h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.env.a7, h₂.env.a7]
  · rw [h₁.env.s5, h₂.env.s5]
  · rw [h₁.env.t0, h₂.env.t0]
  · rw [h₁.env.s6, h₂.env.s6]

theorem rcPre_ct : RelCT isa (Two RC)
    (.seq (PublicChecked.montOp 5 4 1) (.block [.addi .a0 .s6 0, ldh .a1 hWsLen])) (Two RCm) :=
  two_post (two_taint _ pins_RC (by taint_decide)) fun _ _ h => rcPre_ok h

theorem rc_pub {d : RcD} {s₁ s₂ : State} (h₁ : RCm d s₁) (h₂ : RCm d s₂) (hsp : s₁.sp = s₂.sp) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pub
      (s₁.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) (s₂.callEntry.withRegions [] [⟨d.B, 8 * d.L⟩]) := by
  have e96 : (96 : Nat) = 95 + 1 := rfl
  rw [e96]
  sig_reduce [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, RISCV64.abi,
    RISCV64.argRegs]
  obtain ⟨p₁, -, a0₁, a1₁, -⟩ := h₁
  obtain ⟨p₂, -, a0₂, a1₂, -⟩ := h₂
  rw [a0₁, a1₁, a0₂, a1₂, p₁.width, p₂.width]
  exact ⟨⟨hsp, rfl⟩, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- After the call: the working space's address. -/
def RCc (d : RcD) (s : State) : Prop := s.gpr .s6 = d.B

theorem rcCall_ct (R : RoundImpl) : RelCT isa (Two RCm) (.call R.name R.code) (Two RCc) := by
  refine two_post ?_ fun d s h => ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨d, h₁, h₂, hsp⟩ := hp
    exact RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) R.verified.1 R.verified.2.1 [] [⟨d.B, 8 * d.L⟩]
      (fun a b ⟨ha, hb⟩ => by
        subst ha hb
        exact ⟨rcm_pre h₁, rcm_pre h₂, rc_pub h₁ h₂ hsp, scr_covers' h₁.1.env.hs, fun _ _ => scr_covers h₁.1.env.hs,
          scr_covers' h₂.1.env.hs, fun _ _ => scr_covers h₂.1.env.hs⟩)
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · have h6 := h.1.env.s6
    exact WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96)
      R.verified.1 (rd := []) (wr := [⟨d.B, 8 * d.L⟩]) (rcm_pre h) (scr_covers' h.1.env.hs)
      (fun _ _ => scr_covers h.1.env.hs)
      (fun s' _ _ _ _ hcs _ => (hcs .s6 (by decide)).trans h6) (by have := R.stack; omega_arith)

theorem pins_RCc : Pins RCc [.s6] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁, h₂]

/-- The round's call leaks the same from the same working space and witness. -/
theorem roundCall_ct (R : RoundImpl) : RelCT isa (Two RC) (roundCall R.name R.code) fun _ _ => True := by
  unfold roundCall
  refine RelCT.assoc (RelCT.seq rcPre_ct (RelCT.seq (rcCall_ct R) ?_))
  exact two_taint _ pins_RCc (by taint_decide)

end

end VG.Proof.Ffdh.RISCV64.Search
