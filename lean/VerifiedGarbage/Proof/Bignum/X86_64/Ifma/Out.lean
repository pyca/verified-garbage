module
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Block

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Core
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication's result

After the loop and the steps of the last, partial block, `ammCore` stores the `R`
accumulators of each prime at `r11` (and `r11 + D`), then carries the `4 R`
limbs of each in order (`carryOut`), the two chains interleaved
(`ammCore_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside ofs_off writeW_outside word_writeW_self)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique Upd ex_add_mem ex_mov ex_and
  ex_shr ex_store add_ofNat' shr_ofNat wrList_outside Keeps)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem AmmOk.D_bounds (hl : AmmOk l) : l.NB ≤ l.D ∧ l.D + l.NB ≤ 2 ^ 20 := by
  rcases hl with (rfl | rfl | rfl) | rfl | rfl | rfl <;> decide

theorem LayOk.D_bounds (hl : LayOk l) : l.NB ≤ l.D ∧ l.D + l.NB ≤ 2 ^ 20 := hl.amm.D_bounds

/-- At most two lanes, whose carries are `rdx` and `rsi`. -/
theorem AmmOk.nl_le (hl : AmmOk l) : 1 ≤ l.nl ∧ l.nl ≤ 2 := by
  rcases hl with (rfl | rfl | rfl) | rfl | rfl | rfl <;> decide

theorem off_ltN (hl : AmmOk l) {j : Nat} (hj : j < l.L) : l.off j + 8 ≤ l.NB := by
  obtain ⟨hR, _⟩ := hl.bounds
  have h1 := Nat.mod_lt j (show 0 < l.R by omega)
  have h2 : j / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hj; rw [Nat.mul_comm]; exact hj)
  unfold Lay.off Lay.NB; omega

theorem off_lt (hl : LayOk l) {j : Nat} (hj : j < l.L) : l.off j + 8 ≤ l.NB := off_ltN hl.amm hj

theorem off_sepN (hl : AmmOk l) {j q : Nat} (hj : j < l.L) (hq : q < l.L) (h : q ≠ j) :
    l.off q + 8 ≤ l.off j ∨ l.off j + 8 ≤ l.off q := by
  obtain ⟨hR, _⟩ := hl.bounds
  have h1 := Nat.mod_lt j (show 0 < l.R by omega)
  have h2 : j / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hj; rw [Nat.mul_comm]; exact hj)
  have h3 := Nat.mod_lt q (show 0 < l.R by omega)
  have h4 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
  unfold Lay.off
  by_cases e : q % l.R = j % l.R
  · have e' : q / l.R ≠ j / l.R := fun e' => h (by rw [← Nat.div_add_mod q l.R, ← Nat.div_add_mod j l.R, e, e'])
    omega
  · omega

theorem off_sep (hl : LayOk l) {j q : Nat} (hj : j < l.L) (hq : q < l.L) (h : q ≠ j) :
    l.off q + 8 ≤ l.off j ∨ l.off j + 8 ≤ l.off q := off_sepN hl.amm hj hq h

theorem carryIn_lt63 {L : Nat → Nat} {n : Nat} (h : ∀ j < n, L j < 2 ^ 63) : carryIn L n < 2 ^ 12 := by
  induction n with
  | zero => simp only [carryIn]; decide
  | succ n ih =>
    have := ih fun j hj => h j (by omega)
    have := h n (by omega)
    simp only [carryIn]
    exact Nat.div_lt_of_lt_mul (by omega)

theorem and_mask {y : Nat} (hy : y < 2 ^ 64) : BitVec.ofNat 64 y &&& mask52 = BitVec.ofNat 64 (y % 2 ^ 52) :=
  AmmSym.and_mask hy

theorem eaG {s : State} {B : Addr} {b : Reg} (h : s.gpr b = B) (d : Nat) : s.ea (at_ b d) = off B d := by
  simp only [State.ea, at_, h, off]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-! ## The stores -/

/-- 32-byte stores of registers at `b` plus offsets. -/
def storeCode (b : Reg) (xs : List (Nat × VReg)) : List Instr :=
  xs.map fun x => .evStore (at_ b x.1) x.2

theorem stores_gen {B : Addr} {b : Reg} :
    ∀ (xs : List (Nat × VReg)) (s : State), s.gpr b = B →
      (∀ x ∈ xs, InRegions s.wr (off B x.1) 32) →
      WP isa (.block (storeCode b xs)) s fun s' => s' = { s with mem := wrList s.mem B (xs.map fun x => (x.1, s.vy x.2)) }
  | [], s, _, _ => WP.block_nil rfl
  | (e, r) :: rest, s, hB, hw => by
    rw [storeCode, List.map_cons, WP.block_cons_iff]
    refine ⟨{ s with mem := s.mem.writeW (off B e) (s.vy r) }, ?_, ?_⟩
    · simp only [exec, eaG hB, State.store256, hw (e, r) (List.mem_cons_self ..), ite_true]
    · refine WP.mono (stores_gen rest _ hB fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => ?_
      rw [h]
      rfl

/-- The accumulators' stores of `ammCore`. -/
def accStores (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Nat × VReg) :=
  (List.range l.nl).flatMap fun p => (List.range l.R).map fun k => (l.D * p + 32 * k, acc l p k (l.S % l.R))

theorem accStores_code :
    ((List.range l.nl).flatMap fun p => (List.range l.R).map fun k =>
      (Instr.evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k (l.S % l.R)))) = storeCode .r11 (accStores l) := by
  simp only [storeCode, accStores, List.map_flatMap, List.map_map, Function.comp_def]

theorem mem_accStores {x : Nat × VReg} (hx : x ∈ accStores l) :
    ∃ p < l.nl, ∃ k < l.R, x = (l.D * p + 32 * k, acc l p k (l.S % l.R)) := by
  simp only [accStores, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨p, hp, k, hk, rfl⟩ := hx
  exact ⟨p, hp, k, hk, rfl⟩

theorem accStores_win :
    ∀ x ∈ accStores l, ∃ p < l.nl, l.D * p + 0 ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + 0 + l.NB := by
  intro x hx
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_accStores hx
  exact ⟨p, hp, by omega, by simp only [Lay.NB]; omega⟩

/-- Lane `p` within the lanes' regions. -/
theorem D_lane {p : Nat} (hp : p < l.nl) : l.D * p ≤ l.D * (l.nl - 1) := Nat.mul_le_mul_left _ (by omega)

theorem accStores_lt : ∀ x ∈ accStores l, x.1 + 32 ≤ l.D * (l.nl - 1) + l.NB := by
  intro x hx
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_accStores hx
  have := D_lane (l := l) hp
  simp only [Lay.NB]; omega

/-- Each lane's region starts within `D` of the first. -/
theorem D_le (hl : AmmOk l) {p : Nat} (hp : p < l.nl) : l.D * p ≤ l.D :=
  Nat.le_trans (Nat.mul_le_mul_left _ (show p ≤ 1 by have := hl.nl_le; omega)) (Nat.le_of_eq (Nat.mul_one _))

/-- Two lanes' regions, `D ≥ NB` apart. -/
theorem lane_sep (hl : AmmOk l) {p p' : Nat} (hp : p < l.nl) (hp' : p' < l.nl) (h : p ≠ p') :
    l.D * p + l.NB ≤ l.D * p' ∨ l.D * p' + l.NB ≤ l.D * p := by
  have hD := hl.D_bounds
  have hn := hl.nl_le
  rcases (by omega : (p = 0 ∧ p' = 1) ∨ (p = 1 ∧ p' = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

/-- The word of limb `k + R t` of lane `p` after the stores. -/
theorem read_stores (hl : AmmOk l) (m : Mem) (B : Addr) (s : State) {p k t : Nat} (hp : p < l.nl) (hk : k < l.R)
    (ht : t < 4) :
    word (wrList m B ((accStores l).map fun x => (x.1, s.vy x.2))) B (l.D * p + 32 * k + 8 * t) =
      qv s (vreg (regOf l p k (l.S % l.R))) t := by
  have hD := hl.D_bounds
  simp only [Lay.NB] at hD
  have hD1 : ∀ {q}, q < l.nl → l.D * q ≤ l.D := fun hq => D_le hl hq
  have hp' := hD1 hp
  refine word_wrList_unique B ht (by omega) _ m ?_ (fun x hx => ?_) (fun x hx he => ?_)
  · simp only [List.mem_map]
    exact ⟨_, List.mem_flatMap.2 ⟨p, List.mem_range.2 hp, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩, rfl⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp'', k', hk', rfl⟩ := mem_accStores hy
    have := hD1 hp''
    simp only
    by_cases e : p' = p
    · subst e; omega
    · have := lane_sep hl hp hp'' (Ne.symm e)
      simp only [Lay.NB] at this
      omega
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp'', k', hk', rfl⟩ := mem_accStores hy
    have : p' = p ∧ k' = k := by
      by_cases e : p' = p
      · subst e; simp only at he; omega
      · have := lane_sep hl hp hp'' (Ne.symm e)
        simp only [Lay.NB] at this
        simp only at he; omega
    obtain ⟨rfl, rfl⟩ := this
    rfl

/-! ## Frames of both regions -/

/-- `m'` agrees with `m` but on the bytes at offsets `[D p + o, D p + o + n)` of `B`, for `p < 2`. -/
def Out2 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ p < 2, ofs B x < l.D * p + o ∨ l.D * p + o + n ≤ ofs B x) → m' x = m x

theorem Out2.refl (B : Addr) (o n : Nat) (m : Mem) : Out2 l B o n m m := fun _ _ => rfl

theorem Out2.trans {B : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Out2 l B o n m₁ m₂) (h₂ : Out2 l B o n m₂ m₃) :
    Out2 l B o n m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Out2.of_outside {B : Addr} {o n p : Nat} {m m' : Mem} (hp : p < 2)
    (h : Outside B (l.D * p + o) n m m') : Out2 l B o n m m' := fun x hx => h x (hx p hp)

/-- Writes of 32 bytes within the windows. -/
theorem wrList_out2 (B : Addr) {o n : Nat} (hn : l.D + o + n ≤ 2 ^ 63) :
    ∀ (xs : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ xs, ∃ p < 2, l.D * p + o ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + o + n) →
      Out2 l B o n m (wrList m B xs)
  | [], m, _ => Out2.refl B o n m
  | (e, v) :: rest, m, h => by
    obtain ⟨p, hp, h1, h2⟩ := h (e, v) (List.mem_cons_self ..)
    have hDp : l.D * p ≤ l.D := by rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
    exact (Out2.of_outside hp ((writeW256_outside m B v (by omega)).mono h1 (by omega))).trans
      (wrList_out2 B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `m'` agrees with `m` but on the bytes at offsets `[D p + o, D p + o + n)` of `B`, for each lane. -/
def OutN (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ p < l.nl, ofs B x < l.D * p + o ∨ l.D * p + o + n ≤ ofs B x) → m' x = m x

theorem OutN.refl (B : Addr) (o n : Nat) (m : Mem) : OutN l B o n m m := fun _ _ => rfl

theorem OutN.trans {B : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : OutN l B o n m₁ m₂) (h₂ : OutN l B o n m₂ m₃) :
    OutN l B o n m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem OutN.of_outside {B : Addr} {o n p : Nat} {m m' : Mem} (hp : p < l.nl)
    (h : Outside B (l.D * p + o) n m m') : OutN l B o n m m' := fun x hx => h x (hx p hp)

/-- With two lanes, `Out2`. -/
theorem OutN.out2 (hn : l.nl = 2) {B : Addr} {o n : Nat} {m m' : Mem} (h : OutN l B o n m m') :
    Out2 l B o n m m' := fun x hx => h x fun p hp => hx p (by omega)

/-- Writes of 32 bytes within the lanes' windows. -/
theorem wrList_outN (B : Addr) {o n : Nat} (hn : l.D * (l.nl - 1) + o + n ≤ 2 ^ 63) :
    ∀ (xs : List (Nat × BitVec 256)) (m : Mem),
      (∀ x ∈ xs, ∃ p < l.nl, l.D * p + o ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + o + n) →
      OutN l B o n m (wrList m B xs)
  | [], m, _ => OutN.refl B o n m
  | (e, v) :: rest, m, h => by
    obtain ⟨p, hp, h1, h2⟩ := h (e, v) (List.mem_cons_self ..)
    have hDp := D_lane (l := l) hp
    exact (OutN.of_outside hp ((writeW256_outside m B v (by omega)).mono h1 (by omega))).trans
      (wrList_outN B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## The carries -/

/-- After limb `j` of the lanes below `p` (and every limb below `j`), from
the stored limbs `L p`. -/
structure CarryN (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (L : Nat → Nat → Nat) (m₀ : Mem) (s : State)
    (j p : Nat) : Prop where
  r11 : s.gpr .r11 = B
  r12 : s.gpr .r12 = mask52
  c : ∀ p' < l.nl, s.gpr (cReg p') = BitVec.ofNat 64 (carryIn (L p') (if p' < p then j + 1 else j))
  words : ∀ p' < l.nl, ∀ q < l.L, word s.mem B (l.D * p' + l.off q) =
    BitVec.ofNat 64 (if q < j ∨ (q = j ∧ p' < p) then carried (L p') q else L p' q)
  frame : OutN l B 0 l.NB m₀ s.mem

/-- The lanes' carries and temporaries are four distinct registers. -/
theorem cReg_cases (p : Nat) : (cReg p = .rdx ∧ cTmp p = .rax) ∨ (cReg p = .rsi ∧ cTmp p = .rcx) := by
  unfold cReg cTmp; split <;> simp

theorem cReg_inj (hl : AmmOk l) {p p' : Nat} (hp : p < l.nl) (hp' : p' < l.nl) (h : p' ≠ p) :
    cReg p' ≠ cReg p := by
  have := hl.nl_le
  rcases (by omega : (p = 0 ∧ p' = 1) ∨ (p = 1 ∧ p' = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem cTmp_ne (p p' : Nat) : cReg p' ≠ cTmp p := by
  rcases cReg_cases p with ⟨_, h⟩ | ⟨_, h⟩ <;> rcases cReg_cases p' with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h, h'] <;> decide

/-- Limb `j` of lane `p`'s chain. -/
theorem laneStep_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j p : Nat}
    (hj : j < l.L) (hp : p < l.nl) (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63)
    (hw : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8)
    (h : CarryN l B L m₀ s j p) :
    WP isa (.block (carryStep l j p)) s fun s' => CarryN l B L m₀ s' j (p + 1) ∧
      (∀ r, r ≠ cTmp p → r ≠ cReg p → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  have hDp := D_lane (l := l) hp
  have hDl := D_le hl hp
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by have := hl.nl_le; omega)
  have ho := off_ltN hl hj
  have c0 := carryIn_lt63 (L := L p) (n := j) fun q hq => hL p hp q (by omega)
  have l0 := hL p hp j hj
  have w0 : s.mem.readW (off B (l.D * p + l.off j)) 64 = BitVec.ofNat 64 (L p j) := by
    have := h.words p hp j hj
    rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have hc0 : s.gpr (cReg p) = BitVec.ofNat 64 (carryIn (L p) j) := by
    have := h.c p hp; rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have rin : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions (s.rd ++ s.wr) (off B d) 8 := fun d hd => by
    obtain ⟨r, hr, hc⟩ := hw d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨n1, n2, n3, n4, n5⟩ : cReg p ≠ cTmp p ∧ Reg.r11 ≠ cReg p ∧ Reg.r12 ≠ cReg p ∧ Reg.r11 ≠ cTmp p ∧
      Reg.r12 ≠ cTmp p := by
    rcases cReg_cases p with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  rw [carryStep, WP.block_cons_iff]
  obtain ⟨s1, e1, u1⟩ := ex_add_mem (s := s) (r := cReg p) (m := at_ .r11 (l.D * p + l.off j))
    (by rw [eaG h.r11]; exact rin _ (by omega))
  refine ⟨s1, e1, ?_⟩
  rw [eaG h.r11, hc0, w0, add_ofNat' (by omega)] at u1
  rw [WP.block_cons_iff]
  obtain ⟨s2, e2, u2⟩ := ex_mov (s := s1) (d := cTmp p) (r := cReg p)
  refine ⟨s2, e2, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s3, e3, u3⟩ := ex_and (s := s2) (d := cTmp p) (r := .r12)
  refine ⟨s3, e3, ?_⟩
  rw [u2.self, u2.other _ n5, u1.self, u1.other _ n3, h.r12, and_mask (by omega)] at u3
  rw [WP.block_cons_iff]
  have r11₃ : s3.gpr .r11 = B := by rw [u3.other _ n4, u2.other _ n4, u1.other _ n2, h.r11]
  obtain ⟨s4, e4, m4, g4, rd4, wr4, x4⟩ := ex_store (s := s3) (r := cTmp p) (m := at_ .r11 (l.D * p + l.off j))
    (by rw [eaG r11₃, u3.wr, u2.wr, u1.wr]; exact hw _ (by omega))
  refine ⟨s4, e4, ?_⟩
  rw [eaG r11₃, u3.self] at m4
  rw [WP.block_cons_iff]
  obtain ⟨s5, e5, u5⟩ := ex_shr (s := s4) (d := cReg p)
  refine ⟨s5, e5, ?_⟩
  rw [congrFun g4, u3.other _ n1, u2.other _ n1, u1.self, shr_ofNat (by omega)] at u5
  have mem₅ : s5.mem = s.mem.writeW (off B (l.D * p + l.off j))
      (BitVec.ofNat 64 ((carryIn (L p) j + L p j) % 2 ^ 52)) := by
    rw [u5.mem, m4, u3.mem, u2.mem, u1.mem]
  have g5 : ∀ r, r ≠ cTmp p → r ≠ cReg p → s5.gpr r = s.gpr r := fun r a b => by
    rw [u5.other _ b, congrFun g4, u3.other _ a, u2.other _ a, u1.other _ b]
  refine WP.block_nil ⟨⟨by rw [g5 _ n4 n2, h.r11], by rw [g5 _ n5 n3, h.r12], fun p' hp' => ?_, fun p' hp' q hq => ?_, ?_⟩,
    g5, by rw [u5.rd, rd4, u3.rd, u2.rd, u1.rd], by rw [u5.wr, wr4, u3.wr, u2.wr, u1.wr],
    by rw [u5.mxcsr, x4, u3.mxcsr, u2.mxcsr, u1.mxcsr]⟩
  · by_cases e : p' = p
    · subst e
      rw [u5.self]
      simp only [Nat.lt_succ_self, ↓reduceIte, carryIn]; rw [Nat.add_comm]
    · rw [g5 _ (cTmp_ne p p') (cReg_inj hl hp hp' e), h.c p' hp']
      rcases Nat.lt_or_ge p' p with e' | e'
      · simp only [e', show p' < p + 1 by omega, ↓reduceIte]
      · simp only [show ¬ p' < p by omega, show ¬ p' < p + 1 by omega, ↓reduceIte]
  · have hoq := off_ltN hl hq
    have hDp' := D_lane (l := l) hp'
    have hDl' := D_le hl hp'
    rw [mem₅]
    by_cases e : p' = p ∧ q = j
    · obtain ⟨rfl, rfl⟩ := e
      rw [word_writeW_self]
      simp only [Nat.lt_irrefl, Nat.lt_succ_self, and_self, or_true, ↓reduceIte, carried]; rw [Nat.add_comm]
    · have hsep : l.D * p' + l.off q + 8 ≤ l.D * p + l.off j ∨ l.D * p + l.off j + 8 ≤ l.D * p' + l.off q := by
        by_cases e' : p' = p
        · subst e'
          have := off_sepN hl hj hq (fun h => e ⟨rfl, h⟩)
          omega
        · have := lane_sep hl hp hp' (Ne.symm e')
          omega
      rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega), h.words p' hp' q hq]
      by_cases c : q < j ∨ (q = j ∧ p' < p)
      · simp only [c, show q < j ∨ (q = j ∧ p' < p + 1) by omega, ↓reduceIte]
      · simp only [c, show ¬ (q < j ∨ (q = j ∧ p' < p + 1)) by omega, ↓reduceIte]
  · rw [mem₅]
    exact h.frame.trans (OutN.of_outside hp ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)))

/-- Limb `j` of the lanes from `p`. -/
theorem lanes_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {j : Nat} (hj : j < l.L)
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63) :
    ∀ n p (s : State), p + n = l.nl → (∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8) →
      CarryN l B L m₀ s j p →
      WP isa (.block ((List.range' p n).flatMap (carryStep l j))) s fun s' => CarryN l B L m₀ s' j l.nl ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, p, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, p, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (laneStep_ok hl hj (by omega) hL hw h) fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (lanes_ok hl hj hL n (p + 1) s₁ (by omega) (fun d hd => wr₁ ▸ hw d hd) h₁)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r ?_ ?_),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)
    · rcases cReg_cases p with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> with_reducible assumption
    · rcases cReg_cases p with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> with_reducible assumption

/-- Limb `j` of every lane. -/
theorem lanesAll_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {j : Nat} (hj : j < l.L)
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63) {s : State}
    (hw : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8) (h : CarryN l B L m₀ s j 0) :
    WP isa (.block ((List.range l.nl).flatMap (carryStep l j))) s fun s' => CarryN l B L m₀ s' j l.nl ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [List.range_eq_range']
  exact lanes_ok hl hj hL l.nl 0 s (Nat.zero_add _) hw h

/-- All lanes of limb `j` done: limb `j + 1` of none. -/
theorem CarryN.next {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j : Nat}
    (h : CarryN l B L m₀ s j l.nl) : CarryN l B L m₀ s (j + 1) 0 :=
  ⟨h.r11, h.r12, fun p' hp' => by rw [h.c p' hp']; simp only [hp', Nat.not_lt_zero, ↓reduceIte],
    fun p' hp' q hq => by
      rw [h.words p' hp' q hq]
      by_cases c : q < j + 1
      · simp only [show q < j ∨ (q = j ∧ p' < l.nl) by omega, show q < j + 1 ∨ (q = j + 1 ∧ p' < 0) by omega,
          ↓reduceIte]
      · simp only [show ¬ (q < j ∨ (q = j ∧ p' < l.nl)) by omega,
          show ¬ (q < j + 1 ∨ (q = j + 1 ∧ p' < 0)) by omega, ↓reduceIte], h.frame⟩

/-- The limbs from `j` on. -/
theorem limbs_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem}
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63) :
    ∀ n j (s : State), j + n = l.L → (∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8) →
      CarryN l B L m₀ s j 0 →
      WP isa (.block ((List.range' j n).flatMap fun j => (List.range l.nl).flatMap (carryStep l j))) s fun s' =>
        CarryN l B L m₀ s' l.L 0 ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, j, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, j, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (lanesAll_ok hl (by omega) hL hw h)
      fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (limbs_ok hl hL n (j + 1) s₁ (by omega) (fun d hd => wr₁ ▸ hw d hd) h₁.next)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r a b c d),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)

/-- The lanes' carries set to zero. -/
theorem zeroC_ok (hl : AmmOk l) (s : State) :
    WP isa (.block ((List.range l.nl).map fun p => Instr.mov32 (cReg p) (.imm 0))) s fun s' =>
      (∀ p < l.nl, s'.gpr (cReg p) = 0) ∧ (∀ r, r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have := hl.nl_le
  have c0 : cReg 0 = .rdx := rfl
  have c1 : cReg 1 = .rsi := rfl
  rcases (by omega : l.nl = 1 ∨ l.nl = 2) with hn | hn <;> rw [hn]
  · rw [List.range_one, List.map_singleton, WP.block_cons_iff, c0]
    refine ⟨_, rfl, WP.block_nil ⟨fun p hp => ?_, fun r a _ => ?_, rfl, rfl, rfl, rfl⟩⟩
    · obtain rfl : p = 0 := by omega
      dsimp only; rw [c0, State.setReg32, RegUpd.gpr_setReg_self]; rfl
    · dsimp only; rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ a]
  · rw [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_singleton, WP.block_cons_iff, c0, c1]
    refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, rfl, WP.block_nil ⟨fun p hp => ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
      · dsimp only
        rw [c0, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (by decide), State.setReg32, RegUpd.gpr_setReg_self]; rfl
      · dsimp only; rw [c1, State.setReg32, RegUpd.gpr_setReg_self]; rfl
    · dsimp only
      rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ b, State.setReg32, RegUpd.gpr_setReg_of_ne _ _ a]

/-- The carry pass, from the limbs `L p` stored. -/
theorem carryOut_ok (hl : AmmOk l) {B : Addr} {L : Nat → Nat → Nat} {s : State}
    (hL : ∀ p < l.nl, ∀ q < l.L, L p q < 2 ^ 63)
    (hw : ∀ d, d + 8 ≤ l.D * (l.nl - 1) + l.NB → InRegions s.wr (off B d) 8)
    (hr11 : s.gpr .r11 = B) (hr12 : s.gpr .r12 = mask52)
    (hwords : ∀ p < l.nl, ∀ q < l.L, word s.mem B (l.D * p + l.off q) = BitVec.ofNat 64 (L p q)) :
    WP isa (.block (carryOut l)) s fun s' => CarryN l B L s.mem s' l.L 0 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [carryOut, WP.block_append_iff, List.range_eq_range' (n := l.L)]
  refine WP.mono (zeroC_ok hl s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_
  refine WP.mono (limbs_ok hl hL (m₀ := s.mem) l.L 0 s₁ (Nat.zero_add _) (fun d hd => wr₁ ▸ hw d hd)
    ⟨by rw [g₁ _ (by decide) (by decide), hr11], by rw [g₁ _ (by decide) (by decide), hr12],
      fun p hp => by rw [c₁ p hp]; simp only [Nat.not_lt_zero, ↓reduceIte, carryIn]; rfl,
      fun p hp q hq => by
        rw [m₁, hwords p hp q hq]; simp only [Nat.not_lt_zero, and_false, or_self, ↓reduceIte],
      by rw [m₁]; exact OutN.refl _ _ _ _⟩) fun s' ⟨h, g, rd, wr, x⟩ =>
    ⟨h, fun r a b c d => (g r a b c d).trans (g₁ r c d), rd.trans rd₁, wr.trans wr₁, x.trans x₁⟩

/-! ## The whole multiplication -/

/-- `ammCore` from the operands `a` (at `r8`), `b` (at `r9`) and the modulus `m`
with `k` (at `rbx`), into limbs at `r11 = B`: each lane's limbs carried, and
its carry out. -/
theorem ammCore_ok (hl : AmmOk l) {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} (e : Env l (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B)
    (hs : Scr s B (l.D * (l.nl - 1) + l.NB)) :
    WP isa (ammCore l) s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (lm l a m k bl p l.S) q)) ∧
      (∀ p < l.nl, s'.gpr (cReg p) = BitVec.ofNat 64 (carryIn (lm l a m k bl p l.S) l.L)) ∧
      OutN l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  obtain ⟨_, hrg⟩ := hl.regs
  have hD := hl.D_bounds
  have hDn : l.D * (l.nl - 1) ≤ l.D := D_le hl (show l.nl - 1 < l.nl by have := hl.nl_le; omega)
  refine WP.seq ?_
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (zeros_ok hl (s := (s.setReg .r10 (s.gpr .rbx)).setReg32 .rcx (BitVec.ofNat 32 (l.S / l.R))))
    fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = (s.setReg .r10 (s.gpr .rbx)).gpr r := fun r a c => by
    rw [k₁.gpr r a]; exact RegUpd.gpr_setReg_of_ne _ _ c
  have i₁ : InBlk l (s.setReg .r10 (s.gpr .rbx)) s₁ a m k bl 0 0 :=
    ⟨fun p hp kk hk t ht => by
      rw [hz _ (by have := regOf_lt (k := kk) (i := 0) hp hR; omega) t ht]; rfl,
     fun t ht => hz _ (by simp only [zN]; omega) t ht, g₁ _ (by decide) (by decide),
     by rw [g₁ _ (by decide) (by decide), Nat.mul_zero, BitVec.add_zero], g₁ _ (by decide) (by decide),
     k₁.mem, k₁.rd, k₁.wr⟩
  have hst := hl.steps
  refine WP.seq (WP.mono (loop_ok hl e (l.S / l.R) s₁ hst.1 (Nat.le_refl _) (by rw [Nat.sub_self]; exact i₁)
      (by rw [k₁.gpr _ (by decide)]; rcases hl with (rfl | rfl | rfl) | rfl | rfl | rfl <;> rfl))
    fun s₂ₐ ⟨i₂ₐ, g₂ₐ, x₂ₐ⟩ => ?_)
  rw [accStores_code, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (steps_chain hl e (l.S % l.R) (by omega) (by omega) s₂ₐ i₂ₐ) fun s₂ ⟨i₂, g₂', x₂'⟩ => ?_
  have g₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s₂.gpr r = s₁.gpr r := fun r a c n =>
    (g₂' r a).trans (g₂ₐ r a c n)
  have x₂ : s₂.mxcsr = s₁.mxcsr := x₂'.trans x₂ₐ
  have hB₂ : s₂.gpr .r11 = B := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₂ : s₂.wr = s.wr := by rw [i₂.wr]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (stores_gen (accStores l) s₂ hB₂ fun x hx =>
    wr₂ ▸ (let ⟨_, h, c⟩ := hs.region (accStores_lt x hx) (by decide); ⟨_, h, c⟩)) fun s₃ h₃ => ?_
  subst h₃
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  have m₂ : s₂.mem = s.mem := i₂.mem
  refine WP.mono (carryOut_ok hl (B := B) (L := fun p => lm l a m k bl p l.S)
    (fun p _ q hq => lm_lt hR10 hst.2.2.2.1 hq)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₂]; exact hs.st hd)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₂)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp q hq => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have h1 := Nat.mod_lt q (show 0 < l.R by omega)
    have h2 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have := read_stores hl s₂.mem B s₂ hp (k := q % l.R) (t := q / l.R) h1 h2
    rw [i₂.lanes p hp _ h1 _ h2, Nat.mod_add_div, hst.2.2.2.2.1] at this
    rw [RegUpd.mem_setReg, show l.D * p + l.off q = l.D * p + 32 * (q % l.R) + 8 * (q / l.R) by
      unfold Lay.off; omega]
    exact this
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, true_or, ite_true],
    fun p hp => by rw [h.c p hp]; simp only [Nat.not_lt_zero, ↓reduceIte], ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_, by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _,
    by rw [rd, RegUpd.rd_setReg, i₂.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₂],
    by rw [x, RegUpd.mxcsr_setReg, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_outN (l := l) B (o := 0) (n := l.NB) (by omega)
      ((accStores l).map fun x => (x.1, s₂.vy x.2)) s₂.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact accStores_win y hy
    have hf : OutN l B 0 l.NB (wrList s₂.mem B ((accStores l).map fun x => (x.1, s₂.vy x.2))) s'.mem := h.frame
    have o' : OutN l B 0 l.NB s.mem (wrList s₂.mem B ((accStores l).map fun x => (x.1, s₂.vy x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₂ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₂ r r1 r2 r5, g₁ r r1 r2, RegUpd.gpr_setReg_of_ne _ _ r6]

/-- What `ammCore_ok` proves of `ammCore l`, of a code `c`. -/
def CoreOk (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (c : Prog isa) : Prop :=
  ∀ {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat},
    Env l (s.setReg .r10 (s.gpr .rbx)) a m k bl → s.gpr .r11 = B → Scr s B (l.D * (l.nl - 1) + l.NB) →
    WP isa c s fun s' =>
      (∀ p < l.nl, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (lm l a m k bl p l.S) q)) ∧
      (∀ p < l.nl, s'.gpr (cReg p) = BitVec.ofNat 64 (carryIn (lm l a m k bl p l.S) l.L)) ∧
      OutN l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.gpr .r12 = mask52 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr

theorem ammCore_core (hl : AmmOk l) : CoreOk l (ammCore l) := fun e hB hs => ammCore_ok hl e hB hs

end VG.Proof.Bignum.X86_64.Ifma
