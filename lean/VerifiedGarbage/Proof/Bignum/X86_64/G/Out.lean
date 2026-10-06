import VerifiedGarbage.Proof.Bignum.X86_64.G.Core
import VerifiedGarbage.Proof.Bignum.X86_64.AmmOut

/-!
# RSA with AVX512_IFMA on x86-64, any size: the multiplication's result

`AmmOut` for `CrtIfmaG`: after the loop, `ammCore` stores the `R`
accumulators of each prime at `r11` (and `r11 + D`), then carries the `4 R`
limbs of each in order (`carryOut`), the two chains interleaved
(`ammCore_ok`).
-/

namespace VG.Proof.Bignum.X86_64.G

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside ofs_off writeW_outside word_writeW_self)
open VG.Impl.Rsa.X86_64.CrtIfmaG
open VG.Proof.Bignum.X86_64.AmmSym (wrList writeW256_outside word_wrList_unique Upd ex_add_mem ex_mov ex_and
  ex_shr ex_store add_ofNat' shr_ofNat wrList_outside Keeps)

variable {l : Lay}

theorem LayOk.D_bounds (hl : LayOk l) : l.NB ≤ l.D ∧ l.D + l.NB ≤ 2 ^ 20 := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem off_lt (hl : LayOk l) {j : Nat} (hj : j < l.L) : l.off j + 8 ≤ l.NB := by
  obtain ⟨hR, _⟩ := hl.bounds
  have h1 := Nat.mod_lt j (show 0 < l.R by omega)
  have h2 : j / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hj; rw [Nat.mul_comm]; exact hj)
  unfold Lay.off Lay.NB; omega

theorem off_sep (hl : LayOk l) {j q : Nat} (hj : j < l.L) (hq : q < l.L) (h : q ≠ j) :
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

theorem carryIn_lt62 {L : Nat → Nat} {n : Nat} (h : ∀ j < n, L j < 2 ^ 62) : carryIn L n < 2 ^ 11 := by
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
def accStores (l : Lay) : List (Nat × VReg) :=
  (List.range 2).flatMap fun p => (List.range l.R).map fun k => (l.D * p + 32 * k, acc l p k 0)

theorem accStores_code :
    ((List.range 2).flatMap fun p => (List.range l.R).map fun k =>
      (Instr.evStore (at_ .r11 (l.D * p + 32 * k)) (acc l p k 0))) = storeCode .r11 (accStores l) := by
  simp only [storeCode, accStores, List.map_flatMap, List.map_map, Function.comp_def]

theorem mem_accStores {x : Nat × VReg} (hx : x ∈ accStores l) :
    ∃ p < 2, ∃ k < l.R, x = (l.D * p + 32 * k, acc l p k 0) := by
  simp only [accStores, List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨p, hp, k, hk, rfl⟩ := hx
  exact ⟨p, hp, k, hk, rfl⟩

theorem accStores_win :
    ∀ x ∈ accStores l, ∃ p < 2, l.D * p + 0 ≤ x.1 ∧ x.1 + 32 ≤ l.D * p + 0 + l.NB := by
  intro x hx
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_accStores hx
  exact ⟨p, hp, by omega, by simp only [Lay.NB]; omega⟩

theorem accStores_lt (hl : LayOk l) : ∀ x ∈ accStores l, x.1 + 32 ≤ l.D + l.NB := by
  intro x hx
  obtain ⟨p, hp, k, hk, rfl⟩ := mem_accStores hx
  have := hl.D_bounds
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp only [Lay.NB] at * <;> omega

/-- The word of limb `k + R t` of prime `p` after the stores. -/
theorem read_stores (hl : LayOk l) (m : Mem) (B : Addr) (s : State) {p k t : Nat} (hp : p < 2) (hk : k < l.R)
    (ht : t < 4) :
    word (wrList m B ((accStores l).map fun x => (x.1, s.vy x.2))) B (l.D * p + 32 * k + 8 * t) =
      qv s (vreg (regOf l p k 0)) t := by
  have hD := hl.D_bounds
  simp only [Lay.NB] at hD
  have hp' : l.D * p ≤ l.D := by rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
  refine word_wrList_unique B ht (by omega) _ m ?_ (fun x hx => ?_) (fun x hx he => ?_)
  · simp only [List.mem_map]
    exact ⟨_, List.mem_flatMap.2 ⟨p, List.mem_range.2 hp, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩, rfl⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp', k', hk', rfl⟩ := mem_accStores hy
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega : p' = 0 ∨ p' = 1) with rfl | rfl <;>
      simp only [Nat.mul_zero, Nat.mul_one] <;> omega
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p', hp', k', hk', rfl⟩ := mem_accStores hy
    have : p' = p ∧ k' = k := by
      rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rcases (by omega : p' = 0 ∨ p' = 1) with rfl | rfl <;>
        simp only [Nat.mul_zero, Nat.mul_one] at he <;> omega
    obtain ⟨rfl, rfl⟩ := this
    rfl

/-! ## Frames of both regions -/

/-- `m'` agrees with `m` but on the bytes at offsets `[D p + o, D p + o + n)` of `B`, for `p < 2`. -/
def Out2 (l : Lay) (B : Addr) (o n : Nat) (m m' : Mem) : Prop :=
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

/-! ## The carries -/

/-- Limb `j` of both primes' carry chains. -/
def limbCode (l : Lay) (j : Nat) : List Instr :=
  [.alu .add .rdx (.mem (at_ .r11 (l.off j))), .mov .rax (.reg .rdx),
   .alu .and .rax (.reg .r12), .store (at_ .r11 (l.off j)) .rax, .shift .shr .rdx 52,
   .alu .add .rsi (.mem (at_ .r11 (l.D + l.off j))), .mov .rcx (.reg .rsi),
   .alu .and .rcx (.reg .r12), .store (at_ .r11 (l.D + l.off j)) .rcx,
   .shift .shr .rsi 52]

theorem carryOut_eq (l : Lay) :
    carryOut l = ([.mov32 .rdx (.imm 0), .mov32 .rsi (.imm 0)] : List Instr) ++ (List.range l.L).flatMap (limbCode l) :=
  rfl

/-- After the carries of the limbs below `j`, from the stored limbs `L p`. -/
structure CarryInv (l : Lay) (B : Addr) (L : Nat → Nat → Nat) (m₀ : Mem) (s : State) (j : Nat) : Prop where
  r11 : s.gpr .r11 = B
  r12 : s.gpr .r12 = mask52
  rdx : s.gpr .rdx = BitVec.ofNat 64 (carryIn (L 0) j)
  rsi : s.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) j)
  words : ∀ p < 2, ∀ q < l.L,
    word s.mem B (l.D * p + l.off q) = BitVec.ofNat 64 (if q < j then carried (L p) q else L p q)
  frame : Out2 l B 0 l.NB m₀ s.mem

/-- One limb of both chains. -/
theorem limb_ok (hl : LayOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j : Nat} (hj : j < l.L)
    (hL : ∀ p < 2, ∀ q < l.L, L p q < 2 ^ 62)
    (hw : ∀ d, d + 8 ≤ l.D + l.NB → InRegions s.wr (off B d) 8)
    (h : CarryInv l B L m₀ s j) :
    WP isa (.block (limbCode l j)) s fun s' => CarryInv l B L m₀ s' (j + 1) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  have ho := off_lt hl hj
  have c0 := carryIn_lt62 (L := L 0) (n := j) fun q hq => hL 0 (by decide) q (by omega)
  have c1 := carryIn_lt62 (L := L 1) (n := j) fun q hq => hL 1 (by decide) q (by omega)
  have l0 := hL 0 (by decide) j hj
  have l1 := hL 1 (by decide) j hj
  have w0 : s.mem.readW (off B (l.off j)) 64 = BitVec.ofNat 64 (L 0 j) := by
    have := h.words 0 (by decide) j hj
    rw [Nat.mul_zero, Nat.zero_add, ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have w1 : s.mem.readW (off B (l.D + l.off j)) 64 = BitVec.ofNat 64 (L 1 j) := by
    have := h.words 1 (by decide) j hj
    rw [Nat.mul_one, ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have rin : ∀ d, d + 8 ≤ l.D + l.NB → InRegions (s.rd ++ s.wr) (off B d) 8 := fun d hd => by
    obtain ⟨r, hr, hc⟩ := hw d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [limbCode, WP.block_cons_iff]
  -- p = 0
  obtain ⟨s1, e1, u1⟩ := ex_add_mem (s := s) (r := .rdx)
    (m := at_ .r11 (l.off j))
    (by rw [eaG h.r11]; exact rin (l.off j) (by omega))
  refine ⟨s1, e1, ?_⟩
  rw [eaG h.r11, h.rdx, w0, add_ofNat' (by omega)] at u1
  rw [WP.block_cons_iff]
  obtain ⟨s2, e2, u2⟩ := ex_mov (s := s1) (d := .rax) (r := .rdx)
  refine ⟨s2, e2, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s3, e3, u3⟩ := ex_and (s := s2) (d := .rax) (r := .r12)
  refine ⟨s3, e3, ?_⟩
  rw [u2.self, u2.other _ (by decide), u1.self, u1.other _ (by decide), h.r12, and_mask (by omega)] at u3
  rw [WP.block_cons_iff]
  have r11₃ : s3.gpr .r11 = B := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r11]
  obtain ⟨s4, e4, m4, g4, rd4, wr4, x4⟩ := ex_store (s := s3) (r := .rax)
    (m := at_ .r11 (l.off j))
    (by rw [eaG r11₃, u3.wr, u2.wr, u1.wr]; exact hw _ (by omega))
  refine ⟨s4, e4, ?_⟩
  rw [eaG r11₃, u3.self] at m4
  rw [WP.block_cons_iff]
  obtain ⟨s5, e5, u5⟩ := ex_shr (s := s4) (d := .rdx)
  refine ⟨s5, e5, ?_⟩
  rw [congrFun g4, u3.other _ (by decide), u2.other _ (by decide), u1.self, shr_ofNat (by omega)] at u5
  -- p = 1
  have r11₅ : s5.gpr .r11 = B := by rw [u5.other _ (by decide), congrFun g4, r11₃]
  have mem₅ : s5.mem = (s.mem.writeW (off B (l.off j))
      (BitVec.ofNat 64 ((carryIn (L 0) j + L 0 j) % 2 ^ 52))) := by
    rw [u5.mem, m4, u3.mem, u2.mem, u1.mem]
  have w1' : s5.mem.readW (off B (l.D + l.off j)) 64 = BitVec.ofNat 64 (L 1 j) := by
    rw [mem₅]
    exact ((writeW_outside s.mem B _ (by omega)).word (by omega) (by omega)).trans w1
  have wr₅ : s5.wr = s.wr := by rw [u5.wr, wr4, u3.wr, u2.wr, u1.wr]
  have rd₅ : s5.rd = s.rd := by rw [u5.rd, rd4, u3.rd, u2.rd, u1.rd]
  rw [WP.block_cons_iff]
  obtain ⟨s6, e6, u6⟩ := ex_add_mem (s := s5) (r := .rsi)
    (m := at_ .r11 (l.D + l.off j))
    (by rw [eaG r11₅, rd₅, wr₅]; exact rin _ (by omega))
  refine ⟨s6, e6, ?_⟩
  have rsi₅ : s5.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) j) := by
    rw [u5.other _ (by decide), congrFun g4, u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), h.rsi]
  rw [eaG r11₅, rsi₅, w1', add_ofNat' (by omega)] at u6
  rw [WP.block_cons_iff]
  obtain ⟨s7, e7, u7⟩ := ex_mov (s := s6) (d := .rcx) (r := .rsi)
  refine ⟨s7, e7, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s8, e8, u8⟩ := ex_and (s := s7) (d := .rcx) (r := .r12)
  refine ⟨s8, e8, ?_⟩
  have r12₇ : s7.gpr .r12 = mask52 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), congrFun g4,
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r12]
  rw [u7.self, u6.self, r12₇, and_mask (by omega)] at u8
  have r11₈ : s8.gpr .r11 = B := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), r11₅]
  rw [WP.block_cons_iff]
  obtain ⟨s9, e9, m9, g9, rd9, wr9, x9⟩ := ex_store (s := s8) (r := .rcx)
    (m := at_ .r11 (l.D + l.off j))
    (by rw [eaG r11₈, u8.wr, u7.wr, u6.wr, wr₅]; exact hw _ (by omega))
  refine ⟨s9, e9, ?_⟩
  rw [eaG r11₈, u8.self] at m9
  rw [WP.block_cons_iff]
  obtain ⟨s10, e10, u10⟩ := ex_shr (s := s9) (d := .rsi)
  refine ⟨s10, e10, ?_⟩
  rw [congrFun g9, u8.other _ (by decide), u7.other _ (by decide), u6.self, shr_ofNat (by omega)] at u10
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [u10.other _ (by decide), congrFun g9, r11₈]
  · rw [u10.other _ (by decide), congrFun g9, u8.other _ (by decide), r12₇]
  · rw [u10.other _ (by decide), congrFun g9, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.self]
    simp only [carryIn]; rw [Nat.add_comm]
  · rw [u10.self]; simp only [carryIn]; rw [Nat.add_comm]
  · have mem₁₀ : s10.mem = (s5.mem.writeW (off B (l.D + l.off j))
        (BitVec.ofNat 64 ((carryIn (L 1) j + L 1 j) % 2 ^ 52))) := by
      rw [u10.mem, m9, u8.mem, u7.mem, u6.mem]
    intro p hp q hq
    have hoq := off_lt hl hq
    rw [mem₁₀, mem₅]
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.zero_add, (writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
      by_cases hqj : q = j
      · subst hqj
        rw [word_writeW_self]
        simp only [carried, show q < q + 1 by omega, ite_true]; rw [Nat.add_comm]
      · have hs := off_sep hl hj hq hqj
        rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
        have := h.words 0 (by decide) q hq
        rw [Nat.mul_zero, Nat.zero_add] at this
        rw [this]
        by_cases hqt : q < j
        · simp only [hqt, show q < j + 1 by omega, ite_true]
        · simp only [hqt, show ¬ q < j + 1 by omega, ite_false]
    · rw [Nat.mul_one]
      by_cases hqj : q = j
      · subst hqj
        rw [word_writeW_self]
        simp only [carried, show q < q + 1 by omega, ite_true]; rw [Nat.add_comm]
      · have hs := off_sep hl hj hq hqj
        rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega),
          (writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
        have := h.words 1 (by decide) q hq
        rw [Nat.mul_one] at this
        rw [this]
        by_cases hqt : q < j
        · simp only [hqt, show q < j + 1 by omega, ite_true]
        · simp only [hqt, show ¬ q < j + 1 by omega, ite_false]
  · rw [u10.mem, m9, u8.mem, u7.mem, u6.mem, mem₅]
    exact (h.frame.trans (Out2.of_outside (p := 0) (by decide)
      ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)))).trans
      (Out2.of_outside (p := 1) (by decide) ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega)))
  · intro r h1 h2 h3 h4
    rw [u10.other _ h4, congrFun g9, u8.other _ h2, u7.other _ h2, u6.other _ h4, u5.other _ h3, congrFun g4,
      u3.other _ h1, u2.other _ h1, u1.other _ h3]
  · rw [u10.rd, rd9, u8.rd, u7.rd, u6.rd, rd₅]
  · rw [u10.wr, wr9, u8.wr, u7.wr, u6.wr, wr₅]
  · rw [u10.mxcsr, x9, u8.mxcsr, u7.mxcsr, u6.mxcsr, u5.mxcsr, x4, u3.mxcsr, u2.mxcsr, u1.mxcsr]


/-- The limbs from `j` on. -/
theorem limbs_ok (hl : LayOk l) {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem}
    (hL : ∀ p < 2, ∀ q < l.L, L p q < 2 ^ 62) :
    ∀ n j (s : State), j + n = l.L → (∀ d, d + 8 ≤ l.D + l.NB → InRegions s.wr (off B d) 8) →
      CarryInv l B L m₀ s j →
      WP isa (.block ((List.range' j n).flatMap (limbCode l))) s fun s' => CarryInv l B L m₀ s' l.L ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, j, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, j, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (limb_ok hl (by omega) hL hw h) fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (limbs_ok hl hL n (j + 1) s₁ (by omega) (fun d hd => wr₁ ▸ hw d hd) h₁)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r a b c d),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)

/-- The carry pass, from the limbs `L p` stored. -/
theorem carryOut_ok (hl : LayOk l) {B : Addr} {L : Nat → Nat → Nat} {s : State}
    (hL : ∀ p < 2, ∀ q < l.L, L p q < 2 ^ 62) (hw : ∀ d, d + 8 ≤ l.D + l.NB → InRegions s.wr (off B d) 8)
    (hr11 : s.gpr .r11 = B) (hr12 : s.gpr .r12 = mask52)
    (hwords : ∀ p < 2, ∀ q < l.L, word s.mem B (l.D * p + l.off q) = BitVec.ofNat 64 (L p q)) :
    WP isa (.block (carryOut l)) s fun s' => CarryInv l B L s.mem s' l.L ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have g2 : ∀ r, r ≠ .rdx → r ≠ .rsi → ((s.setReg .rdx 0).setReg .rsi 0).gpr r = s.gpr r :=
    fun r a b => by rw [RegUpd.gpr_setReg_of_ne _ _ b, RegUpd.gpr_setReg_of_ne _ _ a]
  rw [carryOut_eq l, List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .rdx 0, rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨(s.setReg .rdx 0).setReg .rsi 0, rfl, ?_⟩
  rw [List.nil_append, List.range_eq_range']
  refine WP.mono (limbs_ok hl hL l.L 0 _ (Nat.zero_add _) hw ⟨by rw [g2 _ (by decide) (by decide), hr11],
    by rw [g2 _ (by decide) (by decide), hr12], ?_, by rw [RegUpd.gpr_setReg_self]; rfl,
    fun p hp q hq => hwords p hp q hq, fun _ _ => rfl⟩) fun s' ⟨h, g, rd, wr, x⟩ =>
    ⟨h, fun r a b c d => (g r a b c d).trans (g2 r c d), rd, wr, x⟩
  rfl


/-! ## The whole multiplication -/

/-- `ammCore` from the operands `a` (at `r8`), `b` (at `r9`) and the modulus `m`
with `k` (at `rbx`), into limbs at `r11 = B`: each prime's limbs carried, and
its carry out. -/
theorem ammCore_ok (hl : LayOk l) {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat}
    {bl : Nat → Nat → Nat} (e : Env l (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B)
    (hs : Scr s B (l.D + l.NB)) :
    WP isa (ammCore l) s fun s' =>
      (∀ p < 2, ∀ q < l.L, word s'.mem B (l.D * p + l.off q) =
        BitVec.ofNat 64 (carried (lm l a m k bl p l.L) q)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (carryIn (lm l a m k bl 0 l.L) l.L) ∧
      s'.gpr .rsi = BitVec.ofNat 64 (carryIn (lm l a m k bl 1 l.L) l.L) ∧
      Out2 l B 0 l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨hR, hR10⟩ := hl.bounds
  have hD := hl.D_bounds
  refine WP.seq ?_
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (zeros_ok hl (s := (s.setReg .r10 (s.gpr .rbx)).setReg32 .rcx 4)) fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = (s.setReg .r10 (s.gpr .rbx)).gpr r := fun r a c => by
    rw [k₁.gpr r a]; exact RegUpd.gpr_setReg_of_ne _ _ c
  have i₁ : InBlk l (s.setReg .r10 (s.gpr .rbx)) s₁ a m k bl 0 0 :=
    ⟨fun p hp kk hk t ht => by
      rw [hz _ (by have := regOf_lt (k := kk) (i := 0) hp hR; omega) t ht]; rfl,
     fun t ht => hz _ (by simp only [zN]; omega) t ht, g₁ _ (by decide) (by decide),
     by rw [g₁ _ (by decide) (by decide), Nat.mul_zero, BitVec.add_zero], g₁ _ (by decide) (by decide),
     k₁.mem, k₁.rd, k₁.wr⟩
  refine WP.seq (WP.mono (loop_ok hl e 4 s₁ (by decide) (by decide) i₁ (by rw [k₁.gpr _ (by decide)]; rfl))
    fun s₂ ⟨i₂, g₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .r11 = B := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₂ : s₂.wr = s.wr := by rw [i₂.wr]; rfl
  rw [accStores_code, List.append_assoc, WP.block_append_iff]
  refine WP.mono (stores_gen (accStores l) s₂ hB₂ fun x hx =>
    wr₂ ▸ (let ⟨_, h, c⟩ := hs.region (accStores_lt hl x hx) (by decide); ⟨_, h, c⟩)) fun s₃ h₃ => ?_
  subst h₃
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  have m₂ : s₂.mem = s.mem := i₂.mem
  refine WP.mono (carryOut_ok hl (B := B) (L := fun p => lm l a m k bl p l.L)
    (fun p _ q hq => lm_lt hR10 (Nat.le_refl _) hq)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₂]; exact hs.st hd)
    (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₂)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp q hq => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have h1 := Nat.mod_lt q (show 0 < l.R by omega)
    have h2 : q / l.R < 4 := Nat.div_lt_of_lt_mul (by simp only [Lay.L] at hq; rw [Nat.mul_comm]; exact hq)
    have := read_stores hl s₂.mem B s₂ hp (k := q % l.R) (t := q / l.R) h1 h2
    rw [i₂.lanes p hp _ h1 _ h2, Nat.mod_add_div,
      show l.R * 4 + 0 = l.L by simp only [Lay.L]; omega] at this
    rw [RegUpd.mem_setReg, show l.D * p + l.off q = l.D * p + 32 * (q % l.R) + 8 * (q / l.R) by
      unfold Lay.off; omega]
    exact this
  refine ⟨fun p hp q hq => by rw [h.words p hp q hq]; simp only [hq, ite_true], h.rdx, h.rsi, ?_,
    fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [rd, RegUpd.rd_setReg, i₂.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₂],
    by rw [x, RegUpd.mxcsr_setReg, x₂, k₁.mxcsr]; rfl⟩
  · have o := wrList_out2 (l := l) B (o := 0) (n := l.NB) (by omega)
      ((accStores l).map fun x => (x.1, s₂.vy x.2)) s₂.mem fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact accStores_win y hy
    have hf : Out2 l B 0 l.NB (wrList s₂.mem B ((accStores l).map fun x => (x.1, s₂.vy x.2))) s'.mem := h.frame
    have o' : Out2 l B 0 l.NB s.mem (wrList s₂.mem B ((accStores l).map fun x => (x.1, s₂.vy x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₂ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₂ r r1 r2 r5, g₁ r r1 r2, RegUpd.gpr_setReg_of_ne _ _ r6]

end VG.Proof.Bignum.X86_64.G
