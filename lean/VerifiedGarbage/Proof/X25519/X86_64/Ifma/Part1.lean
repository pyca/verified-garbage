module

import VerifiedGarbage.Proof.X25519.X86_64.Env
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X25519.X86_64.Small
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.X25519.X86_64.Ifma
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Mul
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Arith
import VerifiedGarbage.Proof.X25519.Field

/-! ### `X25519.X86_64.Ifma.Lanes`, which this module and modules that import it used -/

section

/-! ### `X25519.X86_64.Ifma.Phase`, which this module and modules that import it used -/

section

/-! ### `X25519.X86_64.Ifma.Carry`, which only this module used -/

section

/-!
# X25519 on x86-64 with AVX512_IFMA: carries

`carry r` leaves each limb's low 51 bits plus the bits from 51 up of the limb
below (of the top limb, times 19, for the lowest): the same number modulo `p`
(`carryNat_mod`), in limbs below `2⁵²` if they were below `2⁶³`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- The limbs `carry` leaves, with the mask `m` and the constant `k19`. -/
def carryNat (m k19 : Nat) (x : Nat → Nat) : Nat → Nat
  | 0 => (x 0 &&& m) + x 4 / 2 ^ 51 % 2 ^ 52 * (k19 % 2 ^ 52) % 2 ^ 52
  | 1 => (x 1 &&& m) + x 0 / 2 ^ 51
  | 2 => (x 2 &&& m) + x 1 / 2 ^ 51
  | 3 => (x 3 &&& m) + x 2 / 2 ^ 51
  | _ => (x 4 &&& m) + x 3 / 2 ^ 51

theorem carryNat_mod (x : Nat → Nat) (h4 : x 4 < 2 ^ 63) :
    lv (carryNat (2 ^ 51 - 1) 19 x) % P = lv x % P := by
  have e : lv (carryNat (2 ^ 51 - 1) 19 x) + 2 ^ 255 * (x 4 / 2 ^ 51) = lv x + 19 * (x 4 / 2 ^ 51) := by
    simp only [lv, carryNat, Nat.and_two_pow_sub_one_eq_mod]
    omega_using [h4]
  have := fold255 (lv (carryNat (2 ^ 51 - 1) 19 x)) (x 4 / 2 ^ 51)
  rw [e] at this
  simp only [P] at this ⊢
  omega_using [e]

/-- `carry r` run from its start. -/
def carryS (r : Nat → Nat) (h : (Sym.init.run (carry r)).isSome := by decide +kernel) : Sym :=
  (Sym.init.run (carry r)).get h

theorem carryS_eq (r : Nat → Nat) (h : (Sym.init.run (carry r)).isSome) :
    Sym.init.run (carry r) = some (carryS r h) := (Option.some_get _).symm

def carryI : Sym := carryS id
def carryF : Sym := carryS (5 + ·)

theorem carryI_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryI.reg k).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v i l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryF_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryF.reg (5 + k)).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v (5 + i) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

/-- The bounds `carry r` needs: limbs below `2⁶³`, and the constants. -/
def carryB (r : Nat → Nat) : Bnds :=
  ⟨fun i => if i = r 0 ∨ i = r 1 ∨ i = r 2 ∨ i = r 3 ∨ i = r 4 then 2 ^ 63 - 1 else 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun d => if d = KM then 2 ^ 51 - 1 else if d = K19 then 19 else 2 ^ 64 - 1,
    fun _ => 0, fun _ => 2 ^ 64 - 1⟩

theorem carryI_ok : ∀ k < 5, ∀ l < 4, (carryI.reg k).ok (carryB id) l = true ∧
    (carryI.reg k).bnd (carryB id) l < 2 ^ 52 := by decide +kernel

theorem carryF_ok : ∀ k < 5, ∀ l < 4, (carryF.reg (5 + k)).ok (carryB (5 + ·)) l = true ∧
    (carryF.reg (5 + k)).bnd (carryB (5 + ·)) l < 2 ^ 52 := by decide +kernel

theorem carryI_keep : ∀ r < 16, ¬ (r < 5 ∨ (10 ≤ r ∧ r < 13)) → carryI.reg r = .reg r := by
  decide +kernel

theorem carryF_keep : ∀ r < 16, ¬ ((5 ≤ r ∧ r < 13)) → carryF.reg r = .reg r := by
  decide +kernel

theorem carryI_st : carryI.st = [] := by decide +kernel
theorem carryF_st : carryF.st = [] := by decide +kernel

/-! ## The carries of stages 2 and 3 (`carryT`) -/

/-- Stage 2's carry, of its first operand in `ymm10–ymm14`. -/
def carryU : Sym := (Sym.init.run (carryT (10 + ·) 15 5 6)).get (by decide +kernel)
/-- Stage 3's carry, of stage 2's product in `ymm0–ymm4`. -/
def carryR : Sym := (Sym.init.run (carryT id 15 5 6)).get (by decide +kernel)

theorem carryU_eq : Sym.init.run (carryT (10 + ·) 15 5 6) = some carryU := (Option.some_get _).symm
theorem carryR_eq : Sym.init.run (carryT id 15 5 6) = some carryR := (Option.some_get _).symm

theorem carryU_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryU.reg (10 + k)).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v (10 + i) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryR_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryR.reg k).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v i l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryU_ok : ∀ k < 5, ∀ l < 4, (carryU.reg (10 + k)).ok (carryB (10 + ·)) l = true ∧
    (carryU.reg (10 + k)).bnd (carryB (10 + ·)) l < 2 ^ 52 := by decide +kernel

theorem carryR_ok : ∀ k < 5, ∀ l < 4, (carryR.reg k).ok (carryB id) l = true ∧
    (carryR.reg k).bnd (carryB id) l < 2 ^ 52 := by decide +kernel

theorem carryU_keep : ∀ r < 16, ¬ ((5 ≤ r ∧ r < 7) ∨ 10 ≤ r) → carryU.reg r = .reg r := by decide +kernel
theorem carryR_keep : ∀ r < 16, ¬ (r < 7 ∨ r = 15) → carryR.reg r = .reg r := by decide +kernel

theorem carryU_st : carryU.st = [] := by decide +kernel
theorem carryR_st : carryR.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma

end

end

/-! ### `X25519.X86_64.Ifma.Block`, which only this module used -/

section

/-!
# X25519 on x86-64 with AVX512_IFMA: what a block leaves in memory

After a block whose stores (`Sym.st`) are 32-byte slots apart, each quadword
of a slot it stored is its term, and every quadword it did not store is as
before.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64

/-- The quadword at `base + d`. -/
def mq (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (base + BitVec.ofNat 64 d) 64

theorem val_extract (s₀ : State) (t : T) {l : Nat} (hl : l < 4) :
    (t.val s₀).extractLsb' (8 * (8 * l)) (8 * 8) = t.eval s₀ l := by
  have := VG.Proof.Poly1305.X86_64.Avx2.qword256_cat (t.eval s₀ 3) (t.eval s₀ 2) (t.eval s₀ 1)
    (t.eval s₀ 0) hl
  rw [show 8 * (8 * l) = 64 * l by omega_using []]
  refine this.trans ?_
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- Slots 32 bytes apart. -/
def Apart (st : List (Nat × T)) : Prop := st.Pairwise fun x y => x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1

instance (st : List (Nat × T)) : Decidable (Apart st) := by unfold Apart; infer_instance

/-- A quadword of a stored slot. -/
theorem stores_mq (s₀ : State) (base : Addr) (m : Mem) :
    ∀ (st : List (Nat × T)) {e : Nat} {t : T} {l : Nat}, (e, t) ∈ st → l < 4 →
      (∀ x ∈ st, x.1 < 2 ^ 62) → Apart st → mq (stores s₀ base st m) base (e + 8 * l) = t.eval s₀ l
  | [], _, _, _, h, _, _, _ => by cases h
  | (e₀, t₀) :: st, e, t, l, h, hl, hs, ha => by
    simp only [Apart, List.pairwise_cons] at ha
    simp only [stores]
    rcases List.mem_cons.1 h with h | h
    · cases h
      rw [mq, BitVec.ofNat_add, ← BitVec.add_assoc,
        readW_writeW_inside _ _ _ (k := 8 * l) (n := 8) (by omega_using [hl]) (by decide), val_extract _ _ hl]
    · have h₀ := ha.1 _ h
      have e1 := readW_writeW_off (stores s₀ base st m) base (t₀.val s₀) (d := e + 8 * l) (e := e₀) (n := 8)
        (by have := hs _ (List.mem_cons_of_mem _ h); simp at this; omega_using [hl, this])
        (by have := hs _ (List.mem_cons_self ..); simp at this; omega_using [this])
        (by simp at h₀; omega_using [hl, h₀])
      exact e1.trans (stores_mq s₀ base m st h hl (fun x hx => hs x (List.mem_cons_of_mem _ hx)) ha.2)

end VG.Proof.X25519.X86_64.Ifma

end

end

/-! ### `X25519.X86_64.Ifma.Stage`, which only this module used -/

section

/-!
# X25519 on x86-64 with AVX512_IFMA: the stages' operands

The blocks between the carries and the products of an iteration, run
symbolically: each output limb, lane by lane, as a number (`rfl`), and its
bounds (`decide`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- A block run from its start. -/
def symOf (is : List Instr) (h : (Sym.init.run is).isSome := by decide +kernel) : Sym :=
  (Sym.init.run is).get h

theorem symOf_eq (is : List Instr) (h : (Sym.init.run is).isSome) :
    Sym.init.run is = some (symOf is h) := (Option.some_get _).symm

/-! ## Stage 1 -/

def s1a : Sym := symOf stage1a

/-- `(x₂ + bias - z₂, x₂ + z₂, x₃ + bias - z₃, x₃ + z₃)`, limb `j`. -/
def s1aNat (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 0 + (E.m (kb j) 0 - E.v j 1)
  | 1 => E.v j 0 + E.v j 1
  | 2 => E.v j 2 + (E.m (kb j) 2 - E.v j 3)
  | _ => E.v j 2 + E.v j 3

theorem s1a_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s1a.reg j).nat E l = s1aNat E j l := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- Bounds: limbs below `2⁶¹`, and the bias. -/
def s1aB : Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0, fun _ => 2 ^ 64 - 1⟩

theorem s1a_ok : ∀ j < 5, ∀ l < 4, (s1a.reg j).ok s1aB l = true ∧ (s1a.reg j).bnd s1aB l < 2 ^ 63 := by
  decide +kernel

theorem s1a_keep : ∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → s1a.reg r = .reg r := by decide +kernel
theorem s1a_st : s1a.st = [] := by decide +kernel

def s1b : Sym := symOf stage1b

/-- `vidx`'s index of the first operand, a quadword: the mask's doublewords
below 4, by `K4D`, onto `KIU`'s. -/
def idxU : T := .xor (.and (.reg 15) (.ld K4D)) (.ld KIU)
/-- The second operand's, onto `KIV`'s. -/
def idxV : T := .xor (.and (.reg 15) (.ld K4D)) (.ld KIV)

theorem s1b_regsU : ∀ j < 5, s1b.reg (10 + j) = .pd idxU (.reg j) := by decide +kernel
theorem s1b_regsV : ∀ j < 5, s1b.reg (5 + j) = .pd idxV (.reg j) := by decide +kernel
theorem s1b_st : s1b.st = [] := by decide +kernel
theorem s1b_keep : ∀ r < 5, s1b.reg r = .reg r := by decide +kernel

/-! ## Stage 2 -/

def s2a : Sym := symOf stage2a

/-- `(AA, AA + bias - BB, DA + CB, DA + bias - CB)` from `(BB, AA, CB, DA)`, limb `j`. -/
def s2aU (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 1
  | 1 => E.v j 1 + (E.m (kb j) 1 - E.v j 0)
  | 2 => E.v j 3 + E.v j 2
  | _ => E.v j 3 + (E.m (kb j) 3 - E.v j 2)

theorem s2a_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s2a.reg (10 + j)).nat E l = s2aU E j l := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

theorem s2a_ok : ∀ j < 5, ∀ l < 4, (s2a.reg (10 + j)).ok s1aB l = true ∧
    (s2a.reg (10 + j)).bnd s1aB l < 2 ^ 63 := by
  decide +kernel

theorem s2a_keep : ∀ r < 5, s2a.reg r = .reg r := by decide +kernel
theorem s2a_st : s2a.st = [] := by decide +kernel

def s2b : Sym := symOf stage2b

/-- No bounds: for the blocks that only move quadwords. -/
def topB : Bnds := ⟨fun _ => 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1, fun _ => 0, fun _ => 2 ^ 64 - 1⟩

theorem s2b_nat (E : Env) : ∀ j < 5, ∀ l < 4, (s2b.reg (5 + j)).nat E l =
    if l < 2 then E.m (KA24 + 32 * j) l else E.v (10 + j) l := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl
theorem s2b_ok : ∀ j < 5, ∀ l < 4, (s2b.reg (5 + j)).ok topB l = true := by decide +kernel
theorem s2b_st : s2b.st = [] := by decide +kernel
theorem s2b_keep : ∀ r < 16, (r < 5 ∨ 10 ≤ r) → s2b.reg r = .reg r := by decide +kernel

/-! ## Stage 3 -/

def s3b : Sym := symOf stage3b

theorem s3b_nat (E : Env) : ∀ j < 5, ∀ l < 4,
    (s3b.reg (10 + j)).nat E l = (if l < 2 then E.v (10 + j) l else E.v j l) ∧
    (s3b.reg (5 + j)).nat E l = (if l < 2 then E.v j l else E.m (KX1 + 32 * j) l) := by
  intro j hj l hl
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
theorem s3b_ok : ∀ j < 5, ∀ l < 4, (s3b.reg (10 + j)).ok topB l = true ∧ (s3b.reg (5 + j)).ok topB l = true := by
  decide +kernel
theorem s3b_st : s3b.st = [] := by decide +kernel

/-! ## The mask -/

def mkS : Sym := symOf vmask

theorem mkS_reg : mkS.reg 15 = .bc (.lane0 (.gpr .rcx)) := by decide +kernel
theorem mkS_keep : ∀ r < 15, mkS.reg r = .reg r := by decide +kernel
theorem mkS_st : mkS.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma

end

end

/-!
# X25519 on x86-64 with AVX512_IFMA: the blocks of an iteration

Each block of `vstep` as a fact about states: the limbs it leaves in registers
and slots (`lanes`, `slotv`), as numbers, from those it starts with, and what
it keeps.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw sel4)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

/-- Limb `i` of lane `l` of the registers from `r` up. -/
def lanes (s : State) (r l i : Nat) : Nat := (qw s (xr (r + i)) l).toNat

/-- Limb `i` of lane `l` of the slot at `d`. -/
def slotv (m : Mem) (base : Addr) (d l i : Nat) : Nat := (mq m base (d + 32 * i + 8 * l)).toNat

/-- The quadword of `vpermd`'s indices of the doublewords of lane `q`. -/
def kq (q : Nat) : BitVec 64 := BitVec.ofNat 64 (2 * q + (2 * q + 1) * 2 ^ 32)
/-- The quadwords of `vidx`'s indices: `KIU`'s, of the lanes `(0, 1, 3, 2)`,
and `KIV`'s, of the lanes `(0, 1, 0, 1)`. -/
def kiu (l : Nat) : BitVec 64 := kq (if l < 2 then l else 5 - l)
def kiv (l : Nat) : BitVec 64 := kq (l % 2)

/-- The constants of the working space, with `x₁`'s limbs. -/
structure Consts (m : Mem) (base : Addr) (x1 : Nat → Nat) : Prop where
  km : ∀ l < 4, (mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048
  a24 : ∀ i < 5, ∀ l < 4, slotv m base KA24 l i = if i = 0 ∧ l = 1 then 121665 else 0
  kx1 : ∀ i < 5, ∀ l < 4, slotv m base KX1 l i = if l = 3 then x1 i else if i = 0 ∧ l ≠ 1 then 1 else 0
  x1 : ∀ i < 5, x1 i < 2 ^ 52
  k13 : ∀ l < 4, (mq m base (K13 + 8 * l)).toNat = 2 ^ 13 - 1
  k26 : ∀ l < 4, (mq m base (K26 + 8 * l)).toNat = 2 ^ 26 - 1
  k39 : ∀ l < 4, (mq m base (K39 + 8 * l)).toNat = 2 ^ 39 - 1
  k4d : ∀ l < 4, mq m base (K4D + 8 * l) = 0x0000000400000004
  kiu : ∀ l < 4, mq m base (KIU + 8 * l) = kiu l
  kiv : ∀ l < 4, mq m base (KIV + 8 * l) = kiv l

/-- The constants the carries and the differences read. -/
structure CConsts (m : Mem) (base : Addr) : Prop where
  km : ∀ l < 4, (mq m base (KM + 8 * l)).toNat = 2 ^ 51 - 1
  k19 : ∀ l < 4, (mq m base (K19 + 8 * l)).toNat = 19
  kb0 : ∀ l < 4, (mq m base (KB0 + 8 * l)).toNat = 2 ^ 62 - 38912
  kb1 : ∀ l < 4, (mq m base (KB1 + 8 * l)).toNat = 2 ^ 62 - 2048

theorem Consts.c {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1) : CConsts m base :=
  ⟨hk.km, hk.k19, hk.kb0, hk.kb1⟩

theorem envOf_m {s : State} {base : Addr} (hs : s.gpr .rdi = base) (d l : Nat) :
    (envOf s).m d l = (mq s.mem base (d + 8 * l)).toNat := by
  simp only [envOf, mq, hs]

theorem envOf_v (s : State) (r l : Nat) : (envOf s).v r l = (qw s (xr r) l).toNat := rfl

/-- The environment's bounds, from the registers and memory. -/
theorem envOK_of {s : State} {base : Addr} (hs : s.gpr .rdi = base) {B : Bnds}
    (hv : ∀ r l, l < 4 → (qw s (xr r) l).toNat ≤ B.v r) (hg : ∀ g, B.g g = 2 ^ 64 - 1)
    (hm : ∀ d l, l < 4 → (mq s.mem base (d + 8 * l)).toNat ≤ B.m d)
    (hml : ∀ d l, l < 4 → B.ml d ≤ (mq s.mem base (d + 8 * l)).toNat)
    (hh : ∀ r l, l < 4 → (qwH s (hr r) l).toNat ≤ B.h r := by intros; exact Nat.le_sub_one_of_lt (BitVec.isLt _)) :
    EnvOK s B :=
  ⟨hv, fun g => by rw [hg]; exact Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun d k hk => by have := hm d k hk; simpa only [mq, hs] using this,
    fun d k hk => by have := hml d k hk; simpa only [mq, hs] using this, hh⟩

theorem lt64 (x : BitVec 64) : x.toNat ≤ 2 ^ 64 - 1 := Nat.le_sub_one_of_lt x.isLt

/-- What a block run symbolically leaves in a register. -/
theorem SRel.out {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r l : Nat}
    (hr : r < 16) (hl : l < 4) (ho : (σ.reg r).ok B l = true) :
    (qw s (xr r) l).toNat = (σ.reg r).nat (envOf s₀) l ∧ (qw s (xr r) l).toNat ≤ (σ.reg r).bnd B l := by
  have := h.nat hE (r := xr r) hl (by rw [xi_xr r hr]; exact ho)
  rwa [xi_xr r hr] at this

theorem SRel.keep {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {r l : Nat} (hr : r < 16) (hl : l < 4)
    (hk : σ.reg r = .reg r) : qw s (xr r) l = qw s₀ (xr r) l := by
  rw [h.reg _ l hl, xi_xr r hr, hk]; rfl

/-- Limb `i` of lane `l` of `ymm (16 + i)`, as a number. -/
def hlanes (s : State) (l i : Nat) : Nat := (qwH s (hr i) l).toNat

theorem hidx_hr : ∀ r < 16, hidx (hr r) = r := by decide

/-- The term a block run symbolically leaves in `ymm (16 + r)`. -/
theorem SRel.hterm {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {r l : Nat} (hr16 : r < 16) (hl : l < 4) :
    qwH s (hr r) l = (σ.hreg r).eval s₀ l := by
  rw [h.hreg _ l hl, hidx_hr r hr16]

/-! ## Carries -/

theorem kx1_le {m : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1) {i l : Nat} (hi : i < 5)
    (hl : l < 4) : slotv m base KX1 l i < 2 ^ 52 := by
  rw [hk.kx1 i hi l hl]; have := hk.x1 i hi; split <;> [omega_arith; split <;> omega_arith]

/-- What `carry r` leaves: limbs `r0` to `r0 + 4` carried. -/
def CarryPost (r0 : Nat) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' r0 l i = carryNat (2 ^ 51 - 1) 19 (lanes s r0 l) i ∧
      lanes s' r0 l i < 2 ^ 52) ∧
    (∀ r < 16, ¬ (r0 ≤ r ∧ r < r0 + 5) → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem carry_env {r : Nat → Nat} {r0 : Nat} (hr : ∀ i, r i = r0 + i) {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s r0 l i < 2 ^ 63) : EnvOK s (carryB r) := by
  refine envOK_of hs (fun r' l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
  · simp only [carryB, hr]
    split
    · rename_i h
      have : ∃ i < 5, r' = r0 + i := by rcases h with h | h | h | h | h <;> exact ⟨_, by omega_arith, h⟩
      obtain ⟨i, hi, rfl⟩ := this
      exact Nat.le_sub_one_of_lt (hx l hl i hi)
    · exact lt64 _
  · simp only [carryB]
    split
    · subst_vars; rw [hk.km l hl]
    · split
      · subst_vars; rw [hk.k19 l hl]
      · exact lt64 _

theorem carryI_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 63) :
    WP isa (.block (carry id)) s (CarryPost 0 s) := by
  have hE := carry_env (r := id) (fun i => (Nat.zero_add i).symm) hs hk hx
  have e : Sym.init.run (carry id) = some carryI := carryS_eq id _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryI_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := carryI_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
    have hs' : (fun j => lanes s 0 l j) = fun j => (envOf s).v j l := by
      funext j; simp only [lanes, Nat.zero_add, envOf_v]
    refine ⟨?_, by simp only [lanes, Nat.zero_add]; omega_arith⟩
    simp only [lanes, Nat.zero_add] at e ⊢
    rw [e, carryI_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (carryI_keep r hr (by omega_arith))

theorem carryF_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 63) :
    WP isa (.block (carry (5 + ·))) s (CarryPost 5 s) := by
  have hE := carry_env (r := (5 + ·)) (fun i => rfl) hs hk hx
  have e : Sym.init.run (carry (5 + ·)) = some carryF := carryS_eq (5 + ·) _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryF_st]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => ?_⟩
  · obtain ⟨o, b⟩ := carryF_ok i hi l hl
    obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
    have hs' : (fun j => lanes s 5 l j) = fun j => (envOf s).v (5 + j) l := by
      funext j; simp only [lanes, envOf_v]
    refine ⟨?_, by simp only [lanes]; omega_arith⟩
    simp only [lanes] at e ⊢
    rw [e, carryF_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']
  · exact h.keep hr hl (carryF_keep r hr (by omega_arith))

/-! ## Memory -/

open VG.Proof.X25519.X86_64 (Outside ofs word off) in
/-- Stores to slots in `[o, o + n)` change nothing outside it. -/
theorem stores_outside (s₀ : State) (base : Addr) (m : Mem) {o n : Nat} (hn : o + n < 2 ^ 63) :
    ∀ st : List (Nat × T), (∀ e ∈ st, o ≤ e.1 ∧ e.1 + 32 ≤ o + n) →
      Outside base o n m (stores s₀ base st m)
  | [], _ => fun _ _ => rfl
  | (e, t) :: st, h => by
    intro x hx
    have h₀ := h _ (List.mem_cons_self ..)
    simp only at h₀
    simp only [stores]
    rw [writeW_byte_off _ _ _ _ ?_]
    · exact stores_outside s₀ base m hn st (fun x hx => h x (List.mem_cons_of_mem _ hx)) x hx
    · show 256 / 8 ≤ (x - (base + BitVec.ofNat 64 e)).toNat
      rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
      simp only [ofs] at hx
      have := (x - base).isLt
      rw [Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega_arith)]
      omega_arith

theorem mq_eq_word (m : Mem) (base : Addr) (d : Nat) : mq m base d = word m base d := rfl

/-! ## Products -/

/-- What `mul4 a` leaves: the product of the slot `a` and `ymm5–ymm9`, lane by
lane, in `ymm0–ymm4`. -/
def MulPost (base : Addr) (a : Nat) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' 0 l i = mulNat (slotv s.mem base a l) (lanes s 5 l) i ∧
      lanes s' 0 l i < 2 ^ 61) ∧
    (∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem mul4_wp {a : Nat} (ha : a % 32 = 0) {σ : Sym}
    (he : Sym.init.run (mul4 a) = some σ)
    (hnat : ∀ E l, ∀ k < 5, (σ.reg k).nat E l = mulNat (fun i => E.m (a + 32 * i) l) (fun j => E.v (5 + j) l) k)
    (hok : ∀ k < 5, ∀ l < 4, (σ.reg k).ok (mulB a) l = true ∧ (σ.reg k).bnd (mulB a) l < 2 ^ 61)
    (hkeep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → σ.reg r = .reg r) (hst : σ.st = [])
    {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, slotv s.mem base a l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mul4 a)) s (MulPost base a s) := by
  have hE : EnvOK s (mulB a) := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun _ _ _ => Nat.zero_le _)
    · simp only [mulB]
      split
      · rename_i h
        have := hy l hl (r - 5) (by omega_arith)
        simp only [lanes, show 5 + (r - 5) = r by omega_arith] at this
        omega_arith
      · exact lt64 _
    · simp only [mulB]
      split
      · rename_i h
        obtain ⟨i, hi, rfl⟩ : ∃ i < 5, d = a + 32 * i := ⟨(d - a) / 32, by omega_arith, by omega_arith⟩
        have := hx l hl i hi
        simp only [slotv] at this
        omega_arith
      · exact lt64 _
  refine WP.mono (run_ok hc he) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, hst]; rfl, fun l hl i hi => ?_, fun r hr h1 h2 l hl => h.keep hr hl (hkeep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := hok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith⟩
  have hf : (fun i => (envOf s).m (a + 32 * i) l) = slotv s.mem base a l :=
    funext fun j => by rw [envOf_m hs, slotv]
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e, hnat _ _ i hi, hf, hg]

/-- What `mulG` leaves: the product of `ymm10–ymm14` and `ymm5–ymm9`, lane by
lane, in `ymm0–ymm4`, added with `pre` to lanes 0 and 1 of what they held. -/
def MulPostG (pre : Bool) (s s' : State) : Prop :=
  vm s s' = s' ∧ s'.mem = s.mem ∧
    (∀ l < 4, ∀ i < 5, lanes s' 0 l i =
        (if pre = true ∧ l < 2 then lanes s 0 l i else 0) + mulNat (lanes s 10 l) (lanes s 5 l) i ∧
      lanes s' 0 l i < 2 ^ 62 ∧ (pre = false → lanes s' 0 l i < 2 ^ 61)) ∧
    (∀ r < 15, 5 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)

theorem mulGB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base)
    (hp : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) : EnvOK s mulGB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun _ _ _ => lt64 _) (fun _ _ _ => Nat.zero_le _)
  simp only [mulGB]
  split
  · rename_i h
    rcases (by omega_arith : r < 10 ∨ 10 ≤ r) with h' | h'
    · have := hy l hl (r - 5) (by omega_arith)
      simp only [lanes, show 5 + (r - 5) = r by omega_arith] at this
      omega_arith
    · have := hx l hl (r - 10) (by omega_arith)
      simp only [lanes, show 10 + (r - 10) = r by omega_arith] at this
      omega_arith
  · split
    · have := hp l hl r (by omega_arith); simp only [lanes, Nat.zero_add] at this; omega_arith
    · exact lt64 _

theorem mulG0_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mulG false)) s fun s' => MulPostG false s s' ∧
      ∀ l < 4, qw s' (xr 15) l = qw s (xr 15) l := by
  have hE : EnvOK s mulG0B := by
    refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun _ _ _ => lt64 _) (fun _ _ _ => Nat.zero_le _)
    simp only [mulG0B]
    split
    · rename_i h
      rcases (by omega_arith : r < 10 ∨ 10 ≤ r) with h' | h'
      · have := hy l hl (r - 5) (by omega_arith)
        simp only [lanes, show 5 + (r - 5) = r by omega_arith] at this
        omega_arith
      · have := hx l hl (r - 10) (by omega_arith)
        simp only [lanes, show 10 + (r - 10) = r by omega_arith] at this
        omega_arith
    · exact lt64 _
  refine WP.mono (run_ok hc mulG0_eq) fun s' h => ?_
  refine ⟨⟨h.eq, by rw [h.mem]; exact congrArg (fun st => stores s (s.gpr .rdi) st s.mem) mulG0_st,
    fun l hl i hi => ?_, fun r hr h1 l hl => h.keep (by omega_arith) hl (mulG0_keep r (by omega_arith) h1)⟩,
    fun l hl => h.keep (by decide) hl (mulG0_keep 15 (by decide) (by decide))⟩
  obtain ⟨o, b⟩ := mulG0_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith, fun _ => by omega_arith⟩
  have hf : (fun i => (envOf s).v (10 + i) l) = lanes s 10 l := funext fun j => rfl
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e]
  show (mulG0.reg i).nat (envOf s) l = _
  rw [mulG0_nat _ _ i hi, hf, hg, mulNatG_eq _ _ _ i hi]
  simp

theorem mulG1_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hp : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 52)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 5 l i < 2 ^ 52) :
    WP isa (.block (mulG true)) s (MulPostG true s) := by
  have hE := mulGB_env hs hp hx hy
  refine WP.mono (run_ok hc mulG1_eq) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem]; exact congrArg (fun st => stores s (s.gpr .rdi) st s.mem) mulG1_st,
    fun l hl i hi => ?_, fun r hr h1 l hl => h.keep (by omega_arith) hl (mulG1_keep r hr h1)⟩
  obtain ⟨o, b⟩ := mulG1_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith, fun h => by cases h⟩
  have hf : (fun i => (envOf s).v (10 + i) l) = lanes s 10 l := funext fun j => rfl
  have hg : (fun j => (envOf s).v (5 + j) l) = lanes s 5 l := funext fun j => rfl
  rw [e]
  show (mulG1.reg i).nat (envOf s) l = _
  rw [mulG1_nat _ l hl i hi, hf, hg, mulNatG_eq _ _ _ i hi]
  simp only [true_and, envOf_v]

/-! ## The carries of stages 2 and 3 -/

/-- What stage 2's carry leaves: `ymm10–ymm14` carried. -/
theorem carryU_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 10 l i < 2 ^ 63) :
    WP isa (.block (carryT (10 + ·) 15 5 6)) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 10 l i = carryNat (2 ^ 51 - 1) 19 (lanes s 10 l) i ∧
        lanes s' 10 l i < 2 ^ 52) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := carry_env (r := (10 + ·)) (fun i => rfl) hs hk hx
  refine WP.mono (run_ok hc carryU_eq) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryU_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega_arith) hl (carryU_keep r (by omega_arith) (by omega_arith))⟩
  obtain ⟨o, b⟩ := carryU_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  have hs' : (fun j => lanes s 10 l j) = fun j => (envOf s).v (10 + j) l := by
    funext j; simp only [lanes, envOf_v]
  refine ⟨?_, by simp only [lanes]; omega_arith⟩
  simp only [lanes] at e ⊢
  rw [e, carryU_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']

/-- What stage 3's carry leaves: `ymm0–ymm4` carried, and `ymm10–ymm14` as they were. -/
theorem carryR_wp {s : State} {base : Addr}
    (hs : s.gpr .rdi = base) (hc : Ctx s) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 63) :
    WP isa (.block (carryT id 15 5 6)) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = carryNat (2 ^ 51 - 1) 19 (lanes s 0 l) i ∧
        lanes s' 0 l i < 2 ^ 52) ∧
      (∀ r < 15, 10 ≤ r → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := carry_env (r := id) (fun i => (Nat.zero_add i).symm) hs hk hx
  refine WP.mono (run_ok hc carryR_eq) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, carryR_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep (by omega_arith) hl (carryR_keep r (by omega_arith) (by omega_arith))⟩
  obtain ⟨o, b⟩ := carryR_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  have hs' : (fun j => lanes s 0 l j) = fun j => (envOf s).v j l := by
    funext j; simp only [lanes, Nat.zero_add, envOf_v]
  refine ⟨?_, by simp only [lanes, Nat.zero_add]; omega_arith⟩
  simp only [lanes, Nat.zero_add] at e ⊢
  rw [e, carryR_nat _ _ i hi, envOf_m hs, envOf_m hs, hk.km l hl, hk.k19 l hl, ← hs']

/-! ## The stages -/

/-- The bias's limb `j`. -/
def kbv (j : Nat) : Nat := if j = 0 then 2 ^ 62 - 38912 else 2 ^ 62 - 2048

theorem kb_m {m : Mem} {base : Addr} (hk : CConsts m base) {j l : Nat} (hl : l < 4) :
    (mq m base (kb j + 8 * l)).toNat = kbv j := by
  simp only [kb, kbv]; split
  · exact hk.kb0 l hl
  · exact hk.kb1 l hl

/-- The environment of a block that reads products below `2⁶¹` in `ymm0–ymm4`
and the bias. -/
theorem s1aB_env {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hk : CConsts s.mem base)
    (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) : EnvOK s s1aB := by
  refine envOK_of hs (fun r l hl => ?_) (fun _ => rfl) (fun d l hl => ?_) (fun d l hl => ?_)
  · simp only [s1aB]
    split
    · have := hx l hl r (by omega_arith); simp only [lanes, Nat.zero_add] at this; omega_arith
    · exact lt64 _
  · simp only [s1aB]
    split
    · subst_vars; rw [hk.kb0 l hl]
    · split
      · subst_vars; rw [hk.kb1 l hl]
      · exact lt64 _
  · simp only [s1aB]
    split
    · subst_vars; rw [hk.kb0 l hl]
    · split
      · subst_vars; rw [hk.kb1 l hl]
      · exact Nat.zero_le _

/-- Stage 1's differences and sums, limb `i` of lane `l`, from the lanes `x`
(`x l i`), `(x₂, z₂, x₃, z₃)`: `(B, A, D, C)`. -/
def sumDiff (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 0 i + (kbv i - x 1 i)
  | 1 => x 0 i + x 1 i
  | 2 => x 2 i + (kbv i - x 3 i)
  | _ => x 2 i + x 3 i

theorem s1a_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage1a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i = sumDiff (lanes s 0) l i ∧ lanes s' 0 l i < 2 ^ 63) ∧
      (∀ r < 16, 5 ≤ r → ¬ (10 ≤ r ∧ r < 13) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := s1aB_env hs hk hx
  have e : Sym.init.run stage1a = some s1a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s1a_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 h2 l hl => h.keep hr hl (s1a_keep r hr h1 h2)⟩
  obtain ⟨o, b⟩ := s1a_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes, Nat.zero_add] at e ⊢
  refine ⟨?_, by omega_arith⟩
  rw [e, s1a_nat _ i hi l hl]
  have kbe : (envOf s).m (kb i) = fun l => (mq s.mem base (kb i + 8 * l)).toNat := by
    funext l; rw [envOf_m hs]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [s1aNat, sumDiff, lanes, Nat.zero_add, envOf_v, kbe, kb_m hk (show 0 < 4 by decide),
      kb_m hk (show 2 < 4 by decide)]

/-! ### The mask and the swap -/

theorem mk_wp {s : State} (hc : Ctx s) :
    WP isa (.block vmask) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, qw s' (xr 15) l = s.gpr .rcx) ∧
      (∀ r < 15, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run vmask = some mkS := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, mkS_st]; rfl, fun l hl => ?_,
    fun r hr l hl => h.keep (by omega_arith) hl (mkS_keep r hr)⟩
  rw [h.reg _ l hl, xi_xr _ (by decide), mkS_reg]
  simp only [T.eval, ite_true]

theorem xor_mask (x y : BitVec 64) (b : Bool) :
    x ^^^ ((y ^^^ x) &&& VG.Proof.X25519.X86_64.mask b) = if b then y else x := by
  cases b
  · simp [VG.Proof.X25519.X86_64.mask]
  · simp only [VG.Proof.X25519.X86_64.mask, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm y x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cat_halves (x : BitVec 64) : x.extractLsb' 32 32 ++ x.extractLsb' 0 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, Bool.false_and, decide_eq_true (show j - 32 < 32 by omega_arith),
      Bool.true_and]
    exact congrArg _ (by omega_arith)

/-- `vpermd`'s quadword with the indices of the two doublewords of quadword `q`. -/
theorem pdq_pair (f : Nat → BitVec 64) (i : BitVec 64) (q : Nat) (h0 : (i.extractLsb' 0 3).toNat = 2 * q)
    (h1 : (i.extractLsb' 32 3).toNat = 2 * q + 1) : pdq i f = f q := by
  rw [pdq, h0, h1, dsel, dsel, show (2 * q + 1) / 2 = q by omega_arith, show 2 * q / 2 = q by omega_arith,
    show (2 * q + 1) % 2 = 1 by omega_arith, show 2 * q % 2 = 0 by omega_arith]
  exact cat_halves _

/-- The lane of `(B, A, D, C)` in lane `l` of stage 1's first operand,
`(B, A, C, D)`, or with the swap `(D, C, A, B)`; and of its second,
`(B, A, B, A)`, or with the swap `(D, C, D, C)`. -/
def pu (b : Bool) (l : Nat) : Nat := (if l < 2 then l else 5 - l) ^^^ (if b then 2 else 0)
def pv (b : Bool) (l : Nat) : Nat := l % 2 ^^^ (if b then 2 else 0)

theorem idx_lo (b : Bool) : ∀ l < 4,
    ((((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiu l).extractLsb' 0 3).toNat = 2 * pu b l ∧
      (((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiu l).extractLsb' 32 3).toNat =
        2 * pu b l + 1) ∧
    ((((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiv l).extractLsb' 0 3).toNat = 2 * pv b l ∧
      (((VG.Proof.X25519.X86_64.mask b &&& 0x0000000400000004) ^^^ kiv l).extractLsb' 32 3).toNat =
        2 * pv b l + 1) := by
  cases b <;> decide

/-- What `stage1b` leaves, with the mask of the swap `b` in `ymm15`:
`(B, A, C, D)` in `ymm10–ymm14` and `(B, A, B, A)` in `ymm5–ymm9`, of the
pairs swapped if `b`. -/
theorem s1b_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) {b : Bool} (hm : ∀ l < 4, qw s (xr 15) l = VG.Proof.X25519.X86_64.mask b) :
    WP isa (.block stage1b) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 10 l i = lanes s 0 (pu b l) i ∧
        lanes s' 5 l i = lanes s 0 (pv b l) i) := by
  have e : Sym.init.run stage1b = some s1b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  have ld : ∀ d l, (T.ld d).eval s l = mq s.mem base (d + 8 * l) := fun d l => by
    simp only [T.eval, mq, hs]
  refine ⟨h.eq, by rw [h.mem, s1b_st]; rfl, fun l hl i hi => ⟨?_, ?_⟩⟩
  · have := h.reg (xr (10 + i)) l hl
    rw [xi_xr _ (by omega_arith), s1b_regsU i hi] at this
    simp only [lanes, this]
    simp only [T.eval, idxU, mq, hs] at ld ⊢
    rw [hm l hl]
    have k4 := hk.k4d l hl; have ku := hk.kiu l hl
    simp only [mq] at k4 ku
    rw [k4, ku, pdq_pair _ _ _ (idx_lo b l hl).1.1 (idx_lo b l hl).1.2, Nat.zero_add]
  · have := h.reg (xr (5 + i)) l hl
    rw [xi_xr _ (by omega_arith), s1b_regsV i hi] at this
    simp only [lanes, this]
    simp only [T.eval, idxV, mq, hs] at ld ⊢
    rw [hm l hl]
    have k4 := hk.k4d l hl; have kv := hk.kiv l hl
    simp only [mq] at k4 kv
    rw [k4, kv, pdq_pair _ _ _ (idx_lo b l hl).2.1 (idx_lo b l hl).2.2, Nat.zero_add]

/-! ### Stage 2 -/

/-- Stage 2's first operand from `(BB, AA, CB, DA)` (`x l i`):
`(AA, AA + bias - BB, DA + CB, DA + bias - CB)`. -/
def opU (x : Nat → Nat → Nat) (l i : Nat) : Nat :=
  match l with
  | 0 => x 1 i
  | 1 => x 1 i + (kbv i - x 0 i)
  | 2 => x 3 i + x 2 i
  | _ => x 3 i + (kbv i - x 2 i)

theorem s2a_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : CConsts s.mem base) (hx : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block stage2a) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 10 l i = opU (lanes s 0) l i ∧ lanes s' 10 l i < 2 ^ 63) ∧
      (∀ r < 5, ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have hE := s1aB_env hs hk hx
  have e : Sym.init.run stage2a = some s2a := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s2a_st]; rfl, fun l hl i hi => ?_,
    fun r hr l hl => h.keep (by omega_arith) hl (s2a_keep r hr)⟩
  obtain ⟨o, b⟩ := s2a_ok i hi l hl
  obtain ⟨e, be⟩ := h.out hE (by omega_arith) hl o
  simp only [lanes] at e ⊢
  refine ⟨?_, by omega_arith⟩
  rw [e, s2a_nat _ i hi l hl]
  have kbe : (envOf s).m (kb i) = fun l => (mq s.mem base (kb i + 8 * l)).toNat := by
    funext l; rw [envOf_m hs]
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [s2aU, opU, lanes, Nat.zero_add, envOf_v, kbe, kb_m hk (show 1 < 4 by decide),
      kb_m hk (show 3 < 4 by decide)]

theorem topB_env (s : State) : EnvOK s topB :=
  ⟨fun _ _ _ => lt64 _, fun _ => lt64 _, fun _ _ _ => lt64 _, fun _ _ _ => Nat.zero_le _, fun _ _ _ => lt64 _⟩

/-- What `stage2b` leaves: `(0, a24, …)` and lanes 2 and 3 of the first operand in `ymm5–ymm9`. -/
theorem s2b_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) :
    WP isa (.block stage2b) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5, lanes s' 5 l i =
        if l < 2 then (if i = 0 ∧ l = 1 then 121665 else 0) else lanes s 10 l i) ∧
      (∀ r < 16, (r < 5 ∨ 10 ≤ r) → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l) := by
  have e : Sym.init.run stage2b = some s2b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s2b_st]; rfl, fun l hl i hi => ?_,
    fun r hr h1 l hl => h.keep hr hl (s2b_keep r hr h1)⟩
  obtain ⟨e, _⟩ := h.out (topB_env s) (by omega_arith) hl (s2b_ok i hi l hl)
  have ka := hk.a24 i hi l hl
  simp only [slotv] at ka
  simp only [lanes] at e ⊢
  rw [e, s2b_nat _ i hi l hl, envOf_m hs, ka]
  rfl

/-- What `stage3b` leaves: lanes 0 and 1 of `ymm10–ymm14` with lanes 2 and 3 of
`ymm0–ymm4` in `ymm10–ymm14`, and lanes 0 and 1 of `ymm0–ymm4` with `(1, x₁)`
in `ymm5–ymm9`. -/
theorem s3b_wp {s : State} {base : Addr} {x1 : Nat → Nat} (hs : s.gpr .rdi = base) (hc : Ctx s)
    (hk : Consts s.mem base x1) :
    WP isa (.block stage3b) s fun s' => vm s s' = s' ∧ s'.mem = s.mem ∧
      (∀ l < 4, ∀ i < 5,
        lanes s' 10 l i = (if l < 2 then lanes s 10 l i else lanes s 0 l i) ∧
        lanes s' 5 l i = (if l < 2 then lanes s 0 l i else if l = 3 then x1 i else if i = 0 then 1 else 0)) := by
  have e : Sym.init.run stage3b = some s3b := symOf_eq _ _
  refine WP.mono (run_ok hc e) fun s' h => ?_
  refine ⟨h.eq, by rw [h.mem, s3b_st]; rfl, fun l hl i hi => ?_⟩
  obtain ⟨o1, o2⟩ := s3b_ok i hi l hl
  obtain ⟨e1, _⟩ := h.out (topB_env s) (by omega_arith) hl o1
  obtain ⟨e2, _⟩ := h.out (topB_env s) (by omega_arith) hl o2
  obtain ⟨n1, n2⟩ := s3b_nat (envOf s) i hi l hl
  have kx := hk.kx1 i hi l hl
  simp only [slotv] at kx
  simp only [lanes, Nat.zero_add] at e1 e2 ⊢
  rw [e1, n1, e2, n2, envOf_m hs, kx]
  refine ⟨rfl, ?_⟩
  rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> simp [envOf_v]

end VG.Proof.X25519.X86_64.Ifma

end

end

/-!
# X25519 on x86-64 with AVX512_IFMA: limbs as field elements

Five limbs stand for an element of `GF(p)` (`fe5`); the sums, differences
(with the bias `2¹¹ p`), carries and products of the stages are the field's
operations on them.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG.Proof.X25519 VG.Spec.X25519

/-- The element of `GF(p)` five limbs stand for. -/
def fe5 (x : Nat → Nat) : Fe := toFe (lv x)

theorem lv_congr {x y : Nat → Nat} (h : ∀ i < 5, x i = y i) : lv x = lv y := by
  simp only [lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem fe5_congr {x y : Nat → Nat} (h : ∀ i < 5, x i = y i) : fe5 x = fe5 y := by
  rw [fe5, fe5, lv_congr h]

theorem fe5_add {x y z : Nat → Nat} (h : ∀ i < 5, z i = x i + y i) : fe5 z = fe5 x + fe5 y := by
  refine toFe_add (congrArg (· % P) ?_)
  simp only [lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
  omega_using []

theorem lv_kbv : lv kbv = 2 ^ 11 * P := by decide

theorem fe5_sub {x y z : Nat → Nat} (h : ∀ i < 5, z i = x i + (kbv i - y i)) (hy : ∀ i < 5, y i ≤ kbv i) :
    fe5 z = fe5 x - fe5 y := by
  refine toFe_sub ?_
  have e : lv z + lv y = lv x + P * 2 ^ 11 := by
    rw [Nat.mul_comm, ← lv_kbv]
    have h0 := hy 0 (by decide); have h1 := hy 1 (by decide); have h2 := hy 2 (by decide)
    have h3 := hy 3 (by decide); have h4 := hy 4 (by decide)
    simp only [lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
    simp only [kbv] at h0 h1 h2 h3 h4 ⊢
    omega_using [h1, h2, h3, h4, h0]
  rw [e, Nat.add_mul_mod_self_left]

theorem fe5_carry (x : Nat → Nat) (h4 : x 4 < 2 ^ 63) : fe5 (carryNat (2 ^ 51 - 1) 19 x) = fe5 x :=
  toFe_congr (carryNat_mod x h4)

theorem fe5_mul {a b : Nat → Nat} (ha : ∀ i < 5, a i < 2 ^ 52) (hb : ∀ i < 5, b i < 2 ^ 52) :
    fe5 (fun k => mulNat a b k) = fe5 a * fe5 b := by
  refine toFe_mul ?_
  rw [show (fun k => mulNat a b k) = mulNat a b from rfl, mulNat_mod,
    lv_congr (x := fun i => a i % 2 ^ 52) (y := a) (fun i hi => Nat.mod_eq_of_lt (ha i hi)),
    lv_congr (x := fun i => b i % 2 ^ 52) (y := b) (fun i hi => Nat.mod_eq_of_lt (hb i hi))]

theorem fe5_one : fe5 (fun i => if i = 0 then 1 else 0) = 1 := rfl

theorem fe5_a24 : fe5 (fun i => if i = 0 then 121665 else 0) = a24 := rfl

end VG.Proof.X25519.X86_64.Ifma

end

end

/-!
# X25519 on x86-64 with AVX512_IFMA: stage 1 of an iteration

From `(x₂, z₂, x₃, z₃)` in the lanes of `ymm0–ymm4` and the mask of the swap
in `ymm15`, stage 1 and its product leave `(BB, AA, CB, DA)` there, of the
swapped pairs.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono contains_sc)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4)

theorem scr_ctx {s : State} {base : Addr} (hs : Scr s base) : Ctx s := fun d hd => by
  rw [hs.rdi]; exact ⟨_, hs.wr, contains_sc hd⟩

theorem vm_gpr {s s' : State} (h : vm s s' = s') : s'.gpr = s.gpr := by rw [← h]; rfl
theorem vm_rd {s s' : State} (h : vm s s' = s') : s'.rd = s.rd := by rw [← h]; rfl
theorem vm_wr {s s' : State} (h : vm s s' = s') : s'.wr = s.wr := by rw [← h]; rfl

theorem scr_of {s s' : State} {base : Addr} (hs : Scr s base) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : Scr s' base := ⟨by rw [hg]; exact hs.rdi, by rw [hw]; exact hs.wr, hs.nowrap⟩

/-- What a part of an iteration keeps. -/
structure Kept (base : Addr) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 1024 480 s.mem s'.mem

theorem Kept.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : Kept base s₁ s₂) (h₂ : Kept base s₂ s₃) :
    Kept base s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.mem.trans h₂.mem⟩

theorem Kept.vm {base : Addr} {s s' : State} (h : vm s s' = s') (hm : s'.mem = s.mem) : Kept base s s' :=
  ⟨vm_gpr h, vm_rd h, vm_wr h, by rw [hm]; exact Outside.refl _ _ _ _⟩

theorem lanes_keep {s s' : State} {r0 : Nat} (h : ∀ r < 16, r0 ≤ r → r < r0 + 5 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)
    (hr : r0 + 5 ≤ 16) : ∀ l < 4, ∀ i < 5, lanes s' r0 l i = lanes s r0 l i := fun l hl i hi => by
  simp only [lanes]; rw [h (r0 + i) (by omega_using [hr, hi]) (by omega_using []) (by omega_using [hi]) l hl]

theorem le_kbv {x : Nat} (i : Nat) (h : x < 2 ^ 61) : x ≤ kbv i := by simp only [kbv]; split <;> omega_using [h]

theorem pu_lt (b : Bool) {l : Nat} (hl : l < 4) : pu b l < 4 := by
  cases b <;> rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide

theorem pv_lt (b : Bool) {l : Nat} (hl : l < 4) : pv b l < 4 := by
  cases b <;> rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The lane of the ladder's state that the swap `b` puts in lane `l`. -/
def swl (b : Bool) (l : Nat) : Nat := if b then l ^^^ 2 else l

/-- Stage 1 and its product, with the mask of the swap `b` in `ymm15`: from
`(x₂, z₂, x₃, z₃)`, swapped if `b`, `(BB, AA, CB, DA)`. -/
theorem part1_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) {b : Bool}
    (hm : ∀ l < 4, qw s (xr 15) l = VG.Proof.X25519.X86_64.mask b) :
    WP isa (.block (stage1 ++ mulG false)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 61) ∧
      fe5 (lanes s' 0 0) = (fe5 (lanes s 0 (swl b 0)) - fe5 (lanes s 0 (swl b 1))) *
        (fe5 (lanes s 0 (swl b 0)) - fe5 (lanes s 0 (swl b 1))) ∧
      fe5 (lanes s' 0 1) = (fe5 (lanes s 0 (swl b 0)) + fe5 (lanes s 0 (swl b 1))) *
        (fe5 (lanes s 0 (swl b 0)) + fe5 (lanes s 0 (swl b 1))) ∧
      fe5 (lanes s' 0 2) = (fe5 (lanes s 0 (swl b 2)) + fe5 (lanes s 0 (swl b 3))) *
        (fe5 (lanes s 0 (swl b 0)) - fe5 (lanes s 0 (swl b 1))) ∧
      fe5 (lanes s' 0 3) = (fe5 (lanes s 0 (swl b 2)) - fe5 (lanes s 0 (swl b 3))) *
        (fe5 (lanes s 0 (swl b 0)) + fe5 (lanes s 0 (swl b 1))) := by
  have hr := hs.rdi
  simp only [stage1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (s1a_wp hr (scr_ctx hs) hk.c hy) fun s₁ ⟨v₁, m₁, u₁, k₁⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  have hm₁ : ∀ l < 4, qw s₁ (xr 15) l = VG.Proof.X25519.X86_64.mask b := fun l hl => by
    rw [k₁ 15 (by decide) (by decide) (by decide) l hl]; exact hm l hl
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁.rdi (scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2) fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have hm₂ : ∀ l < 4, qw s₂ (xr 15) l = VG.Proof.X25519.X86_64.mask b := fun l hl => by
    rw [k₂ 15 (by decide) (by decide) (by decide) l hl]; exact hm₁ l hl
  rw [WP.block_append_iff]
  refine WP.mono (s1b_wp hs₂.rdi (scr_ctx hs₂) hk₂ hm₂) fun s₃ ⟨v₃, m₃, u₃⟩ => ?_
  have hs₃ := scr_of hs₂ (vm_gpr v₃) (vm_wr v₃)
  have bU : ∀ l < 4, ∀ i < 5, lanes s₃ 10 l i < 2 ^ 52 := fun l hl i hi => by
    rw [(u₃ l hl i hi).1]; exact (u₂ _ (pu_lt b hl) i hi).2
  have bV : ∀ l < 4, ∀ i < 5, lanes s₃ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [(u₃ l hl i hi).2]; exact (u₂ _ (pv_lt b hl) i hi).2
  refine WP.mono (mulG0_wp hs₃.rdi (scr_ctx hs₃) bU bV) fun s₄ ⟨⟨v₄, m₄, u₄, _⟩, _⟩ => ?_
  have K : Kept base s s₄ :=
    (((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans (Kept.vm v₄ m₄)
  -- the values of the lanes
  have fU : ∀ l < 4, fe5 (lanes s₂ 0 l) = fe5 (fun i => sumDiff (lanes s 0) l i) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega_using [this])]
    exact fe5_congr fun i hi => (u₁ l hl i hi).1
  have hle : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ kbv i := fun l hl i hi => le_kbv i (hy l hl i hi)
  have f0 : fe5 (fun i => sumDiff (lanes s 0) 0 i) = fe5 (lanes s 0 0) - fe5 (lanes s 0 1) :=
    fe5_sub (fun i _ => rfl) (hle 1 (by decide))
  have f1 : fe5 (fun i => sumDiff (lanes s 0) 1 i) = fe5 (lanes s 0 0) + fe5 (lanes s 0 1) :=
    fe5_add fun i _ => rfl
  have f2 : fe5 (fun i => sumDiff (lanes s 0) 2 i) = fe5 (lanes s 0 2) - fe5 (lanes s 0 3) :=
    fe5_sub (fun i _ => rfl) (hle 3 (by decide))
  have f3 : fe5 (fun i => sumDiff (lanes s 0) 3 i) = fe5 (lanes s 0 2) + fe5 (lanes s 0 3) :=
    fe5_add fun i _ => rfl
  have fM : ∀ l < 4, fe5 (lanes s₄ 0 l) = fe5 (lanes s₂ 0 (pu b l)) * fe5 (lanes s₂ 0 (pv b l)) :=
    fun l hl => by
      have e4 : ∀ i < 5, lanes s₄ 0 l i = mulNat (lanes s₃ 10 l) (lanes s₃ 5 l) i := fun i hi => by
        rw [(u₄ l hl i hi).1]; simp
      rw [fe5_congr e4, fe5_mul (bU l hl) (bV l hl), fe5_congr (fun i hi => (u₃ l hl i hi).1),
        fe5_congr (fun i hi => (u₃ l hl i hi).2)]
  refine ⟨K, fun l hl i hi => (u₄ l hl i hi).2.2 rfl, ?_, ?_, ?_, ?_⟩
  · rw [fM 0 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 0 (by decide), f0] | rw [fU 2 (by decide), f2]
  · rw [fM 1 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 1 (by decide), f1] | rw [fU 3 (by decide), f3]
  · rw [fM 2 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 3 (by decide), fU 0 (by decide), f3, f0] | rw [fU 1 (by decide), fU 2 (by decide), f1, f2]
  · rw [fM 3 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 2 (by decide), fU 1 (by decide), f2, f1] | rw [fU 0 (by decide), fU 3 (by decide), f0, f3]

end VG.Proof.X25519.X86_64.Ifma
