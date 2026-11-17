module

public import VerifiedGarbage.Proof.Framework.Arm.StraightNot
public import VerifiedGarbage.Proof.Framework.Arm.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Anf32
public import VerifiedGarbage.Proof.Sha3.Spec
public import VerifiedGarbage.Proof.Sha3.Arm.Lit
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Arm.StraightNot
meta import VerifiedGarbage.Proof.Framework.Arm.Linear
meta import VerifiedGarbage.Proof.Framework.Bitslice.Anf32
meta import VerifiedGarbage.Proof.Sha3.Spec
meta import VerifiedGarbage.Proof.Sha3.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Keccak-f[1600] on ARMv7: the interleaved lanes, by evaluation

The blocks of `Impl/Sha3/Arm.lean` that compute on the interleaved lanes are
checked by evaluating their code (`Framework/Arm/Straight.lean`):

* θ, ρ, π and χ of a round (`roundCore src dst`), over the ANF domain for
  32-bit words (`Bitslice.Anf32`), the 50 words of the state at `src`, as
  stored, being the atoms: what the code stores at `dst` is compared with
  the round computed from the specification's `out` on the halves of the
  lanes, rotated as each word is stored (`specP`, `specP_rel`);
* the prologue's `enter` and the epilogue's `leave`, over the lane domain
  (`Bitslice.Lanes`), the bits of the 50 words they read being the atoms:
  every bit of every word of the state they store is compared with the bit
  of the lanes that it is (`inBit`, `outBit`), and the words of the round
  constants that `enter` stores with their halves.
-/

-- separate module: its checks by evaluation cost more than its imports, and `Permute`'s proofs
-- then do not repeat them

@[expose] public section

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Bitslice.Anf VG.Impl.Sha3.Arm
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Proof.Sha3 (C D B out rotl)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## The halves of a lane -/

theorem testBit_evenBits (n : Nat) : ∀ (x i : Nat),
    (evenBits x n).testBit i = (decide (i < n) && x.testBit (2 * i)) := by
  induction n with
  | zero => intro x i; simp [evenBits]
  | succ n ih =>
    intro x i
    cases i with
    | zero =>
      rw [evenBits, Nat.mul_zero, Nat.testBit_zero, Nat.testBit_zero, Nat.add_mul_mod_self_left, Nat.mod_mod]
      simp
    | succ i =>
      rw [evenBits, Nat.testBit_succ, show (x % 2 + 2 * evenBits (x / 4) n) / 2 = evenBits (x / 4) n by omega_arith,
        ih, show 2 * (i + 1) = 2 * i + 1 + 1 from rfl, Nat.testBit_succ, Nat.testBit_succ, Nat.div_div_eq_div_mul]
      simp

theorem getLsbD_half (h : Nat) (x : Lane) (i : Nat) :
    (half h x).getLsbD i = (decide (i < 32) && x.getLsbD (2 * i + h)) := by
  rw [half, BitVec.getLsbD_ofNat, testBit_evenBits, Nat.testBit_shiftRight, BitVec.testBit_toNat,
    Nat.add_comm h, ← Bool.and_assoc, Bool.and_self]

theorem half_xor (h : Nat) (a b : Lane) : half h (a ^^^ b) = half h a ^^^ half h b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_half, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]

theorem half_and (h : Nat) (a b : Lane) : half h (a &&& b) = half h a &&& half h b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_half, BitVec.getLsbD_and, hi, decide_true, Bool.true_and]

theorem half_ones {h : Nat} (hh : h < 2) : half h (0xffffffffffffffff : Lane) = BitVec.allOnes 32 := by
  have : h = 0 ∨ h = 1 := by omega_arith
  rcases this with rfl | rfl <;> decide

/-- A rotation of a lane by `n`, when it takes the bits of half `h` from
those of half `h'`, `k` further. -/
theorem half_rotr {n k h h' : Nat} (hh : h < 2)
    (hn : ∀ i < 32, (2 * i + h + n) % 64 = 2 * ((i + k) % 32) + h') (v : Lane) :
    half h (v.rotateRight n) = (half h' v).rotateRight k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_half, getLsbD_rotateRight_lt _ _ _ (show 2 * i + h < 64 by omega_using [hi, hh]),
    getLsbD_rotateRight_lt _ _ _ hi, getLsbD_half, hn i hi]
  simp only [hi, decide_true, Bool.true_and, Nat.mod_lt _ (show 0 < 32 by decide)]

/-! ## Rotations of 32-bit words -/

theorem ror_ror (x : BitVec 32) (a b : Nat) : (x.rotateRight a).rotateRight b = x.rotateRight (a + b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_rotateRight_lt _ _ _ hi, getLsbD_rotateRight_lt _ _ _ (Nat.mod_lt _ (by decide)),
    getLsbD_rotateRight_lt _ _ _ hi]
  congr 1
  omega_arith

theorem ror_of_mod {n : Nat} (h : n % 32 = 0) (x : BitVec 32) : x.rotateRight n = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_rotateRight_lt _ _ _ hi]
  congr 1
  omega_using [h, hi]

/-! ## The state as stored -/

theorem sub32_lt (a b : Nat) : sub32 a b < 32 := Nat.mod_lt _ (by decide)

theorem rot_lt (j h : Nat) : rot j h < 32 := by
  unfold rot; split
  · decide
  · exact sub32_lt _ _

/-- Half `h` of lane `j`, of value `v`, as stored: rotated left by `rot j h`. -/
def stw (v : Lane) (j h : Nat) : BitVec 32 := (half h v).rotateRight (sub32 0 (rot j h))

theorem stw_ror (v : Lane) (j h : Nat) : (stw v j h).rotateRight (rot j h) = half h v := by
  rw [stw, ror_ror]
  exact ror_of_mod (by have := rot_lt j h; simp only [sub32]; omega_arith) _

/-- Lane 0 is stored as its halves. -/
theorem stw_zero (v : Lane) (h : Nat) : stw v 0 h = half h v :=
  ror_of_mod (by simp only [rot, ite_true]; decide) _

/-! ## The round over the ANF domain -/

/-- Half `h` of lane `j` of the input, from the word as stored (atom `2 j + h`). -/
def sT (j h : Nat) : Poly := pror32 (rot j h) (atom (2 * j + h))

def sC (x h : Nat) : Poly :=
  pxor (pxor (pxor (pxor (sT x h) (sT (x + 5) h)) (sT (x + 10) h)) (sT (x + 15) h)) (sT (x + 20) h)

def sD (x h : Nat) : Poly :=
  if h = 0 then pxor (pror32 31 (sC ((x + 1) % 5) 1)) (sC ((x + 4) % 5) 0)
  else pxor (sC ((x + 1) % 5) 0) (sC ((x + 4) % 5) 1)

def sB (x y h : Nat) : Poly :=
  let r := rotSrc (rhoOff (piSrc x y)) h
  pror32 (sub32 0 r.2) (pxor (sT (piSrc x y) r.1) (sD ((x + 3 * y) % 5) r.1))

def sOut (x y h : Nat) : Poly :=
  pxor (pand (pxor (sB ((x + 1) % 5) y h) one) (sB ((x + 2) % 5) y h)) (sB x y h)

/-- Word `m` (half `m % 2` of lane `m / 2`) of the round's output before ι, as stored. -/
def specP (m : Nat) : Poly := pror32 (sub32 0 (rot (m / 2) (m % 2))) (sOut (m / 2 % 5) (m / 2 / 5) (m % 2))

/-! ## The checks -/

/-- The output state at `dst` (slots), the input state at `src` (external words). -/
def cfg (src dst : Reg) : Cfg := { base := dst, slots := 50, ext := src, exts := 50 }

def atoms (k : Nat) : Option Poly := some (atom k)

def env₀ : Env Poly := { reg := fun _ => none, slot := fun _ => none }

def post (e : Env Poly) : Bool := (List.range 50).all fun m => e.slot m == some (specP m)

theorem coreA_check : checkN anf32 (cfg .r1 .r0) atoms (instrs coreA.lit) env₀ post = true := by
  lit_decide

theorem coreB_check : checkN anf32 (cfg .r0 .r1) atoms (instrs coreB.lit) env₀ post = true := by
  lit_decide

theorem coreA_code : instrs coreA.lit = roundCore .r1 .r0 := by rw [← coreA.lit_eq]; rfl

theorem coreB_code : instrs coreB.lit = roundCore .r0 .r1 := by rw [← coreB.lit_eq]; rfl

theorem coreA_ok : checkN anf32 (cfg .r1 .r0) atoms (roundCore .r1 .r0) env₀ post = true := by
  rw [← coreA_code]; exact coreA_check

theorem coreB_ok : checkN anf32 (cfg .r0 .r1) atoms (roundCore .r0 .r1) env₀ post = true := by
  rw [← coreB_code]; exact coreB_check

/-! ## What the polynomials are -/

section
variable {V : Nat → BitVec 32} {K : KState}

/-- The atoms are the words of `K`, as stored. -/
def IsStored (V : Nat → BitVec 32) (K : KState) : Prop :=
  ∀ j < 25, ∀ h < 2, V (2 * j + h) = stw K[j]! j h

theorem rel_xor {p q : Poly} {x y : BitVec 32} (hp : Anf32Rel V p x) (hq : Anf32Rel V q y) :
    Anf32Rel V (pxor p q) (x ^^^ y) := by
  simp only [Anf32Rel] at *; rw [eval_pxor, hp, hq, dbl_xor]

theorem rel_and {p q : Poly} {x y : BitVec 32} (hp : Anf32Rel V p x) (hq : Anf32Rel V q y) :
    Anf32Rel V (pand p q) (x &&& y) := by
  simp only [Anf32Rel] at *; rw [eval_pand, hp, hq, dbl_and]

theorem rel_ror {p : Poly} {x : BitVec 32} (n : Nat) (hp : Anf32Rel V p x) :
    Anf32Rel V (pror32 n p) (x.rotateRight n) := by
  simp only [Anf32Rel] at *; rw [eval_pror32, hp, dbl_ror]

theorem rel_one : Anf32Rel V one (BitVec.allOnes 32) := by
  simp only [Anf32Rel]; rw [eval_one, dbl_ones]

theorem sT_rel (hV : IsStored V K) {j h : Nat} (hj : j < 25) (hh : h < 2) :
    Anf32Rel V (sT j h) (half h K[j]!) := by
  have := rel_ror (rot j h) (anf32Rel_atom V (2 * j + h))
  rw [hV j hj h hh, stw_ror] at this
  exact this

theorem sC_rel (hV : IsStored V K) {x h : Nat} (hx : x < 5) (hh : h < 2) :
    Anf32Rel V (sC x h) (half h (C K x)) := by
  simp only [C, half_xor]
  exact rel_xor (rel_xor (rel_xor (rel_xor (sT_rel hV (by omega_using [hx]) hh)
    (sT_rel hV (by omega_using [hx]) hh)) (sT_rel hV (by omega_using [hx]) hh))
    (sT_rel hV (by omega_using [hx]) hh)) (sT_rel hV (by omega_using [hx]) hh)

theorem sD_rel (hV : IsStored V K) (x : Nat) {h : Nat} (hh : h < 2) :
    Anf32Rel V (sD x h) (half h (D K x)) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by decide)
  unfold sD D
  rw [half_xor]
  split
  · rename_i h0; subst h0
    rw [half_rotr (k := 31) (h' := 1) (by decide) (by decide)]
    exact rel_xor (rel_ror 31 (sC_rel hV h1 (by decide))) (sC_rel hV h4 (by decide))
  · rename_i h0
    have e : h = 1 := by omega_using [hh, h0]
    subst e
    rw [half_rotr (k := 0) (h' := 0) (by decide) (by decide), ror_of_mod (by decide)]
    exact rel_xor (sC_rel hV h1 (by decide)) (sC_rel hV h4 (by decide))

theorem rotSrc_lt (ρ : Nat) {h : Nat} (hh : h < 2) : (rotSrc ρ h).1 < 2 := by
  unfold rotSrc; split
  · exact hh
  · split
    · exact (by decide : 1 < 2)
    · exact (by decide : 0 < 2)

/-- `rotSrc`: where a rotation left takes the bits of each half from. -/
theorem rotSrc_ok : ∀ ρ < 64, ∀ h < 2, ∀ i < 32,
    (2 * i + h + (64 - ρ)) % 64 = 2 * ((i + sub32 0 (rotSrc ρ h).2) % 32) + (rotSrc ρ h).1 := by
  decide +kernel

theorem half_rotl (v : Lane) {ρ h : Nat} (hρ : ρ < 64) (hh : h < 2) :
    half h (rotl v ρ) = (half (rotSrc ρ h).1 v).rotateRight (sub32 0 (rotSrc ρ h).2) := by
  unfold rotl; split
  · rename_i h0; subst h0
    rw [ror_of_mod (by simp [rotSrc, sub32])]
    simp [rotSrc]
  · exact half_rotr hh (rotSrc_ok ρ hρ h hh) v

theorem sB_rel (hV : IsStored V K) {x y h : Nat} (hx : x < 5) (hh : h < 2) :
    Anf32Rel V (sB x y h) (half h (B K x y)) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega_using [hx]
  have hh' := rotSrc_lt (rhoOff (piSrc x y)) hh
  unfold sB B
  rw [half_rotl _ (Proof.Sha3.rhoOff_lt _ hj) hh, half_xor]
  exact rel_ror _ (rel_xor (sT_rel hV hj hh') (sD_rel hV _ hh'))

/-- The round's output without ι. -/
theorem out_zero (K : KState) (x y : Nat) :
    out K 0 x y = (B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^ B K x y := by
  unfold out; split <;> simp

theorem sOut_rel (hV : IsStored V K) {x y h : Nat} (hx : x < 5) (hh : h < 2) :
    Anf32Rel V (sOut x y h) (half h (out K 0 x y)) := by
  rw [out_zero, half_xor, half_and, half_xor, half_ones hh]
  exact rel_xor (rel_and (rel_xor (sB_rel hV (Nat.mod_lt _ (by decide)) hh) rel_one)
    (sB_rel hV (Nat.mod_lt _ (by decide)) hh)) (sB_rel hV hx hh)

theorem specP_rel (hV : IsStored V K) (m : Nat) :
    Anf32Rel V (specP m) (stw (out K 0 (m / 2 % 5) (m / 2 / 5)) (m / 2) (m % 2)) :=
  rel_ror _ (sOut_rel hV (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))

end

/-! ## θ, ρ, π and χ on the machine -/

/-- The state at `b` holds `K`, interleaved. -/
def Stored (m : Mem) (b : BitVec 32) (K : KState) : Prop :=
  ∀ j < 25, ∀ h < 2, m.readW (wordAddr b (2 * j + h)) 32 = stw K[j]! j h

/-- θ, ρ, π and χ from the state at `src` to the state at `dst`: every word
of the round's output but for ι, as stored. -/
theorem core_ok {src dst : Reg} {is : List Instr}
    (hc : checkN anf32 (cfg src dst) atoms is env₀ post = true) {s : State} {K : KState}
    (hok : Ok (cfg src dst) s) (hK : Stored s.mem (s.gpr src) K) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ m < 50, s'.mem.readW (wordAddr (s.gpr dst) m) 32 =
        stw (out K 0 (m / 2 % 5) (m / 2 / 5)) (m / 2) (m % 2)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr src = s.gpr src ∧ s'.gpr dst = s.gpr dst ∧
      Frame [⟨State.addr (s.gpr dst), 200⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_checkN _ _ _ hc
  let V : Nat → BitVec 32 := fun m => s.mem.readW (wordAddr (s.gpr src) m) 32
  have hV : IsStored V K := fun j hj h hh => hK j hj h hh
  have hrel : Rel (Anf32Rel V) (cfg src dst) atoms env₀ s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun k a _ h => ?_),
      (fun _ _ h => by cases h)⟩
    simp only [atoms, Option.some.injEq] at h
    subst h
    exact anf32Rel_atom V k
  obtain ⟨s', hs', p⟩ := runN (anf32_sound V) hok hrel he
  refine ⟨s', hs', fun m hm => ?_, p.rd, p.wr, p.sp, p.ext, p.base, p.frame⟩
  have h := p.rel.slot m _ hm (beq_iff_eq.mp (List.all_eq_true.mp hpost m (List.mem_range.mpr hm)))
  rw [p.base] at h
  exact Anf32Rel.unique V h (specP_rel hV m)

/-! ## To and from the interleaved lanes -/

/-- The atom that bit `p` of word `m` of the state as stored is, the atoms
being the bits of the state's lanes (bit `b` of lane `j` is atom `64 j + b`). -/
def inBit (m p : Nat) : List Nat :=
  [64 * (m / 2) + (2 * ((p + sub32 0 (rot (m / 2) (m % 2))) % 32) + m % 2)]

/-- The interleaved state and the round constants (slots), the state
(external words). -/
def cfgIn : Cfg := { base := .r1, slots := 98, ext := .r0, exts := 50 }

def envL : Env (Nat × Nat) := { reg := fun _ => none, slot := fun _ => none }

def postIn (e : Env (Nat × Nat)) : Bool :=
  ((List.range 50).all fun m => e.slot m == some (outWord (inBit m))) &&
    (List.range 48).all fun i => e.slot (50 + i) == some ((half (i % 2) (Spec.Sha3.RC (i / 2))).toNat, 0)

theorem enter_check : check (lanes 32 11) cfgIn (linExt 0) (instrs enterCode.lit) envL postIn = true := by
  lit_decide

theorem enter_code : instrs enterCode.lit = enter := by rw [← enterCode.lit_eq]; rfl

/-- The atom that bit `p` of word `m` of the state is, the atoms being the
bits of the words of the state as stored (bit `t` of word `i` is atom
`32 i + t`). -/
def outBit (m p : Nat) : List Nat :=
  [32 * (2 * (m / 2) + (32 * (m % 2) + p) % 2) +
    ((32 * (m % 2) + p) / 2 + rot (m / 2) ((32 * (m % 2) + p) % 2)) % 32]

def postOut (e : Env (Nat × Nat)) : Bool :=
  (List.range 50).all fun m => e.slot m == some (outWord (outBit m))

theorem leave_check : check (lanes 32 11) (cfg .r1 .r0) (linExt 0) (instrs leaveCode.lit) envL postOut = true := by
  lit_decide

theorem leave_code : instrs leaveCode.lit = leave := by rw [← leaveCode.lit_eq]; rfl

/-- Bit `b` of the lane whose words are words `2 j` and `2 j + 1`. -/
theorem bitOf_lane (W : Nat → BitVec 32) (j : Nat) {b : Nat} (hb : b < 64) :
    bitOf W (64 * j + b) = (W (2 * j + 1) ++ W (2 * j) : BitVec 64).getLsbD b := by
  have e : (W (2 * j + 1) ++ W (2 * j) : BitVec (32 + 32)).getLsbD b =
      if b < 32 then (W (2 * j)).getLsbD b else (W (2 * j + 1)).getLsbD (b - 32) := BitVec.getLsbD_append
  rw [e, bitOf]
  split
  · rename_i h
    rw [show (64 * j + b) / 32 = 2 * j by omega_using [h], show (64 * j + b) % 32 = b by omega_using [h]]
  · rename_i h
    rw [show (64 * j + b) / 32 = 2 * j + 1 by omega_using [h, hb],
      show (64 * j + b) % 32 = b - 32 by omega_using [h, hb]]

/-- A word the lane domain knows as a constant. -/
theorem laneRel_const {k A c : Nat} {x : BitVec 32} (h : LaneRel k A (c, 0) x) : x = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_getLsbD_eq; intro q hq
  rw [h.2 q hq, BitVec.getLsbD_ofNat, par_zero]
  simp [hq]

/-- The prologue's `enter`: the lanes of the state at `r0`, as stored, and
the round constants, at `r1`. -/
theorem enter_ok {s : State} (hok : Ok cfgIn s) :
    ∃ s', runBlock isa enter s = some s' ∧
      (∀ j < 25, ∀ h < 2, s'.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32 =
        stw (s.mem.readW (wordAddr (s.gpr .r0) (2 * j + 1)) 32 ++
          s.mem.readW (wordAddr (s.gpr .r0) (2 * j)) 32) j h) ∧
      (∀ i < 48, s'.mem.readW (wordAddr (s.gpr .r1) (50 + i)) 32 =
        half (i % 2) (Spec.Sha3.RC (i / 2))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      Frame [⟨State.addr (s.gpr .r1), 392⟩] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => s.mem.readW (wordAddr (s.gpr .r0) i) 32
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ enter_check
  rw [enter_code] at he
  have hrel : Rel (LaneRel 11 (assign W (2 ^ 11))) cfgIn (linExt 0) envL s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun j a hj h => ?_),
      (fun _ _ h => by cases h)⟩
    simp only [linExt, Option.some.injEq, Nat.zero_add] at h
    subst h
    exact inWord_rel W (by have : j < 50 := hj; omega_using [this])
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [postIn, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hs', fun j hj h hh => ?_, fun i hi => ?_, p.rd, p.wr, p.sp, p.ext, p.base, p.frame⟩
  · have hs : LaneRel 11 (assign W (2 ^ 11)) (outWord (inBit (2 * j + h)))
        (s'.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32) := by
      have := p.rel.slot (2 * j + h) _ (show 2 * j + h < 98 by omega_using [hj, hh])
        (hpost.1 _ (by omega_using [hj, hh]))
      rw [p.base] at this
      exact this
    have bits := outWord_rel (fun q _ a ha => by
      simp only [inBit, List.mem_singleton] at ha; subst ha; omega_using [hj, hh]) hs
    apply BitVec.eq_of_getLsbD_eq; intro q hq
    have hm : (q + sub32 0 (rot j h)) % 32 < 32 := Nat.mod_lt _ (by decide)
    rw [bits q hq, stw, getLsbD_rotateRight_lt _ _ _ hq, getLsbD_half]
    simp only [inBit, xorBits_cons, xorBits_nil, Bool.xor_false, hm, decide_true, Bool.true_and,
      show (2 * j + h) / 2 = j by omega_using [hh], show (2 * j + h) % 2 = h by omega_using [hh]]
    exact bitOf_lane W j (by omega_using [hm, hh])
  · have hs : LaneRel 11 (assign W (2 ^ 11)) ((half (i % 2) (Spec.Sha3.RC (i / 2))).toNat, 0)
        (s'.mem.readW (wordAddr (s.gpr .r1) (50 + i)) 32) := by
      have := p.rel.slot (50 + i) _ (show 50 + i < 98 by omega_using [hi]) (hpost.2 i hi)
      rw [p.base] at this
      exact this
    rw [laneRel_const hs, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The epilogue's `leave`: the lanes of the state stored at `r1`, at `r0`. -/
theorem leave_ok {s : State} {K : KState} (hok : Ok (cfg .r1 .r0) s) (hK : Stored s.mem (s.gpr .r1) K) :
    ∃ s', runBlock isa leave s = some s' ∧
      (∀ j < 25, (s'.mem.readW (wordAddr (s.gpr .r0) (2 * j + 1)) 32 ++
        s'.mem.readW (wordAddr (s.gpr .r0) (2 * j)) 32 : BitVec 64) = K[j]!) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      Frame [⟨State.addr (s.gpr .r0), 200⟩] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => s.mem.readW (wordAddr (s.gpr .r1) i) 32
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ leave_check
  rw [leave_code] at he
  have hrel : Rel (LaneRel 11 (assign W (2 ^ 11))) (cfg .r1 .r0) (linExt 0) envL s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun j a hj h => ?_),
      (fun _ _ h => by cases h)⟩
    simp only [linExt, Option.some.injEq, Nat.zero_add] at h
    subst h
    exact inWord_rel W (by have : j < 50 := hj; omega_using [this])
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [postOut, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  -- Bit `q` of word `m` is bit `32 (m % 2) + q` of lane `m / 2`.
  have word : ∀ m < 50, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .r0) m) 32).getLsbD q =
      (K[m / 2]!).getLsbD (32 * (m % 2) + q) := by
    intro m hm q hq
    have hs : LaneRel 11 (assign W (2 ^ 11)) (outWord (outBit m))
        (s'.mem.readW (wordAddr (s.gpr .r0) m) 32) := by
      have := p.rel.slot m _ hm (hpost m hm)
      rw [p.base] at this
      exact this
    have bits := outWord_rel (fun q _ a ha => by
      simp only [outBit, List.mem_singleton] at ha; subst ha; omega_using [hm]) hs
    have hr := rot_lt (m / 2) ((32 * (m % 2) + q) % 2)
    rw [bits q hq]
    simp only [outBit, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word W _ _ (Nat.mod_lt _ (by decide)),
      show W (2 * (m / 2) + (32 * (m % 2) + q) % 2) = stw K[m / 2]! (m / 2) ((32 * (m % 2) + q) % 2) from
        hK _ (by omega_using [hm]) _ (Nat.mod_lt _ (by decide)),
      stw, getLsbD_rotateRight_lt _ _ _ (Nat.mod_lt _ (by decide)), getLsbD_half]
    generalize rot (m / 2) ((32 * (m % 2) + q) % 2) = r at hr
    simp only [sub32, Nat.mod_lt _ (show 0 < 32 by decide), decide_true, Bool.true_and]
    refine congrArg (BitVec.getLsbD _) ?_
    omega_using [hq, hr]
  refine ⟨s', hs', fun j hj => ?_, p.rd, p.wr, p.sp, p.base, p.ext, p.frame⟩
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have e : ∀ x y : BitVec 32, (x ++ y : BitVec (32 + 32)).getLsbD b =
      if b < 32 then y.getLsbD b else x.getLsbD (b - 32) := fun _ _ => BitVec.getLsbD_append
  rw [e]
  split
  · rename_i h
    rw [word (2 * j) (by omega_using [hj]) b h, show 2 * j / 2 = j by omega_using [],
      show 2 * j % 2 = 0 by omega_using [], Nat.mul_zero, Nat.zero_add]
  · rename_i h
    rw [word (2 * j + 1) (by omega_using [hj]) (b - 32) (by omega_using [h, hb]),
      show (2 * j + 1) / 2 = j by omega_using [], show (2 * j + 1) % 2 = 1 by omega_using [],
      show 32 * 1 + (b - 32) = b by omega_using [h]]

/-- `Ok` for slots in a writable region at `Bs` and external words in
another, at `Es`, that does not overlap it. -/
theorem ok_of {c : Cfg} {s : State} {Bs Es : BitVec 32} {lb le : Nat} (hb : s.gpr c.base = Bs)
    (he : s.gpr c.ext = Es) (hB : (⟨State.addr Bs, lb⟩ : Region) ∈ s.wr)
    (hE : (⟨State.addr Es, le⟩ : Region) ∈ s.wr) (fB : Bs.toNat + lb ≤ 2 ^ 32)
    (fE : Es.toNat + le ≤ 2 ^ 32) (hs : 4 * c.slots ≤ lb) (hx : 4 * c.exts ≤ le)
    (hd : Region.Disjoint ⟨State.addr Bs, lb⟩ ⟨State.addr Es, le⟩) : Ok c s where
  slotIn k hk := by rw [hb]; exact in_off hB fB (by omega_using [hs, hk]) (by decide)
  extIn k hk := by
    rw [he]; exact in_off (List.mem_append_right _ hE) fE (by omega_using [hx, hk]) (by decide)
  slots := by rw [hb]; omega_using [fB, hs]
  sep k hk j hj := by
    rw [hb, he]
    exact hd.sep (contains_off fB (by omega_using [hs, hk]) (by decide))
      (contains_off fE (by omega_using [hx, hj]) (by decide))

end VG.Proof.Sha3.Arm
