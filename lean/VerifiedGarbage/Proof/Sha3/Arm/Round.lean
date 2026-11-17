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
* `enter` and `leave`, over the lane domain (`Bitslice.Lanes`), the bits of
  the 50 words they read being the atoms: every bit of every word of the
  state they store is compared with the bit of the lanes that it is
  (`inBit`, `outBit`), and the words of the round constants that `enter`
  stores with their halves;
* the lanes of a block that the sponge's functions XOR into the interleaved
  state (`xorSeg`) and copy out of it (`copySeg`), likewise, for each run of
  lanes between two rates (`segs`).
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

theorem stw_xor (a b : Lane) (j h : Nat) : stw (a ^^^ b) j h = stw a j h ^^^ stw b j h := by
  rw [stw, stw, stw, half_xor]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, getLsbD_rotateRight_lt _ _ _ hi, getLsbD_rotateRight_lt _ _ _ hi,
    getLsbD_rotateRight_lt _ _ _ hi, BitVec.getLsbD_xor]

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

/-- The first `2 n` words at `d` (slots), the interleaved state (external
words). -/
def cfgC (d : Reg) (n : Nat) : Cfg := { base := d, slots := 2 * n, ext := .r1, exts := 50 }

/-- The slots are the words of the lanes `a ≤ j < a + n` of the state. -/
def postC (a n : Nat) (e : Env (Nat × Nat)) : Bool :=
  (List.range (2 * n)).all fun m => e.slot m == some (outWord (outBit (2 * a + m)))

theorem leave_check :
    check (lanes 32 11) (cfgC .r0 25) (linExt 0) (instrs leaveCode.lit) envL (postC 0 25) = true := by
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

/-- A block that stores at `d` the lanes `a ≤ j < a + n` of the state stored
at `r1`. -/
theorem out_ok {d : Reg} {a n : Nat} {is : List Instr} {e : Env (Nat × Nat)}
    (hc : check (lanes 32 11) (cfgC d n) (linExt 0) is e (postC a n) = true) (han : a + n ≤ 25)
    {s : State} {K : KState} (hok : Ok (cfgC d n) s) (hK : Stored s.mem (s.gpr .r1) K)
    (hreg : ∀ r v, e.reg r = some v → ∀ A, LaneRel 11 A v (s.gpr r)) (hslot : ∀ k, e.slot k = none)
    (hcst : ∀ r, e.cst r = none) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ i < n, (s'.mem.readW (wordAddr (s.gpr d) (2 * i + 1)) 32 ++
        s'.mem.readW (wordAddr (s.gpr d) (2 * i)) 32 : BitVec 64) = K[a + i]!) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr d = s.gpr d ∧ s'.gpr .r1 = s.gpr .r1 ∧
      (∀ r, (is.all fun i => !clobbers i r) = true → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr (s.gpr d), 4 * (2 * n)⟩] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => s.mem.readW (wordAddr (s.gpr .r1) i) 32
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hc
  have hrel : Rel (LaneRel 11 (assign W (2 ^ 11))) (cfgC d n) (linExt 0) e s := by
    refine ⟨(fun r v h => hreg r v h _), (fun k _ _ h => by rw [hslot k] at h; cases h),
      (fun j a hj h => ?_), (fun r _ h => by rw [hcst r] at h; cases h)⟩
    simp only [linExt, Option.some.injEq, Nat.zero_add] at h
    subst h
    exact inWord_rel W (by have : j < 50 := hj; omega_using [this])
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [postC, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  -- Bit `q` of word `m` is bit `32 (M % 2) + q` of lane `M / 2`, for `M = 2 a + m`.
  have word : ∀ m < 2 * n, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr d) m) 32).getLsbD q =
      (K[(2 * a + m) / 2]!).getLsbD (32 * ((2 * a + m) % 2) + q) := by
    intro m hm q hq
    have hs : LaneRel 11 (assign W (2 ^ 11)) (outWord (outBit (2 * a + m)))
        (s'.mem.readW (wordAddr (s.gpr d) m) 32) := by
      have := p.rel.slot m _ hm (hpost m hm)
      rw [p.base] at this
      exact this
    generalize hM : 2 * a + m = M at hs ⊢
    have hM50 : M < 50 := by omega_using [hM, hm, han]
    have bits := outWord_rel (fun q _ a ha => by
      simp only [outBit, List.mem_singleton] at ha; subst ha; omega_using [hM50]) hs
    have hr := rot_lt (M / 2) ((32 * (M % 2) + q) % 2)
    rw [bits q hq]
    simp only [outBit, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word W _ _ (Nat.mod_lt _ (by decide)),
      show W (2 * (M / 2) + (32 * (M % 2) + q) % 2) = stw K[M / 2]! (M / 2) ((32 * (M % 2) + q) % 2) from
        hK _ (by omega_using [hM50]) _ (Nat.mod_lt _ (by decide)),
      stw, getLsbD_rotateRight_lt _ _ _ (Nat.mod_lt _ (by decide)), getLsbD_half]
    generalize rot (M / 2) ((32 * (M % 2) + q) % 2) = r at hr
    simp only [sub32, Nat.mod_lt _ (show 0 < 32 by decide), decide_true, Bool.true_and]
    refine congrArg (BitVec.getLsbD _) ?_
    omega_using [hq, hr]
  refine ⟨s', hs', fun i hi => ?_, p.rd, p.wr, p.sp, p.base, p.ext,
    fun r hr => p.other r (by rw [hr]; exact Bool.noConfusion), p.frame⟩
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have e : ∀ x y : BitVec 32, (x ++ y : BitVec (32 + 32)).getLsbD b =
      if b < 32 then y.getLsbD b else x.getLsbD (b - 32) := fun _ _ => BitVec.getLsbD_append
  rw [e]
  split
  · rename_i h
    rw [word (2 * i) (by omega_using [hi]) b h, show (2 * a + 2 * i) / 2 = a + i by omega_using [],
      show (2 * a + 2 * i) % 2 = 0 by omega_using [], Nat.mul_zero, Nat.zero_add]
  · rename_i h
    rw [word (2 * i + 1) (by omega_using [hi]) (b - 32) (by omega_using [h, hb]),
      show (2 * a + (2 * i + 1)) / 2 = a + i by omega_using [],
      show (2 * a + (2 * i + 1)) % 2 = 1 by omega_using [], show 32 * 1 + (b - 32) = b by omega_using [h]]

/-- `leave`: the lanes of the state stored at `r1`, at `r0`. -/
theorem leave_ok {s : State} {K : KState} (hok : Ok (cfg .r1 .r0) s) (hK : Stored s.mem (s.gpr .r1) K) :
    ∃ s', runBlock isa leave s = some s' ∧
      (∀ j < 25, (s'.mem.readW (wordAddr (s.gpr .r0) (2 * j + 1)) 32 ++
        s'.mem.readW (wordAddr (s.gpr .r0) (2 * j)) 32 : BitVec 64) = K[j]!) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      Frame [⟨State.addr (s.gpr .r0), 200⟩] s.mem s'.mem := by
  have hc := leave_check
  rw [leave_code] at hc
  obtain ⟨s', hs', hl, rd, wr, sp, g0, g1, -, f⟩ := out_ok hc (by decide) hok hK
    (fun _ _ h => by cases h) (fun _ => rfl) (fun _ => rfl)
  exact ⟨s', hs', fun j hj => by rw [hl j hj, Nat.zero_add], rd, wr, sp, g0, g1, f⟩

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

/-- `Ok` for slots at offset `ob` of a writable region at `Bs` and external
words at offset `oe` of another region, at `Es`, that does not overlap it. -/
theorem ok_offs {c : Cfg} {s : State} {Bs Es : BitVec 32} {lb le ob oe : Nat}
    (hb : s.gpr c.base = Bs + BitVec.ofNat 32 ob) (he : s.gpr c.ext = Es + BitVec.ofNat 32 oe)
    (hB : (⟨State.addr Bs, lb⟩ : Region) ∈ s.wr) (hE : (⟨State.addr Es, le⟩ : Region) ∈ s.rd ++ s.wr)
    (fB : Bs.toNat + lb ≤ 2 ^ 32) (fE : Es.toNat + le ≤ 2 ^ 32) (hs : ob + 4 * c.slots ≤ lb)
    (hx : oe + 4 * c.exts ≤ le) (hd : Region.Disjoint ⟨State.addr Bs, lb⟩ ⟨State.addr Es, le⟩) :
    Ok c s := by
  have eb : ∀ k, wordAddr (s.gpr c.base) k = State.addr (Bs + BitVec.ofNat 32 (ob + 4 * k)) := fun k => by
    rw [hb]; exact congrArg State.addr (add_ofNat_ofNat _ _ _)
  have ee : ∀ k, wordAddr (s.gpr c.ext) k = State.addr (Es + BitVec.ofNat 32 (oe + 4 * k)) := fun k => by
    rw [he]; exact congrArg State.addr (add_ofNat_ofNat _ _ _)
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_⟩
  · rw [eb]; exact in_off hB fB (by omega_using [hs, hk]) (by decide)
  · rw [ee]; exact in_off hE fE (by omega_using [hx, hk]) (by decide)
  · rw [hb, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [fB, hs]
  · rw [eb, ee]
    exact hd.sep (contains_off fB (by omega_using [hs, hk]) (by decide))
      (contains_off fE (by omega_using [hx, hj]) (by decide))

/-! ## The lanes of a block -/

/-- The masks of the exchanges, in their registers. -/
def Masks (s : State) : Prop :=
  s.gpr .r4 = 0x0000ffff#32 ∧ s.gpr .r5 = 0x00ff00ff#32 ∧ s.gpr .r6 = 0x0f0f0f0f#32 ∧
    s.gpr .r7 = 0x33333333#32 ∧ s.gpr .r8 = 0x55555555#32

/-- The masks as the evaluator knows them, and the slots `slot`. -/
def envM (slot : Nat → Option (Nat × Nat)) : Env (Nat × Nat) where
  reg r := match r with
    | .r4 => some (0x0000ffff, 0) | .r5 => some (0x00ff00ff, 0) | .r6 => some (0x0f0f0f0f, 0)
    | .r7 => some (0x33333333, 0) | .r8 => some (0x55555555, 0) | _ => none
  slot := slot

/-- A constant, in the lane domain. -/
theorem laneRel_ofNat {k A c : Nat} (hc : c < 2 ^ 32) : LaneRel k A (c, 0) (BitVec.ofNat 32 c) :=
  ⟨hc, fun q hq => by rw [par_zero, Bool.xor_false, BitVec.getLsbD_ofNat]; simp [hq]⟩

theorem rel_masks {s : State} (hm : Masks s) (slot : Nat → Option (Nat × Nat)) (r : Reg) (v : Nat × Nat)
    (h : (envM slot).reg r = some v) (k A : Nat) : LaneRel k A v (s.gpr r) := by
  obtain ⟨h4, h5, h6, h7, h8⟩ := hm
  cases r <;> simp only [envM, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · rw [h4]; exact laneRel_ofNat (by decide)
  · rw [h5]; exact laneRel_ofNat (by decide)
  · rw [h6]; exact laneRel_ofNat (by decide)
  · rw [h7]; exact laneRel_ofNat (by decide)
  · rw [h8]; exact laneRel_ofNat (by decide)

/-- The registers that the lanes of a block leave alone, but the pointers. -/
def keeps (is : List Instr) : Bool :=
  [Reg.r0, .r4, .r5, .r6, .r7, .r8, .r10, .r11].all fun r => is.all fun i => !clobbers i r

theorem keeps_gpr {is : List Instr} (h : keeps is = true) :
    ∀ r ∈ [Reg.r0, .r4, .r5, .r6, .r7, .r8, .r10, .r11], (is.all fun i => !clobbers i r) = true :=
  fun r hr => List.all_eq_true.mp h r hr

/-- The runs of lanes between the rates: the blocks of `Spec.Sha3.rates` are
of 9, 13, 17, 18 and 21 lanes. -/
def segs : List (Nat × Nat) := [(0, 9), (9, 13), (13, 17), (17, 18), (18, 21)]

theorem segs_ok : ∀ p ∈ segs, p.1 ≤ p.2 ∧ p.2 ≤ 21 ∧ p.2 - p.1 ≤ 9 := by decide

/-! ### XORed into the interleaved state -/

/-- The words of the lanes below 21 of the interleaved state (slots), and
`n` lanes of the block (external words). -/
def cfgX (n : Nat) : Cfg := { base := .r1, slots := 42, ext := .r9, exts := 2 * n }

/-- The atoms are the bits of the words of the interleaved state (bit `t`
of word `m` is atom `32 m + t`) and, after them, those of the block. -/
def envX : Env (Nat × Nat) := envM fun m => if m < 42 then some (inWord m) else none

/-- The atoms of bit `p` of word `m` of the interleaved state, after the
lanes `a ≤ j < b` of the block: the bit, and for a word of those lanes the
bit of the block's lane that is stored there. -/
def xorBit (a b m p : Nat) : List Nat :=
  if a ≤ m / 2 ∧ m / 2 < b then
    [32 * m + p, 64 * (21 + (m / 2 - a)) + (2 * ((p + sub32 0 (rot (m / 2) (m % 2))) % 32) + m % 2)]
  else [32 * m + p]

def postX (a b : Nat) (e : Env (Nat × Nat)) : Bool :=
  (List.range 42).all fun m => e.slot m == some (outWord (xorBit a b m))

theorem xorA_check : (check (lanes 32 11) (cfgX 9) (linExt 42) (instrs xorA.lit) envX (postX 0 9) &&
    keeps (instrs xorA.lit)) = true := by lit_decide
theorem xorB_check : (check (lanes 32 11) (cfgX 4) (linExt 42) (instrs xorB.lit) envX (postX 9 13) &&
    keeps (instrs xorB.lit)) = true := by lit_decide
theorem xorC_check : (check (lanes 32 11) (cfgX 4) (linExt 42) (instrs xorC.lit) envX (postX 13 17) &&
    keeps (instrs xorC.lit)) = true := by lit_decide
theorem xorD_check : (check (lanes 32 11) (cfgX 1) (linExt 42) (instrs xorD.lit) envX (postX 17 18) &&
    keeps (instrs xorD.lit)) = true := by lit_decide
theorem xorE_check : (check (lanes 32 11) (cfgX 3) (linExt 42) (instrs xorE.lit) envX (postX 18 21) &&
    keeps (instrs xorE.lit)) = true := by lit_decide

theorem xorA_code : instrs xorA.lit = xorSeg 0 9 := by rw [← xorA.lit_eq]; rfl
theorem xorB_code : instrs xorB.lit = xorSeg 9 13 := by rw [← xorB.lit_eq]; rfl
theorem xorC_code : instrs xorC.lit = xorSeg 13 17 := by rw [← xorC.lit_eq]; rfl
theorem xorD_code : instrs xorD.lit = xorSeg 17 18 := by rw [← xorD.lit_eq]; rfl
theorem xorE_code : instrs xorE.lit = xorSeg 18 21 := by rw [← xorE.lit_eq]; rfl

theorem xorSeg_check : ∀ p ∈ segs, (check (lanes 32 11) (cfgX (p.2 - p.1)) (linExt 42) (xorSeg p.1 p.2) envX
    (postX p.1 p.2) && keeps (xorSeg p.1 p.2)) = true := by
  intro p hp
  simp only [segs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · have h := xorA_check; rw [xorA_code] at h; exact h
  · have h := xorB_check; rw [xorB_code] at h; exact h
  · have h := xorC_check; rw [xorC_code] at h; exact h
  · have h := xorD_check; rw [xorD_code] at h; exact h
  · have h := xorE_check; rw [xorE_code] at h; exact h

/-- The lanes `a ≤ j < b` of the block, of which lane `a` is at `r9`, XORed
into the words of the interleaved state at `r1`, each rotated as its word
is stored. -/
theorem xorSeg_ok {a b : Nat} (hp : (a, b) ∈ segs) {s : State} (hok : Ok (cfgX (b - a)) s)
    (hm : Masks s) :
    ∃ s', runBlock isa (xorSeg a b) s = some s' ∧
      (∀ j < 21, ∀ h < 2, s'.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32 =
        if a ≤ j ∧ j < b then
          s.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32 ^^^
            stw (s.mem.readW (wordAddr (s.gpr .r9) (2 * (j - a) + 1)) 32 ++
              s.mem.readW (wordAddr (s.gpr .r9) (2 * (j - a))) 32) j h
        else s.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r9 = s.gpr .r9 ∧
      (∀ r ∈ [Reg.r0, .r4, .r5, .r6, .r7, .r8, .r10, .r11], s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr (s.gpr .r1), 168⟩] s.mem s'.mem := by
  obtain ⟨-, -, hn⟩ := segs_ok _ hp
  have hc := xorSeg_check _ hp
  simp only [Bool.and_eq_true] at hc
  let W : Nat → BitVec 32 := fun i =>
    if i < 42 then s.mem.readW (wordAddr (s.gpr .r1) i) 32
    else s.mem.readW (wordAddr (s.gpr .r9) (i - 42)) 32
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hc.1
  have hrel : Rel (LaneRel 11 (assign W (2 ^ 11))) (cfgX (b - a)) (linExt 42) envX s := by
    refine ⟨(fun r v h => rel_masks hm _ r v h _ _), (fun k v hk h => ?_), (fun j v hj h => ?_),
      (fun _ _ h => by cases h)⟩
    · have hk' : k < 42 := hk
      simp only [envX, envM, hk', ite_true, Option.some.injEq] at h
      subst h
      have := inWord_rel (k := 11) W (i := k) (by omega_using [hk'])
      simp only [W, hk', ite_true] at this
      exact this
    · have hj' : j < 2 * (b - a) := hj
      simp only [linExt, Option.some.injEq] at h
      subst h
      have := inWord_rel (k := 11) W (i := 42 + j) (by omega_using [hj', hn])
      simp only [W, show ¬ 42 + j < 42 by omega_using [], ite_false, Nat.add_sub_cancel_left] at this
      exact this
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [postX, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hs', fun j hj h hh => ?_, p.rd, p.wr, p.sp, p.base, p.ext,
    fun r hr => p.other r (by rw [keeps_gpr hc.2 r hr]; exact Bool.noConfusion), p.frame⟩
  have hm42 : 2 * j + h < 42 := by omega_using [hj, hh]
  have e1 : (2 * j + h) / 2 = j := by omega_using [hh]
  have e2 : (2 * j + h) % 2 = h := by omega_using [hh]
  have hs : LaneRel 11 (assign W (2 ^ 11)) (outWord (xorBit a b (2 * j + h)))
      (s'.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32) := by
    have := p.rel.slot (2 * j + h) _ hm42 (hpost _ hm42)
    rw [p.base] at this
    exact this
  have bits := outWord_rel (fun q hq x hx => by
    simp only [xorBit, e1, e2] at hx
    split at hx
    · rename_i hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · omega_using [hm42, hq]
      · have := Nat.mod_lt (q + sub32 0 (rot j h)) (show 0 < 32 by decide)
        omega_using [hr, hn, hh, this]
    · simp only [List.mem_singleton] at hx; subst hx; omega_using [hm42, hq]) hs
  apply BitVec.eq_of_getLsbD_eq; intro q hq
  have hW : bitOf W (32 * (2 * j + h) + q) =
      (s.mem.readW (wordAddr (s.gpr .r1) (2 * j + h)) 32).getLsbD q := by
    rw [bitOf_word W _ _ hq]; simp only [W, hm42, ite_true]
  rw [bits q hq]
  simp only [xorBit, e1, e2]
  by_cases hr : a ≤ j ∧ j < b
  · have hq' := Nat.mod_lt (q + sub32 0 (rot j h)) (show 0 < 32 by decide)
    simp only [hr.1, hr.2, and_self, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false, hW,
      BitVec.getLsbD_xor]
    rw [stw, getLsbD_rotateRight_lt _ _ _ hq, getLsbD_half, bitOf_lane W _ (by omega_using [hq', hh])]
    simp only [hq', decide_true, Bool.true_and, W, show ¬ 2 * (21 + (j - a)) + 1 < 42 by omega_using [],
      show ¬ 2 * (21 + (j - a)) < 42 by omega_using [], ite_false,
      show 2 * (21 + (j - a)) + 1 - 42 = 2 * (j - a) + 1 by omega_using [],
      show 2 * (21 + (j - a)) - 42 = 2 * (j - a) by omega_using []]
  · simp only [hr, ite_false, xorBits_cons, xorBits_nil, Bool.xor_false, hW]

/-! ### Copied out of the interleaved state -/

theorem copyA_check : (check (lanes 32 11) (cfgC .r9 9) (linExt 0) (instrs copyA.lit) (envM fun _ => none)
    (postC 0 9) && keeps (instrs copyA.lit)) = true := by lit_decide
theorem copyB_check : (check (lanes 32 11) (cfgC .r9 4) (linExt 0) (instrs copyB.lit) (envM fun _ => none)
    (postC 9 4) && keeps (instrs copyB.lit)) = true := by lit_decide
theorem copyC_check : (check (lanes 32 11) (cfgC .r9 4) (linExt 0) (instrs copyC.lit) (envM fun _ => none)
    (postC 13 4) && keeps (instrs copyC.lit)) = true := by lit_decide
theorem copyD_check : (check (lanes 32 11) (cfgC .r9 1) (linExt 0) (instrs copyD.lit) (envM fun _ => none)
    (postC 17 1) && keeps (instrs copyD.lit)) = true := by lit_decide
theorem copyE_check : (check (lanes 32 11) (cfgC .r9 3) (linExt 0) (instrs copyE.lit) (envM fun _ => none)
    (postC 18 3) && keeps (instrs copyE.lit)) = true := by lit_decide

theorem copyA_code : instrs copyA.lit = copySeg 0 9 := by rw [← copyA.lit_eq]; rfl
theorem copyB_code : instrs copyB.lit = copySeg 9 13 := by rw [← copyB.lit_eq]; rfl
theorem copyC_code : instrs copyC.lit = copySeg 13 17 := by rw [← copyC.lit_eq]; rfl
theorem copyD_code : instrs copyD.lit = copySeg 17 18 := by rw [← copyD.lit_eq]; rfl
theorem copyE_code : instrs copyE.lit = copySeg 18 21 := by rw [← copyE.lit_eq]; rfl

theorem copySeg_check : ∀ p ∈ segs, (check (lanes 32 11) (cfgC .r9 (p.2 - p.1)) (linExt 0) (copySeg p.1 p.2)
    (envM fun _ => none) (postC p.1 (p.2 - p.1)) && keeps (copySeg p.1 p.2)) = true := by
  intro p hp
  simp only [segs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · have h := copyA_check; rw [copyA_code] at h; exact h
  · have h := copyB_check; rw [copyB_code] at h; exact h
  · have h := copyC_check; rw [copyC_code] at h; exact h
  · have h := copyD_check; rw [copyD_code] at h; exact h
  · have h := copyE_check; rw [copyE_code] at h; exact h

/-- The lanes `a ≤ j < b` of the state stored at `r1`, at `r9`. -/
theorem copySeg_ok {a b : Nat} (hp : (a, b) ∈ segs) {s : State} {K : KState}
    (hok : Ok (cfgC .r9 (b - a)) s) (hK : Stored s.mem (s.gpr .r1) K) (hm : Masks s) :
    ∃ s', runBlock isa (copySeg a b) s = some s' ∧
      (∀ i < b - a, (s'.mem.readW (wordAddr (s.gpr .r9) (2 * i + 1)) 32 ++
        s'.mem.readW (wordAddr (s.gpr .r9) (2 * i)) 32 : BitVec 64) = K[a + i]!) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      (∀ r ∈ [Reg.r0, .r4, .r5, .r6, .r7, .r8, .r10, .r11], s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr (s.gpr .r9), 4 * (2 * (b - a))⟩] s.mem s'.mem := by
  obtain ⟨hab, hb, -⟩ := segs_ok _ hp
  have hc := copySeg_check _ hp
  simp only [Bool.and_eq_true] at hc
  obtain ⟨s', hs', hl, rd, wr, sp, g9, g1, go, f⟩ := out_ok hc.1 (by omega_using [hab, hb]) hok hK
    (fun r v h A => rel_masks hm _ r v h _ A) (fun _ => rfl) (fun _ => rfl)
  exact ⟨s', hs', hl, rd, wr, sp, g9, g1, fun r hr => go r (keeps_gpr hc.2 r hr), f⟩

/-! ### The masks -/

theorem masks_check : (check (lanes 32 0) ⟨.r0, 0, .r1, 0⟩ (fun _ => none) (instrs masksCode.lit) envL
    (fun e => e.cst .r4 == some 0x0000ffff#32 && e.cst .r5 == some 0x00ff00ff#32 &&
      e.cst .r6 == some 0x0f0f0f0f#32 && e.cst .r7 == some 0x33333333#32 &&
      e.cst .r8 == some 0x55555555#32) &&
    [Reg.r0, .r1, .r2, .r3, .r9, .r10, .r11, .r12, .lr].all fun r =>
      (instrs masksCode.lit).all fun i => !clobbers i r) = true := by lit_decide

theorem masks_code : instrs masksCode.lit = masks := by rw [← masksCode.lit_eq]; rfl

/-- `masks`: the masks, in their registers. -/
theorem masks_ok (s : State) :
    ∃ s', runBlock isa masks s = some s' ∧ Masks s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r ∈ [Reg.r0, .r1, .r2, .r3, .r9, .r10, .r11, .r12, .lr], s'.gpr r = s.gpr r := by
  have hc := masks_check
  rw [masks_code] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨e', he, hpost⟩, hk⟩ := And.imp_left (of_check _ _ _) hc
  have hok : Ok ⟨.r0, 0, .r1, 0⟩ s :=
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      by have := (s.gpr .r0).isLt; show (s.gpr .r0).toNat + 4 * 0 ≤ 2 ^ 32; omega_using [this],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hrel : Rel (LaneRel 0 0) ⟨.r0, 0, .r1, 0⟩ (fun _ => none) envL s :=
    ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [Bool.and_eq_true, beq_iff_eq] at hpost
  obtain ⟨⟨⟨⟨c4, c5⟩, c6⟩, c7⟩, c8⟩ := hpost
  refine ⟨s', hs', ⟨p.rel.cst _ _ c4, p.rel.cst _ _ c5, p.rel.cst _ _ c6, p.rel.cst _ _ c7,
    p.rel.cst _ _ c8⟩, ?_, p.rd, p.wr, p.sp,
    fun r hr => p.other r (by rw [List.all_eq_true.mp hk r hr]; exact Bool.noConfusion)⟩
  funext x
  refine p.frame x fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  intro hx
  have : (x - State.addr (s.gpr .r0)).toNat + 1 ≤ 4 * 0 := hx
  omega_using [this]

end VG.Proof.Sha3.Arm
