import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bitslice.Anf

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.Spec`. -/
section

/-!
# SHA-3: lemmas about the specification

A round of Keccak-f[1600] lane by lane, in the form the implementations
compute it (`out`): the column parities `C`, `D`, the lanes `B` of
`π(ρ(θ(A)))` plane by plane, and χ and ι.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3
open VG.Impl.Sha3 (rhoOff piSrc)

/-! ## ρ's offsets -/

/-- The rotation Algorithm 2 gives lane `j`. -/
def rhoSpec (j : Nat) : Nat :=
  match (List.range 24).find? (fun t => rhoPos t == (j % 5, j / 5)) with
  | some t => (t + 1) * (t + 2) / 2 % 64
  | none => 0

theorem rhoSpec_eq : ∀ j < 25, VG.Proof.Sha3.rhoSpec j = rhoOff j := by decide

theorem rhoOff_lt : ∀ j < 25, rhoOff j < 64 := by decide

theorem rotateLeft_zero (x : Lane) : x.rotateLeft 0 = x := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft]
  split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _

theorem rho_get (A : State) {j : Nat} (hj : j < 25) :
    (rho A)[j] = A[j].rotateLeft (rhoOff j) := by
  rw [← VG.Proof.Sha3.rhoSpec_eq j hj]
  simp only [rho, Vector.getElem_ofFn, VG.Proof.Sha3.rhoSpec]
  cases (List.range 24).find? (fun t => rhoPos t == (j % 5, j / 5)) <;>
    simp [BitVec.rotateLeft_mod_eq_rotateLeft, VG.Proof.Sha3.rotateLeft_zero]

/-! ## A round, lane by lane -/

/-- `C[x]`. -/
def C (A : State) (x : Nat) : Lane := A[x]! ^^^ A[x + 5]! ^^^ A[x + 10]! ^^^ A[x + 15]! ^^^ A[x + 20]!

/-- `D[x]`, as `ROTR⁶³(C[x + 1]) ⊕ C[x - 1]`. -/
def D (A : State) (x : Nat) : Lane := (VG.Proof.Sha3.C A ((x + 1) % 5)).rotateRight 63 ^^^ VG.Proof.Sha3.C A ((x + 4) % 5)

/-- A rotation left by `k < 64`, as a rotation right (none for `k = 0`). -/
def rotl (v : Lane) (k : Nat) : Lane := if k = 0 then v else v.rotateRight (64 - k)

/-- Lane `x` of plane `y` of `π(ρ(θ(A)))`. -/
def B (A : State) (x y : Nat) : Lane := VG.Proof.Sha3.rotl (A[piSrc x y]! ^^^ VG.Proof.Sha3.D A ((x + 3 * y) % 5)) (rhoOff (piSrc x y))

/-- Lane `(x, y)` of `Rnd(A)` with round constant `rc`. -/
def out (A : State) (rc : Lane) (x y : Nat) : Lane :=
  let t := (VG.Proof.Sha3.B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& VG.Proof.Sha3.B A ((x + 2) % 5) y ^^^ VG.Proof.Sha3.B A x y
  if x = 0 ∧ y = 0 then t ^^^ rc else t

/-- `ROTLᵏ` is a rotation right by `64 - k`. -/
theorem rotateLeft_eq (x : Lane) {k : Nat} (hk : 0 < k) (hk' : k < 64) :
    x.rotateLeft k = x.rotateRight (64 - k) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split <;> split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _

theorem rotl_eq (v : Lane) {k : Nat} (hk : k < 64) : VG.Proof.Sha3.rotl v k = v.rotateLeft k := by
  unfold VG.Proof.Sha3.rotl
  split
  · subst_vars; rw [VG.Proof.Sha3.rotateLeft_zero]
  · rw [VG.Proof.Sha3.rotateLeft_eq _ (by omega) hk]

theorem getElem!_eq (A : State) {i : Nat} (hi : i < 25) : A[i]! = A[i] := by
  simp [hi]

theorem lane_mod (A : State) {x : Nat} (hx : x < 5) (y : Nat) (hy : y < 5) :
    lane A x y = A[x + 5 * y]! := by
  simp only [lane, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem theta_get (A : State) {j : Nat} (hj : j < 25) : (theta A)[j] = A[j] ^^^ VG.Proof.Sha3.D A (j % 5) := by
  have hC : ∀ x, x < 5 → lane A x 0 ^^^ lane A x 1 ^^^ lane A x 2 ^^^ lane A x 3 ^^^ lane A x 4 =
      VG.Proof.Sha3.C A x := fun x hx => by
    simp only [VG.Proof.Sha3.lane_mod A hx _ (by decide : 0 < 5), VG.Proof.Sha3.lane_mod A hx _ (by decide : 1 < 5),
      VG.Proof.Sha3.lane_mod A hx _ (by decide : 2 < 5), VG.Proof.Sha3.lane_mod A hx _ (by decide : 3 < 5),
      VG.Proof.Sha3.lane_mod A hx _ (by decide : 4 < 5), VG.Proof.Sha3.C]
    rfl
  simp only [theta, Vector.getElem_ofFn]
  rw [hC _ (Nat.mod_lt _ (by omega)), hC _ (Nat.mod_lt _ (by omega)), VG.Proof.Sha3.D,
    VG.Proof.Sha3.rotateLeft_eq _ (by decide) (by decide), BitVec.xor_comm (VG.Proof.Sha3.C A _)]
  rfl

theorem B_eq (A : State) {x y : Nat} (hx : x < 5) (_hy : y < 5) :
    VG.Proof.Sha3.B A x y = (rho (theta A))[piSrc x y]'(by simp only [piSrc]; omega) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  rw [VG.Proof.Sha3.rho_get _ hj, VG.Proof.Sha3.theta_get _ hj, VG.Proof.Sha3.B, VG.Proof.Sha3.rotl_eq _ (VG.Proof.Sha3.rhoOff_lt _ hj), VG.Proof.Sha3.getElem!_eq _ hj]
  congr 3
  simp only [piSrc]; omega

theorem pi_get (R : State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (pi R)[x + 5 * y]'(by omega) = R[piSrc x y]'(by simp only [piSrc]; omega) := by
  simp only [pi, Vector.getElem_ofFn, lane]
  rw [VG.Proof.Sha3.getElem!_eq _ (by omega)]
  congr 1
  simp only [piSrc]
  rw [show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega, Nat.mod_eq_of_lt hx]

theorem chi_get (P : State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (chi P)[x + 5 * y]'(by omega) =
      P[x + 5 * y]'(by omega) ^^^
        (~~~(P[(x + 1) % 5 + 5 * y]'(by omega)) &&& P[(x + 2) % 5 + 5 * y]'(by omega)) := by
  simp only [chi, Vector.getElem_ofFn]
  rw [show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega]
  simp only [lane, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx]
  rw [VG.Proof.Sha3.getElem!_eq _ (by omega), VG.Proof.Sha3.getElem!_eq _ (by omega), VG.Proof.Sha3.getElem!_eq _ (by omega)]

theorem rnd_get (A : State) (ir : Nat) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (rnd A ir)[x + 5 * y]'(by omega) = VG.Proof.Sha3.out A (RC ir) x y := by
  have hP : ∀ x' (hx' : x' < 5), (pi (rho (theta A)))[x' + 5 * y]'(by omega) = VG.Proof.Sha3.B A x' y := fun x' hx' => by
    rw [VG.Proof.Sha3.pi_get _ hx' hy, VG.Proof.Sha3.B_eq _ hx' hy]
  have hchi := VG.Proof.Sha3.chi_get (pi (rho (theta A))) hx hy
  rw [hP x hx, hP _ (Nat.mod_lt _ (by omega)), hP _ (Nat.mod_lt _ (by omega))] at hchi
  have hnot : ∀ v : Lane, ~~~v = v ^^^ 0xffffffffffffffff := fun v => by
    rw [BitVec.xor_comm]; rfl
  simp only [rnd, iota, VG.Proof.Sha3.out]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [Vector.getElem_set_self, and_self, ite_true]
    rw [show (chi (pi (rho (theta A))))[0] = (chi (pi (rho (theta A))))[0 + 5 * 0] from rfl, hchi,
      hnot, BitVec.xor_comm (VG.Proof.Sha3.B A 0 0)]
  · rw [Vector.getElem_set_ne _ _ (by omega), hchi, hnot, BitVec.xor_comm (VG.Proof.Sha3.B A x y)]
    simp only [h0, ite_false]

end VG.Proof.Sha3

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.Lanes`. -/
section

/-!
# Keccak-f[1600]: states in memory, for every target

The lanes of a state stored as `[u64; 25]`, where a round of the
implementations reads and writes (`Env`), the state a round computes
(`outState`), and offsets from a pointer, none of which depend on the target.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3 (Lane rnd RC)

/-! ## Offsets -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

/-- Two runs of bytes at offsets of the same base. -/
theorem off_disjoint (p : Addr) {a n b k : Nat} (ha : a + n ≤ 2 ^ 32) (hb : b + k ≤ 2 ^ 32)
    (h : a + n ≤ b ∨ b + k ≤ a) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p + BitVec.ofNat 64 b, k⟩ := Offset.disjoint p h (by omega) (by omega)

theorem off_sub (p : Addr) {a n b k : Nat} (_hb : b + k ≤ 2 ^ 32) (h₁ : b ≤ a) (h₂ : a + n ≤ b + k) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p + BitVec.ofNat 64 b, k⟩ := Offset.sub p h₁ h₂

theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := by simp

theorem sub_prefix' {base : Addr} {len len' : Nat} (h : len ≤ len') :
    Region.Sub ⟨base, len⟩ ⟨base, len'⟩ := Region.sub_prefix h

/-! ## Lanes -/

/-- Lane `i` of the state at `p`. -/
abbrev laneAddr (p : Addr) (i : Nat) : Addr := p + BitVec.ofNat 64 (8 * i)

/-- The state at `p` holds `A`. -/
def Lanes (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), m.readW (VG.Proof.Sha3.laneAddr p i) 64 = A[i]

theorem lane_contains (p : Addr) {i : Nat} (hi : i < 25) : (⟨p, 200⟩ : Region).Contains (VG.Proof.Sha3.laneAddr p i) 8 := by
  simp only [Region.Contains, VG.Proof.Sha3.laneAddr]
  rw [show p + BitVec.ofNat 64 (8 * i) - p = BitVec.ofNat 64 (8 * i) by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem lane_sep (p : Addr) {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) :
    Mem.Sep (VG.Proof.Sha3.laneAddr p i) 8 (VG.Proof.Sha3.laneAddr p j) 8 := by
  intro x hx hy
  simp only [VG.Proof.Sha3.laneAddr] at hx hy
  bv_omega

/-- Where a round reads and writes: the state at `src`, the round constant
at `rcp`, and the state at `dst`, which overlaps neither. -/
structure Env (rd wr : List Region) (src dst rcp : Addr) : Prop where
  src_in : ∀ i < 25, InRegions (rd ++ wr) (VG.Proof.Sha3.laneAddr src i) 8
  dst_out : ∀ i < 25, InRegions wr (VG.Proof.Sha3.laneAddr dst i) 8
  rc_in : InRegions (rd ++ wr) rcp 8
  dst_src : Region.Disjoint ⟨dst, 200⟩ ⟨src, 200⟩
  dst_rc : Region.Disjoint ⟨dst, 200⟩ ⟨rcp, 8⟩

/-- Writing the state at `dst` keeps the lanes at `src`. -/
theorem Env.src_frame {rd wr : List Region} {src dst rcp : Addr} (h : VG.Proof.Sha3.Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 200⟩] m m') {i : Nat} (hi : i < 25) :
    m'.readW (VG.Proof.Sha3.laneAddr src i) 64 = m.readW (VG.Proof.Sha3.laneAddr src i) 64 :=
  hf.readW (VG.Proof.Sha3.lane_contains src hi) (by simpa using h.dst_src.symm) (by decide)

theorem Env.rc_frame {rd wr : List Region} {src dst rcp : Addr} (h : VG.Proof.Sha3.Env rd wr src dst rcp)
    {m m' : Mem} (hf : Frame [⟨dst, 200⟩] m m') : m'.readW rcp 64 = m.readW rcp 64 :=
  hf.readW (Region.contains_self _ _) (by simpa using h.dst_rc.symm) (by decide)

/-! ## The round -/

/-- The round's output. -/
def outState (A : Spec.Sha3.State) (rc : Lane) : Spec.Sha3.State :=
  Vector.ofFn fun i => VG.Proof.Sha3.out A rc (i.val % 5) (i.val / 5)

theorem outState_eq (A : Spec.Sha3.State) (ir : Nat) : VG.Proof.Sha3.outState A (RC ir) = rnd A ir := by
  apply Vector.ext
  intro i hi
  simp only [VG.Proof.Sha3.outState, Vector.getElem_ofFn]
  have := VG.Proof.Sha3.rnd_get A ir (x := i % 5) (y := i / 5) (Nat.mod_lt _ (by omega)) (by omega)
  simp only [show i % 5 + 5 * (i / 5) = i by omega] at this
  exact this.symm

theorem foldl_succ (A : Spec.Sha3.State) (r : Nat) :
    (List.range (r + 1)).foldl rnd A = rnd ((List.range r).foldl rnd A) r := by
  simp [List.range_succ, List.foldl_append]

end VG.Proof.Sha3

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.Compl`. -/
section

/-!
# Keccak-f[1600]: a round on complemented lanes, as polynomials

Implementations that keep the lanes `complLanes` complemented (the "lane
complementing" transform) store `A[i] ⊕ msk i` for lane `i` of a state `A`
(`cmpl A`). A round of such an implementation is checked by evaluating its
code over the ANF domain (`Bitslice.Anf`), with the lanes of its input
state, as stored, as atoms `0–24` and the round constant as atom `25`, and
comparing what it stores with `specP`: the same round, computed over the
domain from the specification's `out` (`Proof/Sha3/Spec.lean`) on the
uncomplemented lanes, and complemented again. `eval_specP` says what that
is: lane `j` of the round's output, as stored.
-/

namespace VG.Proof.Sha3.Compl

open VG.Bitslice.Anf
open VG.Impl.Sha3 (rhoOff piSrc complLanes)
open VG.Spec.Sha3 (Lane)

/-- Lane `i` is kept complemented: all ones, or zero. -/
def msk (i : Nat) : Lane := if complLanes.contains i then BitVec.allOnes 64 else 0

/-- The state as stored: lanes `complLanes` complemented. -/
def cmpl (A : Spec.Sha3.State) : Spec.Sha3.State := Vector.ofFn fun i => A[i.val] ^^^ VG.Proof.Sha3.Compl.msk i.val

/-! ## The round over the ANF domain -/

def maskP (i : Nat) : Poly := if complLanes.contains i then one else zero

/-- Lane `i` of the state, from the lane as stored (atom `i`). -/
def sA (i : Nat) : Poly := pxor (atom i) (VG.Proof.Sha3.Compl.maskP i)

def sC (x : Nat) : Poly := pxor (pxor (pxor (pxor (VG.Proof.Sha3.Compl.sA x) (VG.Proof.Sha3.Compl.sA (x + 5))) (VG.Proof.Sha3.Compl.sA (x + 10))) (VG.Proof.Sha3.Compl.sA (x + 15))) (VG.Proof.Sha3.Compl.sA (x + 20))

def sD (x : Nat) : Poly := pxor (pror 63 (VG.Proof.Sha3.Compl.sC ((x + 1) % 5))) (VG.Proof.Sha3.Compl.sC ((x + 4) % 5))

def srotl (p : Poly) (k : Nat) : Poly := if k = 0 then p else pror (64 - k) p

def sB (x y : Nat) : Poly := VG.Proof.Sha3.Compl.srotl (pxor (VG.Proof.Sha3.Compl.sA (piSrc x y)) (VG.Proof.Sha3.Compl.sD ((x + 3 * y) % 5))) (rhoOff (piSrc x y))

def sOut (x y : Nat) : Poly :=
  let t := pxor (pand (pxor (VG.Proof.Sha3.Compl.sB ((x + 1) % 5) y) one) (VG.Proof.Sha3.Compl.sB ((x + 2) % 5) y)) (VG.Proof.Sha3.Compl.sB x y)
  if x = 0 ∧ y = 0 then pxor t (atom 25) else t

/-- Lane `j` of the round's output, as stored. -/
def specP (j : Nat) : Poly := pxor (VG.Proof.Sha3.Compl.sOut (j % 5) (j / 5)) (VG.Proof.Sha3.Compl.maskP j)

/-! ## What it is -/

section
variable {V : Nat → Lane} {A : Spec.Sha3.State}

theorem eval_maskP (i : Nat) : eval V (VG.Proof.Sha3.Compl.maskP i) = VG.Proof.Sha3.Compl.msk i := by
  unfold VG.Proof.Sha3.Compl.maskP VG.Proof.Sha3.Compl.msk; split
  · exact eval_one V
  · exact eval_zero V

theorem msk_msk (x : Lane) (i : Nat) : x ^^^ VG.Proof.Sha3.Compl.msk i ^^^ VG.Proof.Sha3.Compl.msk i = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem eval_sA (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ VG.Proof.Sha3.Compl.msk i) {i : Nat} (hi : i < 25) :
    eval V (VG.Proof.Sha3.Compl.sA i) = A[i]! := by
  rw [VG.Proof.Sha3.Compl.sA, eval_pxor, eval_atom, VG.Proof.Sha3.Compl.eval_maskP, hV i hi, VG.Proof.Sha3.Compl.msk_msk, VG.Proof.Sha3.getElem!_eq _ hi]

theorem eval_sC (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ VG.Proof.Sha3.Compl.msk i) {x : Nat} (hx : x < 5) :
    eval V (VG.Proof.Sha3.Compl.sC x) = VG.Proof.Sha3.C A x := by
  simp only [VG.Proof.Sha3.Compl.sC, eval_pxor, VG.Proof.Sha3.Compl.eval_sA hV (show x < 25 by omega), VG.Proof.Sha3.Compl.eval_sA hV (show x + 5 < 25 by omega),
    VG.Proof.Sha3.Compl.eval_sA hV (show x + 10 < 25 by omega), VG.Proof.Sha3.Compl.eval_sA hV (show x + 15 < 25 by omega),
    VG.Proof.Sha3.Compl.eval_sA hV (show x + 20 < 25 by omega), VG.Proof.Sha3.C]

theorem eval_sD (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ VG.Proof.Sha3.Compl.msk i) (x : Nat) : eval V (VG.Proof.Sha3.Compl.sD x) = VG.Proof.Sha3.D A x := by
  simp only [VG.Proof.Sha3.Compl.sD, eval_pxor, eval_pror, VG.Proof.Sha3.Compl.eval_sC hV (Nat.mod_lt _ (by omega : 0 < 5)), VG.Proof.Sha3.D]

theorem eval_srotl (p : Poly) (k : Nat) : eval V (VG.Proof.Sha3.Compl.srotl p k) = VG.Proof.Sha3.rotl (eval V p) k := by
  unfold VG.Proof.Sha3.Compl.srotl VG.Proof.Sha3.rotl; split
  · rfl
  · exact eval_pror V _ _

theorem eval_sB (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ VG.Proof.Sha3.Compl.msk i) {x y : Nat} (hx : x < 5) (_hy : y < 5) :
    eval V (VG.Proof.Sha3.Compl.sB x y) = VG.Proof.Sha3.B A x y := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  simp only [VG.Proof.Sha3.Compl.sB, VG.Proof.Sha3.Compl.eval_srotl, eval_pxor, VG.Proof.Sha3.Compl.eval_sA hV hj, VG.Proof.Sha3.Compl.eval_sD hV, VG.Proof.Sha3.B]

theorem eval_sOut (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ VG.Proof.Sha3.Compl.msk i) {rc : Lane} (hrc : V 25 = rc)
    {x y : Nat} (hx : x < 5) (hy : y < 5) : eval V (VG.Proof.Sha3.Compl.sOut x y) = VG.Proof.Sha3.out A rc x y := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have e : ∀ v : Lane, eval V (pxor (pand (pxor (VG.Proof.Sha3.Compl.sB ((x + 1) % 5) y) one) (VG.Proof.Sha3.Compl.sB ((x + 2) % 5) y)) (VG.Proof.Sha3.Compl.sB x y)) =
      (VG.Proof.Sha3.B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& VG.Proof.Sha3.B A ((x + 2) % 5) y ^^^ VG.Proof.Sha3.B A x y := fun _ => by
    rw [eval_pxor, eval_pand, eval_pxor, eval_one, VG.Proof.Sha3.Compl.eval_sB hV h1 hy, VG.Proof.Sha3.Compl.eval_sB hV h2 hy, VG.Proof.Sha3.Compl.eval_sB hV hx hy]
    rfl
  unfold VG.Proof.Sha3.Compl.sOut VG.Proof.Sha3.out
  simp only
  split
  · rw [eval_pxor, e 0, eval_atom, hrc]
  · exact e 0

theorem eval_specP (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ VG.Proof.Sha3.Compl.msk i) {rc : Lane} (hrc : V 25 = rc)
    {j : Nat} (hj : j < 25) : eval V (VG.Proof.Sha3.Compl.specP j) = (VG.Proof.Sha3.Compl.cmpl (VG.Proof.Sha3.outState A rc))[j] := by
  simp only [VG.Proof.Sha3.Compl.specP, eval_pxor, VG.Proof.Sha3.Compl.eval_sOut hV hrc (Nat.mod_lt _ (by omega : 0 < 5)) (by omega : j / 5 < 5),
    VG.Proof.Sha3.Compl.eval_maskP, VG.Proof.Sha3.Compl.cmpl, VG.Proof.Sha3.outState, Vector.getElem_ofFn]

end

end VG.Proof.Sha3.Compl

end
