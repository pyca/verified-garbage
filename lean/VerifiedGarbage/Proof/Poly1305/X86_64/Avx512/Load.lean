module

import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Mul
public import VerifiedGarbage.Proof.Poly1305.Limbs26
public import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512
import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! ### `Poly1305.X86_64.Avx512.Mul`, which this module and modules that import it used -/

section

/-!
# Poly1305 on x86-64 with AVX-512: the product

`mul` multiplies the eight quadwords of the accumulator `H` by the low
doublewords of `Y`, quadword by quadword, and carries: `Limbs26.mul`, with the
limbs small enough that nothing wraps (as `Avx2.mul` does on four). `mulM`
multiplies them by the limbs in the state instead, with the products by five
times them in place of five times the products (`pdM`), which is the same.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi hreg_ge yreg_ge vec vec_trans vec_gpr)

/-- Limb `i` of quadword `k` of `H`, and of the low doublewords of `Y`. -/
def hv (s : State) (k i : Nat) : Nat := (qz s (hreg i) k).toNat
def yl (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat % 2 ^ 32

def mulB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 28 - 1
    | _ => 2 ^ 64 - 1,
   fun r => match r with
    | .xmm11 | .xmm12 | .xmm13 | .xmm14 | .xmm15 => 2 ^ 27 - 1
    | _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1⟩

def mulS : Sym := (Sym.init.run false mul).get (by decide +kernel)

theorem mulS_eq : Sym.init.run false mul = some mulS := (Option.some_get _).symm

theorem mulS_ok : ∀ i < 5, ∀ k < 8,
    (mulS.reg (xi (hreg i))).ok mulB k = true ∧ (mulS.reg (xi (hreg i))).bnd mulB k < 2 ^ 27 := by
  decide +kernel

theorem mulS_y : ∀ i < 5, mulS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The limbs `mul` computes, from the registers it starts with. -/
theorem mulS_nat (E : Env) (k : Nat) : ∀ i < 5, (mulS.reg (xi (hreg i))).nat E k =
    Limbs26.carry (Limbs26.pd (fun i => E.v (xi (hreg i)) k % 2 ^ 32)
      (fun i => E.v (xi (yreg i)) k % 2 ^ 32)) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

structure MulPre (s : State) : Prop where
  r8 : s.gpr .r8 = 0x3ffffff
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 28
  y : ∀ k < 8, ∀ i < 5, yl s k i < 2 ^ 27

theorem MulPre.env {s : State} (hp : MulPre s) : EnvOK s mulB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.h k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    cases r <;> simp only [mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.y k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 4 (by decide))
  · have := BitVec.isLt (s.gpr g)
    simp only [mulB]
    split
    · subst g; rw [hp.r8]; decide
    · omega_using []

/-- What `mul` leaves: `H` times the low doublewords of `Y`, carried, and the
rest but the products and `tP` as they were. -/
structure MulPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, ∀ i < 5, hv s' k i = Limbs26.mul (hv s k) (yl s k) i
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27

theorem hv_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : hv s k j = hv s k 4 := by
  simp only [hv, hreg_ge h]

theorem yl_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : yl s k j = yl s k 4 := by
  simp only [yl, yreg_ge h]

theorem hv_mod {s : State} (hh : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 28) {k : Nat} (hk : k < 8) :
    (fun i => (envOf s).v (xi (hreg i)) k % 2 ^ 32) = hv s k := by
  funext i
  rw [envOf_v]
  by_cases hi : i < 5
  · exact Nat.mod_eq_of_lt (Nat.lt_trans (hh k hk i hi) (by decide))
  · rw [hreg_ge (by omega_using [hi])]
    rw [hv_ge s k (by omega_using [hi])]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (hh k hk 4 (by decide)) (by decide))

theorem yl_eq (s : State) (k : Nat) : (fun i => (envOf s).v (xi (yreg i)) k % 2 ^ 32) = yl s k := by
  funext i; rw [envOf_v]; rfl

theorem mul_ok {s : State} (hp : MulPre s) : WP isa (.block mul) s (MulPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) mulS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, mulS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    simp only [hv] at e ⊢
    rw [e, mulS_nat _ _ i hi, Limbs26.mul, hv_mod hp.h hk, yl_eq]
    simp only [envOf, hp.r8]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    exact Nat.lt_of_le_of_lt b (mulS_ok i hi k hk).2

/-! ## The multipliers from memory -/

/-- The products `d_j` as `mulM` sums them, from the limbs `b` and `c = 5 b`
(for limbs 1 to 4). -/
def pdM (a b c : Nat → Nat) : Nat → Nat
  | 0 => a 0 * b 0 + a 1 * c 4 + a 2 * c 3 + a 3 * c 2 + a 4 * c 1
  | 1 => a 0 * b 1 + a 1 * b 0 + a 2 * c 4 + a 3 * c 3 + a 4 * c 2
  | 2 => a 0 * b 2 + a 1 * b 1 + a 2 * b 0 + a 3 * c 4 + a 4 * c 3
  | 3 => a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 + a 4 * c 4
  | _ => a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0

theorem pdM_eq (a b c : Nat → Nat) (hc : ∀ i, 1 ≤ i → i < 5 → c i = 5 * b i) : pdM a b c = Limbs26.pd a b := by
  funext j
  have c1 := hc 1 (by decide) (by decide)
  have c2 := hc 2 (by decide) (by decide)
  have c3 := hc 3 (by decide) (by decide)
  have c4 := hc 4 (by decide) (by decide)
  match j with
  | 0 => simp only [pdM, Limbs26.pd, c1, c2, c3, c4]; ring
  | 1 => simp only [pdM, Limbs26.pd, c2, c3, c4]; ring
  | 2 => simp only [pdM, Limbs26.pd, c3, c4]; ring
  | 3 => simp only [pdM, Limbs26.pd, c4]; ring
  | _ + 4 => simp only [pdM, Limbs26.pd]

/-- The displacements of the limbs of `r⁸` and of five times them in the state. -/
def rDisp : List Nat := [56, 60, 64, 68, 72]
def sDisp : List Nat := [76, 80, 84, 88]

def mulMB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 28 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun _ => 2 ^ 64 - 1,
   fun d => if d = 104 then 2 ^ 26 - 1 else 2 ^ 64 - 1,
   fun d => if d ∈ rDisp then 2 ^ 27 - 1 else if d ∈ sDisp then 5 * (2 ^ 27 - 1) else 2 ^ 32 - 1⟩

def mulMS : Sym := (Sym.init.run true mulM).get (by decide +kernel)

theorem mulMS_eq : Sym.init.run true mulM = some mulMS := (Option.some_get _).symm

theorem mulMS_ok : ∀ i < 5, ∀ k < 8,
    (mulMS.reg (xi (hreg i))).ok mulMB k = true ∧ (mulMS.reg (xi (hreg i))).bnd mulMB k < 2 ^ 27 := by
  decide +kernel

theorem mulMS_y : ∀ i < 5, mulMS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The limbs `mulM` computes, from the registers and memory it starts with. -/
theorem mulMS_nat (E : Env) (k : Nat) : ∀ i < 5, (mulMS.reg (xi (hreg i))).nat E k =
    Limbs26.carry (pdM (fun i => E.v (xi (hreg i)) k % 2 ^ 32) (fun i => E.mb (56 + 4 * i) % 2 ^ 32)
      (fun i => E.mb (72 + 4 * i) % 2 ^ 32)) (E.mb 104) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

/-- Limb `i` of the multiplier in the state: the low doubleword at
`rdi + 56 + 4 i`; and five times it, at `rdi + 72 + 4 i`. -/
def mr (s : State) (i : Nat) : Nat := (envOf s).mb (56 + 4 * i) % 2 ^ 32
def ms (s : State) (i : Nat) : Nat := (envOf s).mb (72 + 4 * i) % 2 ^ 32

/-- What `mulM` needs of the state at `rdi`: the limbs of the multiplier
below `2²⁷` and five times them, and the mask. -/
structure MemM (s : State) : Prop where
  r : ∀ i < 5, mr s i < 2 ^ 27
  five : ∀ i, 1 ≤ i → i < 5 → ms s i = 5 * mr s i
  mask : (envOf s).mb 104 = 0x3ffffff
  pad : (envOf s).mb 112 = 0x1000000

theorem MemM.of_mem {s s' : State} (h : MemM s) (hg : s'.gpr .rdi = s.gpr .rdi) (hm : s'.mem = s.mem) :
    MemM s' := by
  have e : (envOf s').mb = (envOf s).mb := by funext d; simp only [envOf, hg, hm]
  have er : mr s' = mr s := by funext i; simp only [mr, e]
  have es : ms s' = ms s := by funext i; simp only [ms, e]
  exact ⟨by rw [er]; exact h.r, by rw [es, er]; exact h.five, by rw [e]; exact h.mask, by rw [e]; exact h.pad⟩

structure MulMPre (s : State) : Prop where
  ctx : Ctx s
  mem : MemM s
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 28

theorem MulMPre.env {s : State} (hp : MulMPre s) : EnvOK s mulMB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _), fun d => ?_,
    fun d => ?_⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [mulMB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.h k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [mulMB]; omega_using []
  · have := BitVec.isLt (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64)
    simp only [mulMB]
    split
    · subst d; have := hp.mem.mask; simp only [envOf] at this; rw [this]; decide
    · omega_using []
  · have := Nat.mod_lt (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat
      (show 2 ^ 32 > 0 by decide)
    have r := hp.mem.r
    have f := hp.mem.five
    simp only [mr, ms, envOf] at r f
    simp only [mulMB, rDisp, sDisp, List.mem_cons, List.not_mem_nil, or_false]
    split
    · rename_i h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact Nat.le_sub_one_of_lt (r 0 (by decide))
      · exact Nat.le_sub_one_of_lt (r 1 (by decide))
      · exact Nat.le_sub_one_of_lt (r 2 (by decide))
      · exact Nat.le_sub_one_of_lt (r 3 (by decide))
      · exact Nat.le_sub_one_of_lt (r 4 (by decide))
    · split
      · rename_i h
        rcases h with rfl | rfl | rfl | rfl
        · rw [f 1 (by decide) (by decide)]; have := r 1 (by decide); omega_using [this]
        · rw [f 2 (by decide) (by decide)]; have := r 2 (by decide); omega_using [this]
        · rw [f 3 (by decide) (by decide)]; have := r 3 (by decide); omega_using [this]
        · rw [f 4 (by decide) (by decide)]; have := r 4 (by decide); omega_using [this]
      · omega_using []

/-- What `mulM` leaves: `H` times the multiplier in the state, carried, and
the rest but the products and `tP` as they were. -/
structure MulMPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, ∀ i < 5, hv s' k i = Limbs26.mul (hv s k) (mr s) i
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27

theorem mulM_ok {s : State} (hp : MulMPre s) : WP isa (.block mulM) s (MulMPost s) := by
  refine WP.mono (run_ok (fun _ => hp.ctx) mulMS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, mulMS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (mulMS_ok i hi k hk).1
    simp only [hv] at e ⊢
    rw [e, mulMS_nat _ _ i hi, Limbs26.mul, hv_mod hp.h hk]
    have hm : (envOf s).mb 104 = 0x3ffffff := hp.mem.mask
    rw [hm, ← pdM_eq (hv s k) (mr s) (ms s) hp.mem.five]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (mulMS_ok i hi k hk).1
    exact Nat.lt_of_le_of_lt b (mulMS_ok i hi k hk).2

end VG.Proof.Poly1305.X86_64.Avx512

end

end

/-!
# Poly1305 on x86-64 with AVX-512: loading blocks

`addGroup` splits the eight blocks at `rsi` into limbs (block `π k` in
quadword `k`) and adds them, with the pad bit, to `H`; `addGroupM` likewise,
with the pad bit from the state.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec or_pad)

def addS : Sym := (Sym.init.run true addGroup).get (by decide +kernel)

theorem addS_eq : Sym.init.run true addGroup = some addS := (Option.some_get _).symm

theorem addS_y : ∀ i < 5, addS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

def addMS : Sym := (Sym.init.run true addGroupM).get (by decide +kernel)

theorem addMS_eq : Sym.init.run true addGroupM = some addMS := (Option.some_get _).symm

theorem addMS_y : ∀ i < 5, addMS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The block of a group in quadword `k`: blocks `0, 4, 1, 5, 2, 6, 3, 7`. -/
def pi (k : Nat) : Nat := 4 * (k % 2) + k / 2

section
variable (E : Env)

theorem addS_0 : ∀ k < 8, (addS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_1 : ∀ k < 8, (addS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_2 : ∀ k < 8, (addS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * pi k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_3 : ∀ k < 8, (addS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_4 : ∀ k < 8, (addS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * pi k + 1) / 2 ^ 40 ||| E.g .r9)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem addMS_0 : ∀ k < 8, (addMS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_1 : ∀ k < 8, (addMS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_2 : ∀ k < 8, (addMS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * pi k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_3 : ∀ k < 8, (addMS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_4 : ∀ k < 8, (addMS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * pi k + 1) / 2 ^ 40 ||| E.mb 112)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

/-- The words of the block of the group at `rsi` in quadword `k`. -/
def blo (s : State) (k : Nat) : Nat := (envOf s).m (2 * pi k)
def bhi (s : State) (k : Nat) : Nat := (envOf s).m (2 * pi k + 1)

theorem envOf_m_lt (s : State) (j : Nat) : (envOf s).m j < 2 ^ 64 := BitVec.isLt _

structure AddPre (s : State) : Prop where
  r9 : s.gpr .r9 = 0x1000000
  ctx : Ctx s
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27

structure AddMPre (s : State) : Prop where
  pad : (envOf s).mb 112 = 0x1000000
  ctx : Ctx s
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27

/-- What `addGroup` leaves: block `π k`, with its pad bit, added to
quadword `k` of `H`, and `Y` as it was. -/
structure AddPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, Limbs26.val (hv s' k) = Limbs26.val (hv s k) + (blo s k + 2 ^ 64 * bhi s k + 2 ^ 128)
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 28

/-- `AddPost` from the terms that `addGroup` (with the pad bit `pd`) computes. -/
theorem addPost_of {s s' : State} {σ : Sym} (h : SRel σ s s') (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27)
    {pd : Nat} (hpd : pd = 0x1000000) (hy : ∀ i < 5, σ.reg (xi (yreg i)) = .reg (xi (yreg i)))
    (S0 : ∀ k < 8, (σ.reg (xi (hreg 0))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 0)) k + (envOf s).m (2 * pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S1 : ∀ k < 8, (σ.reg (xi (hreg 1))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 1)) k + (envOf s).m (2 * pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S2 : ∀ k < 8, (σ.reg (xi (hreg 2))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 2)) k + ((envOf s).m (2 * pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (envOf s).m (2 * pi k) / 2 ^ 52)) % 2 ^ 64)
    (S3 : ∀ k < 8, (σ.reg (xi (hreg 3))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 3)) k + (envOf s).m (2 * pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S4 : ∀ k < 8, (σ.reg (xi (hreg 4))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 4)) k + ((envOf s).m (2 * pi k + 1) / 2 ^ 40 ||| pd)) % 2 ^ 64) :
    AddPost s s' := by
  have H : ∀ k < 8, hv s' k 0 = hv s k 0 + blo s k * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = hv s k 1 + blo s k * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = hv s k 2 + (2 ^ 12 * (bhi s k % 2 ^ 14) + blo s k / 2 ^ 52) ∧
      hv s' k 3 = hv s k 3 + bhi s k * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = hv s k 4 + (bhi s k / 2 ^ 40 + 2 ^ 24) := by
    intro k hk
    have hl := envOf_m_lt s (2 * pi k)
    have hh := envOf_m_lt s (2 * pi k + 1)
    have b0 := hb k hk 0 (by decide)
    have b1 := hb k hk 1 (by decide)
    have b2 := hb k hk 2 (by decide)
    have b3 := hb k hk 3 (by decide)
    have b4 := hb k hk 4 (by decide)
    simp only [hv] at b0 b1 b2 b3 b4 ⊢
    rw [h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, S0 k hk, S1 k hk,
      S2 k hk, S3 k hk, S4 k hk, envOf_v, envOf_v, envOf_v, envOf_v, envOf_v,
      Limbs26.split_or hl, hpd]
    simp only [envOf, blo, bhi] at hl hh ⊢
    rw [or_pad (by omega_arith)]
    omega_arith
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, hy i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have := Limbs26.split_val (envOf_m_lt s (2 * pi k)) (bhi s k)
    rw [Limbs26.split_or (envOf_m_lt s (2 * pi k))] at this
    simp only [Limbs26.val, e0, e1, e2, e3, e4]
    simp only [blo] at this ⊢
    omega_arith
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have hl := envOf_m_lt s (2 * pi k)
    have hh := envOf_m_lt s (2 * pi k + 1)
    have b := hb k hk
    simp only [blo, bhi] at e0 e1 e2 e3 e4
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [e0]; have := b 0 (by decide); omega_arith
    · rw [e1]; have := b 1 (by decide); omega_arith
    · rw [e2]; have := b 2 (by decide); omega_arith
    · rw [e3]; have := b 3 (by decide); omega_arith
    · rw [e4]; have := b 4 (by decide); omega_arith

theorem addGroup_ok {s : State} (hp : AddPre s) : WP isa (.block addGroup) s (AddPost s) :=
  WP.mono (run_ok (fun _ => hp.ctx) addS_eq) fun _ h =>
    addPost_of h hp.h (show (envOf s).g .r9 = 0x1000000 by simp only [envOf, hp.r9]; rfl) addS_y
      (addS_0 _) (addS_1 _) (addS_2 _) (addS_3 _) (addS_4 _)

theorem addGroupM_ok {s : State} (hp : AddMPre s) : WP isa (.block addGroupM) s (AddPost s) :=
  WP.mono (run_ok (fun _ => hp.ctx) addMS_eq) fun _ h =>
    addPost_of h hp.h hp.pad addMS_y (addMS_0 _) (addMS_1 _) (addMS_2 _) (addMS_3 _) (addMS_4 _)

end VG.Proof.Poly1305.X86_64.Avx512
