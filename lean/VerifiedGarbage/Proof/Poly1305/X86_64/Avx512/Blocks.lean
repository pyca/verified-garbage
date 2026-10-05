import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
import VerifiedGarbage.Proof.Poly1305.Pair
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx512
import VerifiedGarbage.Proof.Poly1305.X86_64.Variant

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Mul`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: the product

`mul` multiplies the eight quadwords of the accumulator `H` by the low
doublewords of `Y`, quadword by quadword, and carries: `Limbs26.mul`, with the
limbs small enough that nothing wraps (as `Avx2.mul` does on four). `mulM`
multiplies them by the limbs in the state instead, with the products by five
times them in place of five times the products (`pdM`), which is the same.
-/

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

theorem mulS_eq : Sym.init.run false mul = some VG.Proof.Poly1305.X86_64.Avx512.mulS := (Option.some_get _).symm

theorem mulS_ok : ∀ i < 5, ∀ k < 8,
    (mulS.reg (xi (hreg i))).ok VG.Proof.Poly1305.X86_64.Avx512.mulB k = true ∧ (mulS.reg (xi (hreg i))).bnd VG.Proof.Poly1305.X86_64.Avx512.mulB k < 2 ^ 27 := by
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
  h : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 28
  y : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.yl s k i < 2 ^ 27

theorem MulPre.env {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.MulPre s) : EnvOK s VG.Proof.Poly1305.X86_64.Avx512.mulB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.h k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.mulB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.y k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.y k hk 4 (by decide))
  · have := BitVec.isLt (s.gpr g)
    simp only [VG.Proof.Poly1305.X86_64.Avx512.mulB]
    split
    · subst g; rw [hp.r8]; decide
    · omega

/-- What `mul` leaves: `H` times the low doublewords of `Y`, carried, and the
rest but the products and `tP` as they were. -/
structure MulPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = Limbs26.mul (VG.Proof.Poly1305.X86_64.Avx512.hv s k) (VG.Proof.Poly1305.X86_64.Avx512.yl s k) i
  hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 27

theorem hv_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx512.hv s k j = VG.Proof.Poly1305.X86_64.Avx512.hv s k 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.hv, hreg_ge h]

theorem yl_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx512.yl s k j = VG.Proof.Poly1305.X86_64.Avx512.yl s k 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.yl, yreg_ge h]

theorem hv_mod {s : State} (hh : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 28) {k : Nat} (hk : k < 8) :
    (fun i => (envOf s).v (xi (hreg i)) k % 2 ^ 32) = VG.Proof.Poly1305.X86_64.Avx512.hv s k := by
  funext i
  rw [envOf_v]
  by_cases hi : i < 5
  · exact Nat.mod_eq_of_lt (Nat.lt_trans (hh k hk i hi) (by decide))
  · rw [hreg_ge (by omega)]
    rw [VG.Proof.Poly1305.X86_64.Avx512.hv_ge s k (by omega)]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (hh k hk 4 (by decide)) (by decide))

theorem yl_eq (s : State) (k : Nat) : (fun i => (envOf s).v (xi (yreg i)) k % 2 ^ 32) = VG.Proof.Poly1305.X86_64.Avx512.yl s k := by
  funext i; rw [envOf_v]; rfl

theorem mul_ok {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.MulPre s) : WP isa (.block mul) s (VG.Proof.Poly1305.X86_64.Avx512.MulPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.mulS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, VG.Proof.Poly1305.X86_64.Avx512.mulS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx512.mulS_ok i hi k hk).1
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hv] at e ⊢
    rw [e, VG.Proof.Poly1305.X86_64.Avx512.mulS_nat _ _ i hi, Limbs26.mul, VG.Proof.Poly1305.X86_64.Avx512.hv_mod hp.h hk, VG.Proof.Poly1305.X86_64.Avx512.yl_eq]
    simp only [envOf, hp.r8]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx512.mulS_ok i hi k hk).1
    exact Nat.lt_of_le_of_lt b (VG.Proof.Poly1305.X86_64.Avx512.mulS_ok i hi k hk).2

/-! ## The multipliers from memory -/

/-- The products `d_j` as `mulM` sums them, from the limbs `b` and `c = 5 b`
(for limbs 1 to 4). -/
def pdM (a b c : Nat → Nat) : Nat → Nat
  | 0 => a 0 * b 0 + a 1 * c 4 + a 2 * c 3 + a 3 * c 2 + a 4 * c 1
  | 1 => a 0 * b 1 + a 1 * b 0 + a 2 * c 4 + a 3 * c 3 + a 4 * c 2
  | 2 => a 0 * b 2 + a 1 * b 1 + a 2 * b 0 + a 3 * c 4 + a 4 * c 3
  | 3 => a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 + a 4 * c 4
  | _ => a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0

theorem pdM_eq (a b c : Nat → Nat) (hc : ∀ i, 1 ≤ i → i < 5 → c i = 5 * b i) : VG.Proof.Poly1305.X86_64.Avx512.pdM a b c = Limbs26.pd a b := by
  funext j
  have c1 := hc 1 (by decide) (by decide)
  have c2 := hc 2 (by decide) (by decide)
  have c3 := hc 3 (by decide) (by decide)
  have c4 := hc 4 (by decide) (by decide)
  match j with
  | 0 => simp only [VG.Proof.Poly1305.X86_64.Avx512.pdM, Limbs26.pd, c1, c2, c3, c4]; ring
  | 1 => simp only [VG.Proof.Poly1305.X86_64.Avx512.pdM, Limbs26.pd, c2, c3, c4]; ring
  | 2 => simp only [VG.Proof.Poly1305.X86_64.Avx512.pdM, Limbs26.pd, c3, c4]; ring
  | 3 => simp only [VG.Proof.Poly1305.X86_64.Avx512.pdM, Limbs26.pd, c4]; ring
  | _ + 4 => simp only [VG.Proof.Poly1305.X86_64.Avx512.pdM, Limbs26.pd]

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
   fun d => if d ∈ VG.Proof.Poly1305.X86_64.Avx512.rDisp then 2 ^ 27 - 1 else if d ∈ VG.Proof.Poly1305.X86_64.Avx512.sDisp then 5 * (2 ^ 27 - 1) else 2 ^ 32 - 1⟩

def mulMS : Sym := (Sym.init.run true mulM).get (by decide +kernel)

theorem mulMS_eq : Sym.init.run true mulM = some VG.Proof.Poly1305.X86_64.Avx512.mulMS := (Option.some_get _).symm

theorem mulMS_ok : ∀ i < 5, ∀ k < 8,
    (mulMS.reg (xi (hreg i))).ok VG.Proof.Poly1305.X86_64.Avx512.mulMB k = true ∧ (mulMS.reg (xi (hreg i))).bnd VG.Proof.Poly1305.X86_64.Avx512.mulMB k < 2 ^ 27 := by
  decide +kernel

theorem mulMS_y : ∀ i < 5, mulMS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The limbs `mulM` computes, from the registers and memory it starts with. -/
theorem mulMS_nat (E : Env) (k : Nat) : ∀ i < 5, (mulMS.reg (xi (hreg i))).nat E k =
    Limbs26.carry (VG.Proof.Poly1305.X86_64.Avx512.pdM (fun i => E.v (xi (hreg i)) k % 2 ^ 32) (fun i => E.mb (56 + 4 * i) % 2 ^ 32)
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
  r : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.mr s i < 2 ^ 27
  five : ∀ i, 1 ≤ i → i < 5 → VG.Proof.Poly1305.X86_64.Avx512.ms s i = 5 * VG.Proof.Poly1305.X86_64.Avx512.mr s i
  mask : (envOf s).mb 104 = 0x3ffffff
  pad : (envOf s).mb 112 = 0x1000000

theorem MemM.of_mem {s s' : State} (h : VG.Proof.Poly1305.X86_64.Avx512.MemM s) (hg : s'.gpr .rdi = s.gpr .rdi) (hm : s'.mem = s.mem) :
    VG.Proof.Poly1305.X86_64.Avx512.MemM s' := by
  have e : (envOf s').mb = (envOf s).mb := by funext d; simp only [envOf, hg, hm]
  have er : VG.Proof.Poly1305.X86_64.Avx512.mr s' = VG.Proof.Poly1305.X86_64.Avx512.mr s := by funext i; simp only [VG.Proof.Poly1305.X86_64.Avx512.mr, e]
  have es : VG.Proof.Poly1305.X86_64.Avx512.ms s' = VG.Proof.Poly1305.X86_64.Avx512.ms s := by funext i; simp only [VG.Proof.Poly1305.X86_64.Avx512.ms, e]
  exact ⟨by rw [er]; exact h.r, by rw [es, er]; exact h.five, by rw [e]; exact h.mask, by rw [e]; exact h.pad⟩

structure MulMPre (s : State) : Prop where
  ctx : VG.Proof.Poly1305.X86_64.Avx512.Ctx s
  mem : VG.Proof.Poly1305.X86_64.Avx512.MemM s
  h : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 28

theorem MulMPre.env {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.MulMPre s) : EnvOK s VG.Proof.Poly1305.X86_64.Avx512.mulMB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _), fun d => ?_,
    fun d => ?_⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.mulMB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hp.h k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hp.h k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [VG.Proof.Poly1305.X86_64.Avx512.mulMB]; omega
  · have := BitVec.isLt (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64)
    simp only [VG.Proof.Poly1305.X86_64.Avx512.mulMB]
    split
    · subst d; have := hp.mem.mask; simp only [envOf] at this; rw [this]; decide
    · omega
  · have := Nat.mod_lt (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat
      (show 2 ^ 32 > 0 by decide)
    have r := hp.mem.r
    have f := hp.mem.five
    simp only [VG.Proof.Poly1305.X86_64.Avx512.mr, VG.Proof.Poly1305.X86_64.Avx512.ms, envOf] at r f
    simp only [VG.Proof.Poly1305.X86_64.Avx512.mulMB, VG.Proof.Poly1305.X86_64.Avx512.rDisp, VG.Proof.Poly1305.X86_64.Avx512.sDisp, List.mem_cons, List.not_mem_nil, or_false]
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
        · rw [f 1 (by decide) (by decide)]; have := r 1 (by decide); omega
        · rw [f 2 (by decide) (by decide)]; have := r 2 (by decide); omega
        · rw [f 3 (by decide) (by decide)]; have := r 3 (by decide); omega
        · rw [f 4 (by decide) (by decide)]; have := r 4 (by decide); omega
      · omega

/-- What `mulM` leaves: `H` times the multiplier in the state, carried, and
the rest but the products and `tP` as they were. -/
structure MulMPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = Limbs26.mul (VG.Proof.Poly1305.X86_64.Avx512.hv s k) (VG.Proof.Poly1305.X86_64.Avx512.mr s) i
  hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 27

theorem mulM_ok {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.MulMPre s) : WP isa (.block mulM) s (VG.Proof.Poly1305.X86_64.Avx512.MulMPost s) := by
  refine WP.mono (run_ok (fun _ => hp.ctx) VG.Proof.Poly1305.X86_64.Avx512.mulMS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, VG.Proof.Poly1305.X86_64.Avx512.mulMS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx512.mulMS_ok i hi k hk).1
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hv] at e ⊢
    rw [e, VG.Proof.Poly1305.X86_64.Avx512.mulMS_nat _ _ i hi, Limbs26.mul, VG.Proof.Poly1305.X86_64.Avx512.hv_mod hp.h hk]
    have hm : (envOf s).mb 104 = 0x3ffffff := hp.mem.mask
    rw [hm, ← VG.Proof.Poly1305.X86_64.Avx512.pdM_eq (VG.Proof.Poly1305.X86_64.Avx512.hv s k) (VG.Proof.Poly1305.X86_64.Avx512.mr s) (VG.Proof.Poly1305.X86_64.Avx512.ms s) hp.mem.five]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx512.mulMS_ok i hi k hk).1
    exact Nat.lt_of_le_of_lt b (VG.Proof.Poly1305.X86_64.Avx512.mulMS_ok i hi k hk).2

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Load`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: loading blocks

`addGroup` splits the eight blocks at `rsi` into limbs (block `π k` in
quadword `k`) and adds them, with the pad bit, to `H`; `addGroupM` likewise,
with the pad bit from the state.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec or_pad)

def addS : Sym := (Sym.init.run true addGroup).get (by decide +kernel)

theorem addS_eq : Sym.init.run true addGroup = some VG.Proof.Poly1305.X86_64.Avx512.addS := (Option.some_get _).symm

theorem addS_y : ∀ i < 5, addS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

def addMS : Sym := (Sym.init.run true addGroupM).get (by decide +kernel)

theorem addMS_eq : Sym.init.run true addGroupM = some VG.Proof.Poly1305.X86_64.Avx512.addMS := (Option.some_get _).symm

theorem addMS_y : ∀ i < 5, addMS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The block of a group in quadword `k`: blocks `0, 4, 1, 5, 2, 6, 3, 7`. -/
def pi (k : Nat) : Nat := 4 * (k % 2) + k / 2

section
variable (E : Env)

theorem addS_0 : ∀ k < 8, (addS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_1 : ∀ k < 8, (addS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_2 : ∀ k < 8, (addS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_3 : ∀ k < 8, (addS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_4 : ∀ k < 8, (addS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) / 2 ^ 40 ||| E.g .r9)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem addMS_0 : ∀ k < 8, (addMS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_1 : ∀ k < 8, (addMS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_2 : ∀ k < 8, (addMS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_3 : ∀ k < 8, (addMS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_4 : ∀ k < 8, (addMS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) / 2 ^ 40 ||| E.mb 112)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

/-- The words of the block of the group at `rsi` in quadword `k`. -/
def blo (s : State) (k : Nat) : Nat := (envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k)
def bhi (s : State) (k : Nat) : Nat := (envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1)

theorem envOf_m_lt (s : State) (j : Nat) : (envOf s).m j < 2 ^ 64 := BitVec.isLt _

structure AddPre (s : State) : Prop where
  r9 : s.gpr .r9 = 0x1000000
  ctx : VG.Proof.Poly1305.X86_64.Avx512.Ctx s
  h : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27

structure AddMPre (s : State) : Prop where
  pad : (envOf s).mb 112 = 0x1000000
  ctx : VG.Proof.Poly1305.X86_64.Avx512.Ctx s
  h : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27

/-- What `addGroup` leaves: block `π k`, with its pad bit, added to
quadword `k` of `H`, and `Y` as it was. -/
structure AddPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.hv s' k) = Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.hv s k) + (VG.Proof.Poly1305.X86_64.Avx512.blo s k + 2 ^ 64 * VG.Proof.Poly1305.X86_64.Avx512.bhi s k + 2 ^ 128)
  hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 28

/-- `AddPost` from the terms that `addGroup` (with the pad bit `pd`) computes. -/
theorem addPost_of {s s' : State} {σ : Sym} (h : SRel σ s s') (hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27)
    {pd : Nat} (hpd : pd = 0x1000000) (hy : ∀ i < 5, σ.reg (xi (yreg i)) = .reg (xi (yreg i)))
    (S0 : ∀ k < 8, (σ.reg (xi (hreg 0))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 0)) k + (envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S1 : ∀ k < 8, (σ.reg (xi (hreg 1))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 1)) k + (envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S2 : ∀ k < 8, (σ.reg (xi (hreg 2))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 2)) k + ((envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) / 2 ^ 52)) % 2 ^ 64)
    (S3 : ∀ k < 8, (σ.reg (xi (hreg 3))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 3)) k + (envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S4 : ∀ k < 8, (σ.reg (xi (hreg 4))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 4)) k + ((envOf s).m (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) / 2 ^ 40 ||| pd)) % 2 ^ 64) :
    VG.Proof.Poly1305.X86_64.Avx512.AddPost s s' := by
  have H : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hv s' k 0 = VG.Proof.Poly1305.X86_64.Avx512.hv s k 0 + VG.Proof.Poly1305.X86_64.Avx512.blo s k * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 1 = VG.Proof.Poly1305.X86_64.Avx512.hv s k 1 + VG.Proof.Poly1305.X86_64.Avx512.blo s k * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 2 = VG.Proof.Poly1305.X86_64.Avx512.hv s k 2 + (2 ^ 12 * (VG.Proof.Poly1305.X86_64.Avx512.bhi s k % 2 ^ 14) + VG.Proof.Poly1305.X86_64.Avx512.blo s k / 2 ^ 52) ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 3 = VG.Proof.Poly1305.X86_64.Avx512.hv s k 3 + VG.Proof.Poly1305.X86_64.Avx512.bhi s k * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 4 = VG.Proof.Poly1305.X86_64.Avx512.hv s k 4 + (VG.Proof.Poly1305.X86_64.Avx512.bhi s k / 2 ^ 40 + 2 ^ 24) := by
    intro k hk
    have hl := VG.Proof.Poly1305.X86_64.Avx512.envOf_m_lt s (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k)
    have hh := VG.Proof.Poly1305.X86_64.Avx512.envOf_m_lt s (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1)
    have b0 := hb k hk 0 (by decide)
    have b1 := hb k hk 1 (by decide)
    have b2 := hb k hk 2 (by decide)
    have b3 := hb k hk 3 (by decide)
    have b4 := hb k hk 4 (by decide)
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hv] at b0 b1 b2 b3 b4 ⊢
    rw [h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, S0 k hk, S1 k hk,
      S2 k hk, S3 k hk, S4 k hk, envOf_v, envOf_v, envOf_v, envOf_v, envOf_v,
      Limbs26.split_or hl, hpd]
    simp only [envOf, VG.Proof.Poly1305.X86_64.Avx512.blo, VG.Proof.Poly1305.X86_64.Avx512.bhi] at hl hh ⊢
    rw [or_pad (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, hy i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have := Limbs26.split_val (VG.Proof.Poly1305.X86_64.Avx512.envOf_m_lt s (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k)) (VG.Proof.Poly1305.X86_64.Avx512.bhi s k)
    rw [Limbs26.split_or (VG.Proof.Poly1305.X86_64.Avx512.envOf_m_lt s (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k))] at this
    simp only [Limbs26.val, e0, e1, e2, e3, e4]
    simp only [VG.Proof.Poly1305.X86_64.Avx512.blo] at this ⊢
    omega
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have hl := VG.Proof.Poly1305.X86_64.Avx512.envOf_m_lt s (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k)
    have hh := VG.Proof.Poly1305.X86_64.Avx512.envOf_m_lt s (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1)
    have b := hb k hk
    simp only [VG.Proof.Poly1305.X86_64.Avx512.blo, VG.Proof.Poly1305.X86_64.Avx512.bhi] at e0 e1 e2 e3 e4
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [e0]; have := b 0 (by decide); omega
    · rw [e1]; have := b 1 (by decide); omega
    · rw [e2]; have := b 2 (by decide); omega
    · rw [e3]; have := b 3 (by decide); omega
    · rw [e4]; have := b 4 (by decide); omega

theorem addGroup_ok {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.AddPre s) : WP isa (.block addGroup) s (VG.Proof.Poly1305.X86_64.Avx512.AddPost s) :=
  WP.mono (run_ok (fun _ => hp.ctx) VG.Proof.Poly1305.X86_64.Avx512.addS_eq) fun _ h =>
    VG.Proof.Poly1305.X86_64.Avx512.addPost_of h hp.h (show (envOf s).g .r9 = 0x1000000 by simp only [envOf, hp.r9]; rfl) VG.Proof.Poly1305.X86_64.Avx512.addS_y
      (VG.Proof.Poly1305.X86_64.Avx512.addS_0 _) (VG.Proof.Poly1305.X86_64.Avx512.addS_1 _) (VG.Proof.Poly1305.X86_64.Avx512.addS_2 _) (VG.Proof.Poly1305.X86_64.Avx512.addS_3 _) (VG.Proof.Poly1305.X86_64.Avx512.addS_4 _)

theorem addGroupM_ok {s : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.AddMPre s) : WP isa (.block addGroupM) s (VG.Proof.Poly1305.X86_64.Avx512.AddPost s) :=
  WP.mono (run_ok (fun _ => hp.ctx) VG.Proof.Poly1305.X86_64.Avx512.addMS_eq) fun _ h =>
    VG.Proof.Poly1305.X86_64.Avx512.addPost_of h hp.h hp.pad VG.Proof.Poly1305.X86_64.Avx512.addMS_y (VG.Proof.Poly1305.X86_64.Avx512.addMS_0 _) (VG.Proof.Poly1305.X86_64.Avx512.addMS_1 _) (VG.Proof.Poly1305.X86_64.Avx512.addMS_2 _) (VG.Proof.Poly1305.X86_64.Avx512.addMS_3 _) (VG.Proof.Poly1305.X86_64.Avx512.addMS_4 _)

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Powers`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: the powers of `r`

`powers` leaves `r⁸` in the low doubleword of every quadword of `Y` and `r^(8 -
π k)` in the high doubleword of quadword `k`, each as limbs below `2²⁷`: `r²`,
then `(r⁴, r³)` in each lane, then `(r^(4 - j), r^(4 - j))` in lane `j`
multiplied by `(r⁴, 1)`.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr or_lo ext5 mul_ge val_congr
  mul_modEq rN hreg_ge yreg_ge)
open VG.Spec.Poly1305 (P)

/-- The high doublewords of `Y`, and the limbs of `D`. -/
def yh (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat / 2 ^ 32
def dv (s : State) (k i : Nat) : Nat := (qz s (dreg i) k).toNat

theorem yh_ge (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx512.yh s k j = VG.Proof.Poly1305.X86_64.Avx512.yh s k 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.yh, yreg_ge h]

theorem cases5 {i : Nat} (hi : i < 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega

/-- `f` holds the limbs of `r10 + 2⁶⁴ r11` (of `s`), as `split` computes
them. (Stated inline, as in `Limbs26`: a definition whose body divides would
be unfolded by `rfl`, very slowly.) -/
def SplitOf (s : State) (f : Nat → Nat) : Prop :=
  f 0 = (s.gpr .r10).toNat * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
  f 1 = (s.gpr .r10).toNat * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
  f 2 = ((s.gpr .r11).toNat * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| (s.gpr .r10).toNat / 2 ^ 52) ∧
  f 3 = (s.gpr .r11).toNat * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
  f 4 = (s.gpr .r11).toNat / 2 ^ 40

theorem SplitOf.eq {s : State} {f g : Nat → Nat} (hf : VG.Proof.Poly1305.X86_64.Avx512.SplitOf s f) (hg : VG.Proof.Poly1305.X86_64.Avx512.SplitOf s g) :
    ∀ i < 5, f i = g i := by
  intro i hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  obtain ⟨b0, b1, b2, b3, b4⟩ := hg
  rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

theorem SplitOf.val {s : State} {f : Nat → Nat} (hf : VG.Proof.Poly1305.X86_64.Avx512.SplitOf s f) : Limbs26.val f = rN s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  rw [Limbs26.val, a0, a1, a2, a3, a4, rN]
  exact Limbs26.split_val (s.gpr .r10).isLt _

theorem SplitOf.lt {s : State} {f : Nat → Nat} (hf : VG.Proof.Poly1305.X86_64.Avx512.SplitOf s f) : ∀ i < 5, f i < 2 ^ 26 := by
  intro i hi
  obtain ⟨a0, a1, a2, a3, a4⟩ := hf
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  rw [Limbs26.split_or l] at a2
  rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl
  · rw [a0]; omega
  · rw [a1]; omega
  · rw [a2]; omega
  · rw [a3]; omega
  · rw [a4]; omega

theorem SplitOf.congr {s s' : State} (hg : s'.gpr = s.gpr) {f : Nat → Nat} (hf : VG.Proof.Poly1305.X86_64.Avx512.SplitOf s f) :
    VG.Proof.Poly1305.X86_64.Avx512.SplitOf s' f := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.SplitOf, hg]; exact hf

/-! ## `r` into `D` and `H` -/

def lrS : Sym := (Sym.init.run false loadRv).get (by decide +kernel)
theorem lrS_eq : Sym.init.run false loadRv = some VG.Proof.Poly1305.X86_64.Avx512.lrS := (Option.some_get _).symm

section
variable (E : Env) (k : Nat)
theorem lrS_h0 : (lrS.reg (xi (hreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h1 : (lrS.reg (xi (hreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h2 : (lrS.reg (xi (hreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_h3 : (lrS.reg (xi (hreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_h4 : (lrS.reg (xi (hreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
theorem lrS_d0 : (lrS.reg (xi (dreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d1 : (lrS.reg (xi (dreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d2 : (lrS.reg (xi (dreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem lrS_d3 : (lrS.reg (xi (dreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem lrS_d4 : (lrS.reg (xi (dreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

def srS : Sym := (Sym.init.run false splitR).get (by decide +kernel)
theorem srS_eq : Sym.init.run false splitR = some VG.Proof.Poly1305.X86_64.Avx512.srS := (Option.some_get _).symm
theorem srS_keep : ∀ i < 5, srS.reg (xi (hreg i)) = .reg (xi (hreg i)) ∧
    srS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env) (k : Nat)
theorem srS_d0 : (srS.reg (xi (dreg 0))).natw E k = E.g .r10 * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d1 : (srS.reg (xi (dreg 1))).natw E k = E.g .r10 * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d2 : (srS.reg (xi (dreg 2))).natw E k =
    (E.g .r11 * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.g .r10 / 2 ^ 52) := rfl
theorem srS_d3 : (srS.reg (xi (dreg 3))).natw E k = E.g .r11 * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := rfl
theorem srS_d4 : (srS.reg (xi (dreg 4))).natw E k = E.g .r11 / 2 ^ 40 := rfl
end

theorem loadRv_ok (s : State) :
    WP isa (.block loadRv) s fun s' => vec s s' = s' ∧
      ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.SplitOf s (VG.Proof.Poly1305.X86_64.Avx512.hv s' k) ∧ VG.Proof.Poly1305.X86_64.Avx512.SplitOf s (VG.Proof.Poly1305.X86_64.Avx512.dv s' k) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.lrS_eq) fun s' h => ⟨h.eq, fun k hk => ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.hv] <;> rw [h.natw _ hk]
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_h0]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_h1]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_h2]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_h3]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_h4]; rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.dv] <;> rw [h.natw _ hk]
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_d0]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_d1]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_d2]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_d3]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.lrS_d4]; rfl

theorem splitR_ok (s : State) :
    WP isa (.block splitR) s fun s' => vec s s' = s' ∧
      ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.SplitOf s (VG.Proof.Poly1305.X86_64.Avx512.dv s' k) ∧ ∀ i < 5, qz s' (hreg i) k = qz s (hreg i) k ∧
        qz s' (yreg i) k = qz s (yreg i) k := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.srS_eq) fun s' h => ⟨h.eq, fun k hk => ⟨?_, fun i hi => ⟨?_, ?_⟩⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.dv] <;> rw [h.natw _ hk]
    · rw [VG.Proof.Poly1305.X86_64.Avx512.srS_d0]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.srS_d1]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.srS_d2]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.srS_d3]; rfl
    · rw [VG.Proof.Poly1305.X86_64.Avx512.srS_d4]; rfl
  · rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx512.srS_keep i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx512.srS_keep i hi).2]; simp only [Q.eval, xr_xi]

/-! ## `initY` -/

def initS : Sym := (Sym.init.run false initY).get (by decide +kernel)
theorem initS_eq : Sym.init.run false initY = some VG.Proof.Poly1305.X86_64.Avx512.initS := (Option.some_get _).symm
theorem initS_shape : ∀ i < 5, initS.reg (xi (yreg i)) =
      .or (.reg (xi (hreg i))) (.shl (.reg (xi (hreg i))) 32) ∧
    initS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem initY_ok {s : State} (hh : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 32) :
    WP isa (.block initY) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i ∧ VG.Proof.Poly1305.X86_64.Avx512.yl s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i ∧ VG.Proof.Poly1305.X86_64.Avx512.yh s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.initS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qz s' (yreg i) k).toNat = VG.Proof.Poly1305.X86_64.Avx512.hv s k i * 2 ^ 32 + VG.Proof.Poly1305.X86_64.Avx512.hv s k i := by
    rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx512.initS_shape i hi).1]
    have := hh k hk i hi
    simp only [Q.natw, envOf_v, VG.Proof.Poly1305.X86_64.Avx512.hv] at this ⊢
    rw [show (qz s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qz s (hreg i) k).toNat * 2 ^ 32 by omega,
      Nat.or_comm, or_lo this]
  have := hh k hk i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.hv]; rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx512.initS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.yl]; rw [e]; omega
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.yh]; rw [e]; omega

/-! ## `pairs` -/

def prS : Sym := (Sym.init.run false pairs).get (by decide +kernel)
theorem prS_eq : Sym.init.run false pairs = some VG.Proof.Poly1305.X86_64.Avx512.prS := (Option.some_get _).symm
theorem prS_shape : ∀ i < 5, prS.reg (xi (hreg i)) =
      .unpl (.reg (xi (hreg i))) (.shr (.reg (xi (yreg i))) 32) ∧
    prS.reg (xi (yreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem pairs_ok (s : State) :
    WP isa (.block pairs) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = (if k % 2 = 0 then VG.Proof.Poly1305.X86_64.Avx512.hv s k i else VG.Proof.Poly1305.X86_64.Avx512.yh s (k - 1) i) ∧
      (qz s' (yreg i) k).toNat = VG.Proof.Poly1305.X86_64.Avx512.hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.prS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.hv, VG.Proof.Poly1305.X86_64.Avx512.yh]
    rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx512.prS_shape i hi).1]
    simp only [Q.natw, envOf_v]
  · rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx512.prS_shape i hi).2]
    simp only [Q.natw, envOf_v, VG.Proof.Poly1305.X86_64.Avx512.hv]

/-! ## `spread` -/

def spS : Sym := (Sym.init.run false spread).get (by decide +kernel)
theorem spS_eq : Sym.init.run false spread = some VG.Proof.Poly1305.X86_64.Avx512.spS := (Option.some_get _).symm

/-- Lane `j` of each `H_i` becomes quadword `0` of `H_i` (`j = 0`), quadword
`1` of `H_i`, quadword `0` of `Y_i`, or quadword `0` of `D_i` (`j = 3`). -/
def spH (E : Env) (i k : Nat) : Nat :=
  if k / 2 = 0 then E.v (xi (hreg i)) 0 else if k / 2 = 1 then E.v (xi (hreg i)) 1
  else if k / 2 = 2 then E.v (xi (yreg i)) 0 else E.v (xi (dreg i)) 0

/-- Each `Y_i` becomes `(H_i[0], 1)` in each lane (`1` as limbs, from `rax`). -/
def spY (E : Env) (i k : Nat) : Nat :=
  if k % 2 = 0 then E.v (xi (hreg i)) 0
  else if i = 0 then E.g .rax else (2 ^ 64 - 1 - E.g .rax) &&& E.g .rax

theorem spS_h (E : Env) : ∀ i < 5, ∀ k < 8, (spS.reg (xi (hreg i))).natw E k = VG.Proof.Poly1305.X86_64.Avx512.spH E i k := by
  intro i hi k hk
  rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem spS_y (E : Env) : ∀ i < 5, ∀ k < 8, (spS.reg (xi (yreg i))).natw E k = VG.Proof.Poly1305.X86_64.Avx512.spY E i k := by
  intro i hi k hk
  rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The limbs of 1. -/
def one (i : Nat) : Nat := if i = 0 then 1 else 0

theorem one_val : Limbs26.val VG.Proof.Poly1305.X86_64.Avx512.one = 1 := rfl

theorem spread_ok {s : State} (hax : s.gpr .rax = 1) :
    WP isa (.block spread) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = (if k / 2 = 0 then VG.Proof.Poly1305.X86_64.Avx512.hv s 0 i else if k / 2 = 1 then VG.Proof.Poly1305.X86_64.Avx512.hv s 1 i
        else if k / 2 = 2 then (qz s (yreg i) 0).toNat else VG.Proof.Poly1305.X86_64.Avx512.dv s 0 i) ∧
      (qz s' (yreg i) k).toNat = if k % 2 = 0 then VG.Proof.Poly1305.X86_64.Avx512.hv s 0 i else VG.Proof.Poly1305.X86_64.Avx512.one i := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.spS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.hv]
    rw [h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.spS_h _ i hi k hk]
    simp only [VG.Proof.Poly1305.X86_64.Avx512.spH, envOf_v, VG.Proof.Poly1305.X86_64.Avx512.dv]
  · rw [h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.spS_y _ i hi k hk]
    have ax : (envOf s).g .rax = 1 := by simp only [envOf, hax]; rfl
    simp only [VG.Proof.Poly1305.X86_64.Avx512.spY, ax, VG.Proof.Poly1305.X86_64.Avx512.one, envOf_v, VG.Proof.Poly1305.X86_64.Avx512.hv]
    split
    · rfl
    · split <;> decide

/-! ## `finishY` -/

def fyS : Sym := (Sym.init.run false finishY).get (by decide +kernel)
theorem fyS_eq : Sym.init.run false finishY = some VG.Proof.Poly1305.X86_64.Avx512.fyS := (Option.some_get _).symm
theorem fyS_shape : ∀ i < 5, fyS.reg (xi (yreg i)) =
      .or (.shl (.reg (xi (hreg i))) 32) (.bc (.reg (xi (hreg i)))) ∧
    fyS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem finishY_ok {s : State} (hh : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 32) :
    WP isa (.block finishY) s fun s' => vec s s' = s' ∧ ∀ k < 8, ∀ i < 5,
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i ∧ VG.Proof.Poly1305.X86_64.Avx512.yl s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s 0 i ∧ VG.Proof.Poly1305.X86_64.Avx512.yh s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.fyS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ?_⟩
  have e : (qz s' (yreg i) k).toNat = VG.Proof.Poly1305.X86_64.Avx512.hv s k i * 2 ^ 32 + VG.Proof.Poly1305.X86_64.Avx512.hv s 0 i := by
    rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx512.fyS_shape i hi).1]
    have := hh k hk i hi
    have := hh 0 (by decide) i hi
    simp only [Q.natw, envOf_v, VG.Proof.Poly1305.X86_64.Avx512.hv] at *
    rw [show (qz s (hreg i) k).toNat * 2 ^ 32 % 2 ^ 64 = (qz s (hreg i) k).toNat * 2 ^ 32 by omega,
      or_lo (by omega)]
  have := hh k hk i hi
  have := hh 0 (by decide) i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.hv]; rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx512.fyS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.yl]; rw [e]; omega
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.yh]; rw [e]; omega

/-! ## The powers -/

/-- What `powers` leaves in `Y`, for `r = R`. -/
structure YInv (s : State) (R : Nat) : Prop where
  lo : ∀ k < 8, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.yl s k) ≡ R ^ 8 [MOD P]
  hi : ∀ k < 8, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.yh s k) ≡ R ^ (8 - VG.Proof.Poly1305.X86_64.Avx512.pi k) [MOD P]
  lob : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.yl s k i < 2 ^ 27
  hib : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.yh s k i < 2 ^ 27

def powersV : List Instr :=
  loadRv ++ (initY ++ (mul ++ (pairs ++ (mul ++ (splitR ++ (spread ++ (mul ++ finishY)))))))

theorem powers_eq : powers = loadRg ++ VG.Proof.Poly1305.X86_64.Avx512.powersV := by
  simp only [powers, VG.Proof.Poly1305.X86_64.Avx512.powersV, List.append_assoc]

theorem hv_ge' (s : State) (k : Nat) {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx512.hv s k j = VG.Proof.Poly1305.X86_64.Avx512.hv s k 4 := VG.Proof.Poly1305.X86_64.Avx512.hv_ge s k h

/-- Limb functions equal below 5 (and both repeating limb 4) are equal. -/
theorem fext {f g : Nat → Nat} (hf : ∀ j, 4 ≤ j → f j = f 4) (hg : ∀ j, 4 ≤ j → g j = g 4)
    (h : ∀ i < 5, f i = g i) : f = g := ext5 hf hg h

theorem one_ge {j : Nat} (h : 4 ≤ j) : VG.Proof.Poly1305.X86_64.Avx512.one j = VG.Proof.Poly1305.X86_64.Avx512.one 4 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.one, show j ≠ 0 by omega, show (4 : Nat) ≠ 0 by decide, ite_false]

theorem one_lt {i : Nat} : VG.Proof.Poly1305.X86_64.Avx512.one i < 2 ^ 27 := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.one]; split <;> decide

/-- Limbs by lane: `a` in lane 0, `b` in lane 1, `c` in lane 2 and `d` in lane 3. -/
def quad (a b c d : Nat → Nat) (k : Nat) : Nat → Nat :=
  if k / 2 = 0 then a else if k / 2 = 1 then b else if k / 2 = 2 then c else d

theorem quad_apply (a b c d : Nat → Nat) (k i : Nat) :
    VG.Proof.Poly1305.X86_64.Avx512.quad a b c d k i = (if k / 2 = 0 then a i else if k / 2 = 1 then b i else if k / 2 = 2 then c i else d i) := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.quad]; split <;> [rfl; split <;> [rfl; split <;> rfl]]

theorem quad_ge {a b c d : Nat → Nat} (ha : ∀ j, 4 ≤ j → a j = a 4) (hb : ∀ j, 4 ≤ j → b j = b 4)
    (hc : ∀ j, 4 ≤ j → c j = c 4) (hd : ∀ j, 4 ≤ j → d j = d 4) (k : Nat) :
    ∀ j, 4 ≤ j → VG.Proof.Poly1305.X86_64.Avx512.quad a b c d k j = VG.Proof.Poly1305.X86_64.Avx512.quad a b c d k 4 := fun j h => by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.quad]; split <;> [exact ha j h; split <;> [exact hb j h; split <;> [exact hc j h; exact hd j h]]]

/-- Limbs by quadword: `a` in the even ones, `b` in the odd ones. -/
def alt (a b : Nat → Nat) (k : Nat) : Nat → Nat := if k % 2 = 0 then a else b

theorem alt_apply (a b : Nat → Nat) (k i : Nat) : VG.Proof.Poly1305.X86_64.Avx512.alt a b k i = if k % 2 = 0 then a i else b i := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.alt]; split <;> rfl

theorem alt_of_even {a b : Nat → Nat} {k : Nat} (h : k % 2 = 0) : VG.Proof.Poly1305.X86_64.Avx512.alt a b k = a := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.alt, h, ite_true]

theorem alt_of_odd {a b : Nat → Nat} {k : Nat} (h : k % 2 = 1) : VG.Proof.Poly1305.X86_64.Avx512.alt a b k = b := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.alt, h, show (1 : Nat) ≠ 0 by decide, ite_false]

theorem alt_ge {a b : Nat → Nat} (ha : ∀ j, 4 ≤ j → a j = a 4) (hb : ∀ j, 4 ≤ j → b j = b 4) (k : Nat) :
    ∀ j, 4 ≤ j → VG.Proof.Poly1305.X86_64.Avx512.alt a b k j = VG.Proof.Poly1305.X86_64.Avx512.alt a b k 4 := fun j h => by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.alt]; split <;> [exact ha j h; exact hb j h]

theorem powersV_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hax : s.gpr .rax = 1) :
    WP isa (.block VG.Proof.Poly1305.X86_64.Avx512.powersV) s fun s' => vec s s' = s' ∧ VG.Proof.Poly1305.X86_64.Avx512.YInv s' (rN s) := by
  have r8 : ∀ {t : State}, vec s t = t → t.gpr .r8 = 0x3ffffff := fun h => by rw [vec_gpr h, hr8]
  have ax : ∀ {t : State}, vec s t = t → t.gpr .rax = 1 := fun h => by rw [vec_gpr h, hax]
  -- `r` in `H` and `D`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.loadRv_ok s) fun s₁ ⟨v₁, L₁⟩ => ?_)
  let rA := VG.Proof.Poly1305.X86_64.Avx512.hv s₁ 0
  have rS : VG.Proof.Poly1305.X86_64.Avx512.SplitOf s rA := (L₁ 0 (by decide)).1
  have A_lt := fun {i : Nat} (hi : i < 5) => rS.lt i hi
  have hA₁ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₁ k i = rA i := fun k hk => (L₁ k hk).1.eq rS
  have rA_ge : ∀ j, 4 ≤ j → rA j = rA 4 := fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h
  -- `Y = r` in both doublewords.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.initY_ok fun k hk i hi => by
    rw [hA₁ k hk i hi]; have := A_lt hi; omega) fun s₂ ⟨v₂, I₂⟩ => ?_)
  have v₂' := vec_trans v₁ v₂
  -- `H = r²`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.mul_ok ⟨r8 v₂', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₃ M₃ => ?_)
  · rw [(I₂ k hk i hi).1, hA₁ k hk i hi]; have := A_lt hi; omega
  · rw [(I₂ k hk i hi).2.1, hA₁ k hk i hi]; have := A_lt hi; omega
  have hA₂ : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hv s₂ k = rA := fun k hk =>
    VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) rA_ge fun i hi => by rw [(I₂ k hk i hi).1, hA₁ k hk i hi]
  have yA₂ : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.yl s₂ k = rA := fun k hk =>
    VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yl_ge _ _ h) rA_ge fun i hi => by rw [(I₂ k hk i hi).2.1, hA₁ k hk i hi]
  let B := Limbs26.mul (rA) (rA)
  have e₃ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₃ k i = B i := fun k hk i hi => by
    rw [M₃.h k hk i hi, hA₂ k hk, yA₂ k hk]
  have yh₃ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.yh s₃ k i = rA i := fun k hk i hi => by
    simp only [VG.Proof.Poly1305.X86_64.Avx512.yh]; rw [M₃.y i hi k hk]
    have := (I₂ k hk i hi).2.2; simp only [VG.Proof.Poly1305.X86_64.Avx512.yh] at this; rw [this, hA₁ k hk i hi]
  have B_lt : ∀ i < 5, B i < 2 ^ 27 := fun i hi => by rw [← e₃ 0 (by decide) i hi]; exact M₃.hb 0 (by decide) i hi
  -- `H = (r², r)` in each lane, `Y = r²`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.pairs_ok s₃) fun s₄ ⟨v₄, P₄⟩ => ?_)
  have v₄' := vec_trans (vec_trans v₂' M₃.vec) v₄
  have h₄ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₄ k i = (if k % 2 = 0 then B i else rA i) := fun k hk i hi => by
    rw [(P₄ k hk i hi).1]; split
    · exact e₃ k hk i hi
    · exact yh₃ (k - 1) (by omega) i hi
  have y₄ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.yl s₄ k i = B i := fun k hk i hi => by
    simp only [VG.Proof.Poly1305.X86_64.Avx512.yl]; rw [(P₄ k hk i hi).2, e₃ k hk i hi]; exact Nat.mod_eq_of_lt (by have := B_lt i hi; omega)
  -- `H = (r⁴, r³)` in each lane.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.mul_ok ⟨r8 v₄', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₅ M₅ => ?_)
  · rw [h₄ k hk i hi]; have := B_lt i hi; have := A_lt hi; split <;> omega
  · rw [y₄ k hk i hi]; exact B_lt i hi
  let C4 := Limbs26.mul B B
  let C3 := Limbs26.mul (rA) B
  have yB₄ : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.yl s₄ k = B := fun k hk =>
    VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yl_ge _ _ h) (fun _ h => mul_ge _ _ h) (y₄ k hk)
  have e₅ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₅ k i = (if k % 2 = 0 then C4 i else C3 i) := fun k hk i hi => by
    rw [M₅.h k hk i hi, yB₄ k hk]
    have hf : VG.Proof.Poly1305.X86_64.Avx512.hv s₄ k = if k % 2 = 0 then B else rA := by
      split
      · exact VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) (fun _ h => mul_ge _ _ h) fun i hi => by
          rw [h₄ k hk i hi, ite_eq_left ‹_›]
      · exact VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) rA_ge fun i hi => by
          rw [h₄ k hk i hi, ite_eq_right ‹_›]
    rw [hf]; split <;> rfl
  have yv₅ : ∀ i < 5, (qz s₅ (yreg i) 0).toNat = B i := fun i hi => by
    rw [M₅.y i hi 0 (by decide), (P₄ 0 (by decide) i hi).2, e₃ 0 (by decide) i hi]
  -- `r` in `D`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.splitR_ok s₅) fun s₆ ⟨v₆, S₆⟩ => ?_)
  have v₆' := vec_trans (vec_trans v₄' M₅.vec) v₆
  have d₆ : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.dv s₆ 0 i = rA i :=
    ((S₆ 0 (by decide)).1.congr (vec_gpr (vec_trans v₄' M₅.vec)).symm).eq rS
  -- `H = (r^(4-j), r^(4-j))` in lane `j`, `Y = (r⁴, 1)`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.spread_ok (ax v₆')) fun s₇ ⟨v₇, D₇⟩ => ?_)
  have v₇' := vec_trans v₆' v₇
  have hv₆ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₆ k i = VG.Proof.Poly1305.X86_64.Avx512.hv s₅ k i := fun k hk i hi => by
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hv]; rw [((S₆ k hk).2 i hi).1]
  have e₅0 : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₅ 0 i = C4 i := fun i hi => by
    rw [e₅ 0 (by decide) i hi, ite_eq_left (show 0 % 2 = 0 from rfl)]
  have e₅1 : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₅ 1 i = C3 i := fun i hi => by
    rw [e₅ 1 (by decide) i hi, ite_eq_right (show ¬ 1 % 2 = 0 by decide)]
  have C4_lt : ∀ i < 5, C4 i < 2 ^ 27 := fun i hi => by
    have := M₅.hb 0 (by decide) i hi; rwa [e₅0 i hi] at this
  have C3_lt : ∀ i < 5, C3 i < 2 ^ 27 := fun i hi => by
    have := M₅.hb 1 (by decide) i hi; rwa [e₅1 i hi] at this
  have B_ge : ∀ j, 4 ≤ j → B j = B 4 := fun j h => mul_ge rA rA h
  have C4_ge : ∀ j, 4 ≤ j → C4 j = C4 4 := fun j h => mul_ge B B h
  have C3_ge : ∀ j, 4 ≤ j → C3 j = C3 4 := fun j h => mul_ge rA B h
  have h₇ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s₇ k i = VG.Proof.Poly1305.X86_64.Avx512.quad C4 C3 B rA k i := fun k hk i hi => by
    rw [(D₇ k hk i hi).1, hv₆ 0 (by decide) i hi, hv₆ 1 (by decide) i hi, e₅0 i hi, e₅1 i hi,
      ((S₆ 0 (by decide)).2 i hi).2, yv₅ i hi, d₆ i hi, VG.Proof.Poly1305.X86_64.Avx512.quad_apply]
  have y₇ : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.yl s₇ k i = VG.Proof.Poly1305.X86_64.Avx512.alt C4 VG.Proof.Poly1305.X86_64.Avx512.one k i := fun k hk i hi => by
    simp only [VG.Proof.Poly1305.X86_64.Avx512.yl]; rw [(D₇ k hk i hi).2, hv₆ 0 (by decide) i hi, e₅0 i hi, VG.Proof.Poly1305.X86_64.Avx512.alt_apply]
    split
    · exact Nat.mod_eq_of_lt (by have := C4_lt i hi; omega)
    · exact Nat.mod_eq_of_lt (Nat.lt_trans VG.Proof.Poly1305.X86_64.Avx512.one_lt (by decide))
  have X_lt : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.quad C4 C3 B rA k i < 2 ^ 27 := fun k hk i hi => by
    rw [VG.Proof.Poly1305.X86_64.Avx512.quad_apply]
    have := C4_lt i hi; have := C3_lt i hi; have := B_lt i hi; have := A_lt hi
    split <;> [omega; split <;> [omega; split <;> omega]]
  -- `H = r^(8 - π k)` in quadword `k`.
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.mul_ok ⟨r8 v₇', fun k hk i hi => ?_, fun k hk i hi => ?_⟩)
    fun s₈ M₈ => ?_)
  · rw [h₇ k hk i hi]; have := X_lt k hk i hi; omega
  · rw [y₇ k hk i hi, VG.Proof.Poly1305.X86_64.Avx512.alt_apply]; split
    · exact C4_lt i hi
    · exact VG.Proof.Poly1305.X86_64.Avx512.one_lt
  -- `Y`: `r⁸` and `r^(8 - π k)`.
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.finishY_ok fun k hk i hi => by have := M₈.hb k hk i hi; omega) fun s₉ ⟨v₉, F₉⟩ => ?_
  refine ⟨vec_trans (vec_trans v₇' M₈.vec) v₉, ?_⟩
  -- Values and bounds of the powers.
  have q₁ : Limbs26.val rA ≡ rN s [MOD P] := by rw [rS.val]
  have q₂ : Limbs26.val B ≡ rN s ^ 2 [MOD P] := by
    rw [show rN s ^ 2 = rN s * rN s by ring]; exact mul_modEq q₁ q₁
  have q₄ : Limbs26.val C4 ≡ rN s ^ 4 [MOD P] := by
    rw [show rN s ^ 4 = rN s ^ 2 * rN s ^ 2 by ring]; exact mul_modEq q₂ q₂
  have q₃ : Limbs26.val C3 ≡ rN s ^ 3 [MOD P] := by
    rw [show rN s ^ 3 = rN s * rN s ^ 2 by ring]; exact mul_modEq q₁ q₂
  have qX : ∀ k < 8, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.quad C4 C3 B rA k) ≡ rN s ^ (4 - k / 2) [MOD P] := fun k hk => by
    rcases (by omega : k / 2 = 0 ∨ k / 2 = 1 ∨ k / 2 = 2 ∨ k / 2 = 3) with h | h | h | h <;>
      simp only [VG.Proof.Poly1305.X86_64.Avx512.quad, h, ite_true, ite_false, show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
        show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
        show (3 : Nat) ≠ 2 by decide]
    · exact q₄
    · exact q₃
    · exact q₂
    · rw [show 4 - 3 = 1 from rfl, Nat.pow_one]; exact q₁
  have e₈ : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hv s₈ k = Limbs26.mul (VG.Proof.Poly1305.X86_64.Avx512.quad C4 C3 B rA k) (VG.Proof.Poly1305.X86_64.Avx512.alt C4 VG.Proof.Poly1305.X86_64.Avx512.one k) := fun k hk => by
    have hx : VG.Proof.Poly1305.X86_64.Avx512.hv s₇ k = VG.Proof.Poly1305.X86_64.Avx512.quad C4 C3 B rA k :=
      VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) (VG.Proof.Poly1305.X86_64.Avx512.quad_ge C4_ge C3_ge B_ge rA_ge k) (h₇ k hk)
    have hy : VG.Proof.Poly1305.X86_64.Avx512.yl s₇ k = VG.Proof.Poly1305.X86_64.Avx512.alt C4 VG.Proof.Poly1305.X86_64.Avx512.one k :=
      VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yl_ge _ _ h) (VG.Proof.Poly1305.X86_64.Avx512.alt_ge (b := VG.Proof.Poly1305.X86_64.Avx512.one) C4_ge (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.one_ge h) k) (y₇ k hk)
    exact VG.Proof.Poly1305.X86_64.Avx512.fext (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) (fun _ h => mul_ge _ _ h) fun i hi => by
      rw [M₈.h k hk i hi, hx, hy]
  have q₈ : ∀ k < 8, Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.hv s₈ k) ≡ rN s ^ (8 - VG.Proof.Poly1305.X86_64.Avx512.pi k) [MOD P] := fun k hk => by
    rw [e₈ k hk]
    rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
    · have e : 8 - VG.Proof.Poly1305.X86_64.Avx512.pi k = (4 - k / 2) + 4 := by simp only [VG.Proof.Poly1305.X86_64.Avx512.pi]; omega
      rw [VG.Proof.Poly1305.X86_64.Avx512.alt_of_even h0, e, pow_add]
      exact mul_modEq (qX k hk) q₄
    · have e : 8 - VG.Proof.Poly1305.X86_64.Avx512.pi k = 4 - k / 2 := by simp only [VG.Proof.Poly1305.X86_64.Avx512.pi]; omega
      rw [VG.Proof.Poly1305.X86_64.Avx512.alt_of_odd h0, e, ← Nat.mul_one (rN s ^ (4 - k / 2))]
      exact mul_modEq (qX k hk) (by rw [VG.Proof.Poly1305.X86_64.Avx512.one_val])
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [val_congr (F₉ k hk · · |>.2.1)]
    have := q₈ 0 (by decide)
    rwa [show VG.Proof.Poly1305.X86_64.Avx512.pi 0 = 0 from rfl] at this
  · rw [val_congr (F₉ k hk · · |>.2.2)]; exact q₈ k hk
  · rw [(F₉ k hk i hi).2.1]; exact M₈.hb 0 (by decide) i hi
  · rw [(F₉ k hk i hi).2.2]; exact M₈.hb k hk i hi

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: groups of eight blocks

Each group of eight blocks is added to the quadwords of `H` (block `π k` to
quadword `k`) and multiplied by `r⁸` (Horner's rule in eight lanes,
`Horner8.lean`), whose limbs are in the state (`MemY`); the last group is
multiplied quadword by quadword by `r^(8 - π k)`, after which the sum of the
quadwords is the accumulator.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr vec_mem vec_rd vec_wr ext5 val_congr)
open VG.Spec.Poly1305 (P leNum bytesAt)
open VG.Proof.Poly1305 (mv lanes8 absorbAll)

/-- Block `j` of the group at `rsi`. -/
def blk (s : State) (j : Nat) : List Byte := bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (16 * j)) 16

theorem blk_length (s : State) (j : Nat) : (VG.Proof.Poly1305.X86_64.Avx512.blk s j).length = 16 := Poly1305.length_bytesAt _ _ _

theorem blk_mv (s : State) (k : Nat) : mv (VG.Proof.Poly1305.X86_64.Avx512.blk s (VG.Proof.Poly1305.X86_64.Avx512.pi k)) = VG.Proof.Poly1305.X86_64.Avx512.blo s k + 2 ^ 64 * VG.Proof.Poly1305.X86_64.Avx512.bhi s k + 2 ^ 128 := by
  rw [mv, Poly1305.leNum_append, VG.Proof.Poly1305.X86_64.Avx512.blk, Poly1305.length_bytesAt, Poly1305.leNum_bytesAt_16]
  have e₁ : s.gpr .rsi + BitVec.ofNat 64 (16 * VG.Proof.Poly1305.X86_64.Avx512.pi k) = s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k)) := by
    rw [show 16 * VG.Proof.Poly1305.X86_64.Avx512.pi k = 8 * (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k) by omega]
  have e₂ : s.gpr .rsi + BitVec.ofNat 64 (16 * VG.Proof.Poly1305.X86_64.Avx512.pi k) + 8 =
      s.gpr .rsi + BitVec.ofNat 64 (8 * (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1)) := by
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
      show 16 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 8 = 8 * (2 * VG.Proof.Poly1305.X86_64.Avx512.pi k + 1) by omega]
  rw [e₂, e₁]
  simp only [VG.Proof.Poly1305.X86_64.Avx512.blo, VG.Proof.Poly1305.X86_64.Avx512.bhi, envOf]
  rfl

/-- The group at `rsi`, block by block. -/
theorem group_bytes (s : State) :
    bytesAt s.mem (s.gpr .rsi) 128 =
      VG.Proof.Poly1305.X86_64.Avx512.blk s 0 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 1 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 2 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 3 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 4 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 5 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 6 ++ VG.Proof.Poly1305.X86_64.Avx512.blk s 7 := by
  have e : ∀ n, bytesAt s.mem (s.gpr .rsi) (n + 16) =
      bytesAt s.mem (s.gpr .rsi) n ++ bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 n) 16 :=
    fun n => Poly1305.bytesAt_add _ _ n 16
  rw [(e 112 : bytesAt s.mem (s.gpr .rsi) 128 = _), (e 96 : bytesAt s.mem (s.gpr .rsi) 112 = _),
    (e 80 : bytesAt s.mem (s.gpr .rsi) 96 = _), (e 64 : bytesAt s.mem (s.gpr .rsi) 80 = _),
    (e 48 : bytesAt s.mem (s.gpr .rsi) 64 = _), (e 32 : bytesAt s.mem (s.gpr .rsi) 48 = _),
    (e 16 : bytesAt s.mem (s.gpr .rsi) 32 = _)]
  simp only [VG.Proof.Poly1305.X86_64.Avx512.blk]
  rw [show BitVec.ofNat 64 (16 * 0) = 0#64 from rfl, BitVec.add_zero]

/-- The value of quadword `k` of `H`. -/
def hval (s : State) (k : Nat) : Nat := Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.hv s k)

/-- The lanes of `H` weighted by the powers of `R` of the last group, in the
order of their blocks (block `j` is in quadword `2 j` for `j < 4`, else
`2 (j - 4) + 1`). -/
def wsum (R : Nat) (s : State) : Nat :=
  lanes8 R (VG.Proof.Poly1305.X86_64.Avx512.hval s 0) (VG.Proof.Poly1305.X86_64.Avx512.hval s 2) (VG.Proof.Poly1305.X86_64.Avx512.hval s 4) (VG.Proof.Poly1305.X86_64.Avx512.hval s 6) (VG.Proof.Poly1305.X86_64.Avx512.hval s 1) (VG.Proof.Poly1305.X86_64.Avx512.hval s 3) (VG.Proof.Poly1305.X86_64.Avx512.hval s 5) (VG.Proof.Poly1305.X86_64.Avx512.hval s 7)

/-- What holds of the vector registers between groups: `Y` holds the powers
of `R`, and the quadwords of `H` (limbs below `2²⁷`) the accumulator `X`,
after Horner's rule in eight lanes. -/
structure LaneInv (R X : Nat) (s : State) : Prop where
  y : VG.Proof.Poly1305.X86_64.Avx512.YInv s R
  hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27
  acc : VG.Proof.Poly1305.X86_64.Avx512.wsum R s ≡ R ^ 8 * X [MOD P]

theorem YInv.of_y {s s' : State} {R : Nat} (h : VG.Proof.Poly1305.X86_64.Avx512.YInv s R)
    (hy : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) : VG.Proof.Poly1305.X86_64.Avx512.YInv s' R := by
  have el : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.yl s' k = VG.Proof.Poly1305.X86_64.Avx512.yl s k := fun k hk => ext5 (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yl_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yl_ge _ _ h)
    fun i hi => by simp only [VG.Proof.Poly1305.X86_64.Avx512.yl, hy i hi k hk]
  have eh : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.yh s' k = VG.Proof.Poly1305.X86_64.Avx512.yh s k := fun k hk => ext5 (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yh_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yh_ge _ _ h)
    fun i hi => by simp only [VG.Proof.Poly1305.X86_64.Avx512.yh, hy i hi k hk]
  exact ⟨fun k hk => by rw [el k hk]; exact h.lo k hk, fun k hk => by rw [eh k hk]; exact h.hi k hk,
    fun k hk => by rw [el k hk]; exact h.lob k hk, fun k hk => by rw [eh k hk]; exact h.hib k hk⟩

/-- The multiplier in the state (`mulM`'s) is `R⁸`. -/
structure MemY (R : Nat) (s : State) : Prop where
  m : VG.Proof.Poly1305.X86_64.Avx512.MemM s
  val : Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.mr s) ≡ R ^ 8 [MOD P]

theorem Ctx.of_vec {s s' : State} (h : VG.Proof.Poly1305.X86_64.Avx512.Ctx s) (hv : vec s s' = s') : VG.Proof.Poly1305.X86_64.Avx512.Ctx s' := by
  have g := vec_gpr hv
  have rd := vec_rd hv
  have wr := vec_wr hv
  exact ⟨fun i hi => by rw [rd, wr, g]; exact h.ld i hi, fun d h₁ h₂ => by rw [rd, wr, g]; exact h.mb d h₁ h₂⟩

/-- `addGroupM`, then `mulM` by the multiplier in the state: quadword `k`
becomes `(V_k + m_(π k)) · r`. -/
theorem addMulM_ok {s : State} (hc : VG.Proof.Poly1305.X86_64.Avx512.Ctx s) (hM : VG.Proof.Poly1305.X86_64.Avx512.MemM s) (hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27) :
    WP isa (.block (addGroupM ++ mulM)) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k) ∧ (∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 27) ∧
      ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hval s' k ≡ (VG.Proof.Poly1305.X86_64.Avx512.hval s k + mv (VG.Proof.Poly1305.X86_64.Avx512.blk s (VG.Proof.Poly1305.X86_64.Avx512.pi k))) * Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.mr s) [MOD P] := by
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.addGroupM_ok ⟨hM.pad, hc, hb⟩) fun s₁ A => ?_)
  have hm : VG.Proof.Poly1305.X86_64.Avx512.mr s₁ = VG.Proof.Poly1305.X86_64.Avx512.mr s := by funext i; simp only [VG.Proof.Poly1305.X86_64.Avx512.mr, envOf, vec_gpr A.vec, vec_mem A.vec]
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.mulM_ok ⟨hc.of_vec A.vec, hM.of_mem (by rw [vec_gpr A.vec]) (vec_mem A.vec), A.hb⟩)
    fun s₂ M => ⟨vec_trans A.vec M.vec, fun i hi k hk => by rw [M.y i hi k hk, A.y i hi k hk], M.hb,
      fun k hk => ?_⟩
  simp only [VG.Proof.Poly1305.X86_64.Avx512.hval]
  rw [val_congr (M.h k hk), VG.Proof.Poly1305.X86_64.Avx512.blk_mv, ← A.h k hk, hm]
  exact Limbs26.mul_mod _ _

theorem pi_0 : VG.Proof.Poly1305.X86_64.Avx512.pi 0 = 0 := rfl
theorem pi_1 : VG.Proof.Poly1305.X86_64.Avx512.pi 1 = 4 := rfl
theorem pi_2 : VG.Proof.Poly1305.X86_64.Avx512.pi 2 = 1 := rfl
theorem pi_3 : VG.Proof.Poly1305.X86_64.Avx512.pi 3 = 5 := rfl
theorem pi_4 : VG.Proof.Poly1305.X86_64.Avx512.pi 4 = 2 := rfl
theorem pi_5 : VG.Proof.Poly1305.X86_64.Avx512.pi 5 = 6 := rfl
theorem pi_6 : VG.Proof.Poly1305.X86_64.Avx512.pi 6 = 3 := rfl
theorem pi_7 : VG.Proof.Poly1305.X86_64.Avx512.pi 7 = 7 := rfl

/-- A group before the last: the invariant for the blocks so far and the group. -/
theorem group_ok {R X : Nat} {s : State} (hc : VG.Proof.Poly1305.X86_64.Avx512.Ctx s) (hM : VG.Proof.Poly1305.X86_64.Avx512.MemY R s) (hI : VG.Proof.Poly1305.X86_64.Avx512.LaneInv R X s) :
    WP isa (.block (addGroupM ++ mulM)) s fun s' => vec s s' = s' ∧
      VG.Proof.Poly1305.X86_64.Avx512.LaneInv R (absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128)) s' := by
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.addMulM_ok hc hM.m hI.hb) fun s' ⟨hv', hy, hb, he⟩ => ⟨hv', hI.y.of_y hy, hb, ?_⟩
  have e : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hval s' k ≡ (VG.Proof.Poly1305.X86_64.Avx512.hval s k + mv (VG.Proof.Poly1305.X86_64.Avx512.blk s (VG.Proof.Poly1305.X86_64.Avx512.pi k))) * R ^ 8 [MOD P] := fun k hk =>
    (he k hk).trans (Nat.ModEq.mul_left _ hM.val)
  rw [VG.Proof.Poly1305.X86_64.Avx512.group_bytes]
  have L := VG.Proof.Poly1305.X86_64.Avx512.blk_length s
  exact Poly1305.horner8_step (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_0] using e 0 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_2] using e 2 (by decide))
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_4] using e 4 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_6] using e 6 (by decide))
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_1] using e 1 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_3] using e 3 (by decide))
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_5] using e 5 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_7] using e 7 (by decide))

/-! ## The last group -/

def shY : List Instr := (List.range 5).map fun i => srl (yreg i) (yreg i) 32

theorem last_eq : last = addGroup ++ (VG.Proof.Poly1305.X86_64.Avx512.shY ++ mul) := rfl

def shS : Sym := (Sym.init.run false VG.Proof.Poly1305.X86_64.Avx512.shY).get (by decide +kernel)
theorem shS_eq : Sym.init.run false VG.Proof.Poly1305.X86_64.Avx512.shY = some VG.Proof.Poly1305.X86_64.Avx512.shS := (Option.some_get _).symm
theorem shS_shape : ∀ i < 5, shS.reg (xi (yreg i)) = .shr (.reg (xi (yreg i))) 32 ∧
    shS.reg (xi (hreg i)) = .reg (xi (hreg i)) := by decide +kernel

theorem shY_ok (s : State) :
    WP isa (.block VG.Proof.Poly1305.X86_64.Avx512.shY) s fun s' => vec s s' = s' ∧ (∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i ∧
      VG.Proof.Poly1305.X86_64.Avx512.yl s' k i = VG.Proof.Poly1305.X86_64.Avx512.yh s k i) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.shS_eq) fun s' h => ⟨h.eq, fun k hk i hi => ⟨?_, ?_⟩⟩
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.hv]; rw [h.reg _ k hk, (VG.Proof.Poly1305.X86_64.Avx512.shS_shape i hi).2]; simp only [Q.eval, xr_xi]
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.yl, VG.Proof.Poly1305.X86_64.Avx512.yh]
    rw [h.natw _ hk, (VG.Proof.Poly1305.X86_64.Avx512.shS_shape i hi).1]
    simp only [Q.natw, envOf_v]
    have := (qz s (yreg i) k).isLt
    omega

/-- The sum of the quadwords, in the order of their blocks. -/
def bsum (s : State) : Nat :=
  VG.Proof.Poly1305.X86_64.Avx512.hval s 0 + VG.Proof.Poly1305.X86_64.Avx512.hval s 2 + VG.Proof.Poly1305.X86_64.Avx512.hval s 4 + VG.Proof.Poly1305.X86_64.Avx512.hval s 6 + VG.Proof.Poly1305.X86_64.Avx512.hval s 1 + VG.Proof.Poly1305.X86_64.Avx512.hval s 3 + VG.Proof.Poly1305.X86_64.Avx512.hval s 5 + VG.Proof.Poly1305.X86_64.Avx512.hval s 7

/-- The last group: quadword `k` multiplied by `r^(8 - π k)`, and the sum of
the quadwords is the accumulator. -/
theorem last_ok {R X : Nat} {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hr9 : s.gpr .r9 = 0x1000000)
    (hc : VG.Proof.Poly1305.X86_64.Avx512.Ctx s) (hI : VG.Proof.Poly1305.X86_64.Avx512.LaneInv R X s) :
    WP isa (.block last) s fun s' => vec s s' = s' ∧ (∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 27) ∧
      VG.Proof.Poly1305.X86_64.Avx512.bsum s' ≡ absorbAll R X (bytesAt s.mem (s.gpr .rsi) 128) [MOD P] := by
  rw [VG.Proof.Poly1305.X86_64.Avx512.last_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.addGroup_ok ⟨hr9, hc, hI.hb⟩) fun s₁ A => ?_)
  have Y₁ := hI.y.of_y A.y
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.shY_ok s₁) fun s₂ ⟨v₂, e₂⟩ => ?_)
  have hH : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hv s₂ k = VG.Proof.Poly1305.X86_64.Avx512.hv s₁ k := fun k hk => ext5 (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h)
    fun i hi => (e₂ k hk i hi).1
  have hY : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.yl s₂ k = VG.Proof.Poly1305.X86_64.Avx512.yh s₁ k := fun k hk => ext5 (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yl_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.yh_ge _ _ h)
    fun i hi => (e₂ k hk i hi).2
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.mul_ok ⟨by rw [vec_gpr v₂, vec_gpr A.vec, hr8], fun k hk i hi => by
      rw [hH k hk]; exact A.hb k hk i hi, fun k hk i hi => by rw [hY k hk]; exact Y₁.hib k hk i hi⟩)
    fun s₃ M => ⟨vec_trans (vec_trans A.vec v₂) M.vec, M.hb, ?_⟩
  have e : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hval s₃ k ≡ (VG.Proof.Poly1305.X86_64.Avx512.hval s k + mv (VG.Proof.Poly1305.X86_64.Avx512.blk s (VG.Proof.Poly1305.X86_64.Avx512.pi k))) * R ^ (8 - VG.Proof.Poly1305.X86_64.Avx512.pi k) [MOD P] := by
    intro k hk
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hval]
    rw [val_congr (M.h k hk), hH k hk, hY k hk, VG.Proof.Poly1305.X86_64.Avx512.blk_mv, ← A.h k hk]
    exact (Limbs26.mul_mod _ _).trans (Nat.ModEq.mul_left _ (Y₁.hi k hk))
  rw [VG.Proof.Poly1305.X86_64.Avx512.group_bytes]
  have L := VG.Proof.Poly1305.X86_64.Avx512.blk_length s
  exact Poly1305.horner8_last (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) hI.acc
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_0] using e 0 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_2] using e 2 (by decide))
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_4] using e 4 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_6] using e 6 (by decide))
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_1] using e 1 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_3] using e 3 (by decide))
    (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_5] using e 5 (by decide)) (by simpa only [VG.Proof.Poly1305.X86_64.Avx512.pi_7, show 8 - 7 = 1 from rfl, pow_one] using e 7 (by decide))

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Final`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: the accumulator in, and the lanes summed

`loadH` splits the accumulator into quadword 0 of `H`; after the last group,
`sumLanes` adds the quadwords into quadword 0 and carries. The rest
(`fullCarry`, `reduce` and `storeH`) is `vg_poly1305_blocks_avx2`'s code, on
quadword 0 (see `Avx2/Final.lean`), whose quadwords are those of `Avx2.qw`
(`qz_qw`).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr hN)
open VG.Spec.Poly1305 (P)

/-! ## `loadH` -/

def ldS : Sym := (Sym.init.run false loadH).get (by decide +kernel)
theorem ldS_eq : Sym.init.run false loadH = some VG.Proof.Poly1305.X86_64.Avx512.ldS := (Option.some_get _).symm
theorem ldS_y : ∀ i < 5, ldS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env)
theorem ldS_0 : ∀ k < 8, (ldS.reg (xi (hreg 0))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_1 : ∀ k < 8, (ldS.reg (xi (hreg 1))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_2 : ∀ k < 8, (ldS.reg (xi (hreg 2))).natw E k =
    ((if k = 0 then E.g .r11 else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
      (if k = 0 then E.g .r10 else 0) / 2 ^ 52) := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_3 : ∀ k < 8, (ldS.reg (xi (hreg 3))).natw E k =
    (if k = 0 then E.g .r11 else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_4 : ∀ k < 8, (ldS.reg (xi (hreg 4))).natw E k =
    ((if k = 0 then E.g .r11 else 0) / 2 ^ 40 ||| (if k = 0 then E.g .rax else 0) * 2 ^ 24 % 2 ^ 64) := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end

/-- What `loadH` leaves: the accumulator in quadword 0 of `H`, zeros in the
others, and `Y` as it was. -/
structure LoadHPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hval s' k = if k = 0 then hN s else 0
  hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 26

theorem loadH_ok {s : State} (hax : (s.gpr .rax).toNat < 4) : WP isa (.block loadH) s (VG.Proof.Poly1305.X86_64.Avx512.LoadHPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.ldS_eq) fun s' h => ?_
  have e : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hv s' k 0 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 1 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 2 = ((if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (if k = 0 then (s.gpr .r10).toNat else 0) / 2 ^ 52) ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 3 = (if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      VG.Proof.Poly1305.X86_64.Avx512.hv s' k 4 = ((if k = 0 then (s.gpr .r11).toNat else 0) / 2 ^ 40 |||
        (if k = 0 then (s.gpr .rax).toNat else 0) * 2 ^ 24 % 2 ^ 64) := fun k hk =>
    ⟨by rw [VG.Proof.Poly1305.X86_64.Avx512.hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.ldS_0 _ k hk]; rfl, by rw [VG.Proof.Poly1305.X86_64.Avx512.hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.ldS_1 _ k hk]; rfl,
      by rw [VG.Proof.Poly1305.X86_64.Avx512.hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.ldS_2 _ k hk]; rfl, by rw [VG.Proof.Poly1305.X86_64.Avx512.hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.ldS_3 _ k hk]; rfl,
      by rw [VG.Proof.Poly1305.X86_64.Avx512.hv, h.natw _ hk, VG.Proof.Poly1305.X86_64.Avx512.ldS_4 _ k hk]; rfl⟩
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  have e4 : ((s.gpr .r11).toNat / 2 ^ 40 ||| (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64) =
      (s.gpr .r11).toNat / 2 ^ 40 + 2 ^ 24 * (s.gpr .rax).toNat := by
    rw [show (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64 = 2 ^ 24 * (s.gpr .rax).toNat by omega, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, VG.Proof.Poly1305.X86_64.Avx512.ldS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4 ⊢
      rw [e4] at a4
      have := Limbs26.split_val l (s.gpr .r11).toNat
      rw [VG.Proof.Poly1305.X86_64.Avx512.hval, Limbs26.val, a0, a1, a2, a3, a4, hN]
      omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4 ⊢
      rw [VG.Proof.Poly1305.X86_64.Avx512.hval, Limbs26.val, a0, a1, a2, a3, a4]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4
      rw [e4] at a4
      rw [Limbs26.split_or l] at a2
      rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; omega
      · rw [a1]; omega
      · rw [a2]; omega
      · rw [a3]; omega
      · rw [a4]; omega
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4
      rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; decide
      · rw [a1]; decide
      · rw [a2]; decide
      · rw [a3]; decide
      · rw [a4]; decide

/-! ## `sumLanes` -/

def sumB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1⟩

def smS : Sym := (Sym.init.run false sumLanes).get (by decide +kernel)
theorem smS_eq : Sym.init.run false sumLanes = some VG.Proof.Poly1305.X86_64.Avx512.smS := (Option.some_get _).symm

theorem smS_ok : ∀ i < 5, ∀ k < 8, (smS.reg (xi (hreg i))).ok VG.Proof.Poly1305.X86_64.Avx512.sumB k = true ∧
    (smS.reg (xi (hreg i))).bnd VG.Proof.Poly1305.X86_64.Avx512.sumB k < (if i = 1 then 2 ^ 27 else 2 ^ 26) := by
  decide +kernel

/-- The sum of the quadwords of `H`, limb by limb, as `sumLanes` adds them. -/
def lsum (h : Nat → Nat → Nat) (i : Nat) : Nat :=
  h 0 i + h 4 i + (h 2 i + h 6 i) + (h 1 i + h 5 i + (h 3 i + h 7 i))

theorem smS_nat (E : Env) : ∀ i < 5, (smS.reg (xi (hreg i))).nat E 0 =
    Limbs26.carry (VG.Proof.Poly1305.X86_64.Avx512.lsum fun k j => E.v (xi (hreg j)) k) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem sumB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27) :
    EnvOK s VG.Proof.Poly1305.X86_64.Avx512.sumB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [VG.Proof.Poly1305.X86_64.Avx512.sumB] <;> first
      | omega
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [VG.Proof.Poly1305.X86_64.Avx512.sumB]; omega
  · have := BitVec.isLt (s.gpr g)
    simp only [VG.Proof.Poly1305.X86_64.Avx512.sumB]
    split
    · subst g; rw [hr8]; decide
    · omega

theorem lsum_val (h : Nat → Nat → Nat) :
    Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.lsum h) = Limbs26.val (h 0) + Limbs26.val (h 2) + Limbs26.val (h 4) + Limbs26.val (h 6) +
      Limbs26.val (h 1) + Limbs26.val (h 3) + Limbs26.val (h 5) + Limbs26.val (h 7) := by
  simp only [Limbs26.val, VG.Proof.Poly1305.X86_64.Avx512.lsum]; omega

/-- What `sumLanes` leaves in quadword 0 of `H`: the sum of the quadwords,
carried. -/
structure SumPost (s s' : State) : Prop where
  vec : vec s s' = s'
  h : VG.Proof.Poly1305.X86_64.Avx512.hval s' 0 ≡ VG.Proof.Poly1305.X86_64.Avx512.bsum s [MOD P]
  hb : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26
  hball : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' k i < 2 ^ 27

theorem sumLanes_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 8, ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s k i < 2 ^ 27) :
    WP isa (.block sumLanes) s (VG.Proof.Poly1305.X86_64.Avx512.SumPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) VG.Proof.Poly1305.X86_64.Avx512.smS_eq) fun s' h => ?_
  have hE := VG.Proof.Poly1305.X86_64.Avx512.sumB_env hr8 hb
  have e : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.hv s' 0 i = Limbs26.carry (VG.Proof.Poly1305.X86_64.Avx512.lsum (VG.Proof.Poly1305.X86_64.Avx512.hv s)) 0x3ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (VG.Proof.Poly1305.X86_64.Avx512.smS_ok i hi 0 (by decide)).1
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hv] at e ⊢
    rw [e, VG.Proof.Poly1305.X86_64.Avx512.smS_nat _ i hi]
    simp only [envOf, hr8, xr_xi]
    rfl
  refine ⟨h.eq, ?_, fun i hi => ?_, fun k hk i hi => ?_⟩
  · rw [VG.Proof.Poly1305.X86_64.Avx512.hval, Avx2.val_congr e, VG.Proof.Poly1305.X86_64.Avx512.bsum]
    have := Limbs26.carry_val (VG.Proof.Poly1305.X86_64.Avx512.lsum (VG.Proof.Poly1305.X86_64.Avx512.hv s))
    rw [VG.Proof.Poly1305.X86_64.Avx512.lsum_val] at this
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hval]
    rw [← this, Nat.ModEq, Nat.add_mul_mod_self_left]
  · obtain ⟨-, b⟩ := h.nat hE (by decide) (VG.Proof.Poly1305.X86_64.Avx512.smS_ok i hi 0 (by decide)).1
    exact Nat.lt_of_le_of_lt b (VG.Proof.Poly1305.X86_64.Avx512.smS_ok i hi 0 (by decide)).2
  · obtain ⟨-, b⟩ := h.nat hE hk (VG.Proof.Poly1305.X86_64.Avx512.smS_ok i hi k hk).1
    have := (VG.Proof.Poly1305.X86_64.Avx512.smS_ok i hi k hk).2
    simp only [VG.Proof.Poly1305.X86_64.Avx512.hv]
    split at this <;> omega

/-! ## Quadword 0 as `vg_poly1305_blocks_avx2` sees it -/

theorem hv_avx2 (s : State) {k : Nat} (hk : k < 4) (i : Nat) : Avx2.hv s k i = VG.Proof.Poly1305.X86_64.Avx512.hv s k i := by
  simp only [Avx2.hv, VG.Proof.Poly1305.X86_64.Avx512.hv, qz_qw _ _ hk]

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: the integer instructions

The short blocks of integer instructions between the vector ones that differ
from `vg_poly1305_blocks_avx2`'s, or after which the upper halves of the `zmm`
registers matter: they leave the whole vector registers as they were (`VKeep`,
unlike `Avx2.VKeep`, includes bits 511:256).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (off off_eq M0 M1)
open VG.Proof.Poly1305.X86_64.Avx2 (vec vec_gpr vec_mem vec_rd vec_wr ea_at se1 se3)

/-- What a block of integer instructions leaves as it was: the vector
registers, MXCSR and the regions. -/
structure VKeep (s s' : State) : Prop where
  xmm : s'.xmm = s.xmm
  ymmHi : s'.ymmHi = s.ymmHi
  zmmHi : s'.zmmHi = s.zmmHi
  mxcsr : s'.mxcsr = s.mxcsr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem VKeep.qz_eq {s s' : State} (h : VG.Proof.Poly1305.X86_64.Avx512.VKeep s s') (r : XReg) (k : Nat) : qz s' r k = qz s r k := by
  unfold qz State.zlane State.lane; rw [h.xmm, h.ymmHi, h.zmmHi]

theorem VKeep.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Poly1305.X86_64.Avx512.VKeep s₁ s₂) (h₂ : VG.Proof.Poly1305.X86_64.Avx512.VKeep s₂ s₃) : VG.Proof.Poly1305.X86_64.Avx512.VKeep s₁ s₃ :=
  ⟨h₂.xmm.trans h₁.xmm, h₂.ymmHi.trans h₁.ymmHi, h₂.zmmHi.trans h₁.zmmHi, h₂.mxcsr.trans h₁.mxcsr,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem VKeep.avx2 {s s' : State} (h : VG.Proof.Poly1305.X86_64.Avx512.VKeep s s') : Avx2.VKeep s s' :=
  ⟨h.xmm, h.ymmHi, h.mxcsr, h.rd, h.wr⟩

/-- Closes what `simp` leaves of a block of integer instructions. -/
macro "finish_gpr8" : tactic => `(tactic| (
  all_goals repeat' first | apply And.intro | apply VKeep.mk
  all_goals first | trivial | rfl | (intros; simp [*])))

theorem se40 : BitVec.signExtend 64 (BitVec.ofNat 32 40) = 40 := by decide
theorem se128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
theorem se7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx512.VKeep s s' ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 40)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', minBlocks, VG.Proof.Poly1305.X86_64.Avx512.se40]
  exact ⟨trivial, trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

set_option simprocs false in
theorem loadRg_ok (s : State) (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 24) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 32) 8) :
    WP isa (.block loadRg) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧ s'.gpr .rax = 1 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx512.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadRg, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, arithFlags, State.load64, State.setReg, State.setReg32, State.setFlags,
    r₁, r₂, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  finish_gpr8

set_option simprocs false in
theorem loadHw_ok (s : State) (r₀ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 0) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 8) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 16) 8) :
    WP isa (.block Impl.Poly1305.X86_64.Avx2.loadHw) s fun s' =>
      s'.gpr .r10 = s.mem.readW (off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rax = s.mem.readW (off (s.gpr .rdi) 16) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx512.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Poly1305.X86_64.Avx2.loadHw, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, State.load64, State.setReg, r₀, r₁, r₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  finish_gpr8

set_option simprocs false in
theorem rcx_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rcx = (s.gpr .rdx >>> 3) - 1 ∧ (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      VG.Proof.Poly1305.X86_64.Avx512.VKeep s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1]
  finish_gpr8

set_option simprocs false in
theorem adv_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ (∀ r, r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx512.VKeep s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1, VG.Proof.Poly1305.X86_64.Avx512.se128]
  finish_gpr8

set_option simprocs false in
theorem consts2_ok (s : State) :
    WP isa (.block Impl.Poly1305.X86_64.Avx2.consts2) s fun s' =>
      s'.gpr .rax = 5 ∧ s'.gpr .r10 = 0x7ffffff ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ VG.Proof.Poly1305.X86_64.Avx512.VKeep s s' := by
  apply WP.of_runBlock
  simp only [Impl.Poly1305.X86_64.Avx2.consts2, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc32, State.setReg32, State.setReg, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  finish_gpr8

set_option simprocs false in
theorem fin3_ok (s : State) :
    WP isa (.block [.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rdx = s.gpr .rdx &&& 7 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, VOp.exec, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.Avx512.se7, VG.Proof.Poly1305.X86_64.Avx512.se128]
  finish_gpr8

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.StoreY`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: the multipliers into the state

`storeY` computes five times the limbs of `Y` (`fiveY`), stores lane 0 of
`Y_i` at `rdi + 56 + 4 i` and of `5 Y_i` at `rdi + 72 + 4 i` (`1 ≤ i ≤ 4`),
each 16-byte store overwriting all but the first doubleword of the one before,
then the mask and the pad bit at `rdi + 104` and `rdi + 112`. The doubleword
at each of these addresses is then the low doubleword of quadword 0 of the
register stored there, which is all that the loop's `vpmuludq`s read (`MemM`).
Everything it writes is working space of the state (`wR`), below MXCSR's slot
at byte 120.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64 (off wR wR_contains sep_off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_keep)

/-! ## `fiveY` -/

def fvS : Sym := (Sym.init.run false fiveY).get (by decide +kernel)
theorem fvS_eq : Sym.init.run false fiveY = some VG.Proof.Poly1305.X86_64.Avx512.fvS := (Option.some_get _).symm

theorem fvS_shape : (∀ i < 5, fvS.reg (xi (hreg i)) = .reg (xi (hreg i)) ∧
    fvS.reg (xi (yreg i)) = .reg (xi (yreg i))) ∧
    ∀ k < 4, fvS.reg (xi (dreg k)) = .add (.shl (.reg (xi (yreg (k + 1)))) 2) (.reg (xi (yreg (k + 1)))) := by
  decide +kernel

theorem five_lo (y : Nat) : (y * 2 ^ 2 % 2 ^ 64 + y) % 2 ^ 64 % 2 ^ 32 = 5 * (y % 2 ^ 32) % 2 ^ 32 := by
  omega

theorem fiveY_ok (s : State) :
    WP isa (.block fiveY) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k) ∧
      ∀ k < 4, (qz s' (dreg k) 0).toNat % 2 ^ 32 = 5 * VG.Proof.Poly1305.X86_64.Avx512.yl s 0 (k + 1) % 2 ^ 32 := by
  refine WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx512.fvS_eq) fun s' h => ⟨h.eq, fun i hi k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · rw [h.reg _ k hk, (fvS_shape.1 i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (fvS_shape.1 i hi).2]; simp only [Q.eval, xr_xi]
  · rw [h.natw _ (by decide), fvS_shape.2 k hk]
    simp only [Q.natw, envOf_v, VG.Proof.Poly1305.X86_64.Avx512.yl]
    exact VG.Proof.Poly1305.X86_64.Avx512.five_lo _

/-! ## The stores -/

/-- 16-byte stores of `xmm` registers at `rdi + d`. -/
def stores (L : List (Nat × XReg)) : List Instr := L.map fun e => .vmovdquStore .l128 (at_ .rdi e.1) e.2

/-- The memory after `stores L` from `m`, at `p`, with the registers `x`. -/
def wrAll (m : Mem) (p : Addr) (x : XReg → BitVec 128) : List (Nat × XReg) → Mem
  | [] => m
  | e :: L => VG.Proof.Poly1305.X86_64.Avx512.wrAll (m.writeW (off p e.1) (x e.2)) p x L

theorem stores_ok : ∀ (L : List (Nat × XReg)) (s : State),
    (∀ e ∈ L, InRegions s.wr (off (s.gpr .rdi) e.1) 16) →
    WP isa (.block (VG.Proof.Poly1305.X86_64.Avx512.stores L)) s fun s' => s' = { s with
                                                         mem := VG.Proof.Poly1305.X86_64.Avx512.wrAll s.mem (s.gpr .rdi) s.xmm L }
  | [], s, _ => WP.block_nil rfl
  | e :: L, s, hw => by
    have h₀ := hw e (List.mem_cons_self ..)
    refine WP.block_cons_iff.2 ⟨{ s with mem := s.mem.writeW (off (s.gpr .rdi) e.1) (s.xmm e.2) }, ?_, ?_⟩
    · show s.store128 (off (s.gpr .rdi) e.1) (s.xmm e.2) = _
      simp only [State.store128, h₀, ite_true]
    · exact WP.mono (VG.Proof.Poly1305.X86_64.Avx512.stores_ok L _ fun e' he => hw e' (List.mem_cons_of_mem _ he)) fun s' h => h

/-- The registers `storeY` stores, at their displacements: `Y_i` at
`56 + 4 i`, and `5 Y_(k+1)` (in `D_k`) at `76 + 4 k`. -/
def stL : List (Nat × XReg) :=
  [(56, yreg 0), (60, yreg 1), (64, yreg 2), (68, yreg 3), (72, yreg 4),
   (76, dreg 0), (80, dreg 1), (84, dreg 2), (88, dreg 3)]

theorem storeY_eq : storeY = fiveY ++ (VG.Proof.Poly1305.X86_64.Avx512.stores VG.Proof.Poly1305.X86_64.Avx512.stL ++ ([.store mMask .r8, .store mPad .r9] : List Instr)) := rfl

theorem wrAll_frame {p : Addr} {x : XReg → BitVec 128} :
    ∀ (L : List (Nat × XReg)) {m m' : Mem}, (∀ e ∈ L, 56 ≤ e.1 ∧ e.1 + 16 ≤ 128) →
      Frame [wR p] m m' → Frame [wR p] m (VG.Proof.Poly1305.X86_64.Avx512.wrAll m' p x L)
  | [], _, _, _, h => h
  | e :: L, _, _, hL, h => by
    have he := hL e (List.mem_cons_self ..)
    exact VG.Proof.Poly1305.X86_64.Avx512.wrAll_frame L (fun e' h' => hL e' (List.mem_cons_of_mem _ h'))
      (h.writeW (List.mem_singleton_self _) _ (wR_contains p he.1 he.2))

theorem rd_sep (m : Mem) (p : Addr) {w n : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hn : n / 8 ≤ 16) (hk : w / 8 ≤ 16) (h : d + n / 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) n = m.readW (off p d) n :=
  Mem.readW_writeW_sep (sep_off p hd he hn hk h) (by omega)

theorem rd32_self (m : Mem) (p : Addr) (d : Nat) (v : BitVec 128) :
    (m.writeW (off p d) v).readW (off p d) 32 = v.extractLsb' 0 32 := by
  have h := readW_writeW_inside m (off p d) v (k := 0) (n := 4) (by decide) (by decide)
  rwa [show off p d + BitVec.ofNat 64 0 = off p d from BitVec.add_zero _] at h

theorem lo32_rd (m : Mem) (a : Addr) : (m.readW a 64).toNat % 2 ^ 32 = (m.readW a 32).toNat := by
  have h := readW_extract m a (w := 64) (k := 0) (n := 4) (by decide)
  rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero _] at h
  rw [← h, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- The memory `storeY` leaves. -/
def yMem (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) : Mem :=
  ((VG.Proof.Poly1305.X86_64.Avx512.wrAll m p x VG.Proof.Poly1305.X86_64.Avx512.stL).writeW (off p 104) a).writeW (off p 112) b

theorem yMem_lo (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    ∀ e ∈ VG.Proof.Poly1305.X86_64.Avx512.stL, ((VG.Proof.Poly1305.X86_64.Avx512.yMem m p x a b).readW (off p e.1) 64).toNat % 2 ^ 32 = ((x e.2).extractLsb' 0 32).toNat := by
  intro e he
  rw [VG.Proof.Poly1305.X86_64.Avx512.lo32_rd]
  simp only [VG.Proof.Poly1305.X86_64.Avx512.stL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [VG.Proof.Poly1305.X86_64.Avx512.yMem, VG.Proof.Poly1305.X86_64.Avx512.stL, VG.Proof.Poly1305.X86_64.Avx512.wrAll, VG.Proof.Poly1305.X86_64.Avx512.rd_sep, VG.Proof.Poly1305.X86_64.Avx512.rd32_self]

theorem yMem_mask (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (VG.Proof.Poly1305.X86_64.Avx512.yMem m p x a b).readW (off p 104) 64 = a := by
  rw [VG.Proof.Poly1305.X86_64.Avx512.yMem, VG.Proof.Poly1305.X86_64.Avx512.rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

theorem yMem_pad (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (VG.Proof.Poly1305.X86_64.Avx512.yMem m p x a b).readW (off p 112) 64 = b := by
  rw [VG.Proof.Poly1305.X86_64.Avx512.yMem, Mem.readW_writeW_self64]

theorem yMem_mx (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (VG.Proof.Poly1305.X86_64.Avx512.yMem m p x a b).readW (off p 120) 32 = m.readW (off p 120) 32 := by
  simp (disch := omega) only [VG.Proof.Poly1305.X86_64.Avx512.yMem, VG.Proof.Poly1305.X86_64.Avx512.stL, VG.Proof.Poly1305.X86_64.Avx512.wrAll, VG.Proof.Poly1305.X86_64.Avx512.rd_sep]

theorem yMem_frame (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    Frame [wR p] m (VG.Proof.Poly1305.X86_64.Avx512.yMem m p x a b) :=
  ((VG.Proof.Poly1305.X86_64.Avx512.wrAll_frame VG.Proof.Poly1305.X86_64.Avx512.stL (by decide) (Frame.refl _ _)).writeW (List.mem_singleton_self _) _
    (wR_contains p (d := 104) (n := 8) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (wR_contains p (d := 112) (n := 8) (by decide) (by decide))

theorem xmm_lo32 (s : State) (r : XReg) : ((s.xmm r).extractLsb' 0 32).toNat = (qz s r 0).toNat % 2 ^ 32 := by
  have e : qz s r 0 = (s.xmm r).extractLsb' 0 64 := rfl
  rw [e, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-- What `storeY` leaves. -/
structure StoreYPost (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  hy : ∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k
  frame : Frame [wR (s.gpr .rdi)] s.mem s'.mem
  mx : s'.mem.readW (off (s.gpr .rdi) 120) 32 = s.mem.readW (off (s.gpr .rdi) 120) 32
  r : ∀ i < 5, VG.Proof.Poly1305.X86_64.Avx512.mr s' i = VG.Proof.Poly1305.X86_64.Avx512.yl s 0 i
  five : ∀ i, 1 ≤ i → i < 5 → VG.Proof.Poly1305.X86_64.Avx512.ms s' i = 5 * VG.Proof.Poly1305.X86_64.Avx512.yl s 0 i % 2 ^ 32
  mask : (envOf s').mb 104 = (s.gpr .r8).toNat
  pad : (envOf s').mb 112 = (s.gpr .r9).toNat

theorem storeY_ok (s : State) (hw : ∀ d, 56 ≤ d → d + 16 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 16)
    (hw8 : ∀ d, 56 ≤ d → d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8) :
    WP isa (.block storeY) s (VG.Proof.Poly1305.X86_64.Avx512.StoreYPost s) := by
  rw [VG.Proof.Poly1305.X86_64.Avx512.storeY_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.fiveY_ok s) fun s₁ ⟨v₁, hy₁, f₁⟩ => ?_)
  obtain ⟨g₁, m₁, rd₁, wr₁, mx₁⟩ := vec_keep v₁
  have hw₁ : ∀ d, 56 ≤ d → d + 16 ≤ 128 → InRegions s₁.wr (off (s₁.gpr .rdi) d) 16 := by
    rw [g₁, wr₁]; exact hw
  have hw₁8 : ∀ d, 56 ≤ d → d + 8 ≤ 128 → InRegions s₁.wr (off (s₁.gpr .rdi) d) 8 := by
    rw [g₁, wr₁]; exact hw8
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.stores_ok VG.Proof.Poly1305.X86_64.Avx512.stL s₁ fun e he => ?_) fun s₂ e₂ => ?_)
  · have b := (show ∀ e ∈ VG.Proof.Poly1305.X86_64.Avx512.stL, 56 ≤ e.1 ∧ e.1 + 16 ≤ 128 by decide) e he
    exact hw₁ e.1 b.1 b.2
  subst e₂
  refine WP.block_cons_iff.2 ⟨_, (show State.store64 _ (off (s₁.gpr .rdi) 104) (s₁.gpr .r8) = _ by
    simp only [State.store64, hw₁8 104 (by decide) (by decide), ite_true]; rfl), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, (show State.store64 _ (off (s₁.gpr .rdi) 112) (s₁.gpr .r9) = _ by
    simp only [State.store64, hw₁8 112 (by decide) (by decide), ite_true]; rfl), WP.block_nil ?_⟩
  show VG.Proof.Poly1305.X86_64.Avx512.StoreYPost s { s₁ with
                              mem := VG.Proof.Poly1305.X86_64.Avx512.yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9) }
  have M : ∀ d, (envOf { s₁ with mem := VG.Proof.Poly1305.X86_64.Avx512.yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9) }).mb d =
      ((VG.Proof.Poly1305.X86_64.Avx512.yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9)).readW (off (s₁.gpr .rdi) d) 64).toNat :=
    fun d => rfl
  have L := VG.Proof.Poly1305.X86_64.Avx512.yMem_lo s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9)
  refine ⟨by rw [← g₁], by rw [← rd₁], by rw [← wr₁], by rw [← mx₁], fun i hi k hk => hy₁ i hi k hk, ?_, ?_, fun i hi => ?_, fun i h₁ hi => ?_, ?_, ?_⟩
  · rw [← g₁, ← m₁]; exact VG.Proof.Poly1305.X86_64.Avx512.yMem_frame _ _ _ _ _
  · rw [← g₁, ← m₁]; exact VG.Proof.Poly1305.X86_64.Avx512.yMem_mx _ _ _ _ _
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.mr]
    rw [M]
    rcases VG.Proof.Poly1305.X86_64.Avx512.cases5 hi with rfl | rfl | rfl | rfl | rfl
    · rw [L (56, yreg 0) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32, (hy₁ 0 (by decide) 0 (by decide)).2]; rfl
    · rw [L (60, yreg 1) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32, (hy₁ 1 (by decide) 0 (by decide)).2]; rfl
    · rw [L (64, yreg 2) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32, (hy₁ 2 (by decide) 0 (by decide)).2]; rfl
    · rw [L (68, yreg 3) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32, (hy₁ 3 (by decide) 0 (by decide)).2]; rfl
    · rw [L (72, yreg 4) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32, (hy₁ 4 (by decide) 0 (by decide)).2]; rfl
  · simp only [VG.Proof.Poly1305.X86_64.Avx512.ms]
    rw [M]
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    · rw [L (76, dreg 0) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32]; exact f₁ 0 (by decide)
    · rw [L (80, dreg 1) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32]; exact f₁ 1 (by decide)
    · rw [L (84, dreg 2) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32]; exact f₁ 2 (by decide)
    · rw [L (88, dreg 3) (by decide), VG.Proof.Poly1305.X86_64.Avx512.xmm_lo32]; exact f₁ 3 (by decide)
  · rw [M, VG.Proof.Poly1305.X86_64.Avx512.yMem_mask, g₁]
  · rw [M, VG.Proof.Poly1305.X86_64.Avx512.yMem_pad, g₁]

end VG.Proof.Poly1305.X86_64.Avx512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: the code as a literal

`blocksAvx512` as a literal (`materialize_code`, `Proof/Framework/Lit.lean`),
which the kernel checks once here and then evaluates in every check of the
code (constant time, `spSafe`, properties of every instruction).
-/

namespace VG

materialize_code Impl.Poly1305.X86_64.Avx512.blocksAvx512

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks`. -/
section

/-!
# Poly1305 on x86-64 with AVX-512: `vg_poly1305_blocks_avx512`

The whole function: with fewer than 40 blocks it calls
`vg_poly1305_blocks_avx2`; otherwise it absorbs the blocks eight at a time
(see `Impl/Poly1305/X86_64/Avx512.lean`), and calls `vg_poly1305_blocks` for
the last `n mod 8`.

As for AVX2 (`Avx2/Blocks.lean`), the vector code computes the right numbers
only if the accumulator on entry is below `2¹⁹⁴`, which holds whenever the
state represents a message: each block's effect on the vector registers is
established under that assumption, and its execution without it (`guard`).
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr clamp)
open VG.Proof.Poly1305.X86_64.Avx2 (guard and_exec TailPre Post tail_ok done_ok cs_ne mxMem mxMem_read
  mxMem_frame mxMem_mx mx_hi mx_bits H2_lt bytesAt_frame vec vec_trans vec_gpr vec_keep repr_frame ret_stk
  ret_frame consts_ok mxcsrIn_ok mxcsrOut_ok storeH_ok finish_ok ext5)

/-- The contract the proof is written against: `blocksX86_64`'s, with the
16 bytes of stack below the return address that its calls use. -/
def blocksAvx512X86_64 : Contract X86_64.isa := Proof.Poly1305.blocksStack 16

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint (sR (st s₀))
  stk_bl : (below (s₀.gpr .rsp) 16).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : blocksAvx512X86_64.pre s₀) : VG.Proof.Poly1305.X86_64.Avx512.APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem below8_16 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by omega) (by omega)

theorem APre.avx2 {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) : Avx2.APre s₀ :=
  ⟨hp.rd, hp.wr, hp.st_bl, hp.ret_st, hp.stk_st.sub_left (VG.Proof.Poly1305.X86_64.Avx512.below8_16 _), hp.stk_bl.sub_left (VG.Proof.Poly1305.X86_64.Avx512.below8_16 _),
    hp.nowrap⟩

/-! ## The call of `vg_poly1305_blocks_avx2` -/

theorem avx2_depth : Impl.Poly1305.X86_64.Avx2.blocksAvx2.depth = 1 := by lit_decide

theorem ret_below16 (s₀ : State) : (retR s₀).Disjoint (below (s₀.gpr .rsp) 16) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 16) (d := 16) (n := 8) (k := 16)
    (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem avx2_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) {s : State} (h : TailPre s₀ 0 s) : WP isa VG.Impl.Poly1305.X86_64.Avx512.avx2 s (Post s₀) := by
  have hn := hp.avx2.bpre.nb_lt
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have hdx : (s.gpr .rdx).toNat = nb s₀ := by rw [h.rdx, Nat.sub_zero, toNat_ofNat_lt (by omega)]
  have hsi : s.gpr .rsi = bp s₀ := by rw [h.rsi]; simp [blkAddr]
  have stS : (below (s.gpr .rsp) 16).Disjoint (sR (st s₀)) := by rw [hsp]; exact hp.stk_st
  have stB : (below (s.gpr .rsp) 16).Disjoint (blR s₀) := by rw [hsp]; exact hp.stk_bl
  refine WP.call_mx (k := Avx2.blocksAvx2X86_64) Avx2.blocksAvx2_ok BlocksImpl.avx2_nosp
    (by rw [VG.Proof.Poly1305.X86_64.Avx512.avx2_depth]; decide) (rd := [blR s₀]) (wr := [sR (st s₀)]) ?_ ?_ ?_ ?_
  · simp only [Avx2.blocksAvx2X86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, hsi, hdx]
    exact ⟨trivial, trivial, hp.st_bl, stS.sub_left (VG.Proof.Poly1305.X86_64.Avx512.below8_16 _), stS.sub_left (below_callee _ 8),
      stB.sub_left (below_callee _ 8), hp.nowrap⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨blR s₀, by simp, 0, by simp, show 0 + 16 * nb s₀ ≤ 16 * nb s₀ by omega⟩
    · exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨sR (st s₀), by simp, 0, by simp, show 0 + 128 ≤ 128 by omega⟩
  · intro s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [VG.Proof.Poly1305.X86_64.Avx512.avx2_depth] at hf
    have Fce : Frame [below (s₀.gpr .rsp) 16] s.mem s.callEntry.mem := by
      rw [State.callEntry_mem, hsp]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
    simp only [Avx2.blocksAvx2X86_64, Proof.Poly1305.blocksX86_64, State.withRegions_gpr,
      State.withRegions_mem, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), h.rdi, hsi, hdx, hm₂] at hpost
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact h.keep r hr, ?_, by rw [hmx]; exact h.mxcsr⟩,
      fun key msg hr => ?_⟩
    · refine (hf.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.ret_st
        · rw [hsp]; exact VG.Proof.Poly1305.X86_64.Avx512.ret_below16 s₀
      · exact h.frame.readW (Region.contains_self _ _) (ret_frame hp.avx2) (by decide)
    · have r₁ := repr_frame Fce (by simpa using hp.stk_st.symm) (h.repr key msg hr)
      have x := hpost key _ r₁
      have tb : bytesAt s.callEntry.mem (bp s₀) (16 * nb s₀) = bytesAt s₀.mem (bp s₀) (16 * nb s₀) := by
        rw [VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame Fce (by simpa using hp.stk_bl.symm) (by omega),
          VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_bl.symm.sub_right (Region.sub_prefix (by omega))
        · exact hp.st_bl.symm.sub_right (sub_sR _ (by omega))
      rw [tb, blks_zero, List.append_nil] at x
      exact x

/-! ## Registers, memory and the vector state -/

theorem qz_of {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (hz : s'.zmmHi = s.zmmHi)
    (r : XReg) (k : Nat) : qz s' r k = qz s r k := by
  unfold qz State.zlane State.lane; rw [hx, hy, hz]

theorem LaneInv.of_qz {R X : Nat} {s s' : State} (h : ∀ r k, qz s' r k = qz s r k)
    (hI : VG.Proof.Poly1305.X86_64.Avx512.LaneInv R X s) : VG.Proof.Poly1305.X86_64.Avx512.LaneInv R X s' := by
  have e₁ : VG.Proof.Poly1305.X86_64.Avx512.hv s' = VG.Proof.Poly1305.X86_64.Avx512.hv s := by funext k i; simp only [VG.Proof.Poly1305.X86_64.Avx512.hv, h]
  have e₂ : VG.Proof.Poly1305.X86_64.Avx512.yl s' = VG.Proof.Poly1305.X86_64.Avx512.yl s := by funext k i; simp only [VG.Proof.Poly1305.X86_64.Avx512.yl, h]
  have e₃ : VG.Proof.Poly1305.X86_64.Avx512.yh s' = VG.Proof.Poly1305.X86_64.Avx512.yh s := by funext k i; simp only [VG.Proof.Poly1305.X86_64.Avx512.yh, h]
  obtain ⟨⟨lo, hi, lob, hib⟩, hb, acc⟩ := hI
  refine ⟨⟨by rw [e₂]; exact lo, by rw [e₃]; exact hi, by rw [e₂]; exact lob, by rw [e₃]; exact hib⟩,
    by rw [e₁]; exact hb, ?_⟩
  simp only [VG.Proof.Poly1305.X86_64.Avx512.wsum, VG.Proof.Poly1305.X86_64.Avx512.hval, e₁] at acc ⊢; exact acc

theorem rcx_val (x : BitVec 64) (h : 8 ≤ x.toNat) : (x >>> 3) - 1 = BitVec.ofNat 64 (x.toNat / 8 - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem and7_toNat (x : BitVec 64) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem LaneInv.of_hy {R X : Nat} {s s' : State}
    (h : ∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k)
    (hI : VG.Proof.Poly1305.X86_64.Avx512.LaneInv R X s) : VG.Proof.Poly1305.X86_64.Avx512.LaneInv R X s' := by
  have eh : ∀ k < 8, VG.Proof.Poly1305.X86_64.Avx512.hv s' k = VG.Proof.Poly1305.X86_64.Avx512.hv s k := fun k hk => ext5 (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h) (fun _ h => VG.Proof.Poly1305.X86_64.Avx512.hv_ge _ _ h)
    fun i hi => by simp only [VG.Proof.Poly1305.X86_64.Avx512.hv, (h i hi k hk).1]
  refine ⟨hI.y.of_y fun i hi k hk => (h i hi k hk).2, fun k hk i hi => by rw [eh k hk]; exact hI.hb k hk i hi, ?_⟩
  have e : VG.Proof.Poly1305.X86_64.Avx512.wsum R s' = VG.Proof.Poly1305.X86_64.Avx512.wsum R s := by
    simp only [VG.Proof.Poly1305.X86_64.Avx512.wsum, VG.Proof.Poly1305.X86_64.Avx512.hval, eh 0 (by decide), eh 1 (by decide), eh 2 (by decide), eh 3 (by decide),
      eh 4 (by decide), eh 5 (by decide), eh 6 (by decide), eh 7 (by decide)]
  rw [e]; exact hI.acc

theorem mr_congr {s s' : State} (hg : s'.gpr .rdi = s.gpr .rdi) (hm : s'.mem = s.mem) : VG.Proof.Poly1305.X86_64.Avx512.mr s' = VG.Proof.Poly1305.X86_64.Avx512.mr s := by
  funext i; simp only [VG.Proof.Poly1305.X86_64.Avx512.mr, envOf, hg, hm]

theorem MemY.of_mem {R : Nat} {s s' : State} (h : VG.Proof.Poly1305.X86_64.Avx512.MemY R s) (hg : s'.gpr .rdi = s.gpr .rdi)
    (hm : s'.mem = s.mem) : VG.Proof.Poly1305.X86_64.Avx512.MemY R s' :=
  ⟨h.m.of_mem hg hm, by rw [VG.Proof.Poly1305.X86_64.Avx512.mr_congr hg hm]; exact h.val⟩

/-! ## The prologue -/

/-- What the prologue leaves in memory for the rest: nothing written outside
the working space `wR`, and MXCSR (bits 31:16 cleared) at byte 120. -/
structure MemOK (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [wR (st s₀)] s₀.mem m₁
  mx : m₁.readW (off (st s₀) 120) 32 = s₀.mxcsr &&& 0xffff

/-- Before group `j` of eight blocks (the loop's invariant), with the memory
`m₁` the prologue leaves. -/
structure LInv (s₀ : State) (m₁ : Mem) (j : Nat) (s : State) : Prop where
  lt : j < nb s₀ / 8
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ (8 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j)
  rdx : s.gpr .rdx = s₀.gpr .rdx
  r8 : s.gpr .r8 = 0x3ffffff
  r9 : s.gpr .r9 = 0x1000000
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : H2 s₀ < 4 → VG.Proof.Poly1305.X86_64.Avx512.LaneInv (Rn s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (8 * j))) s ∧
    VG.Proof.Poly1305.X86_64.Avx512.MemY (Rn s₀) s

theorem powers_split : Impl.Poly1305.X86_64.Avx2.consts ++ Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ powers ++
    Impl.Poly1305.X86_64.Avx2.loadHw ++ loadH ++ storeY ++
    ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr) =
    Impl.Poly1305.X86_64.Avx2.consts ++ (Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ (loadRg ++ (VG.Proof.Poly1305.X86_64.Avx512.powersV ++
      (Impl.Poly1305.X86_64.Avx2.loadHw ++ (loadH ++ (storeY ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))))))) := by
  simp only [VG.Proof.Poly1305.X86_64.Avx512.powers_eq, List.append_assoc]

theorem pro_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) (hbig : 40 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VG.Proof.Poly1305.X86_64.Avx512.VKeep s₀ s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.consts ++ Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ powers ++
      Impl.Poly1305.X86_64.Avx2.loadHw ++ loadH ++ storeY ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (fun s' => VG.Proof.Poly1305.X86_64.Avx512.MemOK s₀ s'.mem ∧ VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ s'.mem 0 s') := by
  have hp2 := hp.avx2
  rw [VG.Proof.Poly1305.X86_64.Avx512.powers_split]
  refine WP.block_append (WP.mono (consts_ok s) fun s₁ ⟨r8₁, r9₁, g₁, m₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide) (by decide), hg]
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, hk.wr]
  refine WP.block_append (WP.mono (mxcsrIn_ok s₁ (hp2.inW wr₁ rdi₁ (by omega)) (hp2.inW wr₁ rdi₁ (by omega))
    (hp2.inRW wr₁ rdi₁ (by omega)) (hp2.inRW wr₁ rdi₁ (by omega)))
    fun s₂ ⟨g₂, m₂, _, x₂, y₂, rd₂, wr₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [g₂ _ (by decide), rdi₁]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  have mm₂ : s₂.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [m₂, m₁, hm, rdi₁, k₁.mxcsr, hk.mxcsr]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.loadRg_ok s₂ (hp2.inRW wr₂' rdi₂ (by omega)) (hp2.inRW wr₂' rdi₂ (by omega)))
    fun s₃ ⟨r10₃, r11₃, ax₃, g₃, m₃, k₃⟩ => ?_)
  have r8₃ : s₃.gpr .r8 = 0x3ffffff := by rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), r8₁]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.powersV_ok r8₃ ax₃) fun s₄ ⟨v₄, Y₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, -⟩ := vec_keep v₄
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [vg₄, g₃ _ (by decide) (by decide) (by decide), rdi₂]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, k₃.wr, wr₂']
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.loadHw_ok s₄ (hp2.inRW wr₄ rdi₄ (by omega)) (hp2.inRW wr₄ rdi₄ (by omega))
    (hp2.inRW wr₄ rdi₄ (by omega))) fun s₅ ⟨a₅, b₅, c₅, g₅, m₅, k₅⟩ => ?_)
  have mm₄ : s₄.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₄, m₃, mm₂]
  have ax₅ : (s₅.gpr .rax).toNat = H2 s₀ := by
    rw [c₅, rdi₄, mm₄, mxMem_read _ _ _ (by omega)]
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₅ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx512.ldS_eq) fun _ h => h.eq)
    fun hA => VG.Proof.Poly1305.X86_64.Avx512.loadH_ok (by rw [ax₅]; exact hA)) fun s₆ ⟨v₆, L₆⟩ => ?_)
  obtain ⟨vg₆, vm₆, vrd₆, vwr₆, -⟩ := vec_keep v₆
  have rdi₆ : s₆.gpr .rdi = st s₀ := by rw [vg₆, g₅ _ (by decide) (by decide) (by decide), rdi₄]
  have wr₆ : s₆.wr = s₀.wr := by rw [vwr₆, k₅.wr, wr₄]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.storeY_ok s₆ (fun _ _ h => hp2.inW wr₆ rdi₆ h)
    (fun _ _ h => hp2.inW wr₆ rdi₆ h)) fun s₇ Y₇ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.rcx_ok s₇) fun s₈ ⟨c₈, g₈, m₈, k₈⟩ => ?_
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      s₈.gpr r = s₀.gpr r := by
    intro r a c e f g h
    rw [g₈ r c, Y₇.gpr, vg₆, g₅ r a g h, vg₄, g₃ r a g h, g₂ r a, g₁ r e f, hg]
  have r8₆ : s₆.gpr .r8 = 0x3ffffff := by rw [vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, r8₃]
  have r9₆ : s₆.gpr .r9 = 0x1000000 := by
    rw [vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, g₃ _ (by decide) (by decide) (by decide),
      g₂ _ (by decide), r9₁]
  have mm₆ : s₆.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [vm₆, m₅, mm₄]
  have hb' := hbig
  simp only [nb] at hb'
  have F₇ : Frame [wR (st s₀)] s₆.mem s₇.mem := by rw [← rdi₆]; exact Y₇.frame
  refine ⟨⟨(mxMem_frame s₀.mem (st s₀) s₀.mxcsr).trans (by rw [m₈, ← mm₆]; exact F₇),
    by rw [m₈, ← rdi₆, Y₇.mx, rdi₆, mm₆, mxMem_mx]⟩, ?_⟩
  refine ⟨by simp only [nb]; omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, rfl, fun hA => ?_⟩
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [blkAddr]
  · rw [c₈, Y₇.gpr, vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide), hg,
      VG.Proof.Poly1305.X86_64.Avx512.rcx_val _ (by omega), nb, Nat.sub_zero]
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [g₈ _ (by decide), Y₇.gpr, r8₆]
  · rw [g₈ _ (by decide), Y₇.gpr, r9₆]
  · obtain ⟨a, c, -, -, e, f, g, h⟩ := cs_ne hr
    exact gk r a c e f g h
  · rw [k₈.rd, Y₇.rd, vrd₆, k₅.rd, vrd₄, k₃.rd, rd₂, k₁.rd, hk.rd]
  · rw [k₈.wr, Y₇.wr, wr₆]
  · -- The accumulator in quadword 0, `Y` from `powers`, and its limbs in memory.
    have L := L₆ hA
    have rN₃ : Avx2.rN s₃ = Rn s₀ := by
      simp only [Avx2.rN, Rn, R0, R1]
      rw [r10₃, r11₃, rdi₂, mm₂, mxMem_read _ _ _ (by omega), mxMem_read _ _ _ (by omega)]
    have hN₅ : Avx2.hN s₅ = A0 s₀ := by
      simp only [Avx2.hN, A0]
      rw [a₅, b₅, c₅, rdi₄, mm₄, mxMem_read _ _ _ (by omega), mxMem_read _ _ _ (by omega),
        mxMem_read _ _ _ (by omega), leNum_acc]
    have Y₆ : VG.Proof.Poly1305.X86_64.Avx512.YInv s₆ (Rn s₀) := by
      rw [← rN₃]
      exact (Y₄.of_y fun i hi k hk => k₅.qz_eq _ _).of_y L.y
    have rdi₈ : s₈.gpr .rdi = s₇.gpr .rdi := g₈ _ (by decide)
    have M₇ : VG.Proof.Poly1305.X86_64.Avx512.MemM s₇ := by
      refine ⟨fun i hi => by rw [Y₇.r i hi]; exact Y₆.lob 0 (by decide) i hi, fun i h₁ hi => ?_,
        by rw [Y₇.mask, r8₆]; rfl, by rw [Y₇.pad, r9₆]; rfl⟩
      rw [Y₇.five i h₁ hi, Y₇.r i hi]
      have := Y₆.lob 0 (by decide) i hi
      omega
    have V₇ : Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.mr s₇) = Limbs26.val (VG.Proof.Poly1305.X86_64.Avx512.yl s₆ 0) := by
      simp only [Limbs26.val, Y₇.r 0 (by decide), Y₇.r 1 (by decide), Y₇.r 2 (by decide),
        Y₇.r 3 (by decide), Y₇.r 4 (by decide)]
    refine ⟨LaneInv.of_qz (fun r k => k₈.qz_eq r k) (LaneInv.of_hy Y₇.hy
      ⟨Y₆, fun k hk i hi => by have := L.hb k hk i hi; omega, ?_⟩),
      MemY.of_mem ⟨M₇, by rw [V₇]; exact Y₆.lo 0 (by decide)⟩ rdi₈ m₈⟩
    simp only [Nat.mul_zero, blks_zero, Poly1305.absorbAll_nil, VG.Proof.Poly1305.X86_64.Avx512.wsum]
    rw [L.h 0 (by decide), L.h 1 (by decide), L.h 2 (by decide), L.h 3 (by decide), L.h 4 (by decide),
      L.h 5 (by decide), L.h 6 (by decide), L.h 7 (by decide), hN₅]
    simp only [reduceCtorEq, ↓reduceIte, Poly1305.lanes8, Nat.mul_zero,
      Nat.add_zero]
    exact Nat.ModEq.refl _

/-! ## The loop -/

theorem grp_sub {s₀ : State} {j : Nat} (hj : 8 * j + 8 ≤ nb s₀) :
    Region.Sub ⟨blkAddr s₀ (8 * j), 128⟩ (blR s₀) :=
  Offset.sub_base _ (by omega)

theorem ctx_of {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdi : s.gpr .rdi = st s₀) {j : Nat} (hsi : s.gpr .rsi = blkAddr s₀ (8 * j)) (hj : 8 * j + 8 ≤ nb s₀) :
    Ctx s := by
  refine ⟨fun i hi => ?_, fun d _ h => hp.avx2.inRW hwr hdi (by omega)⟩
  have := hp.avx2.bpre.nb_lt
  refine ⟨blR s₀, by rw [hrd, hp.rd]; simp, ?_⟩
  rw [hsi, blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by rcases hi with rfl | rfl <;> omega) (by rcases hi with rfl | rfl <;> omega)

/-- The group of blocks at `rsi`, from the memory the prologue leaves. -/
theorem grp_bytes {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) {m₁ : Mem} (hm : VG.Proof.Poly1305.X86_64.Avx512.MemOK s₀ m₁) {j : Nat}
    (hj : 8 * j + 8 ≤ nb s₀) :
    bytesAt m₁ (blkAddr s₀ (8 * j)) 128 = bytesAt s₀.mem (blkAddr s₀ (8 * j)) 128 :=
  VG.Proof.Poly1305.X86_64.Avx2.bytesAt_frame hm.frame (by
    simpa using (hp.st_bl.symm.sub_left (VG.Proof.Poly1305.X86_64.Avx512.grp_sub hj)).sub_right (sub_sR _ (by omega))) (by omega)

theorem absorb_grp (s₀ : State) (R X : Nat) (j : Nat) :
    Poly1305.absorbAll R (Poly1305.absorbAll R X (blks s₀ (8 * j))) (bytesAt s₀.mem (blkAddr s₀ (8 * j)) 128) =
      Poly1305.absorbAll R X (blks s₀ (8 * (j + 1))) := by
  rw [← Poly1305.absorbAll_append (by simp only [blks, Poly1305.length_bytesAt]; omega)]
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * (8 * j) + 128 = 16 * (8 * (j + 1)) by omega]

theorem add128 (s₀ : State) (j : Nat) : blkAddr s₀ (8 * j) + 128 = blkAddr s₀ (8 * (j + 1)) := by
  simp only [blkAddr]
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, Offset.add_add,
    show 16 * (8 * j) + 128 = 16 * (8 * (j + 1)) by omega]

theorem group_body_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) {m₁ : Mem} (hm : VG.Proof.Poly1305.X86_64.Avx512.MemOK s₀ m₁) {j : Nat}
    (hj : j + 1 < nb s₀ / 8) {s : State} (h : VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ m₁ j s) :
    WP isa groupBody s fun s' => VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ m₁ (j + 1) s' ∧ s'.zf = some (decide (nb s₀ / 8 - 1 - j = 1)) := by
  have hb := hp.avx2.bpre.nb_lt
  have hc := VG.Proof.Poly1305.X86_64.Avx512.ctx_of hp h.rd h.wr h.rdi h.rsi (j := j) (by omega)
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s s' = s') (A := H2 s₀ < 4) ?_
    fun hA => VG.Proof.Poly1305.X86_64.Avx512.group_ok hc (h.acc hA).2 (h.acc hA).1) fun s₁ ⟨v₁, G₁⟩ => ?_)
  · exact WP.block_append (WP.mono (run_ok (fun _ => hc) VG.Proof.Poly1305.X86_64.Avx512.addMS_eq) fun s₁ h₁ =>
      WP.mono (run_ok (fun _ => hc.of_vec h₁.eq) VG.Proof.Poly1305.X86_64.Avx512.mulMS_eq) fun s₂ h₂ => vec_trans h₁.eq h₂.eq)
  obtain ⟨vg₁, vm₁, vrd₁, vwr₁, -⟩ := vec_keep v₁
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.adv_ok s₁) fun s₂ ⟨si₂, cx₂, zf₂, g₂, m₂, k₂⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a b, vg₁]
  have hcx : s₁.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j) := by rw [vg₁, h.rcx]
  refine ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩, ?_⟩
  · rw [gk _ (by decide) (by decide), h.rdi]
  · rw [si₂, vg₁, h.rsi, VG.Proof.Poly1305.X86_64.Avx512.add128]
  · rw [cx₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
      Nat.sub_sub]
  · rw [gk _ (by decide) (by decide), h.rdx]
  · rw [gk _ (by decide) (by decide), h.r8]
  · rw [gk _ (by decide) (by decide), h.r9]
  · obtain ⟨-, c, -, e, -⟩ := cs_ne hr
    rw [gk r e c, h.keep r hr]
  · rw [k₂.rd, vrd₁, h.rd]
  · rw [k₂.wr, vwr₁, h.wr]
  · rw [m₂, vm₁, h.mem]
  · have G := (G₁ hA).2
    rw [h.mem, h.rsi, VG.Proof.Poly1305.X86_64.Avx512.grp_bytes hp hm (by omega), VG.Proof.Poly1305.X86_64.Avx512.absorb_grp] at G
    exact ⟨LaneInv.of_qz (fun r k => k₂.qz_eq r k) G,
      (h.acc hA).2.of_mem (by rw [gk _ (by decide) (by decide)]) (by rw [m₂, vm₁])⟩
  · rw [zf₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]

theorem loop_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) {m₁ : Mem} (hm : VG.Proof.Poly1305.X86_64.Avx512.MemOK s₀ m₁) (hG : 1 < nb s₀ / 8) {s : State}
    (h₀ : VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ m₁ 0 s) : WP isa (.loop groupBody .ne) s (VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ m₁ (nb s₀ / 8 - 1)) := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = nb s₀ / 8 - 1 - j ∧ j < nb s₀ / 8 - 1 ∧ VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ m₁ j s
  have hstep : ∀ n s, Inv n s → WP isa groupBody s (fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ m₁ (nb s₀ / 8 - 1) s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.group_body_ok hp hm (by omega) hI) fun s' ⟨h', hz⟩ => ?_
    by_cases e : nb s₀ / 8 - 1 - j = 1
    · have e' : j + 1 = nb s₀ / 8 - 1 := by omega
      exact .inl ⟨by simp [eval, hz, e], e' ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, e], nb s₀ / 8 - 1 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep _ s ⟨0, rfl, by omega, h₀⟩

/-! ## The epilogue -/

theorem epi_eq : Impl.Poly1305.X86_64.Avx2.consts2 ++ last ++ sumLanes ++ Impl.Poly1305.X86_64.Avx2.fullCarry ++
    Impl.Poly1305.X86_64.Avx2.reduce ++ Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
    Impl.Poly1305.X86_64.Avx2.storeH ++
    ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr) =
    Impl.Poly1305.X86_64.Avx2.consts2 ++ (last ++ (sumLanes ++ ((Impl.Poly1305.X86_64.Avx2.fullCarry ++
      Impl.Poly1305.X86_64.Avx2.reduce) ++ (Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
      (Impl.Poly1305.X86_64.Avx2.storeH ++
        ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr)))))) := by
  simp only [List.append_assoc]

theorem epi_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) {M₁ : Mem} (hm : VG.Proof.Poly1305.X86_64.Avx512.MemOK s₀ M₁) {s : State}
    (h : VG.Proof.Poly1305.X86_64.Avx512.LInv s₀ M₁ (nb s₀ / 8 - 1) s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.consts2 ++ last ++ sumLanes ++
      Impl.Poly1305.X86_64.Avx2.fullCarry ++ Impl.Poly1305.X86_64.Avx2.reduce ++
      Impl.Poly1305.X86_64.Avx2.mxcsrOut ++ Impl.Poly1305.X86_64.Avx2.storeH ++
      ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr))) s
      (TailPre s₀ (8 * (nb s₀ / 8))) := by
  have hp2 := hp.avx2
  have hb := hp2.bpre.nb_lt
  have hlt := h.lt
  have h1 : 1 ≤ nb s₀ / 8 := by omega
  rw [VG.Proof.Poly1305.X86_64.Avx512.epi_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.consts2_ok s) fun s₁ ⟨ax₁, r10₁, g₁, m₁, k₁⟩ => ?_)
  have gk₁ : ∀ r, r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r := g₁
  have hc : Ctx s₁ := VG.Proof.Poly1305.X86_64.Avx512.ctx_of hp (by rw [k₁.rd, h.rd]) (by rw [k₁.wr, h.wr])
    (by rw [gk₁ _ (by decide) (by decide), h.rdi]) (by rw [gk₁ _ (by decide) (by decide), h.rsi]) (by omega)
  have r8₁ : s₁.gpr .r8 = 0x3ffffff := by rw [gk₁ _ (by decide) (by decide), h.r8]
  have r9₁ : s₁.gpr .r9 = 0x1000000 := by rw [gk₁ _ (by decide) (by decide), h.r9]
  -- The last group.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₁ s' = s') (A := H2 s₀ < 4) ?_
    fun hA => VG.Proof.Poly1305.X86_64.Avx512.last_ok r8₁ r9₁ hc ((h.acc hA).1.of_qz fun r k => k₁.qz_eq r k)) fun s₂ ⟨v₂, L₂⟩ => ?_)
  · rw [VG.Proof.Poly1305.X86_64.Avx512.last_eq]
    exact WP.block_append (WP.mono (run_ok (fun _ => hc) VG.Proof.Poly1305.X86_64.Avx512.addS_eq) fun _ h₁ =>
      WP.block_append (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx512.shS_eq) fun _ h₂ =>
        WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx512.mulS_eq) fun _ h₃ => vec_trans h₁.eq (vec_trans h₂.eq h₃.eq)))
  obtain ⟨vg₂, vm₂, vrd₂, vwr₂, vx₂⟩ := vec_keep v₂
  have r8₂ : s₂.gpr .r8 = 0x3ffffff := by rw [vg₂, r8₁]
  -- The sum of the quadwords.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₂ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) VG.Proof.Poly1305.X86_64.Avx512.smS_eq) fun _ h => h.eq)
    fun hA => VG.Proof.Poly1305.X86_64.Avx512.sumLanes_ok r8₂ (L₂ hA).2.1) fun s₃ ⟨v₃, S₃⟩ => ?_)
  obtain ⟨vg₃, vm₃, vrd₃, vwr₃, vx₃⟩ := vec_keep v₃
  -- `h mod p`, on quadword 0 (`vg_poly1305_blocks_avx2`'s code).
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₃ s' = s') (A := H2 s₀ < 4)
    (WP.mono (Avx2.run_ok (fun h => by cases h) Avx2.fnS_eq) fun _ h => h.eq)
    fun hA => finish_ok (by rw [vg₃, r8₂]) (by rw [vg₃, vg₂, ax₁]) (by rw [vg₃, vg₂, r10₁])
      (fun k hk i hi => by rw [VG.Proof.Poly1305.X86_64.Avx512.hv_avx2 _ hk]; exact (S₃ hA).hball k (by omega) i hi)
      (fun i hi => by rw [VG.Proof.Poly1305.X86_64.Avx512.hv_avx2 _ (by decide)]; exact (S₃ hA).hb i hi)) fun s₄ ⟨v₄, F₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, vx₄⟩ := vec_keep v₄
  have g₄ : ∀ r, r ≠ .rax → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [vg₄, vg₃, vg₂, gk₁ r a b]
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [g₄ _ (by decide) (by decide), h.rdi]
  have wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, vwr₃, vwr₂, k₁.wr, h.wr]
  have mm₄ : s₄.mem = M₁ := by rw [vm₄, vm₃, vm₂, m₁, h.mem]
  -- MXCSR restored.
  refine WP.block_append (WP.mono (mxcsrOut_ok s₄ (hp2.inRW wr₄ rdi₄ (by omega))
    (by rw [mm₄, rdi₄, hm.mx]; exact mx_hi _)) fun s₅ ⟨g₅, m₅, mx₅, x₅, y₅, rd₅, wr₅⟩ => ?_)
  have rdi₅ : s₅.gpr .rdi = st s₀ := by rw [g₅, rdi₄]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄]
  -- The accumulator stored.
  refine WP.block_append (WP.mono (storeH_ok fun d hd => hp2.inW wr₅' rdi₅ (by omega)) fun s₆ sp₆ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.Avx512.fin3_ok s₆) fun s₇ ⟨si₇, dx₇, g₇, m₇, mx₇, rd₇, wr₇⟩ => ?_
  have g₆ : ∀ r, r ≠ .rax → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r a b => by
    rw [sp₆.gpr, g₅, g₄ r a b]
  have hmx : s₇.mxcsr = s₀.mxcsr &&& 0xffff := by
    rw [mx₇, sp₆.mxcsr, mx₅, mm₄, rdi₄, hm.mx]
  have hframe : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₇.mem := by
    rw [m₇]
    refine (hm.frame.mono (by simp)).trans ?_
    rw [← mm₄, ← m₅]
    exact sp₆.frame.mono (by rw [rdi₅]; simp)
  refine ⟨by omega, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, hframe, by rw [hmx, mx_bits], fun key msg hr => ?_⟩
  · rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), h.rdi]
  · rw [si₇, g₆ _ (by decide) (by decide), h.rsi, VG.Proof.Poly1305.X86_64.Avx512.add128, Nat.sub_add_cancel h1]
  · rw [dx₇, g₆ _ (by decide) (by decide), h.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Poly1305.X86_64.Avx512.and7_toNat, toNat_ofNat_lt (by omega)]
    simp only [nb]
    omega
  · obtain ⟨a, -, c, d, -, -, g, -⟩ := cs_ne hr
    rw [g₇ r d c, g₆ r a g, h.keep r hr]
  · rw [rd₇, sp₆.rd, rd₅, vrd₄, vrd₃, vrd₂, k₁.rd, h.rd]
  · rw [wr₇, sp₆.wr, wr₅']
  · -- The accumulator represents the blocks absorbed.
    have hA := H2_lt hr
    obtain ⟨hlen, hkey, hacc⟩ := hr
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
    have hA0 : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA0]; exact Poly1305.accumulate_lt _ _
    have L := (L₂ hA).2.2
    have S := (S₃ hA).h
    obtain ⟨-, F, Fb⟩ := F₄ hA
    rw [gk₁ _ (by decide) (by decide), h.rsi, m₁, h.mem, VG.Proof.Poly1305.X86_64.Avx512.grp_bytes hp hm (by omega), VG.Proof.Poly1305.X86_64.Avx512.absorb_grp,
      Nat.sub_add_cancel h1] at L
    have e₅ : Avx2.h0 s₅ = Avx2.hv s₄ 0 := by
      funext i; simp only [Avx2.h0, Avx2.hv, Avx2.qw_of x₅ y₅]
    have e₃ : Limbs26.val (Avx2.hv s₃ 0) = VG.Proof.Poly1305.X86_64.Avx512.hval s₃ 0 :=
      congrArg Limbs26.val (funext fun i => VG.Proof.Poly1305.X86_64.Avx512.hv_avx2 _ (by decide) i)
    obtain ⟨W, -, -⟩ := Limbs26.words_val (o := Avx2.h0 s₅) (by rw [e₅]; exact Fb)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega
    · rw [← off_24, key_frame hframe, hkey']
    · rw [leNum_acc, m₇, ← rdi₅, sp₆.w0, sp₆.w1, sp₆.w2, W, e₅, F, e₃, ← hkey', clamp_key,
        Poly1305.accumulate_append hlen]
      change _ = Poly1305.absorbAll (Rn s₀) (accumulate (Rn s₀) msg) _
      rw [hA0, (S.trans L : _ ≡ _ [MOD P]),
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem body_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) (hbig : 40 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VG.Proof.Poly1305.X86_64.Avx512.VKeep s₀ s) :
    WP isa body s (TailPre s₀ (8 * (nb s₀ / 8))) :=
  WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.pro_ok hp hbig hg hm hk) fun _ h₁ =>
    WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.loop_ok hp h₁.1 (by omega) h₁.2) fun _ h₂ => VG.Proof.Poly1305.X86_64.Avx512.epi_ok hp h₁.1 h₂))

theorem correct {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.Avx512.APre s₀) : WP isa blocksAvx512 s₀ (Post s₀) := by
  have hb := hp.avx2.bpre.nb_lt
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.cmp_ok s₀) fun s₁ ⟨g₁, m₁, k₁, cf₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ < 40)) (by simp [eval, cf₁]) (fun hlt => ?_) (fun hge => ?_)
  · refine VG.Proof.Poly1305.X86_64.Avx512.avx2_ok hp ⟨by omega, by rw [g₁], by rw [g₁]; simp [blkAddr], ?_,
      fun r _ => by rw [g₁], k₁.rd, k₁.wr, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.mxcsr],
      fun key msg hr => by rw [m₁, blks_zero, List.append_nil]; exact hr⟩
    rw [g₁, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.Avx512.body_ok hp hge g₁ m₁ k₁) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (Avx2.test_ok s₂) fun s₃ ⟨z₃, g₃, m₃, mx₃, rd₃, wr₃⟩ => ?_)
    have h₃ := h₂.congr g₃ m₃ mx₃ rd₃ wr₃
    refine WP.ite (s₃.gpr .rdx &&& s₃.gpr .rdx == 0) (by simp [eval, z₃, g₃]) (fun h => ?_)
      (fun _ => tail_ok hp.avx2 h₃)
    have e : 8 * (nb s₀ / 8) = nb s₀ := by
      have := h₃.rdx
      simp only [BitVec.and_self, beq_iff_eq] at h
      rw [h] at this
      have := congrArg BitVec.toNat this
      rw [toNat_ofNat_lt (by omega)] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      simp only [nb] at this ⊢
      omega
    exact WP.block_nil (M := isa) (done_ok hp.avx2 (e ▸ h₃))

theorem blocksAvx512_ok (s : State) (hs : blocksAvx512X86_64.pre s) :
    ∃ t s', Exec isa blocksAvx512 s t s' ∧ abiPreserved s s' ∧ blocksAvx512X86_64.post s s' :=
  VG.Proof.Poly1305.X86_64.Avx512.correct (APre.of s hs)

/-! ## Constant time -/

theorem blocksAvx512_ct : ConstantTime isa blocksAvx512X86_64.pre blocksAvx512X86_64.pub blocksAvx512 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3⟩, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem blocksAvx512_verified :
    Verified X86_64.target blocksAvx512 (Spec.Poly1305.blocksContract X86_64.abi 16) :=
  Verified.of_correct VG.Proof.Poly1305.X86_64.Avx512.blocksAvx512_ok VG.Proof.Poly1305.X86_64.Avx512.blocksAvx512_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig, VG.Proof.Poly1305.X86_64.Avx512.blocksAvx512X86_64,
      Proof.Poly1305.blocksStack, Proof.Poly1305.blocksX86_64, X86_64.abi, X86_64.argRegs]
      [Avx2.sat] using Avx2.sat)

end VG.Proof.Poly1305.X86_64.Avx512

end
