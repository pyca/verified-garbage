module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Bound
public import VerifiedGarbage.Impl.Poly1305.X86_64.Ifma
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: the product

`mul` multiplies the eight quadwords of the accumulator `H` by those of `Y`,
with `S` twenty times limbs 1 and 2 of `Y`, and carries: `Limbs44.mul`, with
the limbs small enough that nothing wraps and the multiply-adds take them
whole.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v)

/-- Limb `i` of quadword `k` of `H`, of `Y` and of `S`. -/
def hv (s : State) (k i : Nat) : Nat := (qz s (hreg i) k).toNat
def yv (s : State) (k i : Nat) : Nat := (qz s (yreg i) k).toNat
def sv (s : State) (k i : Nat) : Nat := (qz s (sreg i) k).toNat

def mulB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 => 2 ^ 45
    | .xmm3 | .xmm4 | .xmm5 => 2 ^ 44
    | .xmm6 | .xmm7 => 20 * 2 ^ 44
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun d => if d = 104 then 2 ^ 44 - 1 else 2 ^ 64 - 1⟩

def mulS : Sym := (Sym.init.run true mul).get (by decide +kernel)

theorem mulS_eq : Sym.init.run true mul = some mulS := (Option.some_get _).symm

theorem mulS_ok : ∀ i < 3, ∀ k < 8,
    (mulS.reg (xi (hreg i))).ok mulB k = true ∧ (mulS.reg (xi (hreg i))).bnd mulB k ≤ 2 ^ 44 := by
  decide +kernel

theorem mulS_y : ∀ i < 3, mulS.reg (xi (yreg i)) = .reg (xi (yreg i)) ∧
    mulS.reg (xi (sreg i)) = .reg (xi (sreg i)) := by
  decide +kernel

/-- The limbs `mul` computes, from the registers and memory it starts with. -/
theorem mulS_nat (E : Env) (k : Nat) : ∀ i < 3, (mulS.reg (xi (hreg i))).nat E k =
    Limbs44.carry (Limbs44.pf (fun i => E.v (xi (hreg i)) k) (fun i => E.v (xi (yreg i)) k)
      (fun i => E.v (xi (sreg i)) k)) (E.mb 104) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

/-- What `mul` needs: `H` below `2⁴⁵`, `Y` at most `2⁴⁴`, `S` twenty times
limbs 1 and 2 of `Y`, and the mask in the state. -/
structure MulPre (s : State) : Prop where
  ctx : Ctx s
  mask : (envOf s).mb 104 = 0xfffffffffff
  h : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 45
  y : ∀ k < 8, ∀ i < 3, yv s k i ≤ 2 ^ 44
  s1 : ∀ k < 8, sv s k 1 = 20 * yv s k 1
  s2 : ∀ k < 8, sv s k 2 = 20 * yv s k 2

theorem MulPre.env {s : State} (hp : MulPre s) : EnvOK s mulB := by
  refine ⟨fun r k hk => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _), fun d => ?_⟩
  · have := BitVec.isLt (qz s r k)
    have h0 := hp.h k hk 0 (by decide)
    have h1 := hp.h k hk 1 (by decide)
    have h2 := hp.h k hk 2 (by decide)
    have y0 := hp.y k hk 0 (by decide)
    have y1 := hp.y k hk 1 (by decide)
    have y2 := hp.y k hk 2 (by decide)
    have e1 := hp.s1 k hk
    have e2 := hp.s2 k hk
    simp only [hv, yv, sv, hreg, yreg, sreg] at h0 h1 h2 y0 y1 y2 e1 e2
    cases r <;> simp only [mulB]
    all_goals omega
  · have := BitVec.isLt (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64)
    simp only [mulB]
    split
    · subst d; have := hp.mask; simp only [envOf, Avx512.envOf] at this; rw [this]
    · omega

/-- What `mul` leaves: `H` times `Y`, carried, `Y` and `S` as they were, and
the rest but the sums and scratch registers as they were. -/
structure MulPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 3, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  sr : ∀ i < 3, ∀ k < 8, qz s' (sreg i) k = qz s (sreg i) k
  h : ∀ k < 8, ∀ i < 3, hv s' k i = Limbs44.mul (hv s k) (yv s k) (sv s k) i
  hb : ∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44

theorem mul_ok {s : State} (hp : MulPre s) : WP isa (.block mul) s (MulPost s) := by
  refine WP.mono (run_ok (fun _ => hp.ctx) mulS_eq) fun s' h => ?_
  have hE := hp.env
  refine ⟨h.eq, fun i hi k hk => ?_, fun i hi k hk => ?_, fun k hk i hi => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, (mulS_y i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (mulS_y i hi).2]; simp only [Q.eval, xr_xi]
  · obtain ⟨e, -⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    simp only [hv] at e ⊢
    rw [e, mulS_nat _ _ i hi, Limbs44.mul, hp.mask]
    simp only [envOf_v]
    rfl
  · obtain ⟨-, b⟩ := h.nat hE hk (mulS_ok i hi k hk).1
    exact Nat.le_trans b (mulS_ok i hi k hk).2

/-- `mul` modulo `p`. -/
theorem MulPre.mul_mod {s : State} (hp : MulPre s) {k : Nat} (hk : k < 8) :
    Limbs44.val (Limbs44.mul (hv s k) (yv s k) (sv s k)) % Spec.Poly1305.P =
      Limbs44.val (hv s k) * Limbs44.val (yv s k) % Spec.Poly1305.P := by
  refine Limbs44.mul_mod (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (hp.s1 k hk) (hp.s2 k hk)
  · exact Nat.lt_of_le_of_lt (hp.h k hk i hi) (by decide)
  · exact Nat.lt_of_le_of_lt (hp.y k hk i hi) (by decide)
  · have y1 := hp.y k hk 1 (by decide)
    have y2 := hp.y k hk 2 (by decide)
    have e1 := hp.s1 k hk
    have e2 := hp.s2 k hk
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · have : sv s k 0 = sv s k 2 := rfl
      omega
    · omega
    · omega

end VG.Proof.Poly1305.X86_64.Ifma
