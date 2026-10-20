module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Mul
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Load
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: loading blocks

`addGroup` splits the eight blocks at `rsi` into limbs (block `π k` in
quadword `k`, as for AVX-512) and adds them, with the pad bit from the state,
to `H`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec)
open VG.Proof.Poly1305.X86_64.Avx512 (qz envOf_v pi blo bhi envOf_m_lt cases8)

def addS : Sym := (Sym.init.run true addGroup).get (by decide +kernel)

theorem addS_eq : Sym.init.run true addGroup = some addS := (Option.some_get _).symm

theorem addS_y : ∀ i < 3, addS.reg (xi (yreg i)) = .reg (xi (yreg i)) ∧
    addS.reg (xi (sreg i)) = .reg (xi (sreg i)) := by decide +kernel

section
variable (E : Env)

theorem addS_0 : ∀ k < 8, (addS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + (E.m (2 * pi k) &&& E.mb 104)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_1 : ∀ k < 8, (addS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + ((E.m (2 * pi k) / 2 ^ 44 ||| E.m (2 * pi k + 1) * 2 ^ 20 % 2 ^ 64) &&&
      E.mb 104)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_2 : ∀ k < 8, (addS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * pi k + 1) / 2 ^ 24 ||| E.mb 112)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

/-- The mask `2⁴⁴ - 1` and the pad bit `2⁴⁰` in the state. -/
structure Consts (s : State) : Prop where
  mask : (envOf s).mb 104 = 0xfffffffffff
  pad : (envOf s).mb 112 = 0x10000000000

theorem Consts.of_mem {s s' : State} (h : Consts s) (hg : s'.gpr .rdi = s.gpr .rdi) (hm : s'.mem = s.mem) :
    Consts s' := by
  have e : (envOf s').mb = (envOf s).mb := by
    funext d; simp only [envOf, Avx512.envOf, hg, hm]
  exact ⟨by rw [e]; exact h.mask, by rw [e]; exact h.pad⟩

structure AddPre (s : State) : Prop where
  ctx : Ctx s
  c : Consts s
  h : ∀ k < 8, ∀ i < 3, hv s k i ≤ 2 ^ 44

/-- What `addGroup` leaves: block `π k`, with its pad bit, added to
quadword `k` of `H`, and `Y` and `S` as they were. -/
structure AddPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 3, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  sr : ∀ i < 3, ∀ k < 8, qz s' (sreg i) k = qz s (sreg i) k
  h : ∀ k < 8, Limbs44.val (hv s' k) = Limbs44.val (hv s k) + (blo s k + 2 ^ 64 * bhi s k + 2 ^ 128)
  hb : ∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 45

theorem addGroup_ok {s : State} (hp : AddPre s) : WP isa (.block addGroup) s (AddPost s) := by
  refine WP.mono (run_ok (fun _ => hp.ctx) addS_eq) fun s' h => ?_
  have H : ∀ k < 8, hv s' k 0 = hv s k 0 + blo s k % 2 ^ 44 ∧
      hv s' k 1 = hv s k 1 + (blo s k / 2 ^ 44 + 2 ^ 20 * (bhi s k % 2 ^ 24)) ∧
      hv s' k 2 = hv s k 2 + (2 ^ 40 + bhi s k / 2 ^ 24) := by
    intro k hk
    have hl := envOf_m_lt s (2 * pi k)
    have hh := envOf_m_lt s (2 * pi k + 1)
    have b0 := hp.h k hk 0 (by decide)
    have b1 := hp.h k hk 1 (by decide)
    have b2 := hp.h k hk 2 (by decide)
    simp only [hv] at b0 b1 b2 ⊢
    rw [h.natw _ hk, h.natw _ hk, h.natw _ hk, addS_0 _ k hk, addS_1 _ k hk, addS_2 _ k hk,
      envOf_v, envOf_v, envOf_v, hp.c.mask, hp.c.pad, Limbs44.and_mask, Limbs44.split1 hl,
      Limbs44.split_pad hh]
    simp only [blo, bhi, envOf]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, (addS_y i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (addS_y i hi).2]; simp only [Q.eval, xr_xi]
  · obtain ⟨e0, e1, e2⟩ := H k hk
    have := Limbs44.split_val (blo s k) (bhi s k) 1
    simp only [Limbs44.val, e0, e1, e2]
    omega
  · obtain ⟨e0, e1, e2⟩ := H k hk
    have hl := envOf_m_lt s (2 * pi k)
    have hh := envOf_m_lt s (2 * pi k + 1)
    have b := hp.h k hk
    simp only [blo, bhi] at e0 e1 e2
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [e0]; have := b 0 (by decide); omega
    · rw [e1]; have := b 1 (by decide); omega
    · rw [e2]; have := b 2 (by decide); omega

end VG.Proof.Poly1305.X86_64.Ifma
