module

import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps

/-!
# ML-KEM on AArch64: `decaps`, its contract and its layout

The contract of `decaps` on AArch64 (`decapsAArch64`), where its arguments
and the buffers of `scratch` are (`deL`, `offs`, `pre_of`), and what it
decapsulates (`dkD`, `cD`, `mD`, `gD`, `rhoD`), and what its first phase
establishes (`DInv`, `AfterA`), for the functions of `Kem16/` and `Kem16P/`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64 (KemLay)

/-- AArch64 contract for `decaps(dk = x0, ct = x1, key = x2, scratch = x3) ->
w0` of the parameter set `P`. -/
def decapsAArch64 (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let dk : Region := ⟨s.gpr .x0, P.dkLen⟩
    let ct : Region := ⟨s.gpr .x1, P.ctLen⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [dk, ct] ∧ s.wr = [key, scratch] ∧ dk.Disjoint key ∧ dk.Disjoint scratch ∧ ct.Disjoint key ∧
    ct.Disjoint scratch ∧ key.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint dk ∧ stack.Disjoint ct ∧
    stack.Disjoint key ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => decapsInternal P.params iters (bytesAt s.mem (s.gpr .x0) P.dkLen)
        (bytesAt s.mem (s.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x2) 32)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
      leakRho (dkRho P.params (bytesAt s₁.mem (s₁.gpr .x0) P.dkLen)) =
        leakRho (dkRho P.params (bytesAt s₂.mem (s₂.gpr .x0) P.dkLen))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- 0 `dk`, 1 `ct` (read); 2 `key`, 3 `scratch` (written), kept in `x25`–`x28`. -/
def deL (P : KemLay) : Layout where
  nb := 4
  nrd := 2
  len b := [P.dkLen, P.ctLen, 32, P.scl].getD b 0
  slot k := k

/-- The offsets of the buffers in `scratch` and `dk` that `dek`'s goals use, proved once. -/
theorem offs (hP : P.Wf) : RB + 32 ≤ P.scl ∧ KP + 32 ≤ P.scl ∧ MB + 32 ≤ P.scl ∧
    768 * P.k + 64 ≤ P.dkLen := by
  have := hP; refine ⟨?_, ?_, ?_, ?_⟩ <;> lom

/-- Arithmetic on the offsets and the buffers of `deL`: decided, or from `offs`,
or by `kom`. -/
tactic_template "dek" : tactic => `(tactic| (
  simp -failIfUnchanged only [deL, List.getD_cons_zero, List.getD_cons_succ, Layout.sc]
  first | decide | omega_using [offs (‹Pre _ _ _›).wf] | kom))

theorem pre_of (hP : P.Wf) {s₀ : State} (h : (decapsAArch64 P).pre s₀) : Pre P (deL P) s₀ := by
  obtain ⟨rd, wr, d02, d03, d12, d13, d23, sp16, k0, k1, k2, k3⟩ := h
  refine ⟨by
    intro b hb
    have hb' : b = 0 ∨ b = 1 := by change b < 2 at hb; omega_using [hb]
    rcases hb' with rfl | rfl <;> rw [rd] <;> simp [kA, deL, argReg], by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    fun k hk => hk, by dek, rfl, hP⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [deL] at hb hc hw
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega_using [hc] : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [deL] at hb
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      simp only [deL, List.getD_cons_zero, List.getD_cons_succ] <;> lom
  · simp only [deL] at hb
    rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> assumption

/-- `dk`. -/
abbrev dkD (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 0) P.dkLen
/-- `c`. -/
abbrev cD (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (kA s₀ 1) P.ctLen
/-- `m'`. -/
abbrev mD (P : KemLay) (s₀ : State) : List Byte := KPke.decM P.params (dkD P s₀) (cD P s₀)
/-- `(K', r') = G(m' ‖ h)`. -/
abbrev gD (P : KemLay) (s₀ : State) : List Byte × List Byte := G (mD P s₀ ++ KPke.dkH P.params (dkD P s₀))
/-- `ρ`. -/
abbrev rhoD (P : KemLay) (s₀ : State) : List Byte := dkRho P.params (dkD P s₀)

/-- Bytes `[o, o + n)` of `dk` or `c`, as they were. -/
theorem slice_eq {s₀ s : State} (h : KB P (deL P) s₀ s) {b o n : Nat} (hb : b < 2) (f : o + n ≤ (deL P).len b) :
    bytesAt s.mem (kA s₀ ((deL P).slot b) + BitVec.ofNat 64 o) n =
      ((bytesAt s₀.mem (kA s₀ b) ((deL P).len b)).drop o).take n := by
  rw [show (deL P).slot b = b from rfl, h.ro_bytes hb f, bytesAt_slice _ _ f]

/-! ## `m'` -/

/-- After `û'[i]` for `i < n`. -/
structure DInv (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : KB P (deL P) s₀ s
  x24 : s.gpr .x24 = 1
  u : ∀ i < n, PolyIs s.mem (sA (deL P) s₀ (yOff P i)) (ntt (KPke.dcU P.params (cD P s₀) i))

/-- A buffer of `scratch` past `û'`. -/
theorem dfar {s₀ : State} (hp : Pre P (deL P) s₀) {n o l : Nat} (hn : n ≤ P.k) (f : o + l ≤ SV P + 48)
    (h : o + l ≤ YH P ∨ YH P + 1024 * n ≤ o) :
    (R (kA s₀) (deL P).sc (YH P) (1024 * n)).Disjoint (R (kA s₀) (deL P).sc o l) :=
  sdisj hp (by kom) f (by omega_using [h])

/-- `ŝ[j] = ByteDecode₁₂(dk[384j : 384j + 384])`. -/
theorem dcS_eq (s₀ : State) {j : Nat} (hj : j < P.k) :
    ((bytesAt s₀.mem (kA s₀ 0) ((deL P).len 0)).drop (384 * j)).take 384 =
      ((KPke.dkPke P.params (dkD P s₀)).drop (384 * j)).take 384 := by
  rw [KPke.dkPke, slice_take _ (show 384 * j + 384 ≤ 384 * P.params.k from mul_succ_le hj)]
  rfl

/-! ## `G(m' ‖ h)` and `ρ` -/

/-- After the first phase. -/
structure AfterA (P : KemLay) (s₀ s : State) : Prop where
  kb : KB P (deL P) s₀ s
  x24 : s.gpr .x24 = 1
  m : bytesAt s.mem (sA (deL P) s₀ MB) 32 = mD P s₀
  kp : bytesAt s.mem (sA (deL P) s₀ KP) 32 = (gD P s₀).1
  r : bytesAt s.mem (sA (deL P) s₀ RB) 32 = (gD P s₀).2
  rho : bytesAt s.mem (sA (deL P) s₀ SB) 32 = rhoD P s₀

end VG.Proof.MlKem.AArch64.Decaps
