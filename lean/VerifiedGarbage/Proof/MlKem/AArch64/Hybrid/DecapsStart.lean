module

import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Correct
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.CopyN
meta import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.MlKem.AArch64.KemCommon
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-!
# The hashing decapsulation's message

`J(z ‖ c)` is absorbed by the matrix's first pairs (`Hybrid.pair3`) from a
copy of `z ‖ c` in `scratch`, just below `c'`'s buffer (`jM`, `Kem16.jSrc`):
`jM_ok`, where it lies. `startJ_ok`: the all-zero third state and the copy
(`Kem16.startJ`), after `m'`, `G(m' ‖ h)` and `ρ` (`AfterA`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Decaps
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- `z ‖ c`, copied to `scratch` (argument 3 of decapsulation) from `CB - 32`. -/
def jM (P : KemLay) : Msg := ⟨Impl.MlKem.AArch64.Kem16.jSrc P, 3, CB P - 32⟩

/-- `J`'s message. -/
abbrev jE (P : KemLay) (s₀ : State) : List Byte := KPke.dkZ P.params (dkD P s₀) ++ cD P s₀

theorem jM_base (s₀ : State) : ((jM P).reg s₀).base = sA (deL P) s₀ (CB P - 32) := rfl

theorem jM_ok {s₀ : State} (hp : Pre P (deL P) s₀) (hk : Stk128 P (deL P) s₀)
    (hs : SrcOk (Impl.MlKem.AArch64.Kem16.jSrc P)) : MsgOk P (deL P) (jM P) s₀ := by
  have hw := hp.wf
  have f : CB P - 32 + (32 + P.ctLen) ≤ SV P + 48 := by lom
  have e : (jM P).reg s₀ = R (kA s₀) (deL P).sc (CB P - 32) (32 + P.ctLen) := rfl
  refine ⟨hs, fun s h => ?_, fun s h => ?_, ?_, fun r hr => ?_, ?_, fun e' he => ?_, ?_⟩
  · show s.gpr .x28 + BitVec.ofNat 64 (CB P - 32) = _
    rw [jM_base, e28 h]
  · rw [e]; exact cov_sr hp h f
  · rw [e]; exact sdisj hp (by lom) f (.inl (by lom))
  · rw [e]
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact sdisj hp f (by lom) (.inr (by lom))
    · exact sdisj hp f (by lom) (.inr (by lom))
    · exact sdisj hp f (by lom) (.inr (by lom))
    · exact below_R hp hp.scb (hp.fs f)
  · rw [e]; exact sdisj hp f (by lom) (.inr (by lom))
  · rw [e]; exact sdisj hp f (by lom) (.inr (by lom))
  · rw [e]; exact hk.R hp.scb (hp.fs f)

/-- After the first phase and `Kem16.startJ`. -/
structure AfterJ (P : KemLay) (s₀ s : State) : Prop where
  a : AfterA P s₀ s
  zero : stateAt s.mem (kA s₀ (deL P).sc) = Spec.Sha3.zero
  msg : bytesAt s.mem ((jM P).reg s₀).base (jM P).S.len = jE P s₀

theorem startJ_ok {s₀ sQ : State} (hp : Pre P (deL P) s₀) (h8 : 8 * (P.ctLen / 8) = P.ctLen)
    (hA : AfterA P s₀ sQ) :
    WP isa (.block (Impl.MlKem.AArch64.Kem16.startJ P)) sQ (AfterJ P s₀) := by
  have hw := hp.wf
  have kbA := hA.kb
  unfold Impl.MlKem.AArch64.Kem16.startJ
  rw [WP.block_append_iff, WP.block_append_iff]
  -- the third state
  have hS := hsetup hp kbA (by decide : 136 ∈ Spec.Sha3.rates)
  refine WP.mono (zeroState_ok hS (s := sQ) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun s₁ ⟨k₁, z₁⟩ => ?_
  have e28' : ∀ o l, (⟨sQ.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) (deL P).sc o l :=
    fun o l => by rw [kbA.x28]
  have kb₁ := kbA.call k₁ fun r hr => by
    rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']; exact safe_scr hp (by lom)
  have far₁ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → 200 ≤ o →
      bytesAt s₁.mem (sA (deL P) s₀ o) l = bytesAt sQ.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame k₁.frame (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr, VG.Proof.MlKem.AArch64.STr, e28']
    exact sdisj hp f (by lom) (.inr (by simp only [KEM.ST]; omega))
  have z₁' : stateAt s₁.mem (kA s₀ (deL P).sc) = Spec.Sha3.zero := by
    rw [kbA.x28, show KEM.ST = 0 from rfl, ptr_zero] at z₁; exact z₁
  have x24₁ : s₁.gpr .x24 = 1 := by rw [k₁.cs _ (by decide) (by decide), hA.x24]
  -- `z`
  refine WP.mono (KeyGen.copy_ok (S := kA s₀ 0) (D := kA s₀ 3) (so := 768 * P.k + 64) (dO := CB P - 32)
    (by decide) (by decide) (by lom) (by lom)
    (hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by lom)) (by dek) (by dek))
    kb₁.x25 kb₁.x28 (cov_r hp kb₁ (b := 0) (by dek) (by dek)) (cov_s hp kb₁ (by lom)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := kb₁.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have far₂ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ CB P - 32 ∨ CB P ≤ o) →
      bytesAt s₂.mem (sA (deL P) s₀ o) l = bytesAt s₁.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₂ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) (by lom)
  have st₂ : stateAt s₂.mem (kA s₀ (deL P).sc) = Spec.Sha3.zero := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₂ (fun r hr => by
      rw [List.mem_singleton.mp hr, stR_sc]; exact sdisj hp (by lom) (by lom) (.inl (by lom)))]
    exact z₁'
  have x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, x24₁]
  -- `c`
  refine WP.mono (KeyGen.copyN_ok (n := P.ctLen / 8) (S := kA s₀ 1) (D := kA s₀ 3) (so := 0) (dO := CB P)
    (by lom) (by decide) (by decide) ⟨by decide, by lom⟩ ⟨by lom, by lom⟩
    (by rw [h8]; exact hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by lom)) (by dek) (by dek))
    kb₂.x26 kb₂.x28 (by rw [h8]; exact cov_r hp kb₂ (b := 1) (by dek) (by dek))
    (by rw [h8]; exact cov_s hp kb₂ (by lom)))
    fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  rw [h8] at f₃ b₃
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by lom)
  have far₃ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ CB P ∨ CB P + P.ctLen ≤ o) →
      bytesAt s₃.mem (sA (deL P) s₀ o) l = bytesAt s₂.mem (sA (deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₃ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact sdisj hp f (by lom) h
  have keep : ∀ {o l : Nat}, o + l ≤ CB P - 32 → 200 ≤ o →
      bytesAt s₃.mem (sA (deL P) s₀ o) l = bytesAt sQ.mem (sA (deL P) s₀ o) l := fun h h' => by
    rw [far₃ (by lom) (.inl (by lom)), far₂ (by lom) (.inl h), far₁ (by lom) h']
  refine ⟨⟨kb₃, by rw [k₃.get .x24, x24₂], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [keep (by lom) (by decide)]; exact hA.m
  · rw [keep (by lom) (by decide)]; exact hA.kp
  · rw [keep (by lom) (by decide)]; exact hA.r
  · rw [keep (by lom) (by decide)]; exact hA.rho
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr, stR_sc]; exact sdisj hp (by lom) (by lom) (.inl (by lom)))]
    exact st₂
  · -- `z ‖ c`
    show bytesAt s₃.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P - 32)) (32 + P.ctLen) = _
    rw [bytesAt_add, ptr_add, show CB P - 32 + 32 = CB P by lom, b₃,
      show bytesAt s₃.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P - 32)) 32 =
        bytesAt s₂.mem (kA s₀ 3 + BitVec.ofNat 64 (CB P - 32)) 32 from far₃ (by lom) (.inl (by lom)), b₂,
      kb₂.ro_bytes (b := 1) (by dek) (by dek), ptr_zero]
    have hz := slice_eq kb₁ (b := 0) (o := 768 * P.k + 64) (n := 32) (by decide) (by dek)
    rw [show (deL P).slot 0 = 0 from rfl] at hz
    rw [hz]
    rfl

/-- `decapsAArch64 P`, with 128 bytes of stack. -/
def decapsAArch64S (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let dk : Region := ⟨s.gpr .x0, P.dkLen⟩
    let ct : Region := ⟨s.gpr .x1, P.ctLen⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 128, 128⟩
    s.rd = [dk, ct] ∧ s.wr = [key, scratch] ∧ dk.Disjoint key ∧ dk.Disjoint scratch ∧ ct.Disjoint key ∧
    ct.Disjoint scratch ∧ key.Disjoint scratch ∧ 128 ≤ s.sp.toNat ∧ stack.Disjoint dk ∧ stack.Disjoint ct ∧
    stack.Disjoint key ∧ stack.Disjoint scratch
  post := (decapsAArch64 P).post
  pub := (decapsAArch64 P).pub

theorem preSD {s : State} (h : (decapsAArch64S P).pre s) : (decapsAArch64 P).pre s ∧ Stk128 P (deL P) s := by
  obtain ⟨rd, wr, d02, d03, d12, d13, d23, sp128, k0, k1, k2, k3⟩ := h
  have sub : Region.Sub ⟨s.sp - 16, 16⟩ (frame s.sp) := below_sub (by decide) (by decide)
  refine ⟨⟨rd, wr, d02, d03, d12, d13, d23, by omega,
    k0.sub_left sub, k1.sub_left sub, k2.sub_left sub, k3.sub_left sub⟩, sp128, ?_⟩
  intro b hb
  have hb : b < 4 := hb
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
  · exact k0
  · exact k1
  · exact k2
  · exact k3

end VG.Proof.MlKem.AArch64.Hybrid
