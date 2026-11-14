module

import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.TCB.X86_64.Residue
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86_64
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# HMAC's `init` for a key of any length on x86-64, choosing on entry

`initEntry B short long` compares `key_len` (`rcx`) with `B + 1` and runs
`long`, verified against `VG.Spec.Hmac.Instance.initAnyKeyContract`, for a key
longer than a block, and `short`, verified against `initContract` (a key of at
most a block), otherwise (`Verified.entryBranch`). The comparison writes only
the flags, which no contract reads, and leaks nothing; the branch depends
only on `key_len`, which is public.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64

theorem initEntry_verified {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ : Nat}
    (hS : Verified X86_64.target short (I.initContract X86_64.abi n₁))
    (hL : Verified X86_64.target long (I.initAnyKeyContract X86_64.abi n₂))
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize + 1 < 2 ^ 31)
    (hsat : ∃ s, (I.initAnyKeyContract X86_64.abi n₂).pre s) :
    Verified X86_64.target (Impl.Pbkdf2.Md.X86_64.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract X86_64.abi n₂) := by
  refine Verified.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .rcx).toNat))
    (fun _ => []) hL hS (fun s hs => ⟨_, rfl, ?_, fun _ => ⟨hs, fun s' a q => ⟨a, q⟩⟩, fun hp => ?_⟩) ?_ hsat
  · show Option.map (!·) (some (decide ((s.gpr .rcx).toNat <
      ((BitVec.ofNat 32 (I.S.H.blockSize + 1)).signExtend 64).toNat))) = _
    rw [Calls.sx_ofNat hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hB])]
    simp only [Option.map_some, ← decide_not, Nat.not_lt]
  · have hk : (s.gpr .rcx).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega_using [this]
    refine ⟨?_, fun s' a q => ⟨a, q⟩⟩
    sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs] at hs
    sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs]
    obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega_using [h₁]⟩
    obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega_using [hn]⟩
    simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hs ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨c0, c1, c2, c3⟩, n1, n2, n3⟩ := hs
    have sb := Offset.sub_below (s.gpr .rsp) (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
      (by omega_using [hn]) (by omega_using [hn])
    exact ⟨by omega_using [hn, h0], h1, h2, h3, h4, h5, h6, h7, ⟨c0, c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2,
      n3, hk⟩
  · intro s s' u u' hs hs' hq e e'
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs] at hq'
    obtain ⟨_, _, _, _, h4⟩ := hq'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    exact ⟨rfl, by rw [h4], fun _ => hq, fun _ => hq⟩

/-- A function that chooses on entry between two branches, each returning
without secret residue (`NoResidue`, for its own contract), returns without
secret residue: if two runs that agree on what is public and outside the
buffers take the same branch, from states that agree in the same way. -/
theorem NoResidue.entryBranch {b : List Instr} {c : Cond} {c₁ c₂ : Prog isa} {k k₁ k₂ : Contract isa}
    {p : State → Bool} {rb : Nat} (tr : State → List Leak)
    (h₁ : NoResidue c₁ k₁ rb) (h₂ : NoResidue c₂ k₂ rb)
    (hb : ∀ s, k.pre s → ∃ u, execBlock isa b s = some (u, tr s) ∧ isa.eval c u = some (p s) ∧
      (p s = true → k₁.pre u) ∧ (p s = false → k₂.pre u))
    (hpub : ∀ s s' u u', k.pre s → k.pre s' → k.pub s s' → Outside 0 s s' → s.unknowns = s'.unknowns →
      execBlock isa b s = some (u, tr s) → execBlock isa b s' = some (u', tr s') →
      p s = p s' ∧ Outside 0 u u' ∧ u.unknowns = u'.unknowns ∧ (p s = true → k₁.pub u u') ∧
        (p s = false → k₂.pub u u')) :
    NoResidue (.seq (.block b) (Code.iteCold c c₁ c₂)) k rb := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hq ho hu e₁ e₂
  obtain ⟨u₁, eb₁, ec₁, k11, k12⟩ := hb s₁ p₁
  obtain ⟨u₂, eb₂, ec₂, k21, k22⟩ := hb s₂ p₂
  cases e₁ with
  | seq a₁ i₁ =>
    cases e₂ with
    | seq a₂ i₂ =>
      have x₁ := Exec.block_eq (T := X86_64.target) a₁
      have x₂ := Exec.block_eq (T := X86_64.target) a₂
      rw [eb₁] at x₁; rw [eb₂] at x₂
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj x₁)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj x₂)
      obtain ⟨ep, ho', hu', pb1, pb2⟩ := hpub s₁ s₂ _ _ p₁ p₂ hq ho hu eb₁ eb₂
      have i₁ := Exec.iteCold_iff.mp i₁
      have i₂ := Exec.iteCold_iff.mp i₂
      cases hp : p s₁
      · have hp' : p s₂ = false := ep ▸ hp
        cases i₁ with
        | iteT hc _ => rw [ec₁, hp] at hc; cases hc
        | iteF _ r₁ =>
          cases i₂ with
          | iteT hc _ => rw [ec₂, hp'] at hc; cases hc
          | iteF _ r₂ => exact h₂ _ _ _ _ _ _ (k12 hp) (k22 hp') (pb2 hp) ho' hu' r₁ r₂
      · have hp' : p s₂ = true := ep ▸ hp
        cases i₁ with
        | iteF hc _ => rw [ec₁, hp] at hc; cases hc
        | iteT _ r₁ =>
          cases i₂ with
          | iteF hc _ => rw [ec₂, hp'] at hc; cases hc
          | iteT _ r₂ => exact h₁ _ _ _ _ _ _ (k11 hp) (k21 hp') (pb1 hp) ho' hu' r₁ r₂

/-- `initEntry` returns without secret residue if its two branches do: the
comparison writes only the flags, from `key_len`. -/
theorem initEntry_noResidue {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ rb : Nat}
    (hS : NoResidue short (I.initContract X86_64.abi n₁) rb)
    (hL : NoResidue long (I.initAnyKeyContract X86_64.abi n₂) rb)
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize + 1 < 2 ^ 31) :
    NoResidue (Impl.Pbkdf2.Md.X86_64.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract X86_64.abi n₂) rb := by
  refine NoResidue.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .rcx).toNat))
    (fun _ => []) hL hS (fun s hs => ⟨_, rfl, ?_, fun _ => hs, fun hp => ?_⟩) ?_
  · show Option.map (!·) (some (decide ((s.gpr .rcx).toNat <
      ((BitVec.ofNat 32 (I.S.H.blockSize + 1)).signExtend 64).toNat))) = _
    rw [Calls.sx_ofNat hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hB])]
    simp only [Option.map_some, ← decide_not, Nat.not_lt]
  · have hk : (s.gpr .rcx).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega_using [this]
    sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs] at hs
    sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs]
    obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega_using [h₁]⟩
    obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega_using [hn]⟩
    simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hs ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨c0, c1, c2, c3⟩, n1, n2, n3⟩ := hs
    have sb := Offset.sub_below (s.gpr .rsp) (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
      (by omega_using [hn]) (by omega_using [hn])
    exact ⟨by omega_using [hn, h0], h1, h2, h3, h4, h5, h6, h7, ⟨c0, c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2,
      n3, hk⟩
  · intro s s' u u' hs hs' hq ho hu e e'
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs] at hq'
    obtain ⟨_, _, _, _, h4⟩ := hq'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15⟩ := ho
    have hc : s.gpr .rcx = s'.gpr .rcx := o3 _ (by decide)
    refine ⟨by rw [h4], ⟨o1, o2, o3, o4, ?_, ?_, ?_, ?_, o9, o10, o11, o12, o13, o14, o15⟩, hu, fun _ => hq,
      fun _ => hq⟩
    all_goals (show some _ = some _; rw [hc])

end VG.Proof.Pbkdf2.Md.X86_64
