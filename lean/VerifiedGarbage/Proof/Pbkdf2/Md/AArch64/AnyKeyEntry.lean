module

import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.AArch64
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.InstancePriority
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# HMAC's `init` for a key of any length on AArch64, choosing on entry

`initEntry B short long` sets `x9` to zero exactly when `key_len` (`x3`) is
at most `B` (`entryCmp`) and runs `long`, verified against
`VG.Spec.Hmac.Instance.initAnyKeyContract`, for a key longer than a block,
and `short`, verified against `initContract` (a key of at most a block),
otherwise (`Verified.entryBranch`). The comparison writes only `x9`–`x12` and
the flags, which no contract reads, and leaks nothing; the branch depends
only on `key_len`, which is public.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64

/-- What `entryCmp` leaves of a state: all but `x9`–`x12` and the flags. -/
structure Ran (s u : State) : Prop where
  g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  v : u.v = s.v

theorem entry_run {B : Nat} (hB : B < 2 ^ 16) (s : State) :
    ∃ u, execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp B) s = some (u, []) ∧ Ran s u ∧
      eval (.nonzero .x .x9) u = some (decide (B + 1 ≤ (s.gpr .x3).toNat)) := by
  refine ⟨_, rfl, ⟨fun r h9 h10 h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [State.write, State.addWithCarry, h9, h10, h11, h12]
  · have hx := (s.gpr .x3).isLt
    simp only [eval, State.write, State.addWithCarry, State.read, Size.bits, reduceCtorEq, ↓reduceIte,
      BitVec.setWidth_eq, BitVec.shiftLeft_zero, Nat.mul_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_not, Bool.toNat_true, decide_eq_true_eq, Option.some.injEq]
    rw [Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt (by omega)]
    split <;> rename_i h
    · rw [decide_eq_false (by omega)]; rfl
    · have h1 : B + 1 ≤ (s.gpr .x3).toNat := by omega
      have hne : s.gpr .x3 ≠ 0 := fun e => by rw [e] at h1; simp at h1
      rw [decide_eq_true h1]; simp only [bne_iff_ne, ne_eq]; exact hne

theorem initEntry_verified {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ : Nat}
    (hS : Verified AArch64.target short (I.initContract AArch64.abi n₁))
    (hL : Verified AArch64.target long (I.initAnyKeyContract AArch64.abi n₂))
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize < 2 ^ 16)
    (hsat : ∃ s, (I.initAnyKeyContract AArch64.abi n₂).pre s) :
    Verified AArch64.target (Impl.Pbkdf2.Md.AArch64.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract AArch64.abi n₂) := by
  have hp : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 := by decide
  refine Verified.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat))
    (fun _ => []) hL hS (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, r, ev⟩ := entry_run hB s
    have g0 := r.g .x0 (by decide) (by decide) (by decide) (by decide)
    have g1 := r.g .x1 (by decide) (by decide) (by decide) (by decide)
    have g2 := r.g .x2 (by decide) (by decide) (by decide) (by decide)
    have g3 := r.g .x3 (by decide) (by decide) (by decide) (by decide)
    have abi : ∀ s', AArch64.target.abiPreserved u s' → AArch64.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by
        obtain ⟨h9, h10, h11, h12⟩ := hp x hx
        rw [a.1 x hx, r.g x h9 h10 h11 h12], by rw [a.2.1, r.sp], fun x hx => by rw [a.2.2 x hx, r.v]⟩
    refine ⟨u, e, ev, fun _ => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hp => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at hs ⊢
      rw [g0, g1, g2, g3, r.sp, r.rd, r.wr]; exact hs
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at q ⊢
      rw [g0, g1, g2, g3, r.mem] at q; exact q
    · have hk : (s.gpr .x3).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at hs
      sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs]
      rw [g0, g1, g2, g3, r.sp, r.rd, r.wr]
      obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega⟩
      simp only [Sig.conj_single, Sig.conj_cons_cons, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hs ⊢
      obtain ⟨h0, h1, h2, h3, h4, h5, ⟨c1, c2, c3⟩, n1, n2, n3⟩ := hs
      have sb := Offset.sub_below s.sp (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
        (by omega) (by omega)
      exact ⟨by omega, h1, h2, h3, h4, h5, ⟨c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2, n3, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs]
      sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at q
      rw [g0, g1, g2, g3, r.mem] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, r, -⟩ := entry_run hB s
    obtain ⟨u₀', e₀', r', -⟩ := entry_run hB s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at hq'
    obtain ⟨q0, q1, q2, q3, q4⟩ := hq'
    have pu : (I.initAnyKeyContract AArch64.abi n₂).pub u₀ u₀' := by
      sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs]
      rw [r.sp, r'.sp, r.g .x0 (by decide) (by decide) (by decide) (by decide),
        r'.g .x0 (by decide) (by decide) (by decide) (by decide), r.g .x1 (by decide) (by decide) (by decide) (by decide),
        r'.g .x1 (by decide) (by decide) (by decide) (by decide), r.g .x2 (by decide) (by decide) (by decide) (by decide),
        r'.g .x2 (by decide) (by decide) (by decide) (by decide), r.g .x3 (by decide) (by decide) (by decide) (by decide),
        r'.g .x3 (by decide) (by decide) (by decide) (by decide)]
      exact ⟨q0, q1, q2, q3, q4⟩
    refine ⟨rfl, by rw [q4], fun _ => pu, fun _ => pu⟩

end VG.Proof.Pbkdf2.Md.AArch64
