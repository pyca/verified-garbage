module

import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.TCB.AArch64.Residue
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
  dit : u.dit = s.dit

theorem entry_run {B : Nat} (hB : B < 2 ^ 16) (s : State) :
    ∃ u, execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp B) s = some (u, []) ∧ Ran s u ∧
      eval (.nonzero .x .x9) u = some (decide (B + 1 ≤ (s.gpr .x3).toNat)) := by
  refine ⟨_, rfl, ⟨fun r h9 h10 h11 h12 => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp [State.write, State.addWithCarry, h9, h10, h11, h12]
  · have hx := (s.gpr .x3).isLt
    simp only [eval, State.write, State.addWithCarry, State.read, Size.bits, reduceCtorEq, ↓reduceIte,
      BitVec.setWidth_eq, BitVec.shiftLeft_zero, Nat.mul_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_not, Bool.toNat_true, decide_eq_true_eq, Option.some.injEq]
    rw [Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt (by omega_using [hB])]
    split <;> rename_i h
    · rw [decide_eq_false (by omega_using [h])]; rfl
    · have h1 : B + 1 ≤ (s.gpr .x3).toNat := by omega_using [h]
      have hne : s.gpr .x3 ≠ 0 := fun e => by rw [e] at h1; simp at h1
      rw [decide_eq_true h1]; simp only [bne_iff_ne, ne_eq]; exact hne

/-- The comparison keeps two states that agree outside the buffers agreeing:
it writes only registers and flags, from registers. -/
theorem entry_outside {B : Nat} {s s' u u' : State} {t t' : List Leak} (h : Outside 0 s s')
    (e : execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp B) s = some (u, t))
    (e' : execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp B) s' = some (u', t')) : Outside 0 u u' := by
  obtain ⟨hrd, hwr, hg, hx0, hsp, hc, hn, hz, hv, hdit, hvv, hm⟩ := h
  have hg' : s.gpr = s'.gpr := funext fun r => by
    by_cases hr : r = .x0
    · subst hr; simpa using hx0
    · exact hg r hr
  have e0 : execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp B) s = some (_, []) := rfl
  have e0' : execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp B) s' = some (_, []) := rfl
  rw [e0] at e; rw [e0'] at e'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
  refine ⟨hrd, hwr, fun r _ => ?_, ?_, hsp, ?_, ?_, ?_, ?_, hdit, hvv, fun x hx => hm x hx⟩ <;>
    simp only [State.write, State.addWithCarry, State.read, hg']

/-- What `entryCmp` leaves for each branch of `initEntry`: the precondition of
`long`'s contract for a key longer than `B` bytes (and of `short`'s
otherwise), and the postcondition from it (`Verified.entryBranch`'s `hb`). -/
theorem initEntry_hb {I : Spec.Hmac.Instance} {n₁ n₂ : Nat} (h₁ : 0 < n₁) (hn : n₁ ≤ n₂)
    (hB : I.S.H.blockSize < 2 ^ 16) :
    ∀ s, (I.initAnyKeyContract AArch64.abi n₂).pre s →
      ∃ u, execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp I.S.H.blockSize) s = some (u, []) ∧
        eval (.nonzero .x .x9) u = some (decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat)) ∧
        (decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat) = true → (I.initAnyKeyContract AArch64.abi n₂).pre u ∧
          ∀ s', AArch64.target.abiPreserved u s' → (I.initAnyKeyContract AArch64.abi n₂).post u s' →
            AArch64.target.abiPreserved s s' ∧ (I.initAnyKeyContract AArch64.abi n₂).post s s') ∧
        (decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat) = false → (I.initContract AArch64.abi n₁).pre u ∧
          ∀ s', AArch64.target.abiPreserved u s' → (I.initContract AArch64.abi n₁).post u s' →
            AArch64.target.abiPreserved s s' ∧ (I.initAnyKeyContract AArch64.abi n₂).post s s') := by
  have hp : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 := by decide
  intro s hs
  obtain ⟨u, e, r, ev⟩ := entry_run hB s
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
  · have hk : (s.gpr .x3).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega_using [this]
    sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at hs
    sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs]
    rw [g0, g1, g2, g3, r.sp, r.rd, r.wr]
    obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega_using [h₁]⟩
    obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega_using [hn]⟩
    simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hs ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, ⟨c1, c2, c3⟩, n1, n2, n3⟩ := hs
    have sb := Offset.sub_below s.sp (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
      (by omega_using [hn]) (by omega_using [hn])
    exact ⟨by omega_using [hn, h0], h1, h2, h3, h4, h5, ⟨c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2, n3, hk⟩
  · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs]
    sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at q
    rw [g0, g1, g2, g3, r.mem] at q; exact q

/-- Two runs of `entryCmp` with the same public data take the same branch,
with the same public data of its contract (`Verified.entryBranch`'s `hpub`). -/
theorem initEntry_hpub {I : Spec.Hmac.Instance} {n₁ n₂ : Nat} (hB : I.S.H.blockSize < 2 ^ 16) :
    ∀ s s' u u', (I.initAnyKeyContract AArch64.abi n₂).pre s → (I.initAnyKeyContract AArch64.abi n₂).pre s' →
      (I.initAnyKeyContract AArch64.abi n₂).pub s s' →
      execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp I.S.H.blockSize) s = some (u, []) →
      execBlock isa (Impl.Pbkdf2.Md.AArch64.entryCmp I.S.H.blockSize) s' = some (u', []) →
      ([] : List Leak) = [] ∧
        decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat) = decide (I.S.H.blockSize + 1 ≤ (s'.gpr .x3).toNat) ∧
        (decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat) = true → (I.initAnyKeyContract AArch64.abi n₂).pub u u') ∧
        (decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat) = false → (I.initContract AArch64.abi n₁).pub u u') := by
  intro s s' u u' hs hs' hq e e'
  obtain ⟨u₀, e₀, r, -⟩ := entry_run hB s
  obtain ⟨u₀', e₀', r', -⟩ := entry_run hB s'
  rw [e₀] at e; rw [e₀'] at e'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
  have hq' := hq
  sig_pub_keep [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
    Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs] at hq'
  obtain ⟨q0, qd, q1, q2, q3, q4⟩ := hq'
  have pu : (I.initAnyKeyContract AArch64.abi n₂).pub u₀ u₀' := by
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, AArch64.abi, AArch64.argRegs]
    rw [r.sp, r'.sp, r.g .x0 (by decide) (by decide) (by decide) (by decide),
      r'.g .x0 (by decide) (by decide) (by decide) (by decide), r.g .x1 (by decide) (by decide) (by decide) (by decide),
      r'.g .x1 (by decide) (by decide) (by decide) (by decide), r.g .x2 (by decide) (by decide) (by decide) (by decide),
      r'.g .x2 (by decide) (by decide) (by decide) (by decide), r.g .x3 (by decide) (by decide) (by decide) (by decide),
      r'.g .x3 (by decide) (by decide) (by decide) (by decide), r.dit, r'.dit]
    exact ⟨q0, qd, q1, q2, q3, q4⟩
  refine ⟨rfl, by rw [q4], fun _ => pu, fun _ => pu⟩

theorem initEntry_verified {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ : Nat}
    (hS : Verified AArch64.target short (I.initContract AArch64.abi n₁))
    (hL : Verified AArch64.target long (I.initAnyKeyContract AArch64.abi n₂))
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize < 2 ^ 16)
    (hsat : ∃ s, (I.initAnyKeyContract AArch64.abi n₂).pre s) :
    Verified AArch64.target (Impl.Pbkdf2.Md.AArch64.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract AArch64.abi n₂) :=
  Verified.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat))
    (fun _ => []) hL hS (initEntry_hb h₁ hn hB) (initEntry_hpub hB) hsat

/-- `initEntry` returns without residue when both of its branches do, under
their contracts: the comparison writes registers only from `key_len`, so two
runs that agree outside the buffers still agree after it, and take the same
branch (`ScrubAll.noResidue_entryBranch`). -/
theorem initEntry_noResidue {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ rb : Nat}
    (hS : NoResidue short (I.initContract AArch64.abi n₁) rb)
    (hL : NoResidue long (I.initAnyKeyContract AArch64.abi n₂) rb)
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize < 2 ^ 16) :
    NoResidue (Impl.Pbkdf2.Md.AArch64.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract AArch64.abi n₂) rb := by
  refine ScrubAll.noResidue_entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .x3).toNat))
    hL hS (fun s u t hs e => ?_) (fun s s' u u' t t' hs hs' hq ho e e' => ?_)
  · obtain ⟨u₀, e₀, ev, k1, k2⟩ := initEntry_hb h₁ hn hB s hs
    rw [e₀] at e
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    exact ⟨ev, fun h => (k1 h).1, fun h => (k2 h).1⟩
  · obtain ⟨u₀, e₀, -⟩ := entry_run hB s
    obtain ⟨u₀', e₀', -⟩ := entry_run hB s'
    have ho' := entry_outside ho e e'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e')
    obtain ⟨-, ep, pb1, pb2⟩ := initEntry_hpub (n₁ := n₁) hB s s' _ _ hs hs' hq e₀ e₀'
    exact ⟨ep, ho', pb1, pb2⟩

end VG.Proof.Pbkdf2.Md.AArch64
