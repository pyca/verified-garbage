module

import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.X86_64
public import VerifiedGarbage.Spec.Hmac.Generic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset

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
    rw [Calls.sx_ofNat hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [Option.map_some, ← decide_not, Nat.not_lt]
  · have hk : (s.gpr .rcx).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega
    refine ⟨?_, fun s' a q => ⟨a, q⟩⟩
    sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs] at hs
    sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs]
    obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega⟩
    obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega⟩
    simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hs ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, ⟨c0, c1, c2, c3⟩, n1, n2, n3⟩ := hs
    have sb := Offset.sub_below (s.gpr .rsp) (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
      (by omega) (by omega)
    exact ⟨by omega, h1, h2, h3, h4, h5, h6, h7, ⟨c0, c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2,
      n3, hk⟩
  · intro s s' u u' hs hs' hq e e'
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, X86_64.abi, X86_64.argRegs] at hq'
    obtain ⟨_, _, _, _, h4⟩ := hq'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    exact ⟨rfl, by rw [h4], fun _ => hq, fun _ => hq⟩

end VG.Proof.Pbkdf2.Md.X86_64
