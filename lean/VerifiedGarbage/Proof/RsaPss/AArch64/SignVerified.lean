module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.AArch64.HashAt
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre

/-!
# RSASSA-PSS signing on AArch64: `Verified`

The shared contract (`Spec.RsaPss.signAnyContract`, with the stack of the
frame and the callee, `stk`) from correctness (`code_ok`), constant time
(`code_ct`) and a state meeting the precondition (`sign_sat`, for the stack
of `vg_rsa_private_checked`), for hash functions `hs` with what the proofs
need of each of them by its number (`HashAt`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK mdHashes)
open VG.Proof.RsaPss.AArch64 (PssChecks)

section
variable {hs : List Hash} (A : ∀ k < 8, HashAt hs k) (hl : hs.length ≤ 4096) (c : PrivChecked)
  (hK : 16 ≤ c.stack)

theorem hashIds_lt {k : Nat} (h : k ∈ Spec.RsaPss.hashIds) : k < 8 := by
  simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- The hash functions an entry state names. -/
def pickA {s : State} (h14 : (stackArg s 14).toNat < 8) (h15 : (stackArg s 15).toNat < 8) : Pick hs s where
  H := (A _ h14).H
  G := (A _ h15).H
  hH := (A _ h14).ok
  hG := (A _ h15).ok
  Hs := (A _ h14).Hs
  Gs := (A _ h15).Hs
  kH := (A _ h14).get
  kG := (A _ h15).get
  hl := hl
  hHh := (A _ h14).hh
  hHl := (A _ h14).hl
  hGh := (A _ h15).hh
  hGl := (A _ h15).hl
  hGv := (A _ h15).hv
  hHv := (A _ h14).hv

include A hl hK in
theorem code_correct (s : State) (h : (Spec.RsaPss.signAnyContract abi (stk c.stack)).pre s) :
    ∃ t s', Exec isa (sign hs c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPss.signAnyContract abi (stk c.stack)).post s s' := by
  obtain ⟨h14, h15⟩ := sel_of h
  have hp := preS_of h (A _ h14).id
  have hdl := hp.dl
  rw [(A _ h14).hl] at hp
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c hK (Nat.le_refl _) (pickA A hl h14 h15) hp
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, stackArgs_sixteen, List.append_eq]
  intro H G e₁ e₂
  rw [(A _ h14).id, Option.some.injEq] at e₁
  rw [(A _ h15).id, Option.some.injEq] at e₂
  subst e₁ e₂
  unfold signOut digB at hr
  rw [hdl]
  exact hr

include A hl hK in
theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.signAnyContract abi (stk c.stack)).pre
      (Spec.RsaPss.signAnyContract abi (stk c.stack)).pub (sign hs c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (α := Fin 8 × Fin 8) fun k =>
    code_ct (A _ k.1.2).get (A _ k.2.2).get hl (A _ k.1.2).ok (A _ k.2.2).ok (A _ k.1.2).hh (A _ k.1.2).hl
      (A _ k.1.2).hv (A _ k.2.2).hh (A _ k.2.2).hl (A _ k.2.2).hv (A _ k.1.2).pss (A _ k.2.2).pss c hK
      (Nat.le_refl _)).mono ?_ fun _ _ h => h)
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨a14, a15⟩ := sel_of h₁
  have P := pubS_of hp
  have e14 : (stackArg s₂ 14).toNat = (stackArg s₁ 14).toNat := by rw [P.args 14 (by decide)]
  have e15 : (stackArg s₂ 15).toNat = (stackArg s₁ 15).toNat := by rw [P.args 15 (by decide)]
  have p₁ := preS_of h₁ (A _ a14).id
  have p₂ := preS_of h₂ (Hs := (A _ a14).Hs) (by show Spec.HashId.mgf1 (stackArg s₂ 14).toNat = _; rw [e14]; exact (A _ a14).id)
  rw [(A _ a14).hl] at p₁ p₂
  exact ⟨(⟨_, a14⟩, ⟨_, a15⟩), s₁, ⟨⟨p₁, PubS.refl s₁⟩, rfl, rfl⟩, ⟨p₂, P⟩, e14, e15⟩

include A hl hK in
theorem code_verified (hsat : ∃ s, (Spec.RsaPss.signAnyContract abi (stk c.stack)).pre s) :
    Verified AArch64.target (sign hs c.name c.code) (Spec.RsaPss.signAnyContract abi (stk c.stack)) :=
  ⟨code_correct A hl c hK, code_constantTime A hl c hK, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A 512-bit modulus, one-byte `e` and key parts, a SHA-256 digest (`hash`
and `mgf1_hash` 3), a one-byte salt, a working space of 2080 words, and the
stack pointer at `2^40`, far above them. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x1000 | .x3 => 64 | .x4 => 0x2000 | .x5 => 1 | .x6 => 0x3000
    | .x7 => 1 | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000001 then 0x60 else bif Nat.beq a.toNat 0x10000000008 then 1
    else bif Nat.beq a.toNat 0x10000000011 then 0x70 else bif Nat.beq a.toNat 0x10000000018 then 1
    else bif Nat.beq a.toNat 0x10000000021 then 0x80 else bif Nat.beq a.toNat 0x10000000028 then 1
    else bif Nat.beq a.toNat 0x10000000031 then 0x90 else bif Nat.beq a.toNat 0x10000000038 then 1
    else bif Nat.beq a.toNat 0x10000000041 then 0xA0 else bif Nat.beq a.toNat 0x10000000048 then 0x20
    else bif Nat.beq a.toNat 0x10000000051 then 0xB0 else bif Nat.beq a.toNat 0x10000000058 then 1
    else bif Nat.beq a.toNat 0x10000000062 then 1 else bif Nat.beq a.toNat 0x10000000068 then 0x20
    else bif Nat.beq a.toNat 0x10000000069 then 8 else bif Nat.beq a.toNat 0x10000000070 then 3
    else bif Nat.beq a.toNat 0x10000000078 then 3
    else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x6000, 1⟩, ⟨0x7000, 1⟩, ⟨0x8000, 1⟩, ⟨0x9000, 1⟩,
    ⟨0xA000, 32⟩, ⟨0xB000, 1⟩, ⟨0x10000000000, 128⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x10000, 2080 * 8⟩]

/-- `signAnyContract` is satisfiable, with the stack of the frame and
`vg_rsa_private_checked`'s 3248 bytes. -/
theorem sign_sat : ∃ s, (Spec.RsaPss.signAnyContract abi (stk 3248)).pre s := by
  sig_implies_sat [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, stk, frameBytes,
    stackArgs_sixteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using satState

end VG.Proof.RsaPss.AArch64.Sgn
