module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.AArch64.HashAt
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.PrecomputedCorrect

/-!
# RSASSA-PSS verification on AArch64: `Verified`

The shared contract (`Spec.RsaPss.verifyAnyContract`, with the stack of the
frame and the callee, `stk`) from correctness (`code_ok`), constant time
(`code_ct`) and a state meeting the precondition (`verify_sat`, for the stack
of the precomputed public operation), for hash functions `hs` with what the
proofs need of each of them by its number (`HashAt`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK mdHashes)
open VG.Proof.RsaPss.AArch64 (PssChecks)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

section
variable {hs : List Hash} (A : ∀ k < 8, HashAt hs k) (hl : hs.length ≤ 4096) (c : PdChecked) {K : Nat}
  (hK : 16 ≤ K) (hcK : c.stack ≤ K)

/-- The hash functions an entry state names. -/
def pickA {s : State} (h6 : (stackArg s 6).toNat < 8) (h7 : (stackArg s 7).toNat < 8) : Pick hs s where
  H := (A _ h6).H
  G := (A _ h7).H
  hH := (A _ h6).ok
  hG := (A _ h7).ok
  Hs := (A _ h6).Hs
  Gs := (A _ h7).Hs
  kH := (A _ h6).get
  kG := (A _ h7).get
  hl := hl
  hHh := (A _ h6).hh
  hHl := (A _ h6).hl
  hGh := (A _ h7).hh
  hGl := (A _ h7).hl
  hGv := (A _ h7).hv
  hHv := (A _ h6).hv

include A hl hK hcK in
theorem code_correct (s : State) (h : (Spec.RsaPss.verifyAnyContract abi (stk K)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed hs c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPss.verifyAnyContract abi (stk K)).post s s' := by
  obtain ⟨h6, h7⟩ := sel_of h
  have hp := preV_of h (A _ h6).id
  have hdl := hp.dl
  rw [(A _ h6).hl] at hp
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c hK hcK (pickA A hl h6 h7) hp
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, stackArgs_eight,
    List.append_eq]
  intro H G e₁ e₂
  rw [(A _ h6).id, Option.some.injEq] at e₁
  rw [(A _ h7).id, Option.some.injEq] at e₂
  subst e₁ e₂
  unfold verifyOut at hr
  rw [hdl]
  exact hr

include A hl hK hcK in
theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.verifyAnyContract abi (stk K)).pre
      (Spec.RsaPss.verifyAnyContract abi (stk K)).pub (verifyPrecomputed hs c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (α := Fin 8 × Fin 8) fun k =>
    code_ct (A _ k.1.2).get (A _ k.2.2).get hl (A _ k.1.2).ok (A _ k.2.2).ok (A _ k.2.2).hh (A _ k.2.2).hl
      (A _ k.2.2).hv (A _ k.1.2).pss (A _ k.2.2).pss c hK hcK).mono ?_ fun _ _ h => h)
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨a6, a7⟩ := sel_of h₁
  have P := pubV_of hp
  have e6 : (stackArg s₂ 6).toNat = (stackArg s₁ 6).toNat := by rw [P.args 6 (by decide) (by decide)]
  have e7 : (stackArg s₂ 7).toNat = (stackArg s₁ 7).toNat := by rw [P.args 7 (by decide) (by decide)]
  have p₁ := preV_of h₁ (A _ a6).id
  have p₂ := preV_of h₂ (Hs := (A _ a6).Hs)
    (by show Spec.HashId.mgf1 (stackArg s₂ 6).toNat = _; rw [e6]; exact (A _ a6).id)
  rw [(A _ a6).hl] at p₁ p₂
  exact ⟨(⟨_, a6⟩, ⟨_, a7⟩), s₁, ⟨⟨p₁, PubV.refl s₁⟩, rfl, rfl⟩, ⟨p₂, P⟩, e6, e7⟩

include A hl hK hcK in
theorem code_verified (hsat : ∃ s, (Spec.RsaPss.verifyAnyContract abi (stk K)).pre s) :
    Verified AArch64.target (verifyPrecomputed hs c.name c.code) (Spec.RsaPss.verifyAnyContract abi (stk K)) :=
  ⟨code_correct A hl c hK hcK, code_constantTime A hl c hK hcK, hsat⟩

end

/-- MGF1's hash function, as a hash function of `MdHash` takes it, is valid. -/
theorem mgf_valid {H : Hash} {hH : HashOK H} (lk : Proof.Pbkdf2.Md.AArch64.MgfLink H hH) :
    Proof.Mgf1.Valid lk.G := by
  have hD := hH.sizes.D0
  refine ⟨by rw [lk.len]; exact hD, fun x => ?_⟩
  rw [lk.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, lk.len]
  have := hH.sizes.DN
  omega

/-! ## A state meeting the precondition -/

/-- A 512-bit modulus, a one-byte `e`, a SHA-256 digest (`hash` and
`mgf1_hash` 3) and the signature, any salt length, a working space of 2080
words, 16 precomputed words, and the stack pointer at `2^40`, far above
them. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | .x5 => 32 | .x6 => 0x4000
    | .x7 => 64 | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000000 then 1 else bif Nat.beq a.toNat 0x10000000012 then 1
    else bif Nat.beq a.toNat 0x10000000018 then 0x20 else bif Nat.beq a.toNat 0x10000000019 then 8
    else bif Nat.beq a.toNat 0x10000000021 then 0x50 else bif Nat.beq a.toNat 0x10000000028 then 16
    else bif Nat.beq a.toNat 0x10000000030 then 3 else bif Nat.beq a.toNat 0x10000000038 then 3
    else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 32⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10000000000, 64⟩]
  wr := [⟨0x10000, 2080 * 8⟩]

/-- `verifyAnyContract` is satisfiable, with the stack of the frame and 16
bytes for the callee and the hash functions' calls. -/
theorem verify_sat : ∃ s, (Spec.RsaPss.verifyAnyContract abi (stk 16)).pre s := by
  sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyAnyContract,
    Spec.RsaPss.verifyAnySig, abi, argRegs, stk, frameBytes, stackArgs_eight, List.append_eq]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPss.AArch64.Vfy
