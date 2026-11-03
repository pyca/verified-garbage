module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTMain
public import VerifiedGarbage.Proof.HashTable.PPC64LE
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Correct
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Pre
public import VerifiedGarbage.Proof.RsaOaep.Scan

/-!
# RSAES-OAEP decryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Constant time
(`code_constantTime`, from `code_ct`, for MGF1's table that of the first
run, which the public data makes the second's); a state meeting the
precondition, which does not depend on the label's hash function, with
MGF1's table that of any `w` of `vs`, at `0x300000` (`dec_sat`); and
`dec_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf Coh)

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) {Hs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
include cH hHh hHl hHv

theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (decSpec Hs (tables vs)).pre (decSpec Hs (tables vs)).pub (decrypt H (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T, hT, hh⟩, -⟩ := spec_tabD h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, hsy, hiff⟩ := pubD_of hp
  have hn := Proof.HashTable.PPC64LE.mem_names hw
  exact code_ct hH cH w.l.ok w.l.ct hHh hHl hHv w.l.hash w.l.len w.l.valid _ _ _ _ _ _
    ⟨s₁, ⟨⟨preD_of h₁, tabS_entryD hc h₁ hw hh⟩, pubD_refl s₁, rfl, rfl, rfl⟩,
      ⟨preD_of h₂, tabS_entryD hc h₂ hw ((hiff _ hT).mp hh)⟩, p, (hsy _ hn.1).symm, (hsy _ hn.2.1).symm,
      (hsy _ hn.2.2).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_<H>_mgf1_decrypt` against its contract, for the tables of
`vs`, given a state meeting it. -/
theorem dec_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (decSpec Hs (tables vs)).pre s) :
    Verified PPC64LE.target (decrypt H (fnsOf vs)) (decSpec Hs (tables vs)) :=
  ⟨code_correct hH hHh hHl hHv hc, code_constantTime hH cH hHh hHl hHv hc, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract, but for the table: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `sp + 96`, and MGF1's
table's address `0x300000`. -/
def decSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1800 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4200 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10060 then 1
    else bif Nat.beq a.toNat 0x10069 then 0x43 else bif Nat.beq a.toNat 0x10070 then 1
    else bif Nat.beq a.toNat 0x10079 then 0x44 else bif Nat.beq a.toNat 0x10080 then 1
    else bif Nat.beq a.toNat 0x10089 then 0x45 else bif Nat.beq a.toNat 0x10090 then 1
    else bif Nat.beq a.toNat 0x10099 then 0x46 else bif Nat.beq a.toNat 0x100A0 then 1
    else bif Nat.beq a.toNat 0x100A9 then 0x47 else bif Nat.beq a.toNat 0x100B9 then 0x41
    else bif Nat.beq a.toNat 0x100C0 then 64 else bif Nat.beq a.toNat 0x100CA then 0x02
    else bif Nat.beq a.toNat 0x100D0 then 0x20 else bif Nat.beq a.toNat 0x100D1 then 0x08
    else bif Nat.beq a.toNat 0x100DA then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 40⟩, ⟨0x10060, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_dsat (j : Nat) (hj : j < 16) : (stackArgAddr decSatState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsat {j : Nat} {v : Addr} (hj : j < 16) (e : stackArg decSatState j = v) :
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) j = v :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_dsat j hj)).trans e

theorem dsat_args :
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 0 = 1 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 1 = 0x4300 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 2 = 1 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 3 = 0x4400 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 4 = 1 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 5 = 0x4500 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 6 = 1 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 7 = 0x4600 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 8 = 1 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 9 = 0x4700 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 10 = 0 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 11 = 0x4100 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 12 = 64 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 13 = 0x20000 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 14 = 2080 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 15 = 0x300000 :=
  ⟨stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide)⟩

/-- A state meeting the contract, with MGF1's table that of `w`, at
`0x300000`. -/
theorem dec_sat (H : Spec.Mgf1.Hash) (hw : w ∈ vs) (hl : (Proof.HashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (decSpec H (tables vs)).pre s := by
  refine ⟨Proof.HashTable.PPC64LE.withTable decSatState vs w, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := dsat_args (vs := vs) (w := w)
  have e : stackArgAddr (Proof.HashTable.PPC64LE.withTable decSatState vs w) 0 = 0x10060 :=
    show stackArgAddr decSatState 0 = _ by decide
  have e3776 : stackBytes = 3775 + 1 := rfl
  unfold decSpec
  rw [e3776]
  sig_pre [Spec.RsaOaep.decryptTableContract, Spec.RsaOaep.decryptTableSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_sixteen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, e]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact ⟨Proof.HashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.PPC64LE.withTable_held _ _ _⟩
    | exact Proof.HashTable.symsOf_distinct hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
