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
(`code_constantTime`, from `code_ct`, for the tables of the first run, which
the public data makes the second's); a state meeting the precondition, with
both tables that of any `w` of `vs`, at `0x300000` (`dec_sat`); and
`dec_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf Coh)

theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (decSpec (tables vs)).pre (decSpec (tables vs)).pub (decrypt (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tabD h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, hsy, hiffL, hiff⟩ := pubD_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := (spec_tabD h₂).2.2.sublist (List.sublist_append_left _ _)
  have hn := Proof.HashTable.PPC64LE.mem_names hw
  have hnL := Proof.HashTable.PPC64LE.mem_names hw₁
  have P₁ := preD_of h₁
  have P₂ := preD_of h₂
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entryD hc P₁ q₁ hw hh₁, tabS_entryDL hc P₁ q₁ hw₁ hhL₁⟩, pubD_refl s₁, ⟨rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩,
      ⟨P₂, tabS_entryD hc P₂ q₂ hw hh₂, tabS_entryDL hc P₂ q₂ hw₁ hhL₂⟩, p,
      ⟨(hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm⟩,
      ⟨(hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2).symm⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt` against its contract, for the tables of `vs`,
given a state meeting it. -/
theorem dec_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (decSpec (tables vs)).pre s) :
    Verified PPC64LE.target (decrypt (fnsOf vs)) (decSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract, but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty label, a
working space of 2080 words, the stack arguments at `sp + 96`, and both
tables' address `0x300000`. -/
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
    else bif Nat.beq a.toNat 0x100DA then 0x30 else bif Nat.beq a.toNat 0x100E2 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x300000, 40⟩, ⟨0x300000, 40⟩, ⟨0x10060, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_dsat (j : Nat) (hj : j < 17) : (stackArgAddr decSatState j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsat {j : Nat} {v : Addr} (hj : j < 17) (e : stackArg decSatState j = v) :
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
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 15 = 0x300000 ∧
    stackArg (Proof.HashTable.PPC64LE.withTable decSatState vs w) 16 = 0x300000 :=
  ⟨stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide), stackArg_dsat (by decide) (by decide),
    stackArg_dsat (by decide) (by decide)⟩

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem dec_sat (hw : w ∈ vs) (hl : (Proof.HashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (decSpec (tables vs)).pre s := by
  refine ⟨Proof.HashTable.PPC64LE.withTable decSatState vs w, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ :=
    dsat_args (vs := vs) (w := w)
  have e : stackArgAddr (Proof.HashTable.PPC64LE.withTable decSatState vs w) 0 = 0x10060 :=
    show stackArgAddr decSatState 0 = _ by decide
  have e3776 : stackBytes = 3775 + 1 := rfl
  unfold decSpec
  rw [e3776]
  sig_pre [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_seventeen, List.append_eq, List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13, a14, a15, a16, e]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact ⟨Proof.HashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.PPC64LE.withTable_held _ _ _⟩
    | exact Proof.HashTable.symsOf_distinct2 hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
