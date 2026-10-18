module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SCorrect
public import VerifiedGarbage.Proof.HashFns.X86_64.Witness
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the contract

`scontract` implies the shared contract (`simplies`), which is satisfiable
(`ssat`), and `vg_rsa_pss_sign` meets its precondition and postcondition
(`sign_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.RsaOaep.X86_64 (decStack fns_of_tab)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack PrivImpl)

/-- The hash functions the selectors of an entry state name, and their
streaming functions in the tables. -/
theorem ssel_of {s : State} (hp : SPre s) :
    ∃ TH TG Hh Gh, Spec.HashId.mgf1 (sselH s) = some Hh ∧ Spec.HashId.mgf1 (sselG s) = some Gh ∧
      HashFns.StreamingOK TH Hh ∧ HashFns.StreamingOK TG Gh ∧
      VG.Proof.RsaOaep.X86_64.FnsD s TH 18 ∧ VG.Proof.RsaOaep.X86_64.FnsD s TG 19 := by
  obtain ⟨TH, Hh, -, eH, oH, fH⟩ := fns_of_tab hp.fH
  obtain ⟨TG, Gh, -, eG, oG, fG⟩ := fns_of_tab hp.fG
  exact ⟨TH, TG, Hh, Gh, eH, eG, oH, oG, fH, fG⟩

/-- `vg_rsa_pss_sign`, calling the implementation `v` of
`vg_rsa_private_checked`. -/
theorem sign_correct (v : PrivImpl) (s : State) (h : scontract.pre s) :
    ∃ t' s', Exec isa (sign v.name v.code) s t' s' ∧ abiPreserved s s' ∧ scontract.post s s' := by
  have hp := spre_of h
  obtain ⟨TH, TG, Hh, Gh, eH, eG, oH, oG, fH, fG⟩ := ssel_of hp
  obtain ⟨t', s', he, ha, hq⟩ := sign_body oH oG v hp fH fG eH eG
  refine ⟨t', s', he, ha, fun H G eH' eG' => ?_⟩
  rw [eH] at eH'
  rw [eG] at eG'
  cases eH'; cases eG'
  exact hq

/-- An entry state: a 512-bit modulus, one-byte `e`, primes, exponents and
`qInv`, an empty salt, SHA-1 for both hash functions, with the table at
`0x6000` of the witnesses' streaming functions (`Witness.funs`), and the
stack arguments at `0x10008`. -/
def ssatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10009 then 0x41 else bif Nat.beq a.toNat 0x10010 then 1
    else bif Nat.beq a.toNat 0x10019 then 0x42 else bif Nat.beq a.toNat 0x10020 then 1
    else bif Nat.beq a.toNat 0x10029 then 0x43 else bif Nat.beq a.toNat 0x10030 then 1
    else bif Nat.beq a.toNat 0x10039 then 0x44 else bif Nat.beq a.toNat 0x10040 then 1
    else bif Nat.beq a.toNat 0x10049 then 0x45 else bif Nat.beq a.toNat 0x10050 then 1
    else bif Nat.beq a.toNat 0x10059 then 0x46 else bif Nat.beq a.toNat 0x10060 then 20
    else bif Nat.beq a.toNat 0x10069 then 0x47 else bif Nat.beq a.toNat 0x1007A then 0x02
    else bif Nat.beq a.toNat 0x10080 then 0x20 else bif Nat.beq a.toNat 0x10081 then 0x08
    else bif Nat.beq a.toNat 0x10088 then 1 else bif Nat.beq a.toNat 0x10090 then 1
    else bif Nat.beq a.toNat 0x10099 then 0x60 else bif Nat.beq a.toNat 0x100A1 then 0x60
    else bif Nat.beq a.toNat 0x6001 then 0x70 else bif Nat.beq a.toNat 0x6009 then 0x71
    else bif Nat.beq a.toNat 0x6011 then 0x72 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, 20⟩, ⟨0x4700, 0⟩, ⟨0x6000, 24⟩, ⟨0x6000, 24⟩, ⟨0x10008, 160⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]
  funs := HashFns.X86_64.Witness.funs

theorem ssat : ∃ s, (Spec.RsaPss.signAnyContract abi decStack).pre s := by
  refine ⟨ssatState, ?_⟩
  sig_pre [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, decStack, privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq]
  sig_and_intros
  all_goals first
    | ((first | rw [show (stackArg ssatState 16).toNat = 1 from by decide]
              | rw [show (stackArg ssatState 17).toNat = 1 from by decide])
       exact HashFns.X86_64.Witness.tableOf_one (s := ssatState) (a₀ := 0x7000) (a₁ := 0x7100) (a₂ := 0x7200)
         rfl rfl rfl (by decide) (by decide) (by decide))
    | (unfold Spec.Rsa.lenValid; decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, ssatState, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

theorem simplies : scontract.Implies (Spec.RsaPss.signAnyContract abi decStack) where
  pre := fun _ h => h
  post := by
    intro s s' _ h
    sig_post [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, scontract, sPostH, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq]
    sig_reduce [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, scontract, sPostH, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq] at h
    sig_simp [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, scontract, sPostH, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq] [] at h
    exact h
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, scontract, sPub, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i hsp hsw hl hdi hsi hdx hcx h8 h9 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
    have a19 := h
    clear h
    obtain ⟨h2, hG⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, Spec.HashFns.tableWords, hcx, h9])
    obtain ⟨hb, hT⟩ := List.append_inj h2 (by simp [Spec.Rsa.bytesAt, hcx, h9])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨?_, by simp only [stackArgs_twenty, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16, a17, a18, a19], hn, he, hT, hG, hsw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := ssat

end VG.Proof.RsaPss.X86_64
