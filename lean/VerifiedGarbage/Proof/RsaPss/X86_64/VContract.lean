module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VCorrect
public import VerifiedGarbage.Proof.HashFns.X86_64.Witness
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the contract

`vcontract` is the shared contract's precondition, `vpostC` (the result for
the hash functions the selectors name, if `pre` holds the values for `n`)
and `vPub`; it implies the shared contract (`vimplies`), which is
satisfiable (`vsat`), and `vg_rsa_pss_verify_precomputed` meets its
precondition and postcondition (`ver_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.RsaOaep.X86_64 (encStack fns_of_tab)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- Entry states agreeing on what the contract makes public. -/
def vPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (∀ j ∈ [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11], stackArg s₁ j = stackArg s₂ j) ∧
    (stackArg s₁ 2).setWidth 32 = (stackArg s₂ 2).setWidth 32 ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
    Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 6) (stackArg s₁ 7).toNat =
      Spec.Rsa.wordsAt s₂.mem (stackArg s₂ 6) (stackArg s₂ 7).toNat ∧
    Spec.HashFns.tableWords s₁.mem (stackArg s₁ 10) = Spec.HashFns.tableWords s₂.mem (stackArg s₂ 10) ∧
    Spec.HashFns.tableWords s₁.mem (stackArg s₁ 11) = Spec.HashFns.tableWords s₂.mem (stackArg s₂ 11) ∧
    abi.sameWorld s₁ s₂

/-- The result for the hash functions the selectors name. -/
def vpostC (s u : State) : Prop :=
  ∀ H G, Spec.HashId.mgf1 (vselH s) = some H → Spec.HashId.mgf1 (vselG s) = some G → VRes s H G (u.gpr .rax)

def vcontract : Contract isa where
  pre := (Spec.RsaPss.verifyAnyContract abi encStack).pre
  post := vpostC
  pub := vPub

/-- The hash functions the selectors of an entry state name, and their
streaming functions in the tables. -/
theorem vsel_of {s : State} (hp : VPre s) :
    ∃ TH TG Hh Gh, Spec.HashId.mgf1 (vselH s) = some Hh ∧ Spec.HashId.mgf1 (vselG s) = some Gh ∧
      HashFns.StreamingOK TH Hh ∧ HashFns.StreamingOK TG Gh ∧ VFns s TH 10 ∧ VFns s TG 11 := by
  obtain ⟨TH, Hh, -, eH, oH, fH⟩ := fns_of_tab hp.fH
  obtain ⟨TG, Gh, -, eG, oG, fG⟩ := fns_of_tab hp.fG
  exact ⟨TH, TG, Hh, Gh, eH, eG, oH, oG, fH, fG⟩

/-- `vg_rsa_pss_verify_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`. -/
theorem ver_correct (v : PublicImpl) (s : State) (h : vcontract.pre s) :
    ∃ t' s', Exec isa (verify v.name v.code) s t' s' ∧ abiPreserved s s' ∧ vpostC s s' := by
  have hp := vpre_of h
  obtain ⟨TH, TG, Hh, Gh, eH, eG, oH, oG, fH, fG⟩ := vsel_of hp
  obtain ⟨t', s', he, ha, hq⟩ := ver_body oH oG v hp fH fG eH eG
  refine ⟨t', s', he, ha, fun H G eH' eG' => ?_⟩
  rw [eH] at eH'
  rw [eG] at eG'
  cases eH'; cases eG'
  exact hq

/-- An entry state: SHA-1 for both hash functions, with the table at
`0x6000` of the witnesses' streaming functions (`Witness.funs`), 16 words of
`pre` at `0x5000`, and the stack arguments at `0x10008`. -/
def vsatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 64 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4600 | .r9 => 20
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x41 else if a = 0x10010 then 64 else if a = 0x1002A then 0x02
    else if a = 0x10030 then 0x20 else if a = 0x10031 then 0x08 else if a = 0x10039 then 0x50
    else if a = 0x10040 then 16 else if a = 0x10048 then 1 else if a = 0x10050 then 1
    else if a = 0x10059 then 0x60 else if a = 0x10061 then 0x60 else if a = 0x6001 then 0x70
    else if a = 0x6009 then 0x71 else if a = 0x6011 then 0x72 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, 20⟩, ⟨0x4100, 64⟩, ⟨0x5000, 128⟩, ⟨0x6000, 24⟩, ⟨0x6000, 24⟩,
    ⟨0x10008, 96⟩]
  wr := [⟨0x20000, 2080 * 8⟩]
  funs := HashFns.X86_64.Witness.funs

theorem vsat : ∃ s, (Spec.RsaPss.verifyAnyContract abi encStack).pre s := by
  refine ⟨vsatState, ?_⟩
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, encStack,
    stackArgs_twelve, List.append_eq]
  sig_and_intros
  all_goals first
    | ((first | rw [show (stackArg vsatState 8).toNat = 1 from by decide]
              | rw [show (stackArg vsatState 9).toNat = 1 from by decide])
       exact HashFns.X86_64.Witness.tableOf_one (s := vsatState) (a₀ := 0x7000) (a₁ := 0x7100) (a₂ := 0x7200)
         rfl rfl rfl (by decide) (by decide) (by decide))
    | (unfold Spec.Rsa.lenValid; decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, vsatState, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

theorem ite_setWidth32 (c : Prop) [Decidable c] :
    (if c then (1 : BitVec 64) else 0).setWidth 32 = if c then 1 else 0 := by
  split <;> rfl

theorem vimplies : vcontract.Implies (Spec.RsaPss.verifyAnyContract abi encStack) where
  pre := fun _ h => h
  post := by
    intro s s' hpre h
    sig_post [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, vcontract, vpostC, VRes,
      VConsistent, encStack, stackArgs_twelve, List.append_eq]
    sig_reduce [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, vcontract, vpostC, VRes,
      VConsistent, encStack, stackArgs_twelve, List.append_eq] at h
    sig_simp [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, vcontract, vpostC, VRes,
      VConsistent, encStack, stackArgs_twelve, List.append_eq] [] at h
    intro H G eH eG hc
    have hp := vpre_of hpre
    rw [h H G eH eG hc, ite_setWidth32, hp.dl H eH]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, vcontract,
      encStack, stackArgs_twelve, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hsw, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    obtain ⟨h3, hG⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, Spec.HashFns.tableWords,
      hsi, hcx, a7])
    obtain ⟨h2, hT⟩ := List.append_inj h3 (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, hsi, hcx, a7])
    obtain ⟨hb, hq⟩ := List.append_inj h2 (by simp [Spec.Rsa.bytesAt, hsi, hcx])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hb
    refine ⟨?_, ?_, a2, hn, he, hq', hT, hG, hsw⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨a0, a1, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩
  sat := vsat

end VG.Proof.RsaPss.X86_64
