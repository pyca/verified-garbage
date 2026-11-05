module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTBase
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCCt
import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyCTop
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS verification on AArch64, calling `checkEncoding`: correctness and constant time

`verifyK vs K`: `verifyPrecomputedTableContract` with the tables of `vs`,
stated on the registers and the stack (its precondition `PreV`, its public
data `PubV` and the tables'), which `verifyC` meets: correctness
(`code_ok`, with the selection `CSel` the tables a state holds give,
`csel_of`) and constant time (`code_ct`, for the index, the functions and
the hash functions of the first run's tables, which every run with the same
public data holds): `verify_correct`, `verify_constantTime`.

The contract implies `verifyK` (`verify_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked Two)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (idx)
open VG.Proof.RsaPss.AArch64 (OK tabsOf csel_of chk_of chkCT_of names_sub Tabs)
open VG.Proof.RsaPss.AArch64.Sgn (stk)

/-- `verifyPrecomputedTableContract` with the tables `tsH` and `tsG` and the
stack `stk K`, on the registers and the stack. -/
def verifyK (tsH tsG : List FnTable) (K : Nat) : Contract isa where
  pre s := PreV tsH tsG K s
  post s s' := ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some H →
    Spec.HashTable.hashAt 64 s.mem (stackArg s 7) = some G → Cons s →
      (s'.gpr .x0).setWidth 32 = if Spec.RsaPss.verify H G (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) H.len)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat)
        (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32)) then 1 else 0
  pub s₁ s₂ := PubV s₁ s₂ ∧
    (∀ f ∈ (tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten, s₁.syms f = s₂.syms f) ∧
    (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 6) (FnTable.words isa s₁ T) ↔
      Abi.tableHeld 64 s₂.mem (stackArg s₂ 6) (FnTable.words isa s₂ T))) ∧
    ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
      Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T))

/-- `verifyK` with the tables of `vs`. -/
abbrev verifyKV (vs : List MdHash) (K : Nat) : Contract isa :=
  verifyK (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K

/-- The tables of a state meeting the precondition: those of variants `w`
and `w'` of `vs`. -/
theorem tabs_of {vs : List MdHash} {K : Nat} {s : State}
    (hp : PreV (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K s) :
    ∃ w ∈ vs, ∃ w' ∈ vs,
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (MdHashTable.AArch64.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.AArch64.tableOf w')) := by
  obtain ⟨_, hT, hH⟩ := hp.tabH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hG⟩ := hp.tabG
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  exact ⟨w, hw, w', hw', hH, hG⟩

variable {vs : List MdHash} (hok : OK vs) (c : PdChecked) {K : Nat} (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include hok h624 hcK in
theorem verify_correct (s : State) (h : (verifyKV vs K).pre s) :
    ∃ t s', Exec isa (verifyC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) s t s' ∧
      abiPreserved s s' ∧ (verifyKV vs K).post s s' := by
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of h
  have E := csel_of hok hw hw' h.hsy h.hdl hH hG
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c h624 hcK h E
  refine ⟨t, s', he, habi, fun H G hH' hG' hc => ?_⟩
  cases hH'.symm.trans E.hH
  cases hG'.symm.trans E.hG
  exact hr hc

/-- The index, the functions and the hash functions `x` whose
`checkEncoding` is correct and constant time. -/
def ChkGood (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) : Prop :=
  (∀ s', (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).pre s' → ∃ t s'',
    Exec isa (checkEncoding (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs)) s' t s'' ∧
      abiPreserved s' s'' ∧ (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).post s' s'') ∧
    ConstantTime isa (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).pre (Chk.chkK x.2.1 x.2.2.1 x.2.2.2).pub
      (checkEncoding (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs))

include hok h624 hcK in
theorem verify_constantTime :
    ConstantTime isa (verifyKV vs K).pre (verifyKV vs K).pub
      (verifyC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True)
      (P := fun (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) s₁ s₂ =>
        ChkGood (vs := vs) x ∧ Two (ES (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs)
          (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K x.1 x.2.1 x.2.2.1 x.2.2.2) s₁ s₂)
      fun x => ?_).mono (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ?_) fun _ _ h => h)
  · by_cases hx : ChkGood (vs := vs) x
    · exact (code_ct c h624 hcK hx.1 hx.2).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => hx h.1
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of h₁
  obtain ⟨pV, hsy, htH, htG⟩ := hpub
  have hH₂ := (htH _ (List.mem_map_of_mem hw)).mp hH
  have hG₂ := (htG _ (List.mem_map_of_mem hw')).mp hG
  refine ⟨(idx w, tabsOf vs w w', w.mgf.G, w'.mgf.G), ⟨chk_of hok hw, chkCT_of hok hw⟩, s₁,
    ⟨⟨h₁, PubV.refl s₁⟩, csel_of hok hw hw' h₁.hsy h₁.hdl hH hG, fun _ _ => rfl⟩,
    ⟨⟨h₂, pV⟩, csel_of hok hw hw' h₂.hsy h₂.hdl hH₂ hG₂, fun n hn => (hsy n (names_sub hw hw' n hn)).symm⟩⟩

/-- The contract, with the tables of `vs`. -/
abbrev verifyCK (vs : List MdHash) (K : Nat) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedTableContract (verifyAbi (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs))
    (stk K)

omit hok c h624 hcK in
/-- The contract implies `verifyK`, if it is satisfiable. -/
theorem verify_implies (hsat : ∃ s, (verifyCK vs K).pre s) : (verifyKV vs K).Implies (verifyCK vs K) where
  pre _ h := preV_of h
  post s s' _ h := by
    sig_post [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
    intro H G hH hG hc
    exact h H G hH hG hc
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htH, htG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    obtain ⟨hne, hw⟩ := List.append_inj hl (by simp [VG.Proof.RsaPkcs1Sig.bytesAt_length, g1, g3])
    obtain ⟨hn, he⟩ := leak_eq2 (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, VG.Proof.RsaPkcs1Sig.bytesAt_length, g1]) hne
    refine ⟨⟨hsp.symm, fun r hr => ?_, a1.symm, fun i hi hi1 => ?_, hn.symm, he.symm,
      ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw).symm⟩, hsy,
      fun T hT => htH _ _ rfl rfl T hT, fun T hT => htG _ _ rfl rfl T hT⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
    · match i, hi, hi1 with
      | 0, _, _ => exact a0.symm | 1, _, h => exact absurd rfl h | 2, _, _ => exact a2.symm
      | 3, _, _ => exact a3.symm | 4, _, _ => exact a4.symm | 5, _, _ => exact a5.symm
      | 6, _, _ => exact a6.symm | 7, _, _ => exact a7.symm | n + 8, h, _ => exact absurd h (by omega)
  sat := hsat

end VG.Proof.RsaPss.AArch64.Vfy
