module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Instances
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTBase
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCCt
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: correctness and constant time

`signTableContract` with the tables of `vs` (and the stack of the frame and
of the deeper callee, `stk K`), from correctness (`code_ok`, with the
selection `ESel` the tables a state holds give, `esel_of`) and constant time
(`code_ct`, for the index, the functions and the hash functions of the
first run's tables, which every run with the same public data holds:
`pubS_of`): `sign_correct`, `sign_constantTime`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked Two)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (idx)
open VG.Proof.RsaPss.AArch64 (OK tabsOf esel_of enc_of encCT_of names_sub Tabs)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The contract, with the tables of `vs`. -/
abbrev signCK (vs : List MdHash) (K : Nat) : Contract isa :=
  Spec.RsaPss.signTableContract (signAbi (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs)) (stk K)

theorem leak_eq {a b a' b' : List Byte} (ha : a.length = a'.length)
    (h : (a ++ b).map (·.toNat) = (a' ++ b').map (·.toNat)) : a = a' ∧ b = b' :=
  List.append_inj ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h) ha

/-- The public data of the contract, by name: the anchor `s₁`'s. -/
theorem pubS_of {tsH tsG : List FnTable} {K : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPss.signTableContract (signAbi tsH tsG) (stk K)).pub s₁ s₂) :
    PubS s₁ s₂ ∧ (∀ f ∈ (tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  sig_pub [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htH, htG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h
  obtain ⟨hn, he⟩ := leak_eq (by rw [bytesAt_length, bytesAt_length, g3]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, hn.symm, he.symm⟩, hsy, fun T hT => htH _ _ rfl rfl T hT,
    fun T hT => htG _ _ rfl rfl T hT⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · match i, hi with
    | 0, _ => exact a0.symm | 1, _ => exact a1.symm | 2, _ => exact a2.symm | 3, _ => exact a3.symm
    | 4, _ => exact a4.symm | 5, _ => exact a5.symm | 6, _ => exact a6.symm | 7, _ => exact a7.symm
    | 8, _ => exact a8.symm | 9, _ => exact a9.symm | 10, _ => exact a10.symm | 11, _ => exact a11.symm
    | 12, _ => exact a12.symm | 13, _ => exact a13.symm | 14, _ => exact a14.symm | 15, _ => exact a15.symm
    | n + 16, h => exact absurd h (by omega)

variable {vs : List MdHash} (hok : OK vs) (c : PrivChecked) {K : Nat} (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

/-- The tables of a state meeting the precondition: those of variants `w`
and `w'` of `vs`. -/
theorem tabs_of {s : State} (hp : PreS (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K s) :
    ∃ w ∈ vs, ∃ w' ∈ vs,
      Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (MdHashTable.AArch64.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (HashTable.AArch64.tableOf w')) := by
  obtain ⟨_, hT, hH⟩ := hp.tabH
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hG⟩ := hp.tabG
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  exact ⟨w, hw, w', hw', hH, hG⟩

include hok h624 hcK in
theorem sign_correct (s : State) (h : (signCK vs K).pre s) :
    ∃ t s', Exec isa (signC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) s t s' ∧
      abiPreserved s s' ∧ (signCK vs K).post s s' := by
  have hp := preS_of h
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of hp
  have E := esel_of hok hw hw' hp.hsy hp.hdl hH hG
  obtain ⟨t, s', he, habi, hr⟩ := code_ok c h624 hcK hp E
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.HashTable.param,
    Spec.MdHashTable.wordCount, Spec.HashTable.wordCount, Spec.MdHashTable.fns, Spec.HashTable.fns,
    Spec.MdHashTable.dataWords, Spec.HashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs,
    List.append_eq, _root_.List.range, _root_.List.range.loop]
  intro H G hH' hG'
  cases hH'.symm.trans E.hH
  cases hG'.symm.trans E.hG
  rw [E.hl, E.hD]
  exact hr

/-- The index, the functions and the hash functions `x` whose `encode` is
correct and constant time. -/
def EncGood (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) : Prop :=
  (∀ s', (Enc.encK x.2.1 x.2.2.1 x.2.2.2).pre s' → ∃ t s'',
    Exec isa (encode (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs)) s' t s'' ∧
      abiPreserved s' s'' ∧ (Enc.encK x.2.1 x.2.2.1 x.2.2.2).post s' s'') ∧
    ConstantTime isa (Enc.encK x.2.1 x.2.2.1 x.2.2.2).pre (Enc.encK x.2.1 x.2.2.1 x.2.2.2).pub
      (encode (MdHashTable.AArch64.fnsOf vs) (ofIdx x.1) (HashTable.AArch64.fnsOf vs))

include hok h624 hcK in
theorem sign_constantTime :
    ConstantTime isa (signCK vs K).pre (signCK vs K).pub
      (signC (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True) (P := fun (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) s₁ s₂ =>
      EncGood (vs := vs) x ∧ Two (ES (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs)
        (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K x.1 x.2.1 x.2.2.1 x.2.2.2) s₁ s₂)
      fun x => ?_).mono (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ?_) fun _ _ h => h)
  · by_cases hx : EncGood (vs := vs) x
    · exact (code_ct c h624 hcK hx.1 hx.2).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => hx h.1
  have p₁ := preS_of h₁
  have p₂ := preS_of h₂
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of p₁
  obtain ⟨pS, hsy, htH, htG⟩ := pubS_of hpub
  have hH₂ := (htH _ (List.mem_map_of_mem hw)).mp hH
  have hG₂ := (htG _ (List.mem_map_of_mem hw')).mp hG
  refine ⟨(idx w, tabsOf vs w w', w.mgf.G, w'.mgf.G), ⟨enc_of hok hw, encCT_of hok hw⟩, s₁,
    ⟨⟨p₁, PubS.refl s₁⟩, esel_of hok hw hw' p₁.hsy p₁.hdl hH hG, fun _ _ => rfl⟩,
    ⟨⟨p₂, pS⟩, esel_of hok hw hw' p₂.hsy p₂.hdl hH₂ hG₂, fun n hn => (hsy n (names_sub hw hw' n hn)).symm⟩⟩

end VG.Proof.RsaPss.AArch64.Sgn
