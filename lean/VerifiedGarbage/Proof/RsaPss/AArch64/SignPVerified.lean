module

-- separate module: its proofs cost more than its imports, and the satisfiability witness's
-- changes (`Sat`) need not re-check them

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPCt
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.RsaPss.AArch64.SignPCall
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSASSA-PSS signing on AArch64 with the key's precomputed values: correctness and constant time

`signPrecomputedMdTableContract` with the tables of `vs`, for `signCP`: its
precondition gives `PreS` and `pre`'s facts `PreXS` (`preSP_of`), its public
data `PubS` and `PubX` (`pubSP_of`); then `codeP_ok` and `codeP_ct`:
`signP_correct`, `signP_constantTime`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivPChecked Two)
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (idx)
open VG.Proof.RsaPss.AArch64 (OK tabsOf esel_of enc_of encCT_of names_sub Tabs)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-- The ABI the contract states, with the tables. -/
abbrev signPAbi (tsH tsG : List FnTable) : Abi isa :=
  abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]

/-- The contract, with the tables of `vs`. -/
abbrev signPCK (vs : List MdHash) (K : Nat) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (signPAbi (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs)) (stk K)

theorem preSP_of {tsH tsG : List FnTable} {K : Nat} {s : State}
    (h : (Spec.RsaPss.signPrecomputedMdTableContract (signPAbi tsH tsG) (stk K)).pre s) :
    PreS tsH tsG K s ∧ PreXS K s := by
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega_using []
  rw [e] at h
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
    Option.some.injEq, exists_eq_left'] at h
  sig_split h
  rename_i sp1 sp2 tabH tabG hsy hrd hwr on oe op oq odp odq oqi odg osl os opr otH otG oa ns es ps qs dps dqs qis
    dgs sls spr stH stG sa ko kn ke kp kq kdp kdq kqi kdg ksl ks kpr ktH ktG ka wo wn we wp wq wdp wdq wqi wdg wsl
    ws wpr wtH wtG _ob1 ol e1 e2 p1 p2 q1 q2 hdp hqi hdq hs prl key
  obtain ⟨k1, k2⟩ := _ob1
  rw [← e] at sp1 ko kn ke kp kq kdp kdq kqi kdg ksl ks kpr ktH ktG ka
  have a128 : Region.Sub (aR s) (aR2 s) := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega_using [sp2], tabH, tabG, hsy, ?_, by rw [hwr]; simp, by rw [hwr]; simp, on, oe,
    op, oq, odp, odq, oqi, odg, osl, os, otH, otG, oa.sub_right a128, ns, es, ps, qs, dps, dqs, qis, dgs, sls, stH,
    stG, sa.sub_right a128, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, ktH, ktG, ka.sub_right a128, wo, wn, we,
    wp, wq, wdp, wdq, wqi, wdg, wsl, ws, wtH, wtG, k1, k2, ol, e1, e2, p1, p2, q1, q2, hdp, hqi, hdq,
    by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hs; omega_using [hs], h⟩,
    ⟨Covers.of_mem fun r hr => by
      rw [hrd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp [prR, aR2],
      sp2, oa, sa, ka, opr, spr, kpr, wpr, prl, key⟩⟩
  rw [hrd]
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨nR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨eR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨pR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨qR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨dpR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨dqR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨qiR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨dgR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨slR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨tHR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨tGR s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨aR2 s, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

/-- The public data of the contract, by name: the anchor `s₁`'s. -/
theorem pubSP_of {tsH tsG : List FnTable} {K : Nat} {s₁ s₂ : State}
    (h : (Spec.RsaPss.signPrecomputedMdTableContract (signPAbi tsH tsG) (stk K)).pub s₁ s₂) :
    PubS s₁ s₂ ∧ PubX s₁ s₂ ∧ (∀ f ∈ (tsH.map (·.fns)).flatten ++ (tsG.map (·.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount,
    Spec.MdHashTable.fns, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htH, htG, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17⟩ := h
  obtain ⟨hl₁, hl₂⟩ := List.append_inj hl (by simp [bytesAt_length, g3, g5])
  obtain ⟨hn, he⟩ := leak_eq (by rw [bytesAt_length, bytesAt_length, g3]) hl₁
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl₂
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, hn.symm, he.symm⟩, ⟨a16.symm, a17.symm, ?_⟩, hsy,
    fun T hT => htH _ _ rfl rfl T hT, fun T hT => htG _ _ rfl rfl T hT⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · match i, hi with
    | 0, _ => exact a0.symm | 1, _ => exact a1.symm | 2, _ => exact a2.symm | 3, _ => exact a3.symm
    | 4, _ => exact a4.symm | 5, _ => exact a5.symm | 6, _ => exact a6.symm | 7, _ => exact a7.symm
    | 8, _ => exact a8.symm | 9, _ => exact a9.symm | 10, _ => exact a10.symm | 11, _ => exact a11.symm
    | 12, _ => exact a12.symm | 13, _ => exact a13.symm | 14, _ => exact a14.symm | 15, _ => exact a15.symm
    | n + 16, h => exact absurd h (by omega_using [])
  · exact hw.symm

theorem PubX.refl (s : State) : PubX s s := ⟨rfl, rfl, rfl⟩

variable {vs : List MdHash} (hok : OK vs) (c : PrivPChecked) {K : Nat} (h624 : 624 ≤ K) (hcK : c.stack ≤ K)

include hok h624 hcK in
theorem signP_correct (s : State) (h : (signPCK vs K).pre s) :
    ∃ t s', Exec isa (signCP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) s t s' ∧
      abiPreserved s s' ∧ (signPCK vs K).post s s' := by
  obtain ⟨hp, hx⟩ := preSP_of h
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of hp
  have E := esel_of hok hw hw' hp.hsy hp.hdl hH hG
  obtain ⟨t, s', he, habi, hr⟩ := codeP_ok c h624 hcK hp hx E
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.wordCount,
    Spec.MdHashTable.fns, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, List.append_eq, _root_.List.range, _root_.List.range.loop]
  intro H G hH' hG'
  cases hH'.symm.trans E.hH
  cases hG'.symm.trans E.hG
  rw [E.hl, E.hD]
  exact hr

include hok h624 hcK in
theorem signP_constantTime :
    ConstantTime isa (signPCK vs K).pre (signPCK vs K).pub
      (signCP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) c.name c.code) := by
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True) (P := fun (x : Nat × Tabs × Spec.Mgf1.Hash × Spec.Mgf1.Hash) s₁ s₂ =>
      EncGood (vs := vs) x ∧ Two (ESP (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs)
        (MdHashTable.AArch64.tables vs) (HashTable.AArch64.tables vs) K x.1 x.2.1 x.2.2.1 x.2.2.2) s₁ s₂)
      fun x => ?_).mono (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ?_) fun _ _ h => h)
  · by_cases hx : EncGood (vs := vs) x
    · exact (codeP_ct c h624 hcK hx.1 hx.2).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => hx h.1
  obtain ⟨p₁, x₁⟩ := preSP_of h₁
  obtain ⟨p₂, x₂⟩ := preSP_of h₂
  obtain ⟨w, hw, w', hw', hH, hG⟩ := tabs_of p₁
  obtain ⟨pS, pX, hsy, htH, htG⟩ := pubSP_of hpub
  have hH₂ := (htH _ (List.mem_map_of_mem hw)).mp hH
  have hG₂ := (htG _ (List.mem_map_of_mem hw')).mp hG
  refine ⟨(idx w, tabsOf vs w w', w.mgf.G, w'.mgf.G), ⟨enc_of hok hw, encCT_of hok hw⟩, s₁,
    ⟨⟨⟨p₁, PubS.refl s₁⟩, esel_of hok hw hw' p₁.hsy p₁.hdl hH hG, fun _ _ => rfl⟩, x₁, PubX.refl s₁⟩,
    ⟨⟨⟨p₂, pS⟩, esel_of hok hw hw' p₂.hsy p₂.hdl hH₂ hG₂, fun n hn => (hsy n (names_sub hw hw' n hn)).symm⟩, x₂, pX⟩⟩

end VG.Proof.RsaPss.AArch64.Sgn
