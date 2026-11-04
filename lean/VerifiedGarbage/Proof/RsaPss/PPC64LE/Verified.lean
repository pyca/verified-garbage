module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTMain
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry

/-!
# RSASSA-PSS verification on PPC64LE with the tables: `Verified`

Untrusted: everything here is checked by Lean. For variants `vs` of `MdHash`
(`Proof/MdHashTable/PPC64LE/Tables.lean`) and `gs` of `Hash`
(`Proof/HashTable/PPC64LE.lean`) whose functions of the same name have the
same code: the tables a state meeting the precondition holds, one of `vs`'
at the stack argument 6 and one of `gs`' at 7, give what the proofs need of
them (`tabs_of`); correctness against the contract (`code_correct`, by
`verify_ok`); constant time (`code_constantTime`, by `code_ct`, the second
run holding the same tables, at the anchor's addresses with the anchor's
addresses of their functions); and `verify_verified`, given a state meeting
the precondition.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (TabS)
open VG.Proof.HashTable.PPC64LE (TVar)
open VG.Proof.MdHashTable.PPC64LE (MVar digName tabsOf)

section
variable {vs : List MVar} {gs : List TVar}

/-- The tables of a state meeting the precondition: one of `vs`' and one of
`gs`', with what the proofs need of them. -/
theorem tabs_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) {s : State}
    (h : (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    ∃ w ∈ vs, ∃ w' ∈ gs,
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.PPC64LE.tableOf w')) ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some w.l.G ∧
      s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (MdHashTable.PPC64LE.idx w) ∧
      ∀ {D : Nat}, PreP D s → TabsOn (tabsOf vs gs w w') s := by
  obtain ⟨⟨T, hT, hh⟩, ⟨T', hT', hh'⟩, hpw⟩ := spec_tab h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  have hpH := hpw.sublist (List.sublist_append_left _ _)
  have hpG := hpw.sublist (List.sublist_append_right _ _)
  have hi := (MdHashTable.PPC64LE.held_tableOf hh).2.2.2
  refine ⟨w, hw, w', hw', hh, hh', MdHashTable.PPC64LE.hashAt_tableOf hi, hi, fun P => ⟨?_, ?_⟩⟩
  · refine HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P.ka (P.sa.sub_left (sc_sub P)) (show tGR s ∈ s.rd by rw [P.hrd]; simp) P.ktg
      (P.stg.sub_left (sc_sub P)) hc' hpG hw' hh'
  · exact MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P.ka (P.sa.sub_left (sc_sub P)) (show tHR s ∈ s.rd by rw [P.hrd]; simp) P.kth
      (P.sth.sub_left (sc_sub P)) hc hpH hw hh

/-- The correctness of `vg_rsa_pss_verify_precomputed`, against its contract,
for the tables of `vs` and `gs`. -/
theorem code_correct (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) (s : State)
    (h : (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs)) s t s' ∧
      abiPreserved s s' ∧ (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).post s s' := by
  obtain ⟨w, hw, w', hw', hh, hh', hH, hi, hT⟩ := tabs_of hc hc' h
  have hG := HashTable.PPC64LE.hashAt_tableOf (HashTable.PPC64LE.held_tableOf hh').2.1
  have P := preP_of h hH
  obtain ⟨Tg, T⟩ := hT P
  have hl : w.F.md.Link w.l.ok.SH w.iv w.l.G.len := w.l.len ▸ w.link
  obtain ⟨t, s', he, habi, hr⟩ := verify_ok P w.l.ok w.l.hash w.l.len w.l.valid w'.l.ok Tg w'.l.hash w'.l.len
    w'.l.valid T w.F.ok hl w.hN w.hB hi w.sh.1 w.sh.2.1 w.sh.2.2
  refine ⟨t, s', he, habi, ?_⟩
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_post [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param, Abi.withTables, abi, argRegs, stackArgs_eight, List.append_eq]
  intro H' G' hH' hG' hc
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [hr hc]
  unfold vOut
  split <;> rfl

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) :
    ConstantTime isa (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre
      (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pub
      (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨w, hw, w', hw', hh₁, hh₁', hH₁, hi₁, hT₁⟩ := tabs_of hc hc' h₁
  obtain ⟨p, hsy, hiffH, hiffG⟩ := pubT_of hp
  have hh₂ := (hiffH _ (List.mem_map_of_mem hw)).mp hh₁
  have hh₂' := (hiffG _ (List.mem_map_of_mem hw')).mp hh₁'
  have hi₂ := (MdHashTable.PPC64LE.held_tableOf hh₂).2.2.2
  have hH₂ := MdHashTable.PPC64LE.hashAt_tableOf hi₂
  have P₁ := preP_of h₁ hH₁
  have P₂ := preP_of h₂ hH₂
  have hpw₂ := (spec_tab h₂).2.2
  have T₂ : TabsOn (tabsOf vs gs w w') s₂ :=
    ⟨HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P₂.ka (P₂.sa.sub_left (sc_sub P₂)) (show tGR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) P₂.ktg
      (P₂.stg.sub_left (sc_sub P₂)) hc' (hpw₂.sublist (List.sublist_append_right _ _)) hw' hh₂',
    MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P₂.ka (P₂.sa.sub_left (sc_sub P₂)) (show tHR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) P₂.kth
      (P₂.sth.sub_left (sc_sub P₂)) hc (hpw₂.sublist (List.sublist_append_left _ _)) hw hh₂⟩
  have hn := MdHashTable.PPC64LE.mem_names hw
  have hn' := HashTable.PPC64LE.mem_names hw'
  have sH : ∀ {f}, f ∈ MdHashTable.PPC64LE.names vs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_left _ hf)).symm
  have sG : ∀ {f}, f ∈ HashTable.PPC64LE.names gs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_right _ hf)).symm
  have hl : w.F.md.Link w.l.ok.SH w.iv w.l.G.len := w.l.len ▸ w.link
  have hk : ∀ {s}, PreP w.l.G.len s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.k1
  exact code_ct (Z := tabsOf vs gs w w') w.l.ok w.l.ct w.l.hash w.l.len w.l.valid w'.l.ok w'.l.ct w'.l.hash
    w'.l.len w'.l.valid w.F.ok w.F.ct w.F.hcc w.F.hdc hl w.hN w.hB w.sh.1 w.sh.2.1 w.sh.2.2 _ _ _ _ _ _
    ⟨s₁, ⟨⟨⟨P₁, hT₁ P₁⟩, ⟨pubP_refl s₁, hk P₁⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi₁⟩,
      ⟨⟨⟨P₂, T₂⟩, ⟨p, hk P₂⟩, p.args 7 (by decide) (by decide), sG hn'.1, sG hn'.2.1, sG hn'.2.2,
        p.args 6 (by decide) (by decide), sH hn.1, sH hn.2.1, sH hn.2.2.1, sH hn.2.2.2.1, sH hn.2.2.2.2⟩, hi₂⟩⟩
    e₁ e₂

/-- `vg_rsa_pss_verify_precomputed` against its contract, for the tables of
`vs` and `gs`, given a state meeting it. -/
theorem verify_verified (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs)
    (hsat : ∃ s, (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    Verified PPC64LE.target (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs))
      (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  ⟨code_correct hc hc', code_constantTime hc hc', hsat⟩

end

end VG.Proof.RsaPss.PPC64LE
