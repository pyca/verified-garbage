module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTMain
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. The shared contract's public
data as `PubO`, with the tables' (`pubT_of`); constant time
(`code_constantTime`, from `code_ct`); states meeting the precondition, with
both tables that of any `w` of `vs`, at `0x300000` (`enc_sat`); and
`enc_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf Coh)

theorem leak_eq {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).2, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubO`, the tables at the same addresses,
the tables' functions at the same addresses, and the same tables held. -/
theorem pubT_of {ts : List FnTable} {s₁ s₂ : State} (h : (encSpec ts).pub s₁ s₂) :
    PubO s₁ s₂ ∧ stackArg s₂ 9 = stackArg s₁ 9 ∧ stackArg s₂ 8 = stackArg s₁ 8 ∧
      (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 8) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 8) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 9) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 9) (FnTable.words isa s₂ T)) := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold encSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h6]) (by simp [bytesAt_length, h8]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩, a9.symm, a8.symm,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT, fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (encSpec (tables vs)).pre (encSpec (tables vs)).pub (encrypt (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, a9, a8, hsy, hiffL, hiff⟩ := pubT_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have hpw₂ := (spec_tab h₂).2.2
  have hn := Proof.HashTable.PPC64LE.mem_names hw
  have hnL := Proof.HashTable.PPC64LE.mem_names hw₁
  have hH₁ := Proof.HashTable.PPC64LE.hashAt_tableOf (Proof.HashTable.PPC64LE.held_tableOf hhL₁).2.1
  have hH₂ := Proof.HashTable.PPC64LE.hashAt_tableOf (Proof.HashTable.PPC64LE.held_tableOf hhL₂).2.1
  have P₁ : PreO w₁.H.D s₁ := w₁.l.len ▸ preO_of h₁ hH₁
  have P₂ : PreO w₁.H.D s₂ := w₁.l.len ▸ preO_of h₂ hH₂
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := hpw₂.sublist (List.sublist_append_left _ _)
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w.l.hash w.l.len w.l.valid w₁.l.hash w₁.l.len w₁.l.lens_mem
    _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entry hc P₁ q₁ hw hh₁, tabS_entryL hc P₁ q₁ hw₁ hhL₁⟩, pubO_refl s₁, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩,
      ⟨P₂, tabS_entry hc P₂ q₂ hw hh₂, tabS_entryL hc P₂ q₂ hw₁ hhL₂⟩, p, a9, (hsy _ hn.1).symm,
      (hsy _ hn.2.1).symm, (hsy _ hn.2.2).symm, a8, (hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm,
      (hsy _ hnL.2.2).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_encrypt_precomputed` against its contract, for the tables
of `vs`, given a state meeting it. -/
theorem enc_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (encSpec (tables vs)).pre s) :
    Verified PPC64LE.target (encrypt (fnsOf vs)) (encSpec (tables vs)) :=
  ⟨code_correct hc, code_constantTime hc, hsat⟩

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for a seed of `D` bytes, but for
the tables: a 512-bit modulus, a one-byte `e`, an empty label and message,
the seed, a working space of 2080 words, 16 words of `pre` at `0x5000`, the
stack arguments at `sp + 96`, and both tables' address `0x300000`. -/
def encSatState (D : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x41
    else bif Nat.beq a.toNat 0x10071 then 0x42 else bif Nat.beq a.toNat 0x10078 then BitVec.ofNat 8 D
    else bif Nat.beq a.toNat 0x10082 then 0x02
    else bif Nat.beq a.toNat 0x10088 then 0x20 else bif Nat.beq a.toNat 0x10089 then 0x08
    else bif Nat.beq a.toNat 0x10091 then 0x50 else bif Nat.beq a.toNat 0x10098 then 16
    else bif Nat.beq a.toNat 0x100A2 then 0x30 else bif Nat.beq a.toNat 0x100AA then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, D⟩, ⟨0x5000, 128⟩, ⟨0x300000, 40⟩,
    ⟨0x300000, 40⟩, ⟨0x10060, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_sat (D j : Nat) (hj : j < 10) :
    (stackArgAddr (encSatState D) j).toNat + 8 ≤ 0x300000 := by
  revert j; show ∀ j < 10, (stackArgAddr (encSatState 0) j).toNat + 8 ≤ 0x300000; decide

theorem sat_a0 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 0 = 0x4100 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 0 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 0 = 0x4100 by decide) D hD)
theorem sat_a1 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 1 = 0 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 1 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 1 = 0 by decide) D hD)
theorem sat_a2 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 2 = 0x4200 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 2 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 2 = 0x4200 by decide) D hD)
theorem sat_a3 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 3 = BitVec.ofNat 64 D :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 3 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 3 = BitVec.ofNat 64 D by decide) D hD)
theorem sat_a4 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 4 = 0x20000 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 4 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 4 = 0x20000 by decide) D hD)
theorem sat_a5 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 5 = 2080 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 5 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 5 = 2080 by decide) D hD)
theorem sat_a6 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 6 = 0x5000 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 6 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 6 = 0x5000 by decide) D hD)
theorem sat_a7 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 7 = 16 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 7 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 7 = 16 by decide) D hD)
theorem sat_a8 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 8 = 0x300000 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 8 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 8 = 0x300000 by decide) D hD)
theorem sat_a9 {D : Nat} (hD : D ∈ Impl.RsaOaep.PPC64LE.lens) :
    stackArg (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 9 = 0x300000 :=
  (Proof.HashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_sat D 9 (by decide))).trans
    ((show ∀ D ∈ Impl.RsaOaep.PPC64LE.lens, stackArg (encSatState D) 9 = 0x300000 by decide) D hD)
theorem sat_e (D : Nat) : stackArgAddr (Proof.HashTable.PPC64LE.withTable (encSatState D) vs w) 0 = 0x10060 :=
  show stackArgAddr (encSatState 0) 0 = _ by decide

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem enc_sat (hw : w ∈ vs) (hl : (Proof.HashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (encSpec (tables vs)).pre s := by
  have hha : ∀ s : State, Spec.HashTable.hashAt 64 (Proof.HashTable.PPC64LE.withTable s vs w).mem 0x300000 =
      some w.l.G := fun s => Proof.HashTable.PPC64LE.hashAt_tableOf
        (Proof.HashTable.PPC64LE.held_tableOf (Proof.HashTable.PPC64LE.withTable_held s vs w)).2.1
  have hl' : w.l.G.len ∈ Impl.RsaOaep.PPC64LE.lens := w.l.len ▸ w.l.lens_mem
  generalize hDd : w.l.G.len = D at hl'
  refine ⟨Proof.HashTable.PPC64LE.withTable (encSatState D) vs w, ?_⟩
  have e304 : (304 : Nat) = 303 + 1 := rfl
  have hha' := hha (encSatState D)
  have a0 := sat_a0 (vs := vs) (w := w) hl'
  have a1 := sat_a1 (vs := vs) (w := w) hl'
  have a2 := sat_a2 (vs := vs) (w := w) hl'
  have a3 := sat_a3 (vs := vs) (w := w) hl'
  have a4 := sat_a4 (vs := vs) (w := w) hl'
  have a5 := sat_a5 (vs := vs) (w := w) hl'
  have a6 := sat_a6 (vs := vs) (w := w) hl'
  have a7 := sat_a7 (vs := vs) (w := w) hl'
  have a8 := sat_a8 (vs := vs) (w := w) hl'
  have a9 := sat_a9 (vs := vs) (w := w) hl'
  unfold encSpec
  rw [e304]
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig, Spec.RsaOaep.seedLenOk,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argRegs, stackArgs_ten, List.append_eq, List.range, List.range.loop]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, sat_e]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨Proof.HashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.PPC64LE.withTable_held _ _ _⟩
      | (intro H' hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         rw [hDd]; rfl)
      | exact Proof.HashTable.symsOf_distinct2 hl
      | (simp only [Spec.Rsa.lenValid]; decide)

end

end VG.Proof.RsaOaep.PPC64LE
