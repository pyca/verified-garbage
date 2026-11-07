module

public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Proof.AesEcb.Wipe

-- separate module: every target's `Proof/AesCbc/<ISA>/Wiped.lean` imports it (PPC64LE's so far).

/-!
# AES-CBC zeroing its scratch: what every target shares

On each target an implementation of `vg_aes_cbc_encrypt` or
`vg_aes_cbc_decrypt` that writes its `scratch` buffer can be called by that
target's `callWipe` (`Proof/Framework/<ISA>/CallWipe.lean`), which then
zeroes the bytes it may write, so that it leaves no secret there.
`Verified.callWipe` needs, of the CBC contracts' pre- and postconditions,
what is proven here for any pointer width `pb`: the precondition reads no
memory (`pre_local`); the postcondition reads the memory on entry only within
the buffers (`encPost_local`, `decPost_local`): the key schedule (of at most
240 bytes for any schedule `Aes.KeySchedule` allows), the chaining value and
the data; and the memory on return only within the buffers apart from
`scratch` (`encPost_out`, `decPost_out`): the chaining value and the data.
-/

@[expose] public section

namespace VG.Proof.AesCbc.Wipe

open VG VG.Spec.Cbc VG.Proof.AesEcb

theorem blocksAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n * 16, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    blocksAt m₂ p n = blocksAt m₁ p n := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => bytesAt_congr fun i hi => ?_
  have hj := List.mem_range.mp hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

variable (pb : Nat)

/-- The CBC functions' precondition. -/
def cbcPre : Curry (aesSig.words pb) (Mem → Prop) := fun _schedule rounds _iv _data _n _scratch _ =>
  rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- `aesDecryptContract`'s postcondition. -/
def decPost : aesSig.Post pb := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Spec.Aes.KeySchedule m schedule rounds.toNat key →
    let ciphInv := aesInv key
    let cs := blocksAt m data n.toNat
    blocksAt m' data n.toNat = decrypt ciphInv (Spec.Aes.bytesAt m iv 16) cs ∧
      Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) cs

/-- `aesEncryptContract`'s postcondition. -/
def encPost : aesSig.Post pb := fun schedule rounds iv data n _scratch m m' _ =>
  ∀ key, Spec.Aes.KeySchedule m schedule rounds.toNat key →
    let ciph := aes key
    let cs := encrypt ciph (Spec.Aes.bytesAt m iv 16) (blocksAt m data n.toNat)
    blocksAt m' data n.toNat = cs ∧ Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) cs

theorem decPost_curry (sch r iv data n scr : BitVec 64) (m m' : Mem) x :
    Curry.apply (aesSig.words pb) (decPost pb) [sch, r, iv, data, n, scr] m m' x =
      ∀ key, Spec.Aes.KeySchedule m sch (r.setWidth pb).toNat key →
        blocksAt m' data (n.setWidth pb).toNat =
            decrypt (aesInv key) (Spec.Aes.bytesAt m iv 16) (blocksAt m data (n.setWidth pb).toNat) ∧
          Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16) (blocksAt m data (n.setWidth pb).toNat) := rfl

theorem encPost_curry (sch r iv data n scr : BitVec 64) (m m' : Mem) x :
    Curry.apply (aesSig.words pb) (encPost pb) [sch, r, iv, data, n, scr] m m' x =
      ∀ key, Spec.Aes.KeySchedule m sch (r.setWidth pb).toNat key →
        blocksAt m' data (n.setWidth pb).toNat =
            encrypt (aes key) (Spec.Aes.bytesAt m iv 16) (blocksAt m data (n.setWidth pb).toNat) ∧
          Spec.Aes.bytesAt m' iv 16 = next (Spec.Aes.bytesAt m iv 16)
            (encrypt (aes key) (Spec.Aes.bytesAt m iv 16) (blocksAt m data (n.setWidth pb).toNat)) :=
  rfl

/-- The six argument words of a list of the signature's length. -/
theorem words6 {vs : List (BitVec 64)} (hlen : vs.length = (aesSig.words pb).length) :
    ∃ sch r iv d n scr, vs = [sch, r, iv, d, n, scr] := by
  obtain ⟨sch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨r, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨d, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨scr, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  exact ⟨sch, r, iv, d, n, scr, rfl⟩

theorem bufs6 (sch r iv d n scr : BitVec 64) :
    Sig.bufs aesSig.params [sch, r, iv, d, n, scr] =
      [(⟨sch, 240⟩, false), (⟨iv, 16⟩, true), (⟨d, n.toNat * 16⟩, true), (⟨scr, 2176⟩, true)] := rfl

/-- The precondition reads no memory. -/
theorem pre_local : ∀ vs (m₁ m₂ : Mem), vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (cbcPre pb) vs m₁ → Curry.apply (aesSig.words pb) (cbcPre pb) vs m₂ := by
  intro vs _ _ hlen _ h
  obtain ⟨_, _, _, _, _, _, rfl⟩ := words6 pb hlen
  exact h

theorem decPost_local : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (decPost pb) vs m₁ m' x → Curry.apply (aesSig.words pb) (decPost pb) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨sch, r, iv, d, n, scr, rfl⟩ := words6 pb hlen
  rw [bufs6] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  replace h := Eq.mp (decPost_curry pb sch r iv d n scr m₁ m' x) h
  refine Eq.mpr (decPost_curry pb sch r iv d n scr m₂ m' x) ?_
  intro key hk
  have hd := agree_of hb.2.2.1
  rw [bytesAt_congr (agree_of hb.2.1), blocksAt_congr (fun i hi => hd i (by have := len_le pb n; omega))]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem encPost_local : ∀ vs m₁ m₂ m' x, vs.length = (aesSig.words pb).length →
    (∀ b ∈ Sig.bufs aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (encPost pb) vs m₁ m' x → Curry.apply (aesSig.words pb) (encPost pb) vs m₂ m' x := by
  intro vs m₁ m₂ m' x hlen hb h
  obtain ⟨sch, r, iv, d, n, scr, rfl⟩ := words6 pb hlen
  rw [bufs6] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  replace h := Eq.mp (encPost_curry pb sch r iv d n scr m₁ m' x) h
  refine Eq.mpr (encPost_curry pb sch r iv d n scr m₂ m' x) ?_
  intro key hk
  have hd := agree_of hb.2.2.1
  rw [bytesAt_congr (agree_of hb.2.1), blocksAt_congr (fun i hi => hd i (by have := len_le pb n; omega))]
  exact h key ((keySchedule_congr (agree_of hb.1)).mp hk)

theorem decPost_out : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (decPost pb) vs m m₁ x → Curry.apply (aesSig.words pb) (decPost pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨sch, r, iv, d, n, scr, rfl⟩ := words6 pb hlen
  rw [bufs6] at hb hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.getD_cons_succ,
    List.getD_cons_zero, Elem.size] at hb
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Bool.true_or, Bool.or_true, forall_const, List.Pairwise.nil, and_true] at hpw
  replace h := Eq.mp (decPost_curry pb sch r iv d n scr m m₁ x) h
  refine Eq.mpr (decPost_curry pb sch r iv d n scr m m₂ x) ?_
  intro key hk
  have hd := agree_of (hb.2.2.1 hpw.2.2.1)
  rw [bytesAt_congr (p := iv) (agree_of (hb.2.1 hpw.2.1.2)),
    blocksAt_congr (fun i hi => hd i (by have := len_le pb n; omega))]
  exact h key hk

theorem encPost_out : ∀ vs m m₁ m₂ x, vs.length = (aesSig.words pb).length →
    (Sig.bufs aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
    (∀ b ∈ Sig.bufs aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
      ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesSig.words pb) (encPost pb) vs m m₁ x → Curry.apply (aesSig.words pb) (encPost pb) vs m m₂ x := by
  intro vs m m₁ m₂ x hlen hpw hb h
  obtain ⟨sch, r, iv, d, n, scr, rfl⟩ := words6 pb hlen
  rw [bufs6] at hb hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.getD_cons_succ,
    List.getD_cons_zero, Elem.size] at hb
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Bool.true_or, Bool.or_true, forall_const, List.Pairwise.nil, and_true] at hpw
  replace h := Eq.mp (encPost_curry pb sch r iv d n scr m m₁ x) h
  refine Eq.mpr (encPost_curry pb sch r iv d n scr m m₂ x) ?_
  intro key hk
  have hd := agree_of (hb.2.2.1 hpw.2.2.1)
  rw [bytesAt_congr (p := iv) (agree_of (hb.2.1 hpw.2.1.2)),
    blocksAt_congr (fun i hi => hd i (by have := len_le pb n; omega))]
  exact h key hk

end VG.Proof.AesCbc.Wipe
