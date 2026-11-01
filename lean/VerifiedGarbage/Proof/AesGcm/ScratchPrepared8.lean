module

public import VerifiedGarbage.Proof.Gcm.Prepared8Contract
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.Framework.Mem

/-! # 384-byte prepared-context scratch contracts and locality

`ScratchPrepared.lean`'s scratch contracts and locality lemmas, for the
384-byte context of `Spec/Gcm/Prepared8.lean`, whose powers
(`PreparedPowers8Repr`) are the first four pairs of `PreparedPowersRepr`
(`preparedPowers8Repr_of`). -/

@[expose] public section

namespace VG.Proof.AesGcm
open VG.Spec.Gcm Proof.Gcm

/-- The 1024-byte prepared powers hold the 384-byte context's. -/
theorem preparedPowers8Repr_of {m : Mem} {p : Addr} (h : PreparedPowersRepr m p) :
    PreparedPowers8Repr m p :=
  fun k hk => h k (by omega)

/-- `vg_aes_gcm_seal_prepared8` with `work: *mut [u64; 320]`. -/
def sealPrepared8ScratchSig : Sig where
  params := [("ctx", .array false .u64 48), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16), ("work", .array true .u64 320)]

/-- `sealPrepared8Contract`, whatever `work` is. -/
def sealPrepared8ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrepared8ScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPrepared8Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_prepared8` with `work: *mut [u64; 320]`. -/
def openPrepared8ScratchSig : Sig where
  params := [("ctx", .array false .u64 48), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"),
    ("work", .array true .u64 320)]
  ret := some .u32

/-- `openPrepared8Contract`, whatever `work` is. -/
def openPrepared8ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrepared8ScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPrepared8Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- The eight prepared powers depend only on bytes within the context. -/
theorem preparedPowers8Repr_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 48 * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : PreparedPowers8Repr m₁ p) : PreparedPowers8Repr m₂ p := by
  have keep (o : Nat) (ho : o + 16 ≤ 384) :
      m₂.readW (p + BitVec.ofNat 64 o) 128 = m₁.readW (p + BitVec.ofNat 64 o) 128 := by
    apply Mem.readW_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (o + i) (by omega)
  intro k hk
  rw [keep _ (by omega), keep _ (by omega), ctxH_congr fun i hi => h i (by omega)]
  exact hr k hk

/-- A context of zeros has the eight prepared powers. -/
theorem preparedPowers8Repr_of_zeroMem {m : Mem} {p : Addr}
    (h : ∀ i < 48 * 8, m (p + BitVec.ofNat 64 i) = 0) : PreparedPowers8Repr m p :=
  preparedPowers8Repr_congr (m₁ := fun _ => 0) h
    (preparedPowers8Repr_of (preparedPowersRepr_zeroMem p))

variable (pb : Nat)

theorem sealPrepared8Pre_local : ∀ vs m₁ m₂, vs.length = (sealPrepared8Sig.words pb).length →
    (∀ b ∈ Sig.bufs sealPrepared8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealPrepared8Sig.words pb) (sealPrepared8Pre pb) vs m₁ →
      Curry.apply (sealPrepared8Sig.words pb) (sealPrepared8Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealPrepared8Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPrepared8Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPrepared8Pre pb) _ m₂
  dsimp only [Curry.apply, sealPrepared8Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowers8Repr_congr hc h.2⟩

theorem openPrepared8Pre_local : ∀ vs m₁ m₂, vs.length = (openPrepared8Sig.words pb).length →
    (∀ b ∈ Sig.bufs openPrepared8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPrepared8Sig.words pb) (openPrepared8Pre pb) vs m₁ →
      Curry.apply (openPrepared8Sig.words pb) (openPrepared8Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openPrepared8Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPrepared8Pre pb) _
    m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPrepared8Pre pb) _
    m₂
  dsimp only [Curry.apply, openPrepared8Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowers8Repr_congr hc h.2⟩

theorem sealPrepared8Post_local : ∀ vs m₁ m₂ m' r, vs.length = (sealPrepared8Sig.words pb).length →
    (∀ b ∈ Sig.bufs sealPrepared8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealPrepared8Sig.words pb) (sealPost pb) vs m₁ m' r →
      Curry.apply (sealPrepared8Sig.words pb) (sealPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealPrepared8Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hn := agree_of hb.2.1
  have ha := agree_of hb.2.2.1
  have hd := agree_of hb.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPost pb) _ m₂ m' r
  dsimp only [Curry.apply, sealPost, ArgWord.ofRaw] at h ⊢
  intro hr
  have hr' := le15 hr
  have := Nat.mod_le nl.toNat (2 ^ pb)
  have := Nat.mod_le al.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [ctxCiph_congr hr' fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega),
    bytesAt_congr (n := (nl.setWidth pb).toNat) fun i hi => hn i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (n := (al.setWidth pb).toNat) fun i hi => ha i (by
      rw [BitVec.toNat_setWidth] at hi; omega),
    bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hr

theorem openPrepared8Post_local : ∀ vs m₁ m₂ m' r, vs.length = (openPrepared8Sig.words pb).length →
    (∀ b ∈ Sig.bufs openPrepared8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPrepared8Sig.words pb) (openPost pb) vs m₁ m' r →
      Curry.apply (openPrepared8Sig.words pb) (openPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openPrepared8Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hN := agree_of hb.2.1
  have hA := agree_of hb.2.2.1
  have hD := agree_of hb.2.2.2.1
  have hT := agree_of hb.2.2.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [openResult_local (pb := pb) (le15 hr) (fun i hi => hc i (by omega)) hN hA hD hT,
    bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hD i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hr

theorem openPrepared8Leak_local : ∀ vs m₁ m₂, vs.length = (openPrepared8Sig.words pb).length →
    (∀ b ∈ Sig.bufs openPrepared8Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPrepared8Sig.words pb) (openLeak pb) vs m₁ =
      Curry.apply (openPrepared8Sig.words pb) (openLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨rd, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nonce, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨nl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨aad, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨al, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openPrepared8Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _
    m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openLeak pb) _ m₂
  dsimp only [Curry.apply, openLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨
    (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openResult_local (pb := pb) (le15 hr) (fun i hi => agree_of hb.1 i (by omega)) (agree_of hb.2.1)
      (agree_of hb.2.2.1) (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesGcm
