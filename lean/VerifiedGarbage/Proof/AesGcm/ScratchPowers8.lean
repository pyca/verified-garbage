module

public import VerifiedGarbage.Proof.AesGcm.ScratchP
public import VerifiedGarbage.Spec.Gcm.Powers8
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared

/-! # Scratch contracts and locality for the `*_with_powers` functions

`Scratch.lean`'s scratch contracts and locality lemmas, for
`vg_aes_gcm_seal_with_powers` and `vg_aes_gcm_open_with_powers`
(`Spec/Gcm/Powers8.lean`), whose precondition adds the 8 prepared powers of
the key context's hash subkey at `pw` (`Powers8Repr`). -/

@[expose] public section

namespace VG.Proof.AesGcm
open VG.Spec.Gcm

/-- The 8 prepared powers depend only on the 128 bytes at `p`. -/
theorem powers8Repr_congr {m₁ m₂ : Mem} {p : Addr} {H : Block}
    (h : ∀ i < 16 * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : Powers8Repr m₁ p H) : Powers8Repr m₂ p H := by
  have keep (o : Nat) (ho : o + 16 ≤ 128) :
      m₂.readW (p + BitVec.ofNat 64 o) 128 = m₁.readW (p + BitVec.ofNat 64 o) 128 := by
    apply Mem.readW_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (o + i) (by omega)
  intro k hk
  rw [keep _ (by omega), keep _ (by omega)]
  exact hr k hk

/-- Zero memory has the prepared powers of the zero subkey. -/
theorem powers8Repr_zeroMem (p : Addr) : Powers8Repr (fun _ => 0) p 0 := by
  intro k hk
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  have hz : ∀ k, hpow 0 (k + 1) = 0 := fun _ => gcmMul_zero_right _
  simp only [hz, w]
  constructor <;> decide

/-- A buffer of zeros has the prepared powers of a zero subkey. -/
theorem powers8Repr_of_zeroMem {m : Mem} {p : Addr} {H : Block} (hH : H = 0)
    (h : ∀ i < 16 * 8, m (p + BitVec.ofNat 64 i) = 0) : Powers8Repr m p H := by
  subst hH
  exact powers8Repr_congr (m₁ := fun _ => 0) h (powers8Repr_zeroMem p)

/-- `vg_aes_gcm_seal_with_powers` with `work: *mut [u64; 320]`. -/
def sealWithPowersScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16), ("pw", .array false .u64 16),
    ("work", .array true .u64 320)]

/-- `sealWithPowersContract`, whatever `work` is. -/
def sealWithPowersScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealWithPowersScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag pw _work =>
      sealWithPowersPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag pw)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag pw _work =>
      sealWithPowersPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag pw)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_with_powers` with `work: *mut [u64; 320]`. -/
def openWithPowersScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"), ("pw", .array false .u64 16),
    ("work", .array true .u64 320)]
  ret := some .u32

/-- `openWithPowersContract`, whatever `work` is. -/
def openWithPowersScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openWithPowersScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw _work =>
      openWithPowersPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw _work =>
      openWithPowersPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw _work =>
      openWithPowersLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw)

/-! ## The `*_store_powers` functions -/

/-- `vg_aes_gcm_seal_store_powers`'s precondition, named: `sealPre` and a
TLS record's lengths (`storePowersOk`). -/
def sealStorePowersPreP (pb : Nat) : Curry (sealStorePowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag _pw m =>
    sealPre pb ctx rounds nonce nonceLen aad aadLen data len tag m ∧ storePowersOk nonceLen aadLen

/-- `vg_aes_gcm_seal_store_powers` with `work: *mut [u64; 320]`. -/
def sealStorePowersScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16), ("pw", .array true .u64 16),
    ("work", .array true .u64 320)]

/-- `sealStorePowersContract`, whatever `work` is. -/
def sealStorePowersScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealStorePowersScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag pw _work =>
      sealStorePowersPreP A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag pw)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag pw _work =>
      sealStorePowersPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag pw)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_store_powers`'s precondition, named: `openPre`, a TLS
record's lengths and an allowed tag length. -/
def openStorePowersPreP (pb : Nat) : Curry (openStorePowersSig.words pb) (Mem → Prop) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw m =>
    openPre pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m ∧
      storePowersOk nonceLen aadLen ∧ tagLenOk tagLen.toNat

/-- `vg_aes_gcm_open_store_powers`'s leakage, named: `openLeak`. -/
def openStorePowersLeakP (pb : Nat) : Curry (openStorePowersSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _pw =>
    openLeak pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen

/-- `vg_aes_gcm_open_store_powers` with `work: *mut [u64; 320]`. -/
def openStorePowersScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len"), ("pw", .array true .u64 16),
    ("work", .array true .u64 320)]
  ret := some .u32

/-- `openStorePowersContract`, whatever `work` is. -/
def openStorePowersScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openStorePowersScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw _work =>
      openStorePowersPreP A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw _work =>
      openStorePowersPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw _work =>
      openStorePowersLeakP A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen pw)

/-! ## Locality -/

variable (pb : Nat)

theorem sealWithPowersPre_local : ∀ vs m₁ m₂, vs.length = (sealWithPowersSig.words pb).length →
    (∀ b ∈ Sig.bufs sealWithPowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealWithPowersSig.words pb) (sealWithPowersPre pb) vs m₁ →
      Curry.apply (sealWithPowersSig.words pb) (sealWithPowersPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealWithPowersSig, sealSig, withPowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hp := agree_of hb.2.2.2.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealWithPowersPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealWithPowersPre pb) _ m₂
  dsimp only [Curry.apply, sealWithPowersPre, sealPre, ArgWord.ofRaw] at h ⊢
  rw [ctxH_congr fun i hi => hc i (by omega)]
  exact ⟨h.1, powers8Repr_congr hp h.2⟩

theorem sealWithPowersPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealWithPowersSig.words pb).length →
    (∀ b ∈ Sig.bufs sealWithPowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealWithPowersSig.words pb) (sealWithPowersPost pb) vs m₁ m' r →
      Curry.apply (sealWithPowersSig.words pb) (sealWithPowersPost pb) vs m₂ m' r := by
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
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealWithPowersSig, sealSig, withPowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hn := agree_of hb.2.1
  have ha := agree_of hb.2.2.1
  have hd := agree_of hb.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealWithPowersPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealWithPowersPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, sealWithPowersPost, sealPost, ArgWord.ofRaw] at h ⊢
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

theorem openWithPowersPre_local : ∀ vs m₁ m₂, vs.length = (openWithPowersSig.words pb).length →
    (∀ b ∈ Sig.bufs openWithPowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openWithPowersSig.words pb) (openWithPowersPre pb) vs m₁ →
      Curry.apply (openWithPowersSig.words pb) (openWithPowersPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openWithPowersSig, openSig, withPowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hp := agree_of hb.2.2.2.2.2
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openWithPowersPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openWithPowersPre pb) _ m₂
  dsimp only [Curry.apply, openWithPowersPre, openPre, ArgWord.ofRaw] at h ⊢
  rw [ctxH_congr fun i hi => hc i (by omega)]
  exact ⟨h.1, powers8Repr_congr hp h.2⟩

theorem openWithPowersPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openWithPowersSig.words pb).length →
    (∀ b ∈ Sig.bufs openWithPowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openWithPowersSig.words pb) (openWithPowersPost pb) vs m₁ m' r →
      Curry.apply (openWithPowersSig.words pb) (openWithPowersPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openWithPowersSig, openSig, withPowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hN := agree_of hb.2.1
  have hA := agree_of hb.2.2.1
  have hD := agree_of hb.2.2.2.1
  have hT := agree_of hb.2.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openWithPowersPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openWithPowersPost pb) _ m₂ m' r
  dsimp only [Curry.apply, openWithPowersPost, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  intro hr
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [openResult_local (pb := pb) (le15 hr) (fun i hi => hc i (by omega)) hN hA hD hT,
    bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hD i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h hr

theorem openWithPowersLeak_local : ∀ vs m₁ m₂, vs.length = (openWithPowersSig.words pb).length →
    (∀ b ∈ Sig.bufs openWithPowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openWithPowersSig.words pb) (openWithPowersLeak pb) vs m₁ =
      Curry.apply (openWithPowersSig.words pb) (openWithPowersLeak pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openWithPowersSig, openSig, withPowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openWithPowersLeak pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (openWithPowersLeak pb) _ m₂
  dsimp only [Curry.apply, openWithPowersLeak, openLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨
    (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openResult_local (pb := pb) (le15 hr) (fun i hi => agree_of hb.1 i (by omega)) (agree_of hb.2.1)
      (agree_of hb.2.2.1) (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.1)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

theorem sealStorePowersPre_local : ∀ vs m₁ m₂, vs.length = (sealStorePowersSig.words pb).length →
    (∀ b ∈ Sig.bufs sealStorePowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealStorePowersSig.words pb) (sealStorePowersPreP pb) vs m₁ →
      Curry.apply (sealStorePowersSig.words pb) (sealStorePowersPreP pb) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealStorePowersPreP pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealStorePowersPreP pb) _ m₂
  dsimp only [Curry.apply, sealStorePowersPreP, sealPre, ArgWord.ofRaw] at h ⊢
  exact h

theorem sealStorePowersPost_local : ∀ vs m₁ m₂ m' r, vs.length = (sealStorePowersSig.words pb).length →
    (∀ b ∈ Sig.bufs sealStorePowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealStorePowersSig.words pb) (sealStorePowersPost pb) vs m₁ m' r →
      Curry.apply (sealStorePowersSig.words pb) (sealStorePowersPost pb) vs m₂ m' r := by
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
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealStorePowersSig, sealSig, storePowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hn := agree_of hb.2.1
  have ha := agree_of hb.2.2.1
  have hd := agree_of hb.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealStorePowersPost pb) _
    m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr] (sealStorePowersPost pb) _
    m₂ m' r
  dsimp only [Curry.apply, sealStorePowersPost, sealPost, ArgWord.ofRaw] at h ⊢
  refine ⟨fun hr => ?_, by rw [ctxH_congr fun i hi => hc i (by omega)]; exact h.2⟩
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
  exact h.1 hr

theorem openStorePowersPre_local : ∀ vs m₁ m₂, vs.length = (openStorePowersSig.words pb).length →
    (∀ b ∈ Sig.bufs openStorePowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openStorePowersSig.words pb) (openStorePowersPreP pb) vs m₁ →
      Curry.apply (openStorePowersSig.words pb) (openStorePowersPreP pb) vs m₂ := by
  intro vs m₁ m₂ hlen _ h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 10
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openStorePowersPreP pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openStorePowersPreP pb) _ m₂
  dsimp only [Curry.apply, openStorePowersPreP, openPre, ArgWord.ofRaw] at h ⊢
  exact h

theorem openStorePowersPost_local : ∀ vs m₁ m₂ m' r, vs.length = (openStorePowersSig.words pb).length →
    (∀ b ∈ Sig.bufs openStorePowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openStorePowersSig.words pb) (openStorePowersPost pb) vs m₁ m' r →
      Curry.apply (openStorePowersSig.words pb) (openStorePowersPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openStorePowersSig, openSig, storePowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hN := agree_of hb.2.1
  have hA := agree_of hb.2.2.1
  have hD := agree_of hb.2.2.2.1
  have hT := agree_of hb.2.2.2.2.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openStorePowersPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openStorePowersPost pb) _ m₂ m' r
  dsimp only [Curry.apply, openStorePowersPost, openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
  refine ⟨fun hr => ?_, by rw [ctxH_congr fun i hi => hc i (by omega)]; exact h.2⟩
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [openResult_local (pb := pb) (le15 hr) (fun i hi => hc i (by omega)) hN hA hD hT,
    bytesAt_congr (p := data) (n := (len.setWidth pb).toNat) fun i hi => hD i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
  exact h.1 hr

theorem openStorePowersLeak_local : ∀ vs m₁ m₂, vs.length = (openStorePowersSig.words pb).length →
    (∀ b ∈ Sig.bufs openStorePowersSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openStorePowersSig.words pb) (openStorePowersLeakP pb) vs m₁ =
      Curry.apply (openStorePowersSig.words pb) (openStorePowersLeakP pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
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
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openStorePowersSig, openSig, storePowersParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
    (openStorePowersLeakP pb) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr]
      (openStorePowersLeakP pb) _ m₂
  dsimp only [Curry.apply, openStorePowersLeakP, openLeak, ArgWord.ofRaw, IntTy.bits]
  by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨
    (rd.setWidth pb).toNat = 14
  · simp only [hr, not_true_eq_false, ↓reduceIte]
    simp only [openResult_local (pb := pb) (le15 hr) (fun i hi => agree_of hb.1 i (by omega)) (agree_of hb.2.1)
      (agree_of hb.2.2.1) (agree_of hb.2.2.2.1) (agree_of hb.2.2.2.2.1)]
    rfl
  · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesGcm
