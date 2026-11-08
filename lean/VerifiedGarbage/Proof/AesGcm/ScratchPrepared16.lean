module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.ScratchP
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
import VerifiedGarbage.Proof.AesGcm.Scratch
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Mem

/-! # Prepared-context scratch contracts and locality -/

@[expose] public section

namespace VG.Proof.AesGcm
open VG.Spec.Gcm


/-- `sealPrepared16RoundsContract`, whatever `work` is. -/
def sealPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPrepared16Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)


/-- `openPrepared16RoundsContract`, whatever `work` is. -/
def openPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPrepared16Pre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openRoundsPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- `streamEncryptPrepared16RoundsContract`, whatever `scratch` is. -/
def streamEncryptPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamCryptPrepared16Pre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamEncryptRoundsPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptPrepared16RoundsContract`, whatever `scratch` is. -/
def streamDecryptPrepared16ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamCryptPrepared16Pre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamDecryptRoundsPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- Prepared powers depend only on bytes within the context. -/
theorem preparedPowers16Repr_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 128 * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : PreparedPowers16Repr m₁ p) : PreparedPowers16Repr m₂ p := by
  have keep (o : Nat) (ho : o + 16 ≤ 1024) :
      m₂.readW (p + BitVec.ofNat 64 o) 128 = m₁.readW (p + BitVec.ofNat 64 o) 128 := by
    apply Mem.readW_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (o + i) (by omega)
  intro k hk
  rw [keep _ (by omega), keep _ (by omega), ctxH_congr fun i hi => h i (by omega)]
  exact hr k hk

/-- Zero memory has the prepared powers of the zero subkey. -/
theorem preparedPowers16Repr_zeroMem (p : Addr) : PreparedPowers16Repr (fun _ => 0) p :=
  fun k hk => preparedPowersRepr_zeroMem p k (by omega)

/-- A context of zeros has the prepared powers. -/
theorem preparedPowers16Repr_of_zeroMem {m : Mem} {p : Addr} (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0) :
    PreparedPowers16Repr m p :=
  preparedPowers16Repr_congr (m₁ := fun _ => 0) h (preparedPowers16Repr_zeroMem p)

variable (pb : Nat)

theorem sealPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.sealPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.sealPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.sealPrecomputedSig.words pb) (sealPrepared16Pre pb) vs m₁ →
      Curry.apply (Spec.Gcm.sealPrecomputedSig.words pb) (sealPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.sealPrecomputedSig, sealPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, sealPrepared16Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowers16Repr_congr hc h.2⟩

theorem openPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.openPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.openPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.openPrecomputedSig.words pb) (openPrepared16Pre pb) vs m₁ →
      Curry.apply (Spec.Gcm.openPrecomputedSig.words pb) (openPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.openPrecomputedSig, openPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPrepared16Pre pb) _
    m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPrepared16Pre pb) _
    m₂
  dsimp only [Curry.apply, openPrepared16Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowers16Repr_congr hc h.2⟩

theorem streamCryptPrepared16Pre_local : ∀ vs m₁ m₂, vs.length = (Spec.Gcm.streamCryptPrecomputedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Gcm.streamCryptPrecomputedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Gcm.streamCryptPrecomputedSig.words pb) (streamCryptPrepared16Pre pb) vs m₁ →
      Curry.apply (Spec.Gcm.streamCryptPrecomputedSig.words pb) (streamCryptPrepared16Pre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 6
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Gcm.streamCryptPrecomputedSig, streamCryptPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamCryptPrepared16Pre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamCryptPrepared16Pre pb) _ m₂
  dsimp only [Curry.apply, streamCryptPrepared16Pre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowers16Repr_congr hc h.2⟩

end VG.Proof.AesGcm
