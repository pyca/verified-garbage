module

public import VerifiedGarbage.Proof.AesGcm.ScratchP
public import VerifiedGarbage.Spec.Gcm.Prepared
import VerifiedGarbage.Proof.AesGcm.Scratch
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Mem

/-! # Prepared-context scratch contracts and locality -/

@[expose] public section

namespace VG.Proof.AesGcm
open VG.Spec.Gcm

/-- `vg_aes_gcm_seal_prepared` with `work: *mut [u64; 320]`. -/
abbrev sealPreparedScratchSig := sealPrecomputedScratchSig

/-- `sealPreparedContract`, whatever `work` is. -/
def sealPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPreparedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_open_prepared` with `work: *mut [u64; 320]`. -/
abbrev openPreparedScratchSig := openPrecomputedScratchSig

/-- `openPreparedContract`, whatever `work` is. -/
def openPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPreparedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (post := fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx rounds nonce nonceLen aad aadLen data len tag tagLen)

/-- `vg_aes_gcm_stream_encrypt_prepared` and `_decrypt_prepared` with
`scratch: *mut [u64; 320]`. -/
abbrev streamCryptPreparedScratchSig := streamCryptPrecomputedScratchSig

/-- `streamEncryptPreparedContract`, whatever `scratch` is. -/
def streamEncryptPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamCryptPreparedPre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptPreparedContract`, whatever `scratch` is. -/
def streamDecryptPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedScratchSig.contract A
    (pre := fun ctx rounds state aadLen textLen data len _scratch =>
      streamCryptPreparedPre A.ptrBits ctx rounds state aadLen textLen data len)
    (post := fun ctx rounds state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx rounds state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- Prepared powers depend only on bytes within the context. -/
theorem preparedPowersRepr_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 128 * 8, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : PreparedPowersRepr m₁ p) : PreparedPowersRepr m₂ p := by
  have keep (o : Nat) (ho : o + 16 ≤ 1024) :
      m₂.readW (p + BitVec.ofNat 64 o) 128 = m₁.readW (p + BitVec.ofNat 64 o) 128 := by
    apply Mem.readW_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h (o + i) (by omega)
  intro k hk
  rw [keep _ (by omega), keep _ (by omega), ctxH_congr fun i hi => h i (by omega)]
  exact hr k hk

private theorem foldl_fix {α β : Type} (f : α → β → α) (a : α) (h : ∀ b, f a b = a) :
    ∀ l : List β, l.foldl f a = a
  | [] => rfl
  | b :: l => by rw [List.foldl_cons, h b]; exact foldl_fix f a h l

/-- Multiplying by zero gives zero. -/
theorem gcmMul_zero_right (x : Block) : mul x 0 = 0 := by
  unfold mul
  rw [foldl_fix _ _ fun i => ?_]
  have e : (0 : Block).getLsbD 0 = false := by decide
  simp only [BitVec.xor_self, e, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

/-- Zero memory has the prepared powers of the zero subkey. -/
theorem preparedPowersRepr_zeroMem (p : Addr) : PreparedPowersRepr (fun _ => 0) p := by
  intro k hk
  have z : ∀ q : Addr, blockAt (fun _ => 0) q = 0 := fun q => by
    simp [blockAt, Spec.Aes.bytesAt, ofBytes]; decide
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  have hz : ∀ k, hpow 0 (k + 1) = 0 := fun _ => gcmMul_zero_right _
  simp only [ctxH, z, hz, w]
  constructor <;> decide

/-- A context of zeros has the prepared powers. -/
theorem preparedPowersRepr_of_zeroMem {m : Mem} {p : Addr} (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0) :
    PreparedPowersRepr m p :=
  preparedPowersRepr_congr (m₁ := fun _ => 0) h (preparedPowersRepr_zeroMem p)

variable (pb : Nat)

theorem sealPreparedPre_local : ∀ vs m₁ m₂, vs.length = (sealPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealPreparedSig.words pb) (sealPreparedPre pb) vs m₁ →
      Curry.apply (sealPreparedSig.words pb) (sealPreparedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 8
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealPreparedSig, sealPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPreparedPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (sealPreparedPre pb) _ m₂
  dsimp only [Curry.apply, sealPreparedPre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowersRepr_congr hc h.2⟩

theorem openPreparedPre_local : ∀ vs m₁ m₂, vs.length = (openPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs openPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (openPreparedSig.words pb) (openPreparedPre pb) vs m₁ →
      Curry.apply (openPreparedSig.words pb) (openPreparedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 9
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [openPreparedSig, openPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPreparedPre pb) _
    m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb] (openPreparedPre pb) _
    m₂
  dsimp only [Curry.apply, openPreparedPre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowersRepr_congr hc h.2⟩

theorem streamCryptPreparedPre_local : ∀ vs m₁ m₂, vs.length = (streamCryptPreparedSig.words pb).length →
    (∀ b ∈ Sig.bufs streamCryptPreparedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamCryptPreparedSig.words pb) (streamCryptPreparedPre pb) vs m₁ →
      Curry.apply (streamCryptPreparedSig.words pb) (streamCryptPreparedPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 6
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamCryptPreparedSig, streamCryptPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamCryptPreparedPre pb) _ m₁ at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr, ArgWord.int pb] (streamCryptPreparedPre pb) _ m₂
  dsimp only [Curry.apply, streamCryptPreparedPre, ArgWord.ofRaw] at h ⊢
  exact ⟨h.1, preparedPowersRepr_congr hc h.2⟩

end VG.Proof.AesGcm
