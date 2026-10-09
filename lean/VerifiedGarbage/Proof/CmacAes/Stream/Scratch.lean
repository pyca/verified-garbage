import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming AES-CMAC with its working space as an argument

`vg_cmac_aes_init`, `absorb` and `finish` keep their working space in a
frame of their own (`Verified.stackScratch`, `Verified.regScratch`), around
code proved with the working space as an argument: `initScratchContract`,
`absorbScratchContract` and `finishScratchContract` are the shared contracts
with a 2304-byte `scratch` buffer appended, whatever it holds.

On x86 and ARMv7 the frame also holds a copy of the arguments passed on the
stack, which needs the pre- and postconditions to read the memory on entry
only within the function's buffers (`initPost_local`, `absorbPost_local`,
`finishPost_local`): the key, the data, and the streaming state, through
`Repr`, which reads only the state's 304 bytes (`repr_congr_304`).
-/

namespace VG.Proof.CmacAes.Stream

open VG.Spec.Cmac

/-- `vg_cmac_aes_init` with `scratch: *mut [u64; 288]`. -/
def initScratchSig : Sig where
  params := [("state", .array true .u64 38), ("key", .slice false .u8 "key_len"),
    ("scratch", .array true .u64 288)]

/-- `aesInitContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (pre := fun state key keyLen _scratch => aesInitPre A.ptrBits state key keyLen)
    (post := fun state key keyLen _scratch => aesInitPost A.ptrBits state key keyLen)
    (stack := stack)

/-- `vg_cmac_aes_absorb` with `scratch: *mut [u64; 288]`. -/
def absorbScratchSig : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("data", .slice false .u8 "len"),
    ("scratch", .array true .u64 288)]

/-- `aesAbsorbContract`, whatever `scratch` is. -/
def absorbScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  absorbScratchSig.contract A
    (pre := fun state rounds count data len _scratch =>
      aesAbsorbPre A.ptrBits state rounds count data len)
    (post := fun state rounds count data len _scratch =>
      aesAbsorbPost A.ptrBits state rounds count data len)
    (stack := stack)

/-- `vg_cmac_aes_finish` with `scratch: *mut [u64; 288]`. -/
def finishScratchSig : Sig where
  params := [("state", .array true .u64 38), ("rounds", .int .usize true),
    ("count", .int .u64 true), ("out", .array true .u8 16),
    ("scratch", .array true .u64 288)]

/-- `aesFinishContract`, whatever `scratch` is. -/
def finishScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finishScratchSig.contract A
    (pre := fun state rounds count out _scratch => aesFinishPre A.ptrBits state rounds count out)
    (post := fun state rounds count out _scratch => aesFinishPost A.ptrBits state rounds count out)
    (stack := stack)

/-! ## Locality -/

private theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `bytesAt_congr`, at an offset `d` into the agreeing bytes. -/
private theorem bytesAt_congr_off {m₁ m₂ : Mem} {p : Addr} {d n N : Nat} (hn : d + n ≤ N)
    (h : ∀ i < N, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n :=
  bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega_arith)

/-- The streaming state represents a message by its 304 bytes alone. -/
theorem repr_congr_304 {m₁ m₂ : Mem} {p : Addr} {key msg : List Byte}
    (h : ∀ i < 304, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i))
    (hr : Repr m₁ p key msg) : Repr m₂ p key msg := by
  obtain ⟨hl, h1, h2, h3, h4⟩ := hr
  have hR : 16 * (Spec.Aes.rounds (key.length / 4) + 1) ≤ 240 := by
    simp only [Spec.Aes.rounds]; omega_arith
  have hc : msg.length - chainedLen 16 msg.length ≤ 16 := by unfold chainedLen; omega_arith
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · rw [bytesAt_congr fun i hi => h i (by omega_arith)]; exact h1
  · rw [show p + 240 = p + BitVec.ofNat 64 240 from rfl, bytesAt_congr_off (N := 304) (by omega_arith) h]
    exact h2
  · rw [show p + 272 = p + BitVec.ofNat 64 272 from rfl, bytesAt_congr_off (N := 304) (by omega_arith) h]
    exact h3
  · rw [show p + 288 = p + BitVec.ofNat 64 288 from rfl, bytesAt_congr_off (N := 304) (by omega_arith) h]
    exact h4

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

variable (pb : Nat)

theorem initPre_local : ∀ vs m₁ m₂, vs.length = (aesInitSig.words pb).length →
    (∀ b ∈ Sig.bufs aesInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesInitSig.words pb) (aesInitPre pb) vs m₁ →
      Curry.apply (aesInitSig.words pb) (aesInitPre pb) vs m₂
  | [_, _, _], _, _, _, _, h => h

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (aesInitSig.words pb).length →
    (∀ b ∈ Sig.bufs aesInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesInitSig.words pb) (aesInitPost pb) vs m₁ m' r →
      Curry.apply (aesInitSig.words pb) (aesInitPost pb) vs m₂ m' r
  | [_, key, kl], m₁, m₂, m', r, _, hb, h => by
    simp only [aesInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (aesInitPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (aesInitPost pb) _ m₂ m' r
    dsimp only [Curry.apply, aesInitPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith)]
    exact h

theorem absorbPre_local : ∀ vs m₁ m₂, vs.length = (aesAbsorbSig.words pb).length →
    (∀ b ∈ Sig.bufs aesAbsorbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesAbsorbSig.words pb) (aesAbsorbPre pb) vs m₁ →
      Curry.apply (aesAbsorbSig.words pb) (aesAbsorbPre pb) vs m₂
  | [_, _, _, _, _], _, _, _, _, h => h

theorem absorbPost_local : ∀ vs m₁ m₂ m' r, vs.length = (aesAbsorbSig.words pb).length →
    (∀ b ∈ Sig.bufs aesAbsorbSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesAbsorbSig.words pb) (aesAbsorbPost pb) vs m₁ m' r →
      Curry.apply (aesAbsorbSig.words pb) (aesAbsorbPost pb) vs m₂ m' r
  | [st, _, _, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [aesAbsorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
      (aesAbsorbPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
      (aesAbsorbPost pb) _ m₂ m' r
    dsimp only [Curry.apply, aesAbsorbPost, ArgWord.ofRaw] at h ⊢
    intro key msg hr h1 h2 h3
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega_arith)]
    exact h key msg (repr_congr_304 (fun i hi => (hs i (by omega_arith)).symm) hr) h1 h2 h3

theorem finishPre_local : ∀ vs m₁ m₂, vs.length = (aesFinishSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinishSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinishSig.words pb) (aesFinishPre pb) vs m₁ →
      Curry.apply (aesFinishSig.words pb) (aesFinishPre pb) vs m₂
  | [_, _, _, _], _, _, _, _, h => h

theorem finishPost_local : ∀ vs m₁ m₂ m' r, vs.length = (aesFinishSig.words pb).length →
    (∀ b ∈ Sig.bufs aesFinishSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (aesFinishSig.words pb) (aesFinishPost pb) vs m₁ m' r →
      Curry.apply (aesFinishSig.words pb) (aesFinishPost pb) vs m₂ m' r
  | [st, _, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [aesFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hs := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int 64, ArgWord.addr]
      (aesFinishPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int 64, ArgWord.addr]
      (aesFinishPost pb) _ m₂ m' r
    dsimp only [Curry.apply, aesFinishPost, ArgWord.ofRaw] at h ⊢
    intro key msg hr
    exact h key msg (repr_congr_304 (fun i hi => (hs i (by omega_arith)).symm) hr)

end VG.Proof.CmacAes.Stream
