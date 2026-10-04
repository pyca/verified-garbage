import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RC2-CBC's streaming functions with their working space as an argument

`vg_rc2_cbc_init`, `vg_rc2_cbc_encrypt_update` and `_decrypt_update` keep
their working space in a frame of their own, which they zero before
returning (`Verified.stackScratchWiped` and its counterparts), around code
proved with the working space as an argument: `cbcInitScratchContract` and
`cbcUpdateScratchContract` are the shared contracts with a 576-byte
`scratch` buffer appended, whatever it holds.

The frames copy the arguments passed on the stack, and wipe the buffer after
the code, which needs the pre- and postconditions to read the memory on
entry (`*_local`) and on return (`*PostOut_local`) only within the
function's buffers: the key, the IV, the data, the output and the context,
through `contextAt`, which reads only its 144 bytes (`contextAt_congr`).
-/

namespace VG.Proof.Rc2

open VG.Spec.Rc2

/-- `vg_rc2_cbc_init` with `scratch: *mut [u64; 72]`. -/
def cbcInitScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("effective_bits", .int .usize true),
    ("iv", .slice false .u8 "iv_len"), ("ctx", .array true .u8 144),
    ("scratch", .array true .u64 72)]
  ret := some .u32

/-- `cbcInitContract`, whatever `scratch` is. -/
def cbcInitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcInitScratchSig.contract A
    (post := fun key keyLen effectiveBits iv ivLen ctx _scratch =>
      cbcInitPost A.ptrBits key keyLen effectiveBits iv ivLen ctx)
    (writeArgs := true) (stack := stack)

/-- The update functions with `scratch: *mut [u64; 72]`. -/
def cbcUpdateScratchSig : Sig where
  params := [("ctx", .array true .u8 144), ("pending_len", .int .usize true),
    ("data", .slice false .u8 "len"), ("out", .slice true .u8 "out_len"),
    ("scratch", .array true .u64 72)]

/-- `cbcUpdateContract`, whatever `scratch` is. -/
def cbcUpdateScratchContract {M : ISA} (A : Abi M) (direction : Direction) (stack : Nat := 0) :
    Contract M :=
  cbcUpdateScratchSig.contract A
    (pre := fun ctx pendingLen data len out outLen _scratch =>
      cbcUpdatePre A.ptrBits ctx pendingLen data len out outLen)
    (post := fun ctx pendingLen data len out outLen _scratch =>
      cbcUpdatePost direction A.ptrBits ctx pendingLen data len out outLen)
    (writeArgs := true) (stack := stack)

def cbcEncryptUpdateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcUpdateScratchContract A .encrypt stack

def cbcDecryptUpdateScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cbcUpdateScratchContract A .decrypt stack

/-! ## Locality -/

private theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- A context with at most 8 pending bytes is in its 144 bytes. -/
theorem contextAt_congr {m₁ m₂ : Mem} {p : Addr} {d : Direction} {k : Nat} (hk : k ≤ 8)
    (h : ∀ i < 144, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    contextAt m₂ p d k = contextAt m₁ p d k := by
  simp only [contextAt, Context.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · simp only [scheduleAt]
    congr 1; funext i
    rw [h _ (by omega), h _ (by omega)]
  · simp only [blockAt]
    congr 1; funext i
    rw [show p + 128 = p + BitVec.ofNat 64 128 from rfl, Offset.add_add, h _ (by omega)]
  · rw [show p + 136 = p + BitVec.ofNat 64 136 from rfl]
    exact bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)

/-- The memory agrees on the `n` bytes at `p`, from its agreeing on the
region. -/
private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

variable (pb : Nat)

theorem cbcInitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcInitSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m₁ m' r →
      Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m₂ m' r
  | [key, kl, _, iv, il, _], m₁, m₂, m', r, _, hb, h => by
    simp only [cbcInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    have hi := agree_of hb.2.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr] (cbcInitPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr] (cbcInitPost pb) _ m₂ m' r
    dsimp only [Curry.apply, cbcInitPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    have := Nat.mod_le il.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi' => hk i (by
        rw [BitVec.toNat_setWidth] at hi'; omega),
      bytesAt_congr (n := (il.setWidth pb).toNat) fun i hi' => hi i (by
        rw [BitVec.toNat_setWidth] at hi'; omega)]
    exact h

theorem cbcInitPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcInitSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m m₁ r →
      Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m m₂ r
  | [_, _, _, _, _, ctx], m, m₁, m₂, r, _, hb, h => by
    simp only [cbcInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr] (cbcInitPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
      ArgWord.addr] (cbcInitPost pb) _ m m₂ r
    dsimp only [Curry.apply, cbcInitPost, ArgWord.ofRaw] at h ⊢
    intro direction
    have h' := h direction
    revert h'
    split
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [contextAt_congr (by omega) hc]; exact h2⟩
    · exact id

theorem cbcUpdatePre_local : ∀ vs m₁ m₂, vs.length = (cbcUpdateSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcUpdateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcUpdateSig.words pb) (cbcUpdatePre pb) vs m₁ →
      Curry.apply (cbcUpdateSig.words pb) (cbcUpdatePre pb) vs m₂
  | [_, _, _, _, _, _], _, _, _, _, h => h

theorem cbcUpdatePost_local (d : Direction) : ∀ vs m₁ m₂ m' r,
    vs.length = (cbcUpdateSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcUpdateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcUpdateSig.words pb) (cbcUpdatePost d pb) vs m₁ m' r →
      Curry.apply (cbcUpdateSig.words pb) (cbcUpdatePost d pb) vs m₂ m' r
  | [ctx, pl, data, len, _, _], m₁, m₂, m', r, _, hb, h => by
    simp only [cbcUpdateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hd := agree_of hb.2.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb] (cbcUpdatePost d pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb] (cbcUpdatePost d pb) _ m₂ m' r
    dsimp only [Curry.apply, cbcUpdatePost, ArgWord.ofRaw] at h ⊢
    intro hp
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [contextAt_congr (by omega) hc, bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi =>
      hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h hp

theorem cbcUpdatePostOut_local (d : Direction) : ∀ vs m m₁ m₂ r,
    vs.length = (cbcUpdateSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcUpdateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcUpdateSig.words pb) (cbcUpdatePost d pb) vs m m₁ r →
      Curry.apply (cbcUpdateSig.words pb) (cbcUpdatePost d pb) vs m m₂ r
  | [ctx, _, _, _, out, ol], m, m₁, m₂, r, _, hb, h => by
    simp only [cbcUpdateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have ho := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb] (cbcUpdatePost d pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb] (cbcUpdatePost d pb) _ m m₂ r
    dsimp only [Curry.apply, cbcUpdatePost, ArgWord.ofRaw] at h ⊢
    intro hp
    obtain ⟨h1, h2⟩ := h hp
    have := Nat.mod_le ol.toNat (2 ^ pb)
    refine ⟨by rw [contextAt_congr (by omega) hc]; exact h1, ?_⟩
    rw [bytesAt_congr (n := (ol.setWidth pb).toNat) fun i hi =>
      ho i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h2

end VG.Proof.Rc2
