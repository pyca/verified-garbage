import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RC4 with its working space as an argument

On x86 and ARMv7, `vg_rc4_init` and `vg_rc4_apply` keep their working space
in a frame of their own, which they zero before returning
(`X86.Verified.stackScratchWiped`, `Arm.Verified.regScratchWiped`), around
code proved with the working space as an argument (on x86-64 and AArch64 the
code uses none, and is proved against the shared contracts directly):
`initScratchContract` and `applyScratchContract` are the shared contracts
with a 64-byte `scratch` buffer appended, whatever it holds.

The frames wipe the buffer after the code, and on x86 copy the arguments
passed on the stack, which needs the postconditions to read the memory on
return (`*PostOut_local`) and on entry (`*Post_local`), and `vg_rc4_apply`'s
leak to read the memory (`applyLeak_local`), only within the function's
buffers: the key, the data and the context, through `contextAt`, which reads
only its 258 bytes (`contextAt_congr`).
-/

namespace VG.Proof.Rc4

open VG.Spec.Rc4

/-- `vg_rc4_init` with `scratch: *mut [u64; 8]`. -/
def initScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u8 258),
    ("scratch", .array true .u64 8)]
  ret := some .u32

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_rc4_apply` with `scratch: *mut [u64; 8]`. -/
def applyScratchSig : Sig where
  params := [("ctx", .array true .u8 258), ("data", .slice true .u8 "len"),
    ("scratch", .array true .u64 8)]

/-- `applyContract`, whatever `scratch` is. -/
def applyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  applyScratchSig.contract A
    (post := fun ctx data len _scratch => applyPost A.ptrBits ctx data len)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx data len _scratch => applyLeak A.ptrBits ctx data len)

/-! ## Locality -/

private theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p n = bytesAt m₁ p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- A context is in its 258 bytes. -/
theorem contextAt_congr {m₁ m₂ : Mem} {p : Addr}
    (h : ∀ i < 258, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    contextAt m₂ p = contextAt m₁ p := by
  simp only [contextAt, Context.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · congr 1; funext i
    rw [h _ (by omega)]
  · rw [show p + 256 = p + BitVec.ofNat 64 256 from rfl]
    exact h _ (by decide)
  · rw [show p + 257 = p + BitVec.ofNat 64 257 from rfl]
    exact h _ (by decide)

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

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m₁ m' r →
      Curry.apply (initSig.words pb) (initPost pb) vs m₂ m' r
  | [key, kl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₂ m' r
    dsimp only [Curry.apply, initPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi' => hk i (by
      rw [BitVec.toNat_setWidth] at hi'; omega)]
    exact h

theorem initPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m m₁ r →
      Curry.apply (initSig.words pb) (initPost pb) vs m m₂ r
  | [_, _, ctx], m, m₁, m₂, r, _, hb, h => by
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m m₂ r
    dsimp only [Curry.apply, initPost, ArgWord.ofRaw] at h ⊢
    revert h
    split
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [contextAt_congr hc]; exact h2⟩
    · exact id

theorem applyPost_local : ∀ vs m₁ m₂ m' r, vs.length = (applySig.words pb).length →
    (∀ b ∈ Sig.bufs applySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (applySig.words pb) (applyPost pb) vs m₁ m' r →
      Curry.apply (applySig.words pb) (applyPost pb) vs m₂ m' r
  | [ctx, data, len], m₁, m₂, m', r, _, hb, h => by
    simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (applyPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (applyPost pb) _ m₂ m' r
    dsimp only [Curry.apply, applyPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [contextAt_congr hc, bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi =>
      hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem applyPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (applySig.words pb).length →
    (∀ b ∈ Sig.bufs applySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (applySig.words pb) (applyPost pb) vs m m₁ r →
      Curry.apply (applySig.words pb) (applyPost pb) vs m m₂ r
  | [ctx, data, len], m, m₁, m₂, r, _, hb, h => by
    simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.1
    have hd := agree_of hb.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (applyPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (applyPost pb) _ m m₂ r
    dsimp only [Curry.apply, applyPost, ArgWord.ofRaw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have := Nat.mod_le len.toNat (2 ^ pb)
    refine ⟨by rw [contextAt_congr hc]; exact h1, ?_⟩
    rw [bytesAt_congr (n := (len.setWidth pb).toNat) fun i hi =>
      hd i (by rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h2

theorem applyLeak_local : ∀ vs m₁ m₂, vs.length = (applySig.words pb).length →
    (∀ b ∈ Sig.bufs applySig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (applySig.words pb) (applyLeak pb) vs m₁ =
      Curry.apply (applySig.words pb) (applyLeak pb) vs m₂
  | [ctx, _, _], m₁, m₂, _, hb => by
    simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (applyLeak pb) _ m₁ =
      Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int pb] (applyLeak pb) _ m₂
    dsimp only [Curry.apply, applyLeak, ArgWord.ofRaw]
    rw [contextAt_congr (agree_of hb.1)]

end VG.Proof.Rc4
