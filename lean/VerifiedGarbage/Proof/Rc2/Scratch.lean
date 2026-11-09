module

public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# RC2-CBC's `init` with its working space as an argument

`vg_rc2_cbc_init` keeps its working space in a frame of its own, which it
zeroes before returning (`Verified.stackScratchWiped` and its counterparts),
around code proved with the working space as an argument:
`cbcInitScratchContract` is the shared contract with a 576-byte `scratch`
buffer appended, whatever it holds.

The frames copy the arguments passed on the stack, and wipe the buffer after
the code, which needs the pre- and postconditions to read the memory on
entry (`*_local`) and on return (`*PostOut_local`) only within the
function's buffers: the key, the IV and the context, through `contextAt`,
which reads only its 144 bytes (`contextAt_congr`).
-/

@[expose] public section

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
    rw [h _ (by omega_arith), h _ (by omega_arith)]
  · simp only [blockAt]
    congr 1; funext i
    rw [show p + 128 = p + BitVec.ofNat 64 128 from rfl, Offset.add_add, h _ (by omega_arith)]
  · rw [show p + 136 = p + BitVec.ofNat 64 136 from rfl]
    exact bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega_arith)

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

theorem cbcInitPost_local : ∀ vs m₁ m₂ m' r, vs.length = (cbcInitSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m₁ m' r →
      Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨key, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨kl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨iv, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨il, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cbcInitSig, Sig.bufs_nil, Sig.bufs_int, Sig.bufs_array, Sig.bufs_slice,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
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
      rw [BitVec.toNat_setWidth] at hi'; omega_arith),
    bytesAt_congr (n := (il.setWidth pb).toNat) fun i hi' => hi i (by
      rw [BitVec.toNat_setWidth] at hi'; omega_arith)]
  exact h

theorem cbcInitPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (cbcInitSig.words pb).length →
    (∀ b ∈ Sig.bufs cbcInitSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m m₁ r →
      Curry.apply (cbcInitSig.words pb) (cbcInitPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 5) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 4
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [cbcInitSig, Sig.bufs_nil, Sig.bufs_int, Sig.bufs_array, Sig.bufs_slice,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
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
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [contextAt_congr (by omega_arith) hc]; exact h2⟩
  · exact id

end VG.Proof.Rc2
