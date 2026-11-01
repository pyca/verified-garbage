module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldProg
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Power
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: the elements as the contracts read them

An element's 32 bytes, little-endian, are its eight words (`read_V`), so the
contracts' `valAt` and `elemAt` are the proofs' `V` and `FS` (`valAt_eq`,
`elemAt_eq`), and their `Keeps` follow from the frames of the code.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

theorem read_V (m : Mem) (b : Addr) (o : Nat) : (m.read (b + BitVec.ofNat 64 o) 32).toNat = V m b o := by
  have e : ∀ k, b + BitVec.ofNat 64 (o + 4 * k) = b + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) :=
    fun k => by rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [← Proof.X25519.leNum_bytesAt_read, Proof.X25519.leNum_bytesAt_words32]
  simp only [V, val32, limb, wd, e]
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  simp only [Nat.reduceMul, BitVec.add_zero]

theorem valAt_eq (m : Mem) (b : Addr) (o : BitVec 32) : Proof.X25519.Field32.valAt m b o = V m b o.toNat :=
  read_V m b o.toNat

theorem valAt_ofNat (m : Mem) (b : Addr) (i : Slot) :
    Proof.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) := by
  have := slot_range i
  rw [valAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem elemAt_eq (m : Mem) (b : Addr) (i : Slot) :
    Proof.Ed25519.Point32.elemAt m b (offset i) = env m b i :=
  congrArg (Fin.ofNat P) (read_V m b (offset i))

theorem pointAt_eq (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.pAt = point (env m b) 0 1 2 3 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

theorem pointAt_q (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.qAt = point (env m b) 4 5 6 7 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

/-- A byte of the working space outside `[e, e + k)` is in no region of a frame there. -/
theorem byte_out {b : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨b + BitVec.ofNat 64 e, k⟩ : Region).Contains (b + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint b (d := i) (n := 1) (e := e) (k := k) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc

/-- `mul`'s `Keeps`, from its frame. -/
theorem keeps_mul {b : Addr} {o : BitVec 32} (ho : o.toNat + 32 ≤ 768) {m m' : Mem}
    (hf : Frame (opFrame b o.toNat) m m') : Proof.X25519.Field32.Keeps b o m m' := by
  intro i hi hown hoi
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.ownAt, Proof.X25519.Field32.ownEnd,
    Proof.X25519.Field32.elemBytes] at hi hown hoi
  have hA := ACC_eq
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega) (by omega) hoi
  · exact byte_out (by omega) (by omega) (by omega)

/-- `pow250`'s `Keeps₂`, from its frame. -/
theorem keeps_pow {b : Addr} {m m' : Mem} (hf : Frame [PR b] m m') : Proof.X25519.Field32.Keeps₂ b m m' := by
  intro i hi hown
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.eAt, Proof.X25519.Field32.ownEnd] at hi hown
  exact hf _ fun r hr => by rw [List.mem_singleton.mp hr]; exact byte_out (by omega) (by omega) hown

/-- What the point addition writes: the sum, the temporaries and the product's limbs. -/
abbrev addW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 64, 128⟩, ⟨b + BitVec.ofNat 64 320, 256⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

/-- The point addition's `Keeps`, from its frame. -/
theorem keeps_add {b : Addr} {m m' : Mem} (hf : Frame (addW b) m m') : Proof.Ed25519.Point32.Keeps b m m' := by
  intro i hi hp ht ho
  simp only [Proof.Ed25519.Point32.wsBytes, Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes] at hi hp ht ho
  have hA := ACC_eq
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact byte_out (by omega) (by omega) hp
  · exact byte_out (by omega) (by omega) ht
  · exact byte_out (by omega) (by omega) (by omega)

/-- A power, as the contract states it. -/
theorem val_of_env {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : env m' b i = Proof.X25519.pw (env m b j) e) :
    V m' b (offset i) % P = V m b (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, FS, Proof.X25519.toFe_val, Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

end VG.Proof.Ed25519.PPC64LE
