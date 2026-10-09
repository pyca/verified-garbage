import VerifiedGarbage.Proof.Ed25519.Arm.FnCall
import VerifiedGarbage.Spec.Ed25519.Point16

/-!
# Ed25519 on ARMv7: the elements as the specification of the functions reads them

`Spec/X25519/Field16.lean` and `Spec/Ed25519/Point16.lean` read an element
at a byte offset given as a 32-bit word; the proofs read it at an offset in
`Nat` (`limb`, `V`, `env`). They agree (`limbAt_ofNat`, `valAt_ofNat`,
`limbs_ofNat`, `elemAt_eq`, `pointAt_eq`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519.Field16 (limbAt valN valAt Limbs)

theorem limbAt_ofNat (m : Mem) (B : Addr) {n : Nat} (hn : n < 2 ^ 32) (k : Nat) :
    limbAt m B (BitVec.ofNat 32 n) k = limb m B n k := by
  simp only [limbAt, limb, wd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem limbs_ofNat {m : Mem} {B : Addr} {n : Nat} (hn : n < 2 ^ 32) :
    Limbs m B (BitVec.ofNat 32 n) ↔ Lim m B n := by
  simp only [Limbs, Lim, limbAt_ofNat m B hn, Spec.X25519.Field16.limbs]

theorem valN_ofNat (m : Mem) (B : Addr) {n : Nat} (hn : n < 2 ^ 32) :
    ∀ k, valN m B (BitVec.ofNat 32 n) k = val16 (limb m B n) k
  | 0 => rfl
  | k + 1 => by rw [valN, val16, valN_ofNat m B hn k, limbAt_ofNat m B hn]

theorem valAt_ofNat (m : Mem) (B : Addr) {n : Nat} (hn : n < 2 ^ 32) :
    valAt m B (BitVec.ofNat 32 n) = V m B n :=
  valN_ofNat m B hn 16

theorem elemAt_eq (m : Mem) (b : BitVec 32) (i : Slot) :
    Spec.Ed25519.Point16.elemAt m (State.addr b) (offset i) = env m b i := by
  rw [Spec.Ed25519.Point16.elemAt, valAt_ofNat m _ (by have := slot_range i; rw [ACC_eq] at this; omega)]
  rfl

theorem pointAt_eq (m : Mem) (b : BitVec 32) (i : Nat) (hi : i + 3 < 22) :
    Spec.Ed25519.Point16.pointAt m (State.addr b) (64 + 64 * i) =
      point (env m b) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ ⟨i + 3, by omega⟩ := by
  have e (j : Nat) (hj : j < 22) : 64 + 64 * j = offset ⟨j, hj⟩ := rfl
  rw [Spec.Ed25519.Point16.pointAt, point, show Spec.Ed25519.Point16.elemBytes = 64 from rfl, e i (by omega),
    show offset ⟨i, _⟩ + 64 = offset ⟨i + 1, by omega⟩ by simp only [offset]; omega,
    show offset ⟨i, _⟩ + 2 * 64 = offset ⟨i + 2, by omega⟩ by simp only [offset]; omega,
    show offset ⟨i, _⟩ + 3 * 64 = offset ⟨i + 3, by omega⟩ by simp only [offset]; omega,
    elemAt_eq, elemAt_eq, elemAt_eq, elemAt_eq]

/-- The limbs of slot `i` as `Spec` asks for them. -/
theorem lim_of_limbs {m : Mem} {b : BitVec 32} {i : Slot} {n : Nat} (hn : n = offset i)
    (h : Limbs m (State.addr b) (BitVec.ofNat 32 n)) : Lim m (State.addr b) (offset i) := by
  subst hn
  exact (limbs_ofNat (by have := slot_range i; rw [ACC_eq] at this; omega)).mp h

theorem limbs_of_lim {m : Mem} {b : BitVec 32} {i : Slot} {n : Nat} (hn : n = offset i)
    (h : Lim m (State.addr b) (offset i)) : Limbs m (State.addr b) (BitVec.ofNat 32 n) := by
  subst hn
  exact (limbs_ofNat (by have := slot_range i; rw [ACC_eq] at this; omega)).mpr h

/-- `limsAfter` adds each operation's result. -/
theorem limsAfter_out : ∀ {ops : List FieldOp} {S S' : List Slot}, limsAfter ops S = some S' →
    ∀ op ∈ ops, opOut op ∈ S'
  | [], _, _, _ => fun _ h => nomatch h
  | op :: ops, S, S', h => by
    simp only [limsAfter] at h
    split at h
    · intro op' hop'
      rcases List.mem_cons.mp hop' with rfl | hop'
      · exact limsAfter_sup h _ List.mem_cons_self
      · exact limsAfter_out h op' hop'
    · cases h

end VG.Proof.Ed25519.Arm
