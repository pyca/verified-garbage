module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.Whole
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Ed448's whole functions on PPC64LE: pruning in place

`prune f o` clears bits 0–1 of the byte at `o(f)`, sets bit 7 of the byte
55 after it and clears the byte 56 after it (`prune_ok`); the 57 bytes then
decode to `Spec.Ed448.prune` of the hash they start (`pruned_value`, as on
ARMv7, `Proof/Ed448/Arm/PublicKey/Base.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Proof.Sha3 (writeW8_apply)

/-! ## The bytes -/

theorem off_ne (q : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) (h : d ≠ e) :
    q + BitVec.ofNat 64 d ≠ q + BitVec.ofNat 64 e := by
  intro x
  have := congrArg (fun a => (a - q).toNat) x
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at this
  exact h this

theorem bytesAt_split (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = m q :: (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 ++
      [m (q + BitVec.ofNat 64 55), m (q + BitVec.ofNat 64 56)]) := by
  have b1 : Spec.X25519.bytesAt m q 1 = [m q] := by
    simp [Spec.X25519.bytesAt]
  have b2 : ∀ p : Addr, Spec.X25519.bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := fun p => by
    simp [Spec.X25519.bytesAt, List.range_succ]
  rw [Proof.Ed448.bytesAt_eq, show 57 = 1 + (54 + 2) from rfl, VG.Proof.X25519.bytesAt_add,
    VG.Proof.X25519.bytesAt_add, b1, b2, Offset.add_add, Offset.add_add]
  rfl

theorem decodeLE_split (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) = (m q).toNat + 256 *
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) + 2 ^ 432 *
        ((m (q + BitVec.ofNat 64 55)).toNat + 256 * (m (q + BitVec.ofNat 64 56)).toNat)) := by
  rw [bytesAt_split, Spec.Ed448.decodeLE, Proof.Ed448.decodeLE_append]
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  rw [hl, show (256 : Nat) ^ 54 = 2 ^ 432 by decide +kernel]
  simp only [Spec.Ed448.decodeLE, Nat.mul_zero, Nat.add_zero]

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [Proof.Ed448.bytesAt_eq, Proof.Ed448.bytesAt_eq, show 114 = 57 + 57 from rfl, VG.Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]

/-- The pruned bytes. -/
abbrev pruned (m : Mem) (q : Addr) : Mem :=
  ((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
    (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
      (q + BitVec.ofNat 64 56) (0 : BitVec 8)

theorem pruned_value (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (pruned m q) q 57) =
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 := by
  have ne : ∀ i j, i < 57 → j < 57 → i ≠ j → q + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j :=
    fun i j hi hj h => off_ne q (by omega) (by omega) h
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne0 : ∀ j, 0 < j → j < 57 → q + BitVec.ofNat 64 j ≠ q := fun j h1 h2 e =>
    ne j 0 h2 (by decide) (by omega) (e.trans z.symm)
  generalize hm' : pruned m q = m'
  have mid : Spec.Ed448.bytesAt m' (q + BitVec.ofNat 64 1) 54 = Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← hm', pruned, Offset.add_add, writeW8_apply, ite_eq_right (ne (1 + i) 56 (by omega) (by omega) (by omega)),
      writeW8_apply, ite_eq_right (ne (1 + i) 55 (by omega) (by omega) (by omega)), writeW8_apply,
      ite_eq_right (ne0 (1 + i) (by omega) (by omega))]
  have e0 : m' q = BitVec.ofNat 8 ((m q).toNat &&& 252) := by
    rw [← hm', pruned, writeW8_apply, ite_eq_right (ne0 56 (by omega) (by omega)).symm,
      writeW8_apply, ite_eq_right (ne0 55 (by omega) (by omega)).symm,
      writeW8_apply, ite_eq_left rfl]
  have e55 : m' (q + BitVec.ofNat 64 55) = BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128) := by
    rw [← hm', pruned, writeW8_apply, ite_eq_right (ne 55 56 (by omega) (by omega) (by omega)),
      writeW8_apply, ite_eq_left rfl]
  have e56 : m' (q + BitVec.ofNat 64 56) = BitVec.ofNat 8 0 := by
    rw [← hm', pruned, writeW8_apply, ite_eq_left rfl]; rfl
  rw [decodeLE_split, decodeLE_split, mid, e0, e55, e56]
  have h0 := (m q).isLt
  have h55 := (m (q + BitVec.ofNat 64 55)).isLt
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  have hM' := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54)
  rw [hl] at hM'
  have hM : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) < 2 ^ 432 :=
    Nat.lt_of_lt_of_le hM' (Nat.le_of_eq (by decide +kernel))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left h0),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) h55 (by decide))]
  exact (Proof.Ed448.prune_bytes (b56 := (m (q + BitVec.ofNat 64 56)).toNat) h0 hM h55).symm

/-- The pruned hash is `Spec.Ed448.prune` of the hash. -/
theorem pruned_prune (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (pruned m q) q 57) = Spec.Ed448.prune (Spec.Ed448.bytesAt m q 114) := by
  rw [pruned_value, Spec.Ed448.prune, bytesAt_take57]

/-- Pruning writes only the 57 bytes. -/
theorem pruned_frame (m : Mem) (q : Addr) : Frame [⟨q, 57⟩] m (pruned m q) := by
  have h : ∀ j, j < 57 → (⟨q, 57⟩ : Region).Contains (q + BitVec.ofNat 64 j) (8 / 8) := fun j hj =>
    Offset.contains_base q (by omega) (by omega)
  refine (((Frame.refl _ _).writeW List.mem_cons_self _ ?_).writeW List.mem_cons_self _ (h 55 (by decide))).writeW
    List.mem_cons_self _ (h 56 (by decide))
  have := h 0 (by decide)
  rwa [BitVec.add_zero] at this

/-! ## The instructions -/

theorem and_fc : ∀ b : Byte,
    ((BitVec.ofNat 64 b.toNat >>> 2) <<< 2).setWidth 8 = BitVec.ofNat 8 (b.toNat &&& 252) := by
  decide

theorem or_80 : ∀ b : Byte,
    (BitVec.ofNat 64 b.toNat ||| (0x80 : BitVec 16).setWidth 64).setWidth 8 = BitVec.ofNat 8 (b.toNat ||| 128) := by
  decide

/-- `prune f o`, at `q = o(f)`: the bytes pruned, only `r8` written. -/
theorem prune_ok {s : State} {f : Reg} {o : Nat} {q : Addr} (hf : f ≠ .r0) (hf8 : f ≠ .r8) (ho : o + 56 < 2 ^ 15)
    (hq : s.gpr f + BitVec.ofNat 64 o = q) (hw : ∀ j < 57, InRegions s.wr (q + BitVec.ofNat 64 j) 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.mem = pruned s.mem q → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      (∀ r, r ≠ .r8 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (prune f o ++ is)) s Q := by
  have hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1 := fun j hj => by
    obtain ⟨R, hR, hc⟩ := hw j hj
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have ea : ∀ j < 57, s.gpr f + BitVec.ofNat 64 (o + j) = q + BitVec.ofNat 64 j := fun j hj => by
    rw [← hq, Offset.add_add]
  have e0 : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne55 : q + BitVec.ofNat 64 55 ≠ q := fun e => off_ne q (d := 55) (e := 0) (by decide) (by decide) (by decide)
    (e.trans e0.symm)
  unfold prune
  simp only [List.cons_append, List.nil_append]
  refine wp_lbz (a := q) hf (by omega) hq (by rw [← e0]; exact hr 0 (by decide))
    fun s1 v1 => ?_
  refine wp_lsr (by decide) fun s2 v2 => wp_lsl (by decide) fun s3 v3 => ?_
  refine wp_stb (a := q) hf (by omega)
    (by rw [v3.other _ hf8, v2.other _ hf8, v1.other _ hf8]; exact hq)
    (by rw [v3.wr, v2.wr, v1.wr, ← e0]; exact hw 0 (by decide)) fun s4 v4 => ?_
  have g4 : s4.gpr f = s.gpr f := by
    rw [v4.gpr, v3.other _ hf8, v2.other _ hf8, v1.other _ hf8]
  refine wp_lbz (a := q + BitVec.ofNat 64 55) hf (by omega) (by rw [g4]; exact ea 55 (by decide))
    (by rw [v4.rd, v4.wr, v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr 55 (by decide)) fun s5 v5 => ?_
  refine wp_ori fun s6 v6 => ?_
  refine wp_stb (a := q + BitVec.ofNat 64 55) hf (by omega)
    (by rw [v6.other _ hf8, v5.other _ hf8, g4]; exact ea 55 (by decide))
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 55 (by decide)) fun s7 v7 => ?_
  refine wp_li (by decide) fun s8 v8 => ?_
  refine wp_stb (a := q + BitVec.ofNat 64 56) hf (by omega)
    (by rw [v8.other _ hf8, v7.gpr, v6.other _ hf8, v5.other _ hf8, g4]; exact ea 56 (by decide))
    (by rw [v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 56 (by decide)) fun t vt => ?_
  refine k t ?_ ?_ ?_ ?_ fun r hr => ?_
  · have r3 : s3.gpr .r8 = ((BitVec.ofNat 64 (s.mem q).toNat) >>> 2) <<< 2 := by
      rw [v3.gpr, v2.gpr, v1.gpr]
    have m4 : s4.mem = s.mem.writeW q (BitVec.ofNat 8 ((s.mem q).toNat &&& 252)) := by
      rw [v4.mem, v3.mem, v2.mem, v1.mem, r3, and_fc]
    have r6 : s6.gpr .r8 = BitVec.ofNat 64 (s.mem (q + BitVec.ofNat 64 55)).toNat ||| (0x80 : BitVec 16).setWidth 64 := by
      rw [v6.gpr, v5.gpr, m4, writeW8_apply, ite_eq_right ne55]
    have m7 : s7.mem = (s.mem.writeW q (BitVec.ofNat 8 ((s.mem q).toNat &&& 252))).writeW (q + BitVec.ofNat 64 55)
        (BitVec.ofNat 8 ((s.mem (q + BitVec.ofNat 64 55)).toNat ||| 128)) := by
      rw [v7.mem, v6.mem, v5.mem, m4, r6, or_80]
    rw [vt.mem, v8.mem, m7, v8.gpr]
    rfl
  · rw [vt.sp, v8.sp, v7.sp, v6.sp, v5.sp, v4.sp, v3.sp, v2.sp, v1.sp]
  · rw [vt.rd, v8.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd]
  · rw [vt.wr, v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]
  · rw [vt.gpr, v8.other r hr, v7.gpr, v6.other r hr, v5.other r hr, v4.gpr, v3.other r hr, v2.other r hr,
      v1.other r hr]

end VG.Proof.Ed448.PPC64LE.Whole
