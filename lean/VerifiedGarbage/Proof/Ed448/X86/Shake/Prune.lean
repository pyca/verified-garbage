import VerifiedGarbage.Proof.Ed448.X86.Shake.Layout
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Impl.Ed448.X86.Shake

/-!
# Ed448 on x86 (32-bit): pruning a hash in place

`Kit.prune_ok`: the block `pruneAt q` clears bits 0–1 of the frame's byte
`q`, sets bit 7 of byte `q + 55` and clears byte `q + 56`, through `eax`;
the 57 bytes at `q` are then `Spec.Ed448.prune` of the 114 there before
(`pruned_value`, by `Proof.Ed448.prune_bytes`). It writes nothing else.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (at_)
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR)
open VG.WriteBytes (writeW8_apply)

/-! ## The bytes -/

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

theorem pruned_value {m : Mem} {q : Addr} :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8)) q 57) =
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 := by
  have ne : ∀ i j, i < 57 → j < 57 → i ≠ j → q + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j :=
    fun i j hi hj h => Offset.add_ofNat_ne q (by omega) (by omega) h
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne0 : ∀ j, 0 < j → j < 57 → q + BitVec.ofNat 64 j ≠ q := fun j h1 h2 e =>
    ne j 0 h2 (by omega) (by omega) (e.trans z.symm)
  generalize hm' : ((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8) = m'
  have mid : Spec.Ed448.bytesAt m' (q + BitVec.ofNat 64 1) 54 = Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← hm', Offset.add_add, writeW8_apply, ite_eq_right (ne (1 + i) 56 (by omega) (by omega) (by omega)),
      writeW8_apply, ite_eq_right (ne (1 + i) 55 (by omega) (by omega) (by omega)), writeW8_apply,
      ite_eq_right (ne0 (1 + i) (by omega) (by omega))]
  have e0 : m' q = BitVec.ofNat 8 ((m q).toNat &&& 252) := by
    rw [← hm', writeW8_apply, ite_eq_right (ne0 56 (by omega) (by omega)).symm,
      writeW8_apply, ite_eq_right (ne0 55 (by omega) (by omega)).symm,
      writeW8_apply, ite_eq_left rfl]
  have e55 : m' (q + BitVec.ofNat 64 55) = BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128) := by
    rw [← hm', writeW8_apply, ite_eq_right (ne 55 56 (by omega) (by omega) (by omega)),
      writeW8_apply, ite_eq_left rfl]
  have e56 : m' (q + BitVec.ofNat 64 56) = BitVec.ofNat 8 0 := by
    rw [← hm', writeW8_apply, ite_eq_left rfl]; rfl
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

/-! ## The instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_ldb {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 1)
    (k : ∀ s', Upd s s' d ((s.mem (addr B o)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, State.load8, ea_mk, hb, hin]) (k _ (Upd.setReg _ _ _))

/-- `mov BYTE PTR [b + o], r` -/
theorem wp_stb {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

theorem wp_ori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem and_fc : ∀ x : BitVec 8, (x.setWidth 32 &&& 0xfc#32).setWidth 8 = BitVec.ofNat 8 (x.toNat &&& 252) := by
  decide

theorem or_80 : ∀ x : BitVec 8, (x.setWidth 32 ||| 0x80#32).setWidth 8 = BitVec.ofNat 8 (x.toNat ||| 128) := by
  decide

variable {E scr : BitVec 32} {n : Nat} {ins outs : List Region} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Kit.prune_ok (hk : Kit E scr n ins outs) (hc : Whole.Ctx E g m₀ ins outs t) {q : Nat}
    (hq : q + 57 ≤ 256) :
    WP isa (.block (pruneAt q)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [fr E q 57] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (E.setWidth 64 + BitVec.ofNat 64 q) 57) =
        Spec.Ed448.prune (Spec.Ed448.bytesAt t.mem (E.setWidth 64 + BitVec.ofNat 64 q) 114) ∧
      ∀ r, r ≠ .eax → u.gpr r = t.gpr r := by
  have hf := hk.frame
  have ea : ∀ k < 57, addr E (q + k) = E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 k := fun k hk' => by
    rw [addr_eq (by omega), Offset.add_add]
  have hw : ∀ k < 57, InRegions t.wr (E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 := fun k hk' => by
    rw [Offset.add_add]
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  have hr : ∀ k < 57, InRegions (t.rd ++ t.wr) (E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 :=
    fun k hk' => by
      obtain ⟨R, hR, hcon⟩ := hw k hk'
      exact ⟨R, List.mem_append_right _ hR, hcon⟩
  have e0 : addr E q = E.setWidth 64 + BitVec.ofNat 64 q := by
    rw [← Nat.add_zero q, ea 0 (by omega), Nat.add_zero, BitVec.add_zero]
  have z : E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 0 = E.setWidth 64 + BitVec.ofNat 64 q :=
    BitVec.add_zero _
  generalize hP : E.setWidth 64 + BitVec.ofNat 64 q = P at ea hw hr e0 z
  unfold pruneAt
  simp only [at_]
  refine wp_ldb (b := .esp) hc.esp (by rw [e0, ← z]; exact hr 0 (by omega)) fun s1 v1 => ?_
  refine wp_andi fun s2 v2 => ?_
  refine wp_stb (b := .esp) (by rw [v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v2.wr, v1.wr, e0, ← z]; exact hw 0 (by omega)) fun s3 v3 => ?_
  refine wp_ldb (b := .esp) (by rw [v3.gpr, v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr, ea 55 (by omega)]; exact hr 55 (by omega)) fun s4 v4 => ?_
  refine wp_ori fun s5 v5 => ?_
  refine wp_stb (b := .esp) (by rw [v5.other _ (by decide), v4.other _ (by decide), v3.gpr,
      v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, ea 55 (by omega)]; exact hw 55 (by omega)) fun s6 v6 => ?_
  refine wp_movi fun s7 v7 => ?_
  refine wp_stb (b := .esp) (by rw [v7.other _ (by decide), v6.gpr, v5.other _ (by decide), v4.other _ (by decide),
      v3.gpr, v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, ea 56 (by omega)]; exact hw 56 (by omega))
    fun u vu => WP.block_nil ?_
  have ne55 : P + BitVec.ofNat 64 55 ≠ P := fun e =>
    Offset.add_ofNat_ne P (a := 55) (b := 0) (by omega) (by omega) (by omega) (e.trans z.symm)
  have al : ∀ s : State, s.gpr Reg8.al.reg = s.gpr .eax := fun _ => rfl
  have r2 : s2.gpr .eax = (t.mem P).setWidth 32 &&& 0xfc#32 := by rw [v2.gpr, v1.gpr, e0]; rfl
  have m3 : s3.mem = t.mem.writeW P (BitVec.ofNat 8 ((t.mem P).toNat &&& 252)) := by
    rw [v3.mem, v2.mem, v1.mem, e0, al, r2, ← and_fc]
  have r5 : s5.gpr .eax = (t.mem (P + BitVec.ofNat 64 55)).setWidth 32 ||| 0x80#32 := by
    rw [v5.gpr, v4.gpr, ea 55 (by omega), m3, writeW8_apply, ite_eq_right ne55]; rfl
  have hm : u.mem = ((t.mem.writeW P (BitVec.ofNat 8 ((t.mem P).toNat &&& 252))).writeW
      (P + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((t.mem (P + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
        (P + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [vu.mem, v7.mem, v6.mem, v5.mem, v4.mem, m3, al, al, v7.gpr, r5, or_80, ea 55 (by omega),
      ea 56 (by omega)]
    rfl
  have hfr : Frame [fr E q 57] t.mem u.mem := by
    rw [hm]
    have c : ∀ k < 57, (fr E q 57).Contains (P + BitVec.ofNat 64 k) 1 := fun k hk' => by
      rw [← hP]; exact Offset.contains_base _ (by omega) (by omega)
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (c 55 (by omega))).writeW (List.mem_singleton_self _) _ (c 56 (by omega))
    have h := c 0 (by omega)
    rw [z] at h
    exact h
  have gp : ∀ r, r ≠ .eax → u.gpr r = t.gpr r := fun r hr => by
    rw [vu.gpr, v7.other r hr, v6.gpr, v5.other r hr, v4.other r hr, v3.gpr, v2.other r hr, v1.other r hr]
  refine ⟨?_, hfr, ?_, gp⟩
  · refine hc.of_frame (by rw [vu.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd])
      (by rw [vu.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]) (gp _ (by decide))
      (fun r hr _ => gp r (by rintro rfl; simp [calleeSaved] at hr)) hfr ?_
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ hq)
  · rw [hm, pruned_value]
    unfold Spec.Ed448.prune
    rw [bytesAt_take57]

end VG.Proof.Ed448.X86.Shake
