module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.RecoverSign
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldTest
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.X25519.PPC64LE.Invert
import VerifiedGarbage.Proof.X25519.PPC64LE.Limbs
import VerifiedGarbage.Proof.X25519.PPC64LE.Setup
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: decoding a point

`pointDecode` with the encoding at `r14`: its words into slot 1, bit 255
split off to `SIGN` (`split_ok`), `y` canonical (`pointDecodeLoad_ok`), and
the recovery of `x` (`recoverPoint_ok`): `decodePoint` of the 32 bytes
(`pointDecode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- What a decoding writes, with its sign. -/
structure DecKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.r17 :: fclob) s t
  frame : Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, FA b] s.mem t.mem

theorem DecKeep.trans {b : Addr} {s t u : State} (h : DecKeep b s t) (k : DecKeep b t u) : DecKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem DecKeep.of_dkeep {b : Addr} {s t : State} (h : DKeep b s t) : DecKeep b s t :=
  ⟨h.rest, h.frame.mono (by simp)⟩

/-- `std t, off(n)`. -/
theorem wp_stdd {s : State} {is : List Instr} {Q : State → Prop} {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hout : InRegions s.wr a 8) (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem toNat_beq_one {x : Nat} (h : x < 2) : (x == 1).toNat = x := by
  rcases (by omega_arith : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

section
variable {b : Addr}

/-- **Bit 255 of slot 1**, to `SIGN`, and cleared. -/
theorem split_ok {s : State} (hc : Ctx b s) :
    WP isa (.block splitYSign) s fun t =>
      Rest [.r7, .r8] s t ∧
      Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, ⟨b + BitVec.ofNat 64 (offset 1 + 28), 4⟩] s.mem t.mem ∧
      SignAt b (limb s.mem b (offset 1) 7 / 2 ^ 31 == 1) t.mem ∧
      limb t.mem b (offset 1) 7 = limb s.mem b (offset 1) 7 % 2 ^ 31 ∧
      ∀ j < 7, limb t.mem b (offset 1) j = limb s.mem b (offset 1) j := by
  have hS : SIGN = 24 := rfl
  have h1 : offset 1 = 96 := rfl
  unfold splitYSign VG.Impl.X25519.PPC64LE.low31
  simp only [List.cons_append, List.nil_append]
  refine lw0_ok hc (d := offset 1 + 28) (by decide) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.r7, .r8] s s3 := (u2.rest (by decide)).trans (u3.rest (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  refine wp_stdd (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide) (by rw [hc3.r6])
    (hc3.inW (by decide)) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest []) (by decide)
  refine wp_lsl (by decide) fun s5 u5 => wp_lsr (by decide) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc4.of_rest ((u5.rest (ws := [.r7]) (by decide)).trans (u6.rest (by decide))) (by decide)
  refine sw0_ok hc6 (d := offset 1 + 28) (by decide) fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hr3.trans ((u4.rest _).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest _))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ ?_)
      (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_ <;> exact Region.contains_self _ _
  · have hw : (s2.gpr .r7).toNat = limb s.mem b (offset 1) 7 := by rw [u2.gpr, toNat_ext32]; rfl
    have hx : limb s.mem b (offset 1) 7 / 2 ^ 31 < 2 := by have := limb_lt s.mem b (offset 1) 7; omega_arith
    unfold SignAt
    rw [u7.mem, Mem.readW_writeW_sep (Offset.sep b (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u6.mem,
      u5.mem, u4.mem, Mem.readW_writeW_self64, u3.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, hw, BitVec.toNat_ofNat, toNat_beq_one hx, Nat.mod_eq_of_lt (by omega_arith)]
  · show wd s7.mem b (offset 1 + 28) = _
    rw [u7.mem, wd_write_self, toNat_lo32, u6.gpr, u5.gpr, low31_val, u4.gpr, u3.other _ (by decide), u2.gpr,
      toNat_ext32]
    show (s.mem.readW (b + BitVec.ofNat 64 (offset 1 + 28)) 32).toNat % 2 ^ 31 % 2 ^ 32 = _
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  · intro j hj
    show wd s7.mem b (offset 1 + 4 * j) = wd s.mem b (offset 1 + 4 * j)
    rw [u7.mem, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), u6.mem, u5.mem, u4.mem, wd,
      Mem.readW_writeW_sep (Offset.sep b (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u3.mem, u2.mem]
    rfl

/-- **The encoding loaded**: `y` (bit 255 cleared) in slot 1, the sign at `SIGN`, and `r5` zero exactly
when `y < p`. -/
theorem pointDecodeLoad_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .r14 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecodeLoad s fun t => DecKeep b s t ∧
      SignAt b (decodeLE (bytesAt s.mem q 32) / 2 ^ 255 == 1) t.mem ∧
      env t.mem b 1 = Proof.X25519.toFe (decodeLE (bytesAt s.mem q 32) % 2 ^ 255) ∧
      (t.gpr .r5 = 0 ↔ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P) := by
  have h1 : offset 1 = 96 := rfl
  have hX := FR_eq
  unfold pointDecodeLoad canonicalY
  refine WP.seq (WP.append (unpackField_ok hc.ctx h14 (o := offset 1) (src := 0) (by decide) (by decide) hr hd)
    fun s1 ⟨r1, f1, l1⟩ => ?_)
  have hn : decodeLE (bytesAt s.mem q 32) = V s1.mem b (offset 1) :=
    bytes_of_words fun j hj => by rw [l1 j hj, Nat.zero_add]
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (split_ok hc1) fun s2 ⟨r2, f2, sg2, l7, lj⟩ => ?_
  -- `y`, and the sign, from the top limb.
  have hv1 := val32_succ (limb s1.mem b (offset 1)) 7
  have hv2 := val32_succ (limb s2.mem b (offset 1)) 7
  have hA := val32_lt (f := limb s1.mem b (offset 1)) (n := 7) fun k _ => limb_lt _ _ _ _
  have hL := limb_lt s1.mem b (offset 1) 7
  rw [val32_congr lj, l7] at hv2
  rw [show (2 : Nat) ^ (32 * 7) = 2 ^ 224 from rfl] at hv1 hv2 hA
  have hy : V s2.mem b (offset 1) = decodeLE (bytesAt s.mem q 32) % 2 ^ 255 := by
    rw [hn, V, V, hv1, hv2]; omega_arith
  have hsg : decodeLE (bytesAt s.mem q 32) / 2 ^ 255 = limb s1.mem b (offset 1) 7 / 2 ^ 31 := by
    rw [hn, V, hv1]; omega_arith
  rw [← hsg] at sg2
  have r12 : Rest [.r7, .r8] s s2 := (r1.mono (by decide)).trans r2
  have hc2 : Ctx8 b s2 := hc.of_rest r12 (by decide)
  have hF2 : Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, FA b] s.mem s2.mem := by
    refine (f1.sub fun r hr => ⟨FA b, by simp, ?_⟩).trans (f2.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨FA b, by simp, Offset.sub b (by omega_arith) (by omega_arith)⟩
  -- `y` canonical.
  refine WP.seq (WP.mono (freeze_ok hc2.ctx 1) fun s3 ⟨r3, f3, _, v3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.ctx.of_rest r3 (by decide)
  refine WP.mono (wordsEqual_ok hc3 (a := offset 1) (c := FR) (by decide) (by decide)) fun t ⟨r4, m4, h4⟩ => ?_
  have hs3 : V s3.mem b (offset 1) = V s2.mem b (offset 1) := by
    unfold V
    exact val32_congr (limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
  refine ⟨⟨(r12.mono (by decide)).trans ((r3.mono (by decide)).trans (r4.mono (by decide))),
    hF2.trans (by rw [m4]; exact (frame_FR f3).mono (by simp))⟩, ?_, ?_, ?_⟩
  · rw [m4]; exact sg2.frame (frame_FR f3)
  · rw [m4, ← hy, ← hs3]; rfl
  · rw [h4, hs3, v3, hy]
    generalize decodeLE (bytesAt s.mem q 32) % 2 ^ 255 = y
    rw [eq_comm, Nat.mod_eq_iff_lt (by decide)]

/-- **A point decoded**, from the 32 bytes at `r14`. -/
theorem pointDecode_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .r14 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecode s fun t => DecKeep b s t ∧
      ∃ o, Spec.Ed25519.decodePoint (bytesAt s.mem q 32) = o ∧ DecodeResult b o t := by
  have hl : (bytesAt s.mem q 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [Proof.Ed25519.decodePoint32 _ hl]
  unfold pointDecode
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc h14 hr hd) fun s1 ⟨k1, sg1, y1, h5⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest k1.rest (by decide)
  refine WP.ite (s1.gpr .r5 == 0) (eval_zero s1 .r5) (fun h => ?_) (fun h => ?_)
  · have hy := h5.mp (beq_iff_eq.mp h)
    refine WP.mono (recoverPoint_ok hc1 sg1) fun t ⟨kt, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), _, ?_, dt⟩
    rw [iteT hy, Proof.Ed25519.recoverResult_spec, y1]; rfl
  · have hy : ¬ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P := fun hy =>
      absurd (beq_iff_eq.mpr (h5.mpr hy)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s1) fun t ⟨kt, _, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), none, ?_, dt⟩
    rw [iteF hy]

end

end VG.Proof.Ed25519.PPC64LE
