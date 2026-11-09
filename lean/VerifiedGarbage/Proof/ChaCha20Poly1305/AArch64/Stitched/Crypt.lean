module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the chunks in the context

`Stitch.bulk` runs on the regions of the stream (the ChaCha20 state, the data
and the working space, as `vg_chacha20_xor`'s contract gives them), which the
context and the data contain (`WP.narrow`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked BPre Acc bulk_ok)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

variable {sve : Bool}

@[simp] theorem withRegions_v (s : State) (rd wr : List Region) : (s.withRegions rd wr).v = s.v := rfl

/-- The data from byte `o`. -/
abbrev dRo (s₀ : State) (o : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 o, L s₀ - o⟩

theorem dRo_sub (s₀ : State) {o : Nat} (ho : o ≤ L s₀) : Region.Sub (dRo s₀ o) (dR s₀) :=
  Offset.sub_base _ (by omega)

/-- The destination from byte `o`. -/
abbrev qRo (s₀ : State) (Q : Addr) (o : Nat) : Region := ⟨Q + BitVec.ofNat 64 o, L s₀ - o⟩

/-- The stream's regions in the context, with the destination from byte `o`. -/
abbrev streamR (s₀ : State) (Q : Addr) (o : Nat) : List Region := [sub s₀ 64 64, qRo s₀ Q o, sub s₀ 128 320]

theorem toNat_off_le {p : Addr} {o L : Nat} (hw : p.toNat + L ≤ 2 ^ 64) (ho : o ≤ L) (hL : L < 2 ^ 64) :
    (p + BitVec.ofNat 64 o).toNat + (L - o) ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

theorem bulk_bpre {s₀ : State} (hp : APre e s₀) {Q : Addr} (hq : DstR s₀ Q) {o : Nat} (ho : o ≤ L s₀)
    {s : State} (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 o)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - o)) (hx3 : s.gpr .x3 = off (cx s₀) 128)
    (hx4 : s.gpr .x4 = Q + BitVec.ofNat 64 o) :
    BPre (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := by
  have hsub := dRo_sub s₀ ho
  have hqsub : Region.Sub (qRo s₀ Q o) ⟨Q, L s₀⟩ := Offset.sub_base _ (by omega)
  have hst : (sub s₀ 64 64).Disjoint (dRo s₀ o) :=
    (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hsub
  have hsq : (sub s₀ 64 64).Disjoint (qRo s₀ Q o) :=
    (hq.ctx.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hqsub
  have hsb : (sub s₀ 64 64).Disjoint (sub s₀ 128 320) :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hdb : (dRo s₀ o).Disjoint (sub s₀ 128 320) :=
    (hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hsub
  have hqb : (qRo s₀ Q o).Disjoint (sub s₀ 128 320) :=
    (hq.ctx.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hqsub
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL : L s₀ - o < 2 ^ 64 := by omega
  have hw : (dp s₀ + BitVec.ofNat 64 o).toNat + (L s₀ - o) ≤ 2 ^ 64 := toNat_off_le hp.wrap_d ho hL5
  have hwq : (Q + BitVec.ofNat 64 o).toNat + (L s₀ - o) ≤ 2 ^ 64 := toNat_off_le hq.wrap ho hL5
  have hal : Q + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 o ∨ (dRo s₀ o).Disjoint (qRo s₀ Q o) := by
    rcases hq.same with he | hd
    · exact .inl (by rw [he])
    · exact .inr ((hd.sub_left hsub).sub_right hqsub)
  have e1 : (s.withRegions [dRo s₀ o] (streamR s₀ Q o)).gpr .x1 = dp s₀ + BitVec.ofNat 64 o := by
    rw [State.withRegions_gpr, hx1]
  have e2 : VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = L s₀ - o := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hL]
  have e0 : VG.Proof.ChaCha20.AArch64.Xor.st (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = off (cx s₀) 64 := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, hx0]
  have e3 : VG.Proof.ChaCha20.AArch64.Xor.bp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = off (cx s₀) 128 := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.bp, State.withRegions_gpr, hx3]
  have e4 : VG.Proof.ChaCha20.AArch64.Xor.tp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) = Q + BitVec.ofNat 64 o := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.tp, State.withRegions_gpr, hx4]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Xor.stR, VG.Proof.ChaCha20.AArch64.Xor.dR,
      VG.Proof.ChaCha20.AArch64.Xor.tR, VG.Proof.ChaCha20.AArch64.Xor.bR,
      VG.Proof.ChaCha20.AArch64.Xor.dp, State.withRegions_rd, State.withRegions_wr, e0, e1, e2, e3, e4]
  all_goals first
    | rfl
    | exact hst
    | exact hsq
    | exact hsb
    | exact hdb
    | exact hqb
    | exact hal
    | exact hw
    | exact hwq
    | simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The chunks, on the context's regions, from byte `o` of the data to byte `o`
of the destination `Q`. -/
theorem bulkA_ok (enc : Bool) {s₀ : State} (hp : APre e s₀) {Q : Addr} (hq : DstR s₀ Q)
    (hin : enc = true → Q = dp s₀) {o : Nat} (ho : o ≤ L s₀) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 o)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - o))
    (hx3 : s.gpr .x3 = off (cx s₀) 128) (hx4 : s.gpr .x4 = Q + BitVec.ofNat 64 o) (hL : 512 ≤ L s₀ - o)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {R a : Nat} (ha : Acc R a s) :
    WP isa (Stitch.bulk sve enc) s fun u =>
      (∃ T, Bulked enc R a (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) T
        (u.withRegions [dRo s₀ o] (streamR s₀ Q o))) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame (streamR s₀ Q o) s.mem u.mem := by
  have hb := bulk_bpre hp hq ho hx0 hx1 hx2 hx3 hx4
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hLo : L s₀ - o < 2 ^ 64 := by omega
  have hL' : 512 ≤ VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hLo]; exact hL
  have hin' : enc = true → VG.Proof.ChaCha20.AArch64.Xor.tp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) =
      VG.Proof.ChaCha20.AArch64.Xor.dp (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := fun he => by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.tp, VG.Proof.ChaCha20.AArch64.Xor.dp, State.withRegions_gpr,
      hx1, hx4, hin he]
  have ha' : Acc R a (s.withRegions [dRo s₀ o] (streamR s₀ Q o)) := ⟨ha.h, ha.h2, ha.key, ha.k0, ha.k1⟩
  have hw : Covers (streamR s₀ Q o) s.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega⟩
    · exact ⟨⟨Q, L s₀⟩, hq.wr, o, rfl, by show o + (L s₀ - o) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  have hr : Covers [dRo s₀ o] (s.rd ++ s.wr) := by
    rw [hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, hp.d_in, o, rfl, by show o + (L s₀ - o) ≤ L s₀; omega⟩
  refine WP.narrow (bulk_ok enc hb hin' hL' ha') (Covers.append_left hr (Covers.right hw)) hw ?_
    (by cases sve <;> cases enc <;> decide +kernel)
  intro u hrd' hwr' hsp hf hu
  exact ⟨hu, hrd', hwr', hsp, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64
