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

/-- The stream's regions in the context, with the data from byte `o`. -/
abbrev streamR (s₀ : State) (o : Nat) : List Region := [sub s₀ 64 64, dRo s₀ o, sub s₀ 128 320]

theorem bulk_bpre {s₀ : State} (hp : APre e s₀) {o : Nat} (ho : o ≤ L s₀) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 o)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - o)) (hx3 : s.gpr .x3 = off (cx s₀) 128) :
    BPre (s.withRegions [] (streamR s₀ o)) := by
  have hsub := dRo_sub s₀ ho
  have hst : (sub s₀ 64 64).Disjoint (dRo s₀ o) :=
    (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hsub
  have hsb : (sub s₀ 64 64).Disjoint (sub s₀ 128 320) :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hdb : (dRo s₀ o).Disjoint (sub s₀ 128 320) :=
    (hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))).sub_left hsub
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hL : L s₀ - o < 2 ^ 64 := by omega
  have hw : (dp s₀ + BitVec.ofNat 64 o).toNat + (L s₀ - o) ≤ 2 ^ 64 := by
    have hwd : (dp s₀).toNat + L s₀ ≤ 2 ^ 64 := hp.wrap_d
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Xor.stR, VG.Proof.ChaCha20.AArch64.Xor.dR,
      VG.Proof.ChaCha20.AArch64.Xor.bR, VG.Proof.ChaCha20.AArch64.Xor.st,
      VG.Proof.ChaCha20.AArch64.Xor.dp, VG.Proof.ChaCha20.AArch64.Xor.L,
      VG.Proof.ChaCha20.AArch64.Xor.bp, State.withRegions_gpr, State.withRegions_wr, hx0, hx1, hx2,
      hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL] <;>
    first | rfl | exact hst | exact hsb | exact hdb | exact hw |
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The chunks, on the context's regions, from byte `o` of the data. -/
theorem bulkA_ok (enc : Bool) {s₀ : State} (hp : APre e s₀) {o : Nat} (ho : o ≤ L s₀) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 o)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - o))
    (hx3 : s.gpr .x3 = off (cx s₀) 128) (hL : 512 ≤ L s₀ - o) (hwr : s.wr = s₀.wr)
    {R a : Nat} (ha : Acc R a s) :
    WP isa (Stitch.bulk sve enc) s fun u => (∃ T, Bulked enc R a (s.withRegions [] (streamR s₀ o)) T
      (u.withRegions [] (streamR s₀ o))) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame (streamR s₀ o) s.mem u.mem := by
  have hb := bulk_bpre hp ho hx0 hx1 hx2 hx3
  have hL5 : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hLo : L s₀ - o < 2 ^ 64 := by omega
  have hL' : 512 ≤ VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [] (streamR s₀ o)) := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hLo]; exact hL
  have ha' : Acc R a (s.withRegions [] (streamR s₀ o)) := ⟨ha.h, ha.h2, ha.key, ha.k0, ha.k1⟩
  have hw : Covers (streamR s₀ o) s.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 1280; omega⟩
    · exact ⟨dR s₀, hp.d_wr, o, rfl, by show o + (L s₀ - o) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  refine WP.narrow (bulk_ok enc hb hL' ha') (Covers.right hw) hw ?_ (by cases sve <;> cases enc <;> decide +kernel)
  intro u hrd' hwr' hsp hf hu
  exact ⟨hu, hrd', hwr', hsp, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64
