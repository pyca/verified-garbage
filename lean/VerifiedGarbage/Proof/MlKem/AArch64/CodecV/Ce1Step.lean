module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM on AArch64: an iteration of `ce1Body`

Coefficients `32 k … 32 k + 31` to bytes `4 k … 4 k + 3` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `umov wd, vn.s[0]`. -/
theorem wp_umov_w0 {s : State} {d : Reg} {n : VReg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.v = s.v → s'.gpr d = ((s.v n).extractLsb' 0 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.umov .w d n 0 :: is)) s Q :=
  WP.cons (s' := s.write .w d ((s.v n).extractLsb' 0 32)) (by simp [exec])
    (k _ (only_write _ _ _ _) rfl (by simp [State.write]))

/-- `str wt, [xn, #off]`, which keeps the vector registers. -/
theorem wp_strw' {s : State} {t n : Reg} {off : Nat} {a : Addr} {is : List Instr} {Q : State → Prop}
    (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → s'.v = s.v → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ rfl)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

/-- Byte `g` of the output for `d = 1`: eight coefficients. -/
theorem L1 (s₀ : State) {g : Nat} (hg : g < 32) :
    L width1 s₀ g = BitVec.ofNat 8 (byte8 (C width1 s₀) g) := by
  have := L_eq width1_ok s₀ (g := g) (j := 0) hg (by decide)
  rw [show width1.nb * g + 0 = g from by simp [width1]] at this
  rw [this]
  congr 1
  rw [show width1.c = 8 from rfl, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ,
    acc_succ, acc, List.range_zero, List.map_nil, digits_nil]
  simp only [show width1.d = 1 from rfl, show width1.c = 8 from rfl, Nat.add_zero, byte8]
  omega

theorem step1 {s₀ : State} (hp : Pre width1 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width1 4 (fun _ => True) s₀ k s) :
    WP isa (.block ce1Body) s fun t =>
      VInv width1 4 (fun _ => True) s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce1Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega)) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts 1 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce1Math_ok cs2 (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega)
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega)
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega)
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega)
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega)) fun s3 ⟨c3, hb⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  refine wp_umov_w0 fun s4 o4 v4 x9 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [o4.get .x2, g3, ptr_zero, h.x2]; rfl)
    (by rw [o4.wr, w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width1]; omega) (by decide)))
    fun s5 h5 v5 => ?_
  have k4 : k < 256 / (width1.c * 4) := by simp [width1]; omega
  have gs : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, o4.gpr r (by simpa using hr), g3]
  refine WP.mono (tail_ok (w := width1) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  refine ⟨⟨by rw [o.rd, h5.rd, o4.rd, c3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h5.wr, o4.wr, w3, h.wr],
    by rw [o.sp, h5.sp, o4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, trivial, ?_, ?_⟩,
    by rw [show 256 / (width1.c * 4) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts 1 s3 := cs2.chg c3
    have hv : t.v = s3.v := by rw [v, v5, v4]
    exact ⟨by rw [hv]; exact cs3.m, by rw [hv]; exact cs3.a, by rw [hv]; exact cs3.k⟩
  · rw [o.mem, h5.mem, o4.mem, m3, show width1.nb * 4 * (k + 1) = 4 * k + 4 by simp [width1]; omega]
    have out := h.out
    rw [show width1.nb * 4 * k = 4 * k by simp [width1]] at out
    refine bytes_write (n := 4) out (by decide) (by simp [width1]; omega) fun j hj => ?_
    rw [x9, L1 s₀ (by omega)]
    have e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v0).extractLsb' 0 32).setWidth 64).setWidth 32).setWidth (8 * (32 / 8))) =
        vbyte (s3.v .v0) j := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [vbyte, hi, show 8 * j + i < 32 by omega]
    rw [e]
    apply BitVec.eq_of_toNat_eq
    rw [hb j hj, BitVec.toNat_ofNat]
    simp only [byte8, C_cf width1_ok]
    rw [show 8 * (4 * k + j) = 32 * k + 8 * j by omega]
    simp only [show ∀ e, 32 * k + 8 * j + e = 32 * k + (8 * j + e) from fun e => by omega]
    have b := fun i => cf_lt 1 (X i)
    have := b (8 * j); have := b (8 * j + 1); have := b (8 * j + 2); have := b (8 * j + 3)
    have := b (8 * j + 4); have := b (8 * j + 5); have := b (8 * j + 6); have := b (8 * j + 7)
    exact (Nat.mod_eq_of_lt (by simp only [X] at *; omega)).symm
  · rw [o.mem, h5.mem, o4.mem, m3]
    exact h.frame.write (n := 4) (List.mem_singleton_self _) _
      (contains_off (by simp [width1]; omega) (by decide))

end VG.Proof.MlKem.AArch64.CE
