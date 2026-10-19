module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce11
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Ce5Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step

/-!
# ML-KEM-1024 on AArch64: an iteration of `ce11Body`

Coefficients `32 k … 32 k + 31` to bytes `44 k … 44 k + 43` of the output: two registers of
16 bytes, then the doubleword and the third word of the third register.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.CE VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `umov`: lane `i` of `n` into `d`. -/
theorem wp_umov' {s : State} {sz : Size} {d : Reg} {n : VReg} {i : Nat} (hi : i * sz.bits < 128)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.v = s.v →
      s'.gpr d = ((s.v n).extractLsb' (sz.bits * i) sz.bits).setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.umov sz d n i :: is)) s Q :=
  WP.cons (s' := s.write sz d ((s.v n).extractLsb' (sz.bits * i) sz.bits)) (by simp [exec, hi])
    (k _ (only_write _ _ _ _) rfl (by simp [State.write]))

/-- `str xt, [xn, #off]`, which keeps the vector registers. -/
theorem wp_strx' {s : State} {t n : Reg} {off : Nat} {a : Addr} {is : List Instr} {Q : State → Prop}
    (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 64)) → s'.v = s.v → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 64) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ rfl)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

/-- The constants of `ce11Body` besides those of `cmpV`. -/
abbrev K11 (s : State) : Prop :=
  s.v .v20 = idxVec ce11Idx0 ∧ s.v .v21 = idxVec ce11Idx1 ∧ s.v .v22 = idxVec ce11Idx2

/-- Byte `b` of group `g` of the output for `d = 11`. -/
theorem L11 (s₀ : State) {g b : Nat} (hg : g < 32) (hb : b < 11) :
    L width11 s₀ (11 * g + b) = BitVec.ofNat 8 (grp11 (C width11 s₀) g / 2 ^ (8 * b)) := by
  have := L_eq width11_ok s₀ (g := g) (j := b) hg hb
  rw [show width11.nb = 11 from rfl] at this
  rw [this]
  refine congrArg (fun x => BitVec.ofNat 8 (x / 2 ^ (8 * b))) ?_
  rw [show width11.c = 8 from rfl, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ,
    acc_succ, acc, List.range_zero, List.map_nil, digits_nil]
  simp only [show width11.d = 11 from rfl, show width11.c = 8 from rfl, Nat.add_zero, grp11, w11, z11,
    Nat.reduceMul, Nat.reducePow]
  rw [show 2 * (2 * (2 * g) + 1) + 1 = 8 * g + 3 by omega, show 2 * (2 * (2 * g) + 1) = 8 * g + 2 by omega,
    show 2 * (2 * (2 * g + 1)) + 1 = 8 * g + 5 by omega, show 2 * (2 * (2 * g + 1)) = 8 * g + 4 by omega,
    show 2 * (2 * (2 * g + 1) + 1) + 1 = 8 * g + 7 by omega,
    show 2 * (2 * (2 * g + 1) + 1) = 8 * g + 6 by omega, show 2 * (2 * (2 * g)) + 1 = 8 * g + 1 by omega,
    show 2 * (2 * (2 * g)) = 8 * g by omega]
  omega

/-- The groups of coefficients from `32 k` are the groups from `4 k`. -/
theorem grp11_shift (F : Nat → Nat) (k l : Nat) : grp11 (fun i => F (32 * k + i)) l = grp11 F (4 * k + l) := by
  simp only [grp11, w11, z11]
  rw [show 32 * k + 2 * (2 * (2 * l)) = 2 * (2 * (2 * (4 * k + l))) by omega,
    show 32 * k + (2 * (2 * (2 * l)) + 1) = 2 * (2 * (2 * (4 * k + l))) + 1 by omega,
    show 32 * k + 2 * (2 * (2 * l) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) by omega,
    show 32 * k + (2 * (2 * (2 * l) + 1) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) + 1 by omega,
    show 32 * k + 2 * (2 * (2 * l + 1)) = 2 * (2 * (2 * (4 * k + l) + 1)) by omega,
    show 32 * k + (2 * (2 * (2 * l + 1)) + 1) = 2 * (2 * (2 * (4 * k + l) + 1)) + 1 by omega,
    show 32 * k + 2 * (2 * (2 * l + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) by omega,
    show 32 * k + (2 * (2 * (2 * l + 1) + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) + 1 by omega]

theorem step11 {s₀ : State} (hp : Pre width11 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width11 4 K11 s₀ k s) :
    WP isa (.block ce11Body) s fun t =>
      VInv width11 4 K11 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce11Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega)) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts width11 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce11Math_ok cs2 (by rw [c2.get .v20, c1.get .v20]; exact h.K.1)
    (by rw [c2.get .v21, c1.get .v21]; exact h.K.2.1) (by rw [c2.get .v22, c1.get .v22]; exact h.K.2.2)
    (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega)
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega)
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega)
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega)
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega)
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega)) fun s3 ⟨c3, b4, b5, b6⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  have inO : ∀ o n, o + n ≤ 44 → InRegions s.wr (oP s₀ + BitVec.ofNat 64 (44 * k + o)) n := fun o n hon => by
    rw [h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width11]; omega) (by decide))
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (44 * k)) (by decide) (by rw [g3, ptr_zero, h.x2]; rfl)
    (by rw [w3]; exact inO 0 16 (by decide)) fun s4 h4 => ?_
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (44 * k + 16)) (by decide)
    (by rw [h4.gpr, g3, h.x2, ptr_add]; rfl) (by rw [h4.wr, w3]; exact inO 16 16 (by decide)) fun s5 h5 => ?_
  refine wp_umov' (sz := .x) (i := 0) (by decide) fun s6 o6 v6 x6 => ?_
  refine wp_strx' (a := oP s₀ + BitVec.ofNat 64 (44 * k + 32)) (by decide)
    (by rw [o6.get .x2, h5.gpr, h4.gpr, g3, h.x2, ptr_add]; rfl)
    (by rw [o6.wr, h5.wr, h4.wr, w3]; exact inO 32 8 (by decide)) fun s7 h7 v7 => ?_
  refine wp_umov' (sz := .w) (i := 2) (by decide) fun s8 o8 v8 x8 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (44 * k + 40)) (by decide)
    (by rw [o8.get .x2, h7.gpr, o6.get .x2, h5.gpr, h4.gpr, g3, h.x2, ptr_add]; rfl)
    (by rw [o8.wr, h7.wr, o6.wr, h5.wr, h4.wr, w3]; exact inO 40 4 (by decide)) fun s9 h9 v9 => ?_
  have k4 : k < 256 / (width11.c * 4) := by simp [width11]; omega
  have gs : ∀ r, r ≠ .x9 → s9.gpr r = s.gpr r := fun r hr => by
    rw [h9.gpr, o8.gpr r (by simpa using hr), h7.gpr, o6.gpr r (by simpa using hr), h5.gpr, h4.gpr, g3]
  refine WP.mono (tail_ok (w := width11) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  have hv : t.v = s3.v := by rw [v, v9, v8, v7, v6, h5.v, h4.v]
  refine ⟨⟨by rw [o.rd, h9.rd, o8.rd, h7.rd, o6.rd, h5.rd, h4.rd, c3.rd, c2.rd, c1.rd, h.rd],
    by rw [o.wr, h9.wr, o8.wr, h7.wr, o6.wr, h5.wr, h4.wr, w3, h.wr],
    by rw [o.sp, h9.sp, o8.sp, h7.sp, o6.sp, h5.sp, h4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width11.c * 4) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts width11 s3 := cs2.chg c3
    exact ⟨by rw [hv]; exact cs3.m, by rw [hv]; exact cs3.a, by rw [hv]; exact cs3.k⟩
  · exact ⟨by rw [hv, c3.get .v20, c2.get .v20, c1.get .v20]; exact h.K.1,
      by rw [hv, c3.get .v21, c2.get .v21, c1.get .v21]; exact h.K.2.1,
      by rw [hv, c3.get .v22, c2.get .v22, c1.get .v22]; exact h.K.2.2⟩
  · have out := h.out
    rw [show width11.nb * 4 * k = 44 * k by simp [width11]] at out
    have hC : C width11 s₀ = fun i => cf width11 ((P s₀)[i]!).val := funext (C_cf width11_ok s₀)
    have sh : ∀ l, grp11 (fun i => cf width11 (X i)) l = grp11 (C width11 s₀) (4 * k + l) := fun l => by
      rw [hC]; exact grp11_shift (fun i => cf width11 ((P s₀)[i]!).val) k l
    -- byte `m` of this iteration's output
    have byte : ∀ m < 44, ∀ x : BitVec 8,
        x.toNat = grp11 (fun i => cf width11 (X i)) (m / 11) / 2 ^ (8 * (m % 11)) % 2 ^ 8 →
        x = L width11 s₀ (44 * k + m) := fun m hm x hx => by
      rw [show 44 * k + m = 11 * (4 * k + m / 11) + m % 11 by omega, L11 s₀ (by omega) (by omega)]
      apply BitVec.eq_of_toNat_eq
      rw [hx, BitVec.toNat_ofNat, sh]
    rw [o.mem, h9.mem, o8.mem, h7.mem, o6.mem, h5.mem, h4.mem, m3, x8, v7, v6, x6, h5.v, h4.v,
      show width11.nb * 4 * (k + 1) = 44 * k + 16 + 16 + 64 / 8 + 32 / 8 by simp [width11]; omega,
      show 44 * k + 32 = 44 * k + 16 + 16 by omega, show 44 * k + 40 = 44 * k + 16 + 16 + 64 / 8 by omega]
    simp only [Mem.writeW]
    refine bytes_write (n := 32 / 8) (bytes_write (n := 64 / 8) (bytes_write (n := 16)
      (bytes_write (n := 16) out (by decide) (by simp [width11]; omega) fun j hj => byte j (by omega) _ (b4 j hj))
      (by decide) (by simp [width11]; omega) fun j hj => by
        rw [show 44 * k + 16 + j = 44 * k + (16 + j) by omega]; exact byte _ (by omega) _ (b5 j hj))
      (by decide) (by simp [width11]; omega) fun j hj => ?_) (by decide) (by simp [width11]; omega) fun j hj => ?_
    · rw [show 44 * k + 16 + 16 + j = 44 * k + (32 + j) by omega]
      refine byte _ (by omega) _ ?_
      have e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v6).extractLsb' (Size.x.bits * 0) Size.x.bits).setWidth 64).setWidth 64).setWidth
          (8 * (64 / 8))) = vbyte (s3.v .v6) j := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp [vbyte, hi, Size.bits, show 8 * j + i < 64 by omega]
      rw [e]
      exact b6 j (by omega)
    · rw [show 44 * k + 16 + 16 + 64 / 8 + j = 44 * k + (32 + (8 + j)) by omega]
      refine byte _ (by omega) _ ?_
      have e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v6).extractLsb' (Size.w.bits * 2) Size.w.bits).setWidth 64).setWidth 32).setWidth
          (8 * (32 / 8))) = vbyte (s3.v .v6) (8 + j) := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp [vbyte, hi, Size.bits, show 8 * j + i < 32 by omega, show 32 * 2 + (8 * j + i) = 8 * (8 + j) + i by omega]
      rw [e]
      exact b6 (8 + j) (by omega)
  · rw [o.mem, h9.mem, o8.mem, h7.mem, o6.mem, h5.mem, h4.mem, m3]
    exact (((h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega) (by decide))).write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega) (by decide))).write (n := 64 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega) (by decide))).write (n := 32 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega) (by decide))

end VG.Proof.MlKem1024.AArch64.CE
