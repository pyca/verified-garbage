module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd4
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSpec
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun

/-!
# ML-KEM on AArch64: the loop of the vector decompression

After `k` iterations of a body that decompresses `G` groups of a width `w` (`DInv`): the
output's first `w.c · G · k` coefficients are written. The input's bytes in a vector
(`DInv.vbyte`), the end of a body (`dtail_ok`), and the loop (`dloop_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Proof.MlKem.AArch64.CE (GFr wp_dupW wp_movImm9 movImm_noV)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- After `k` iterations of `G` groups each, with constants `K` besides those of `decV`. -/
structure DInv (w : Width) (Ng : Nat) (K : State → Prop) (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * k)
  x3 : s.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * k)
  x11 : (s.gpr .x11).toNat = 256 / (w.c * Ng) - k
  cs : DConsts w.d s
  K : K s
  out : CoeffsUpTo s.mem (fP s₀) (w.c * Ng * k) (DD.G w s₀) (old s₀)
  frame : Frame [polyRegion (fP s₀)] s₀.mem s.mem

/-- The 16 bytes of the input at byte `o`, loaded. -/
theorem vbyte_input {w : Width} (hw : WOk w) {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [polyRegion (fP s₀)] s₀.mem m) {o : Nat} (ho : o + 16 ≤ 32 * w.d) {j : Nat} (hj : j < 16) :
    (vbyte (m.read (bP s₀ + BitVec.ofNat 64 o) 16) j).toNat = byte w s₀ (o + j) := by
  change ((m.read _ 16).extractLsb' (8 * j) 8).toNat = _
  rw [Mem.extractLsb'_read m _ hj, ptr_add, hp.byte_eq hf (by omega) hw.d_le]

theorem DInv.in16 {w : Width} (hw : WOk w) {Ng : Nat} {K : State → Prop} {s₀ : State} (hp : Pre w s₀) {k : Nat}
    {s : State} (h : DInv w Ng K s₀ k s) {o : Nat} (ho : o + 16 ≤ 32 * w.d) :
    InRegions (s.rd ++ s.wr) (bP s₀ + BitVec.ofNat 64 o) 16 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  have := hw.d_le
  exact in_rd (in_regions (List.mem_singleton_self _) (contains_off ho (by omega)))

theorem DInv.out16 {w : Width} {Ng : Nat} {K : State → Prop} {s₀ : State} (hp : Pre w s₀) {k : Nat}
    {s : State} (h : DInv w Ng K s₀ k s) {i : Nat} (hi : i + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (fP s₀) i) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))

/-- A vector of four output coefficients, from their values. -/
theorem vword_G {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) {g : Nat → BitVec 32}
    (hg : ∀ e < 4, g e = BitVec.ofNat 32 (f e)) : ∀ e < 4, vword x e = g e := fun e he => by
  rw [hg e he]; apply BitVec.eq_of_toNat_eq; rw [hx e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hx.lt he)]

/-- The pointer and count updates at the end of a body. -/
theorem dtail_ok {w : Width} {Ng : Nat} {s₀ : State} {k : Nat} (hk : k < 256 / (w.c * Ng)) {s : State}
    (h0 : s.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * k)) (h3 : s.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * k))
    (h11 : (s.gpr .x11).toNat = 256 / (w.c * Ng) - k) (hi : 4 * (w.c * Ng) < 4096) (hb : w.nb * Ng < 4096) :
    WP isa (.block [.addImm .x .x0 .x0 (w.nb * Ng), .addImm .x .x3 .x3 (4 * (w.c * Ng)),
      .subImm .x .x11 .x11 1]) s fun t => Only [.x0, .x3, .x11] s t ∧ t.v = s.v ∧
      t.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * (k + 1)) ∧
      t.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * (k + 1)) ∧
      (t.gpr .x11).toNat = 256 / (w.c * Ng) - (k + 1) ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 256 / (w.c * Ng)) := by
  refine WP.mono (WP.keepV (by simp [writesV]) (wp_addImm hb fun s4 h4 e4 => wp_addImm hi fun s5 h5 e5 =>
    wp_subImm (by decide) fun s6 h6 e6 => wp_nil (Q := fun t => Only [.x0, .x3, .x11] s t ∧
      t.gpr .x0 = bP s₀ + BitVec.ofNat 64 (w.nb * Ng * (k + 1)) ∧
      t.gpr .x3 = coeffAddr (fP s₀) (w.c * Ng * (k + 1)) ∧
      (t.gpr .x11).toNat = 256 / (w.c * Ng) - (k + 1)) ⟨((h4.trans h5).trans h6).mono, ?_, ?_, ?_⟩))
    fun t ⟨⟨o, a, b, c⟩, v⟩ => ⟨o, v, a, b, c, by rw [c]; omega⟩
  · rw [h6.get .x0, h5.get .x0, e4, h0, ptr_add, Nat.mul_succ]
  · rw [h6.get .x3, e5, h4.get .x3, h3, coeffAddr, coeffAddr, ptr_add]; congr 2; rw [Nat.mul_succ]; omega
  · have c : (s5.gpr .x11).toNat = 256 / (w.c * Ng) - k := by rw [h5.get .x11, h4.get .x11, h11]
    rw [e6, toNat_sub_n (by rw [c]; simp; omega), c]; simp; omega

/-- The loop of one width. -/
theorem dloop_ok {w : Width} (hw : WOk w) {Ng n : Nat} {K : State → Prop} {setup body : List Instr}
    {s₀ : State} (hn : 256 / (w.c * Ng) = n) (hn0 : 0 < n) (hG : w.c * Ng * n = 256)
    (hset : ∀ s, WP isa (.block setup) s fun t => GFr s t ∧
      (∀ r, r ≠ .v18 → r ≠ .v19 → r ≠ .v20 → r ≠ .v21 → r ≠ .v22 → r ≠ .v23 → t.v r = s.v r) ∧ K t)
    (hK : ∀ s t, t.v = s.v → K s → K t)
    (hstep : ∀ k < n, ∀ s, DInv w Ng K s₀ k s →
      WP isa (.block body) s fun t => DInv w Ng K s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ n)) :
    WP isa (ddLoop w.d n setup body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      PolyIs s'.mem (fP s₀) (decodeDecompress w.d (B w s₀)) := by
  refine WP.seq ?_
  simp only [List.append_assoc]
  have hd := hw.d_le
  have hd' := hw.d_pos
  refine wp_dupW (c := 3329) (by decide) fun s1 g1 v1 l16 =>
    wp_dupW (c := 2 ^ (w.d - 1)) (Nat.pow_lt_pow_right (by decide) (by omega)) fun s2 g2 v2 l17 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hset s2) fun s4 ⟨g4, v4, k4⟩ => ?_
  rw [← List.append_nil (movImm .x11 _)]
  refine wp_scalar (movImm_noV _ _) (wp_movImm (is := []) fun t h e =>
    wp_nil (Q := fun t => Only [.x11] s4 t ∧ t.gpr .x11 = BitVec.ofNat 64 n) ⟨h, e⟩) fun s5 ⟨h5, e5⟩ v5 => wp_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x11 → s5.gpr r = s₀.gpr r := fun r h9 h11 => by
    rw [h5.gpr r (by simpa using h11), g4.gpr r h9, g2.gpr r h9, g1.gpr r h9]
  have m5 : s5.mem = s₀.mem := by rw [h5.mem, g4.mem, g2.mem, g1.mem]
  have h0 : DInv w Ng K s₀ 0 s5 := by
    refine ⟨by rw [h5.rd, g4.rd, g2.rd, g1.rd], by rw [h5.wr, g4.wr, g2.wr, g1.wr],
      by rw [h5.sp, g4.sp, g2.sp, g1.sp], ?_, ?_, ?_, ⟨?_, ?_⟩, hK _ _ v5 k4, ?_, ?_⟩
    · rw [g .x0 (by decide) (by decide), Nat.mul_zero, ptr_zero]
    · rw [g .x3 (by decide) (by decide), Nat.mul_zero]; exact (ptr_zero _).symm
    · rw [e5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.div_le_self 256 (w.c * Ng); omega), hn,
        Nat.sub_zero]
    · rw [v5, v4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v2 _ (by decide)]; exact l16
    · rw [v5, v4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact l17
    · rw [m5, Nat.mul_zero]; exact CoeffsUpTo.zero _
    · rw [m5]; exact Frame.refl _ _
  refine WP.mono (count_loop hn0 (DInv w Ng K s₀) hstep h0) fun s' h => ⟨h.rd, h.wr, h.sp, ?_⟩
  exact (show CoeffsUpTo _ _ 256 _ _ from hG ▸ h.out).polyIs fun _ _ => rfl

end VG.Proof.MlKem.AArch64.DD
