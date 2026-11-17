module

public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Width
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `MlKem.AArch64.CodecV.Narrow`, which this module and modules that import it used -/

section

/-!
# ML-KEM on AArch64: narrowing words to bytes

UZP1 of halfwords keeps the low halfword of each word (`narrow_h`), and UZP1 of bytes the low
byte of each halfword (`narrow_b`): together, the bytes of four registers of words less than
256, in order (`narrow4`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

theorem Lanes.chg {rs : List VReg} {s t : State} (c : VChg rs s t) {r : VReg} (hr : r ∉ rs)
    {f : Nat → Nat} (h : Lanes (s.v r) f) : Lanes (t.v r) f := by rw [c.get r hr]; exact h

theorem toNat_vhalf_word (x : BitVec 128) (j : Nat) : (vhalf x (2 * j)).toNat = (vword x j).toNat % 2 ^ 16 := by
  rw [← Ntt16.vword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem toNat_vbyte_half (x : BitVec 128) (j : Nat) : (vbyte x (2 * j)).toNat = (vhalf x j).toNat % 2 ^ 8 := by
  rw [Cbd16.half_bytes, BitVec.toNat_append, Nat.shiftLeft_eq]
  have := (vbyte x (2 * j)).isLt
  rw [Nat.or_comm, or_shift this]
  omega_using []

/-- The halfwords of UZP1 of words. -/
theorem narrow_h {x y : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (hy : Lanes y fun e => f (4 + e))
    {j : Nat} (hj : j < 8) : (vhalf (VPermOp.eval .uzp1 .h8 x y) j).toNat = f j % 2 ^ 16 := by
  rw [Ntt16.vhalf_perm_h8 _ _ _ hj]
  dsimp only
  split
  · rw [toNat_vhalf_word, hx j (by omega_arith)]
  · rw [show 2 * j - 8 = 2 * (j - 4) by omega_using [], toNat_vhalf_word, hy _ (by omega_using [hj])]
    dsimp only
    rw [show 4 + (j - 4) = j by omega_arith]

/-- The bytes of UZP1 of halfwords. -/
theorem narrow_b {x y : BitVec 128} {g : Nat → Nat} (hx : ∀ j < 8, (vhalf x j).toNat = g j)
    (hy : ∀ j < 8, (vhalf y j).toNat = g (8 + j)) {j : Nat} (hj : j < 16) :
    (vbyte (VPermOp.eval .uzp1 .b16 x y) j).toNat = g j % 2 ^ 8 := by
  rw [Blowfish.AArch64.vbyte_uzp1 _ _ hj]
  split
  · rw [toNat_vbyte_half, hx j (by omega_arith)]
  · rw [show 2 * j - 16 = 2 * (j - 8) by omega_using [], toNat_vbyte_half, hy _ (by omega_using [hj]),
      show 8 + (j - 8) = j by omega_arith]

/-- The bytes of four registers of words less than 256. -/
theorem narrow4 {a b c d : BitVec 128} {f : Nat → Nat} (ha : Lanes a f) (hb : Lanes b fun e => f (4 + e))
    (hc : Lanes c fun e => f (8 + e)) (hd : Lanes d fun e => f (12 + e)) (hf : ∀ j < 16, f j < 256)
    {j : Nat} (hj : j < 16) :
    (vbyte (VPermOp.eval .uzp1 .b16 (VPermOp.eval .uzp1 .h8 a b) (VPermOp.eval .uzp1 .h8 c d)) j).toNat =
      f j := by
  rw [narrow_b (g := fun j => f j % 2 ^ 16) (fun j hj => narrow_h ha (hb.congr fun _ _ => rfl) hj)
    (fun j hj => narrow_h (f := fun e => f (8 + e)) hc
      (hd.congr fun e _ => by rw [← Nat.add_assoc]) hj) hj]
  have := hf j hj
  omega_using [this]

/-- The low halfwords of UZP1 of words, from the first source alone. -/
theorem narrow_h_lo {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (y : BitVec 128) {j : Nat}
    (hj : j < 4) : (vhalf (VPermOp.eval .uzp1 .h8 x y) j).toNat = f j % 2 ^ 16 := by
  rw [Ntt16.vhalf_perm_h8 _ _ _ (by omega_using [hj])]
  dsimp only
  rw [ite_eq_left hj, toNat_vhalf_word, hx j hj]

/-- The low bytes of UZP1 of halfwords, from the first source alone. -/
theorem narrow_b_lo {x : BitVec 128} {g : Nat → Nat} {n : Nat} (hn : n ≤ 8)
    (hx : ∀ j < n, (vhalf x j).toNat = g j) (y : BitVec 128) {j : Nat} (hj : j < n) :
    (vbyte (VPermOp.eval .uzp1 .b16 x y) j).toNat = g j % 2 ^ 8 := by
  rw [Blowfish.AArch64.vbyte_uzp1 _ _ (by omega_using [hn, hj]), ite_eq_left (by omega_using [hn, hj]), toNat_vbyte_half, hx j hj]

/-- The bytes of one register of words less than 256. -/
theorem narrow1 {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (hf : ∀ j < 4, f j < 256) {j : Nat}
    (hj : j < 4) :
    (vbyte (VPermOp.eval .uzp1 .b16 (VPermOp.eval .uzp1 .h8 x x) (VPermOp.eval .uzp1 .h8 x x)) j).toNat =
      f j := by
  rw [narrow_b_lo (n := 4) (g := fun j => f j % 2 ^ 16) (by decide) (fun j hj => narrow_h_lo hx x hj) _ hj]
  have := hf j hj
  omega_using [this]

end VG.Proof.MlKem.AArch64.CodecV

end

end

/-!
# ML-KEM on AArch64: the loads and compressions of the vector codecs

Sixteen coefficients loaded into four registers (`ld4_ok`) and compressed (`cmp4_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- What the coefficients at `p` are, and that they can be read. -/
structure Src (p : Addr) (X : Nat → Nat) (s : State) : Prop where
  rd : ∀ i, i + 4 ≤ 256 → InRegions (s.rd ++ s.wr) (coeffAddr p i) 16
  val : ∀ i < 256, (coeffAt s.mem p i).toNat = X i

theorem Src.chg {p : Addr} {X : Nat → Nat} {s t : State} (h : Src p X s) {rs : List VReg}
    (c : VChg rs s t) : Src p X t :=
  ⟨by rw [c.rd, c.wr]; exact h.rd, by rw [c.mem]; exact h.val⟩

theorem wp_ldc {s : State} {p : Addr} {X : Nat → Nat} (h : Src p X s) {t : VReg} {off j : Nat}
    {is : List Instr} {Q : State → Prop}
    (ho : off % 16 = 0 ∧ off < 4096 * 16) (ha : s.gpr .x0 + BitVec.ofNat 64 off = coeffAddr p j)
    (hj : j + 4 ≤ 256)
    (k : ∀ s', VUpd s s' t (s.mem.read (coeffAddr p j) 16) → Lanes (s'.v t) (fun e => X (j + e)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldrq t .x0 off :: is)) s Q :=
  wp_ldrq ho ha (h.rd j hj) fun s' h' => k s' h' (by
    rw [h'.v]; exact lanes_coeffs fun e he => h.val _ (by omega_using [hj, he]))

/-- Sixteen coefficients, from coefficient `j`. -/
theorem ld4_ok {s : State} {p : Addr} {X : Nat → Nat} (h : Src p X s) (a b c d : VReg) {o j : Nat}
    (ho : o % 16 = 0 ∧ o + 48 < 4096 * 16)
    (h0 : s.gpr .x0 + BitVec.ofNat 64 o = coeffAddr p j) (hj : j + 16 ≤ 256)
    (hab : a ≠ b := by decide) (hac : a ≠ c := by decide) (had : a ≠ d := by decide)
    (hbc : b ≠ c := by decide) (hbd : b ≠ d := by decide) (hcd : c ≠ d := by decide) :
    WP isa (.block (ld4 a b c d o)) s fun t => VChg [a, b, c, d] s t ∧
      Lanes (t.v a) (fun e => X (j + e)) ∧ Lanes (t.v b) (fun e => X (j + 4 + e)) ∧
      Lanes (t.v c) (fun e => X (j + 8 + e)) ∧ Lanes (t.v d) (fun e => X (j + 12 + e)) := by
  have addr (i : Nat) : s.gpr .x0 + BitVec.ofNat 64 (o + 16 * i) = coeffAddr p (j + 4 * i) := by
    rw [← ptr_add, h0, show 16 * i = 4 * (4 * i) by omega_using [], coeffAddr_off]
  unfold ld4
  refine wp_ldc h ⟨ho.1, by omega_using [ho]⟩ h0 (by omega_using [hj]) fun s1 h1 l1 => ?_
  refine wp_ldc (h.chg h1.chg) ⟨by omega_using [ho], by omega_using [ho]⟩ (j := j + 4)
    (by rw [h1.gpr]; exact addr 1) (by omega_using [hj]) fun s2 h2 l2 => ?_
  refine wp_ldc ((h.chg h1.chg).chg h2.chg) ⟨by omega_using [ho], by omega_using [ho]⟩ (j := j + 8)
    (by rw [h2.gpr, h1.gpr]; exact addr 2) (by omega_using [hj]) fun s3 h3 l3 => ?_
  refine wp_ldc (((h.chg h1.chg).chg h2.chg).chg h3.chg) ⟨by omega_using [ho], by omega_using [ho]⟩ (j := j + 12)
    (by rw [h3.gpr, h2.gpr, h1.gpr]; exact addr 3) (by omega_using [hj]) fun s4 h4 l4 => wp_nil ?_
  refine ⟨(((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h) | h) | h <;> simp [h]),
    lanes_get h4 had (lanes_get h3 hac (lanes_get h2 hab l1)),
    lanes_get h4 hbd (lanes_get h3 hbc l2), lanes_get h4 hcd l3, l4⟩

/-- `Compress_d` of a coefficient less than `q`, as the code computes it. -/
abbrev cf (w : Width) (x : Nat) : Nat := (x * w.mul + w.add) / 2 ^ 19 % 2 ^ w.d

/-- The constants of `cmpV`. -/
structure CConsts (w : Width) (s : State) : Prop where
  m : Lanes (s.v .v16) fun _ => w.mul
  a : Lanes (s.v .v17) fun _ => w.add
  k : Lanes (s.v .v18) fun _ => 2 ^ w.d - 1

theorem CConsts.chg {w : Width} {s t : State} (h : CConsts w s) {rs : List VReg} (c : VChg rs s t)
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide)
    (h18 : VReg.v18 ∉ rs := by decide) : CConsts w t :=
  ⟨Lanes.chg c h16 h.m, Lanes.chg c h17 h.a, Lanes.chg c h18 h.k⟩

/-- `Compress_d` of four registers. -/
theorem cmp4_ok {s : State} {w : Width} (hw : WOk w) (hc : CConsts w s) {a b c e : VReg}
    {X : Nat → Nat} (hX : ∀ i < 16, X i < 3329)
    (la : Lanes (s.v a) fun i => X i) (lb : Lanes (s.v b) fun i => X (4 + i))
    (lc : Lanes (s.v c) fun i => X (8 + i)) (le : Lanes (s.v e) fun i => X (12 + i))
    (hab : a ≠ b := by decide) (hac : a ≠ c := by decide) (hae : a ≠ e := by decide)
    (hbc : b ≠ c := by decide) (hbe : b ≠ e := by decide) (hce : c ≠ e := by decide)
    (ha : a ≠ .v16 ∧ a ≠ .v17 ∧ a ≠ .v18 := by decide) (hb : b ≠ .v16 ∧ b ≠ .v17 ∧ b ≠ .v18 := by decide)
    (hc' : c ≠ .v16 ∧ c ≠ .v17 ∧ c ≠ .v18 := by decide) (he : e ≠ .v16 ∧ e ≠ .v17 ∧ e ≠ .v18 := by decide) :
    WP isa (.block (cmp4 a b c e)) s fun t => VChg [a, b, c, e] s t ∧
      Lanes (t.v a) (fun i => cf w (X i)) ∧ Lanes (t.v b) (fun i => cf w (X (4 + i))) ∧
      Lanes (t.v c) (fun i => cf w (X (8 + i))) ∧ Lanes (t.v e) (fun i => cf w (X (12 + i))) := by
  unfold cmp4
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmpV_ok hw.mul_le hw.add_lt hc.m hc.a hc.k ha.2.1 ha.2.2 la fun i hi => hX i (by omega_using [hi]))
    fun s1 ⟨c1, l1⟩ => ?_
  have k1 : CConsts w s1 := hc.chg c1 (by simpa using ha.1.symm) (by simpa using ha.2.1.symm)
    (by simpa using ha.2.2.symm)
  rw [WP.block_append_iff]
  refine WP.mono (cmpV_ok hw.mul_le hw.add_lt k1.m k1.a k1.k hb.2.1 hb.2.2 (Lanes.chg c1 (by simpa using hab.symm) lb)
    fun i hi => hX _ (by omega_using [hi])) fun s2 ⟨c2, l2⟩ => ?_
  have k2 : CConsts w s2 := k1.chg c2 (by simpa using hb.1.symm) (by simpa using hb.2.1.symm)
    (by simpa using hb.2.2.symm)
  rw [WP.block_append_iff]
  refine WP.mono (cmpV_ok hw.mul_le hw.add_lt k2.m k2.a k2.k hc'.2.1 hc'.2.2
    (Lanes.chg c2 (by simpa using hbc.symm) (Lanes.chg c1 (by simpa using hac.symm) lc))
    fun i hi => hX _ (by omega_using [hi])) fun s3 ⟨c3, l3⟩ => ?_
  have k3 : CConsts w s3 := k2.chg c3 (by simpa using hc'.1.symm) (by simpa using hc'.2.1.symm)
    (by simpa using hc'.2.2.symm)
  refine WP.mono (cmpV_ok hw.mul_le hw.add_lt k3.m k3.a k3.k he.2.1 he.2.2
    (Lanes.chg c3 (by simpa using hce.symm) (Lanes.chg c2 (by simpa using hbe.symm)
      (Lanes.chg c1 (by simpa using hae.symm) le)))
    fun i hi => hX _ (by omega_using [hi])) fun t ⟨c4, l4⟩ => ⟨?_, ?_, ?_, ?_, l4⟩
  · exact (((c1.trans c2).trans c3).trans c4).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h) | h) | h <;> simp [h])
  · exact Lanes.chg c4 (by simpa using hae) (Lanes.chg c3 (by simpa using hac)
      (Lanes.chg c2 (by simpa using hab) l1))
  · exact Lanes.chg c4 (by simpa using hbe) (Lanes.chg c3 (by simpa using hbc) l2)
  · exact Lanes.chg c4 (by simpa using hce) l3

end VG.Proof.MlKem.AArch64.CodecV
