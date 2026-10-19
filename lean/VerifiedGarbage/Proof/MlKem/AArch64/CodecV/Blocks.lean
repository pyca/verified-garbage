module
public import VerifiedGarbage.Proof.MlKem.Compress
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane

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
    rw [h'.v]; exact lanes_coeffs fun e he => h.val _ (by omega))

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
    rw [← ptr_add, h0, show 16 * i = 4 * (4 * i) by omega, coeffAddr_off]
  unfold ld4
  refine wp_ldc h ⟨ho.1, by omega⟩ h0 (by omega) fun s1 h1 l1 => ?_
  refine wp_ldc (h.chg h1.chg) ⟨by omega, by omega⟩ (j := j + 4)
    (by rw [h1.gpr]; exact addr 1) (by omega) fun s2 h2 l2 => ?_
  refine wp_ldc ((h.chg h1.chg).chg h2.chg) ⟨by omega, by omega⟩ (j := j + 8)
    (by rw [h2.gpr, h1.gpr]; exact addr 2) (by omega) fun s3 h3 l3 => ?_
  refine wp_ldc (((h.chg h1.chg).chg h2.chg).chg h3.chg) ⟨by omega, by omega⟩ (j := j + 12)
    (by rw [h3.gpr, h2.gpr, h1.gpr]; exact addr 3) (by omega) fun s4 h4 l4 => wp_nil ?_
  refine ⟨(((h1.chg.trans h2.chg).trans h3.chg).trans h4.chg).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h) | h) | h <;> simp [h]),
    lanes_get h4 had (lanes_get h3 hac (lanes_get h2 hab l1)),
    lanes_get h4 hbd (lanes_get h3 hbc l2), lanes_get h4 hcd l3, l4⟩

/-- `Compress_d` of a coefficient less than `q`, as the code computes it. -/
abbrev cf (d x : Nat) : Nat := (x * compressMul d + compressAdd) / 2 ^ 19 % 2 ^ d

/-- The constants of `cmpV`. -/
structure CConsts (d : Nat) (s : State) : Prop where
  m : Lanes (s.v .v16) fun _ => compressMul d
  a : Lanes (s.v .v17) fun _ => compressAdd
  k : Lanes (s.v .v18) fun _ => 2 ^ d - 1

theorem CConsts.chg {d : Nat} {s t : State} (h : CConsts d s) {rs : List VReg} (c : VChg rs s t)
    (h16 : VReg.v16 ∉ rs := by decide) (h17 : VReg.v17 ∉ rs := by decide)
    (h18 : VReg.v18 ∉ rs := by decide) : CConsts d t :=
  ⟨Lanes.chg c h16 h.m, Lanes.chg c h17 h.a, Lanes.chg c h18 h.k⟩

/-- `Compress_d` of four registers. -/
theorem cmp4_ok {s : State} {d : Nat} (hd : d ∈ compressWidths) (hc : CConsts d s) {a b c e : VReg}
    {X : Nat → Nat} (hX : ∀ i < 16, X i < 3329)
    (la : Lanes (s.v a) fun i => X i) (lb : Lanes (s.v b) fun i => X (4 + i))
    (lc : Lanes (s.v c) fun i => X (8 + i)) (le : Lanes (s.v e) fun i => X (12 + i))
    (hab : a ≠ b := by decide) (hac : a ≠ c := by decide) (hae : a ≠ e := by decide)
    (hbc : b ≠ c := by decide) (hbe : b ≠ e := by decide) (hce : c ≠ e := by decide)
    (ha : a ≠ .v16 ∧ a ≠ .v17 ∧ a ≠ .v18 := by decide) (hb : b ≠ .v16 ∧ b ≠ .v17 ∧ b ≠ .v18 := by decide)
    (hc' : c ≠ .v16 ∧ c ≠ .v17 ∧ c ≠ .v18 := by decide) (he : e ≠ .v16 ∧ e ≠ .v17 ∧ e ≠ .v18 := by decide) :
    WP isa (.block (cmp4 a b c e)) s fun t => VChg [a, b, c, e] s t ∧
      Lanes (t.v a) (fun i => cf d (X i)) ∧ Lanes (t.v b) (fun i => cf d (X (4 + i))) ∧
      Lanes (t.v c) (fun i => cf d (X (8 + i))) ∧ Lanes (t.v e) (fun i => cf d (X (12 + i))) := by
  unfold cmp4
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmpV_ok hd hc.m hc.a hc.k ha.2.1 ha.2.2 la fun i hi => hX i (by omega))
    fun s1 ⟨c1, l1⟩ => ?_
  have k1 : CConsts d s1 := hc.chg c1 (by simpa using ha.1.symm) (by simpa using ha.2.1.symm)
    (by simpa using ha.2.2.symm)
  rw [WP.block_append_iff]
  refine WP.mono (cmpV_ok hd k1.m k1.a k1.k hb.2.1 hb.2.2 (Lanes.chg c1 (by simpa using hab.symm) lb)
    fun i hi => hX _ (by omega)) fun s2 ⟨c2, l2⟩ => ?_
  have k2 : CConsts d s2 := k1.chg c2 (by simpa using hb.1.symm) (by simpa using hb.2.1.symm)
    (by simpa using hb.2.2.symm)
  rw [WP.block_append_iff]
  refine WP.mono (cmpV_ok hd k2.m k2.a k2.k hc'.2.1 hc'.2.2
    (Lanes.chg c2 (by simpa using hbc.symm) (Lanes.chg c1 (by simpa using hac.symm) lc))
    fun i hi => hX _ (by omega)) fun s3 ⟨c3, l3⟩ => ?_
  have k3 : CConsts d s3 := k2.chg c3 (by simpa using hc'.1.symm) (by simpa using hc'.2.1.symm)
    (by simpa using hc'.2.2.symm)
  refine WP.mono (cmpV_ok hd k3.m k3.a k3.k he.2.1 he.2.2
    (Lanes.chg c3 (by simpa using hce.symm) (Lanes.chg c2 (by simpa using hbe.symm)
      (Lanes.chg c1 (by simpa using hae.symm) le)))
    fun i hi => hX _ (by omega)) fun t ⟨c4, l4⟩ => ⟨?_, ?_, ?_, ?_, l4⟩
  · exact (((c1.trans c2).trans c3).trans c4).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with ((h | h) | h) | h <;> simp [h])
  · exact Lanes.chg c4 (by simpa using hae) (Lanes.chg c3 (by simpa using hac)
      (Lanes.chg c2 (by simpa using hab) l1))
  · exact Lanes.chg c4 (by simpa using hbe) (Lanes.chg c3 (by simpa using hbc) l2)
  · exact Lanes.chg c4 (by simpa using hce) l3

end VG.Proof.MlKem.AArch64.CodecV
