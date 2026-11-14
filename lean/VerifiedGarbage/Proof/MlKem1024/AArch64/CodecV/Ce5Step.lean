module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dword
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec

/-! ### `MlKem1024.AArch64.CodecV.Ce5`, which only this module used -/

section

/-!
# ML-KEM-1024 on AArch64: `ce5Math`

32 compressed coefficients of five bits, paired twice into values of 20 bits and those into four
groups of 40 bits in doublewords, whose five low bytes TBL picks, as for `d = 10` (`ce10Math_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem1024.AArch64 VG.Spec.MlKem

/-- Pairs of values `Y` of five bits. -/
abbrev z5 (Y : Nat → Nat) (i : Nat) : Nat := Y (2 * i) + Y (2 * i + 1) * 2 ^ 5
/-- Pairs of pairs: values of 20 bits. -/
abbrev w5 (Y : Nat → Nat) (i : Nat) : Nat := z5 Y (2 * i) + z5 Y (2 * i + 1) * 2 ^ 10
/-- A group of 40 bits: eight values `Y (8 l) …` of five bits. -/
abbrev grp5 (Y : Nat → Nat) (l : Nat) : Nat := w5 Y (2 * l) + w5 Y (2 * l + 1) * 2 ^ 20

theorem ce5Math_ok {s : State} (hc : CConsts width5 s) (h20 : s.v .v20 = idxVec ce10Idx)
    (h21 : s.v .v21 = idxVec ce10IdxHi) {X : Nat → Nat} (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce5Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s t ∧
      (∀ j < 16, (vbyte (t.v .v6) j).toNat = grp5 (fun i => cf width5 (X i)) (j / 5) / 2 ^ (8 * (j % 5)) % 2 ^ 8) ∧
      (∀ j < 4, (vbyte (t.v .v7) j).toNat = grp5 (fun i => cf width5 (X i)) 3 / 2 ^ (8 * (1 + j)) % 2 ^ 8) := by
  have hd : WOk width5 := width5_ok
  unfold ce5Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega_arith)) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega_arith))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega_arith)
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega_arith)
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega_arith))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  let Y : Nat → Nat := fun i => cf width5 (X i)
  have hY : ∀ i, Y i < 2 ^ 5 := fun i => cf_lt width5 _
  -- level 1: pairs of values of five bits
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 5
  have hZ : ∀ i, Z i < 2 ^ 10 := fun i => by have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega_arith)
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5))
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 5) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); congr 1; omega_arith)
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega_arith)
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  have q0 : Lanes (s6.v .v0) fun i => Z i := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    (Lanes.chg c4 (by decide) p0))
  have q1 : Lanes (s6.v .v1) fun i => Z (4 + i) := (Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    p1)).congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 5 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 5
    rw [show 8 + 2 * i = 2 * (4 + i) by omega_arith, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega_arith]
  have q2 : Lanes (s6.v .v2) fun i => Z (8 + i) := (Lanes.chg c6 (by decide) p2).congr fun i _ => by
    show Y (16 + 2 * i) + Y (16 + (2 * i + 1)) * 2 ^ 5 = Y (2 * (8 + i)) + Y (2 * (8 + i) + 1) * 2 ^ 5
    rw [show 16 + 2 * i = 2 * (8 + i) by omega_arith, show 16 + (2 * i + 1) = 2 * (8 + i) + 1 by omega_arith]
  have q3 : Lanes (s6.v .v3) fun i => Z (12 + i) := p3.congr fun i _ => by
    show Y (24 + 2 * i) + Y (24 + (2 * i + 1)) * 2 ^ 5 = Y (2 * (12 + i)) + Y (2 * (12 + i) + 1) * 2 ^ 5
    rw [show 24 + 2 * i = 2 * (12 + i) by omega_arith, show 24 + (2 * i + 1) = 2 * (12 + i) + 1 by omega_arith]
  -- level 2: values of 20 bits
  let W : Nat → Nat := fun i => Z (2 * i) + Z (2 * i + 1) * 2 ^ 10
  have hW : ∀ i, W i < 2 ^ 20 := fun i => by have := hZ (2 * i); have := hZ (2 * i + 1); simp only [W]; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 10) (f := Z) (by decide) (by decide) (by decide) (by decide)
    q0 q1 fun i _ => hZ i) fun s7 ⟨c7, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 10) (f := fun i => Z (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c7 (by decide) q2)
    ((Lanes.chg c7 (by decide) q3).congr fun i _ => by show Z (12 + i) = Z (8 + (4 + i)); congr 1; omega_arith)
    fun i _ => hZ _) fun s8 ⟨c8, r1⟩ => ?_
  have u0 : Lanes (s8.v .v4) fun i => W i := Lanes.chg c8 (by decide) r0
  have u1 : Lanes (s8.v .v5) fun i => W (4 + i) := r1.congr fun i _ => by
    show Z (8 + 2 * i) + Z (8 + (2 * i + 1)) * 2 ^ 10 = Z (2 * (4 + i)) + Z (2 * (4 + i) + 1) * 2 ^ 10
    rw [show 8 + 2 * i = 2 * (4 + i) by omega_arith, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega_arith]
  -- level 3: groups of 40 bits in doublewords
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 20) (by decide) (by decide) u0 fun i _ => hW i) fun s9 ⟨c9, d0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 20) (by decide) (by decide) (Lanes.chg c9 (by decide) u1)
    fun i _ => hW _) fun s10 ⟨c10, d1⟩ => ?_
  have e0 : DLanes (s10.v .v4) fun l => grp5 Y l := fun l hl => by
    rw [c10.get .v4 (by decide), d0 l hl]
  have e1 : DLanes (s10.v .v5) fun l => grp5 Y (2 + l) := fun l hl => by
    rw [d1 l hl]
    show W (4 + 2 * l) + W (4 + (2 * l + 1)) * 2 ^ 20 = W (2 * (2 + l)) + W (2 * (2 + l) + 1) * 2 ^ 20
    rw [show 4 + 2 * l = 2 * (2 + l) by omega_arith, show 4 + (2 * l + 1) = 2 * (2 + l) + 1 by omega_arith]
  have cA : VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s s10 :=
    (((((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans c9).trans
      c10).mono
  have g20 : s10.v .v20 = idxVec ce10Idx := by rw [cA.get .v20, h20]
  have g21 : s10.v .v21 = idxVec ce10IdxHi := by rw [cA.get .v21, h21]
  -- byte `8 l + b` of the table: byte `b` of group `l`
  have tb : ∀ l < 4, ∀ b < 8, (if 8 * l + b < 16 then vbyte (s10.v .v4) (8 * l + b)
      else vbyte (s10.v .v5) (8 * l + b - 16)).toNat = grp5 Y l / 2 ^ (8 * b) % 2 ^ 8 := by
    intro l hl b hb
    by_cases h : l < 2
    · rw [ite_eq_left (by omega_arith), toNat_vbyte_dword _ hb, e0 l h]
    · rw [ite_eq_right (by omega_arith),
        show 8 * l + b - 16 = 8 * (l - 2) + b by omega_arith, toNat_vbyte_dword _ hb, e1 (l - 2) (by omega_arith)]
      dsimp only
      rw [show 2 + (l - 2) = l by omega_arith]
  refine wp_vop (by simp only [VOp.eval]; rfl) fun s11 h11 => wp_vop (by simp only [VOp.eval]; rfl)
    fun t h12 => wp_nil ⟨?_, ?_, ?_⟩
  · exact (cA.trans (h11.chg.trans h12.chg)).mono
  · intro j hj
    rw [h12.get .v6 (by decide), h11.v]
    have hk : (vbyte (s10.v .v20) j).toNat = 8 * (j / 5) + j % 5 := by
      rw [g20, toNat_idxVec _ (by decide) hj, ce10Idx_eq j hj]
    rw [vbyte_tbl2 hj hk (by omega_arith), show VReg.v4.succ = .v5 from rfl]
    exact tb (j / 5) (by omega_arith) (j % 5) (by omega_arith)
  · intro j hj
    rw [h12.v]
    have hk : (vbyte (s11.v .v21) j).toNat = 8 * 3 + (1 + j) := by
      rw [h11.get .v21 (by decide), g21, toNat_idxVec _ (by decide) (by omega_arith), ce10IdxHi_eq j hj]; omega_arith
    rw [vbyte_tbl2 (by omega_arith) hk (by omega_arith), show VReg.v4.succ = .v5 from rfl, h11.get .v4 (by decide),
      h11.get .v5 (by decide)]
    exact tb 3 (by decide) (1 + j) (by omega_arith)

end VG.Proof.MlKem1024.AArch64.CodecV

end

end


/-!
# ML-KEM-1024 on AArch64: an iteration of `ce5Body`

Coefficients `32 k … 32 k + 31` to bytes `20 k … 20 k + 19` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem.AArch64.CE VG.Proof.MlKem1024.AArch64
  VG.Proof.MlKem1024.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Byte `b` of group `g` of the output for `d = 5`. -/
theorem L5 (s₀ : State) {g b : Nat} (hg : g < 32) (hb : b < 5) :
    L width5 s₀ (5 * g + b) = BitVec.ofNat 8 (grp5 (C width5 s₀) g / 2 ^ (8 * b)) := by
  have := L_eq width5_ok s₀ (g := g) (j := b) hg hb
  rw [show width5.nb = 5 from rfl] at this
  rw [this]
  refine congrArg (fun x => BitVec.ofNat 8 (x / 2 ^ (8 * b))) ?_
  rw [show width5.c = 8 from rfl, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ, acc_succ,
    acc_succ, acc, List.range_zero, List.map_nil, digits_nil]
  simp only [show width5.d = 5 from rfl, show width5.c = 8 from rfl, Nat.add_zero, grp5, w5, z5,
    Nat.reduceMul, Nat.reducePow]
  rw [show 2 * (2 * (2 * g) + 1) + 1 = 8 * g + 3 by omega_using [], show 2 * (2 * (2 * g) + 1) = 8 * g + 2 by omega_using [],
    show 2 * (2 * (2 * g + 1)) + 1 = 8 * g + 5 by omega_using [], show 2 * (2 * (2 * g + 1)) = 8 * g + 4 by omega_using [],
    show 2 * (2 * (2 * g + 1) + 1) + 1 = 8 * g + 7 by omega_using [],
    show 2 * (2 * (2 * g + 1) + 1) = 8 * g + 6 by omega_using [], show 2 * (2 * (2 * g)) + 1 = 8 * g + 1 by omega_using [],
    show 2 * (2 * (2 * g)) = 8 * g by omega_using []]
  omega_using []

/-- The groups of coefficients from `32 k` are the groups from `4 k`. -/
theorem grp5_shift (F : Nat → Nat) (k l : Nat) : grp5 (fun i => F (32 * k + i)) l = grp5 F (4 * k + l) := by
  simp only [grp5, w5, z5]
  rw [show 32 * k + 2 * (2 * (2 * l)) = 2 * (2 * (2 * (4 * k + l))) by omega_using [],
    show 32 * k + (2 * (2 * (2 * l)) + 1) = 2 * (2 * (2 * (4 * k + l))) + 1 by omega_using [],
    show 32 * k + 2 * (2 * (2 * l) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) by omega_using [],
    show 32 * k + (2 * (2 * (2 * l) + 1) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) + 1 by omega_using [],
    show 32 * k + 2 * (2 * (2 * l + 1)) = 2 * (2 * (2 * (4 * k + l) + 1)) by omega_using [],
    show 32 * k + (2 * (2 * (2 * l + 1)) + 1) = 2 * (2 * (2 * (4 * k + l) + 1)) + 1 by omega_using [],
    show 32 * k + 2 * (2 * (2 * l + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) by omega_using [],
    show 32 * k + (2 * (2 * (2 * l + 1) + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) + 1 by omega_using []]

theorem step5 {s₀ : State} (hp : Pre width5 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width5 4 K10 s₀ k s) :
    WP isa (.block ce5Body) s fun t =>
      VInv width5 4 K10 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce5Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega_using [hk])) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega_using [hk]))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts width5 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce5Math_ok cs2 (by rw [c2.get .v20, c1.get .v20]; exact h.K.1)
    (by rw [c2.get .v21, c1.get .v21]; exact h.K.2) (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega_using [])
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega_using [])
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega_using [])
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega_using [])
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega_using [])
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega_using [])
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega_using [])) fun s3 ⟨c3, b6, b7⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (20 * k)) (by decide) (by rw [g3, ptr_zero, h.x2]; rfl)
    (by rw [w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega_using [hk]) (by decide)))
    fun s4 h4 => ?_
  refine wp_umov_w0 fun s5 o5 v5 x9 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (20 * k + 16)) (by decide)
    (by rw [o5.get .x2, h4.gpr, g3, h.x2, ptr_add]; rfl)
    (by rw [o5.wr, h4.wr, w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width5]; omega_using [hk]) (by decide)))
    fun s6 h6 v6 => ?_
  have k4 : k < 256 / (width5.c * 4) := by simp [width5]; omega_using [hk]
  have gs : ∀ r, r ≠ .x9 → s6.gpr r = s.gpr r := fun r hr => by
    rw [h6.gpr, o5.gpr r (by simpa using hr), h4.gpr, g3]
  refine WP.mono (tail_ok (w := width5) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  have hv : t.v = s3.v := by rw [v, v6, v5, h4.v]
  refine ⟨⟨by rw [o.rd, h6.rd, o5.rd, h4.rd, c3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h6.wr, o5.wr, h4.wr, w3, h.wr],
    by rw [o.sp, h6.sp, o5.sp, h4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width5.c * 4) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts width5 s3 := cs2.chg c3
    exact ⟨by rw [hv]; exact cs3.m, by rw [hv]; exact cs3.a, by rw [hv]; exact cs3.k⟩
  · exact ⟨by rw [hv, c3.get .v20, c2.get .v20, c1.get .v20]; exact h.K.1,
      by rw [hv, c3.get .v21, c2.get .v21, c1.get .v21]; exact h.K.2⟩
  · have out := h.out
    rw [show width5.nb * 4 * k = 20 * k by simp [width5]] at out
    have hC : C width5 s₀ = fun i => cf width5 ((P s₀)[i]!).val := funext (C_cf width5_ok s₀)
    have sh : ∀ l, grp5 (fun i => cf width5 (X i)) l = grp5 (C width5 s₀) (4 * k + l) := fun l => by
      rw [hC]; exact grp5_shift (fun i => cf width5 ((P s₀)[i]!).val) k l
    have out1 := bytes_write (n := 16) out (by decide) (by simp [width5]; omega_using [hk]) (x := s3.v .v6)
      fun j hj => by
        change vbyte _ j = _
        rw [show 20 * k + j = 5 * (4 * k + j / 5) + j % 5 by omega_using [], L5 s₀ (by omega_using [hk, hj]) (by omega_using [])]
        apply BitVec.eq_of_toNat_eq
        rw [b6 j hj, BitVec.toNat_ofNat, sh]
    rw [o.mem, h6.mem, o5.mem, h4.mem, m3, show width5.nb * 4 * (k + 1) = 20 * k + 16 + 4 by
      simp [width5]; omega_using []]
    refine bytes_write (n := 4) out1 (by decide) (by simp [width5]; omega_using [hk]) fun j hj => ?_
    rw [x9, h4.v]
    have e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v7).extractLsb' 0 32).setWidth 64).setWidth 32).setWidth
        (8 * (32 / 8))) = vbyte (s3.v .v7) j := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [vbyte, hi, show 8 * j + i < 32 by omega_using [hj, hi]]
    rw [e, show 20 * k + 16 + j = 5 * (4 * k + 3) + (1 + j) by omega_using [], L5 s₀ (by omega_using [hk]) (by omega_using [hj])]
    apply BitVec.eq_of_toNat_eq
    rw [b7 j hj, BitVec.toNat_ofNat, sh]
  · rw [o.mem, h6.mem, o5.mem, h4.mem, m3]
    exact (h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width5]; omega_using [hk]) (by decide))).write (n := 32 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width5]; omega_using [hk]) (by decide))

end VG.Proof.MlKem1024.AArch64.CE
