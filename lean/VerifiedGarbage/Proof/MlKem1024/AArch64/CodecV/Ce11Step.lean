module

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Dword88
import VerifiedGarbage.Proof.MlKem1024.AArch64.CodecV.Widths
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop

/-! ### `MlKem1024.AArch64.CodecV.Ce11`, which only this module used -/

section

/-!
# ML-KEM-1024 on AArch64: `ce11Math`

32 compressed coefficients of 11 bits, paired into values of 22 bits, those into doublewords of 44
bits, and the two of each register into a group of 88 bits in its 11 low bytes (`merge88_ok`),
whose bytes TBL picks from the four registers.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
  VG.Proof.MlKem.AArch64.CodecV VG.Proof.MlKem1024.AArch64 VG.Spec.MlKem

/-- Pairs of values `Y` of 11 bits. -/
abbrev z11 (Y : Nat → Nat) (i : Nat) : Nat := Y (2 * i) + Y (2 * i + 1) * 2 ^ 11
/-- Pairs of pairs: values of 44 bits. -/
abbrev w11 (Y : Nat → Nat) (i : Nat) : Nat := z11 Y (2 * i) + z11 Y (2 * i + 1) * 2 ^ 22
/-- A group of 88 bits: eight values `Y (8 r) …` of 11 bits. -/
abbrev grp11 (Y : Nat → Nat) (r : Nat) : Nat := w11 Y (2 * r) + w11 Y (2 * r + 1) * 2 ^ 44

/-- The index of byte `m` of the output: byte `m mod 11` of register `m / 11`. -/
abbrev idx11 (m : Nat) : Nat := 16 * (m / 11) + m % 11

theorem ce11Idx0_eq : ∀ j < 16, ce11Idx0.getD j 255 = idx11 j := by decide
theorem ce11Idx1_eq : ∀ j < 16, ce11Idx1.getD j 255 = idx11 (16 + j) := by decide
theorem ce11Idx2_eq : ∀ j < 12, ce11Idx2.getD j 255 = idx11 (32 + j) := by decide

theorem ce11Math_ok {s : State} (hc : CConsts width11 s) (h20 : s.v .v20 = idxVec ce11Idx0)
    (h21 : s.v .v21 = idxVec ce11Idx1) (h22 : s.v .v22 = idxVec ce11Idx2) {X : Nat → Nat}
    (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce11Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19, .v23] s t ∧
      (∀ j < 16, (vbyte (t.v .v4) j).toNat =
        grp11 (fun i => cf width11 (X i)) (j / 11) / 2 ^ (8 * (j % 11)) % 2 ^ 8) ∧
      (∀ j < 16, (vbyte (t.v .v5) j).toNat =
        grp11 (fun i => cf width11 (X i)) ((16 + j) / 11) / 2 ^ (8 * ((16 + j) % 11)) % 2 ^ 8) ∧
      (∀ j < 12, (vbyte (t.v .v6) j).toNat =
        grp11 (fun i => cf width11 (X i)) ((32 + j) / 11) / 2 ^ (8 * ((32 + j) % 11)) % 2 ^ 8) := by
  have hd : WOk width11 := width11_ok
  unfold ce11Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega_arith)) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega_arith))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega_arith)
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega_arith)
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega_arith))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  let Y : Nat → Nat := fun i => cf width11 (X i)
  obtain hY : ∀ i, Y i < 2 ^ 11 := fun i => cf_lt width11 _
  -- level 1: pairs of values of 11 bits
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 11
  obtain hZ : ∀ i, Z i < 2 ^ 22 := fun i => by have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega_arith)
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5))
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 11) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); congr 1; omega_arith)
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega_arith)
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  obtain q0 : Lanes (s6.v .v0) fun i => Z i := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    (Lanes.chg c4 (by decide) p0))
  obtain q1 : Lanes (s6.v .v1) fun i => Z (4 + i) := (Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    p1)).congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 11 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 11
    rw [show 8 + 2 * i = 2 * (4 + i) by omega_arith, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega_arith]
  obtain q2 : Lanes (s6.v .v2) fun i => Z (8 + i) := (Lanes.chg c6 (by decide) p2).congr fun i _ => by
    show Y (16 + 2 * i) + Y (16 + (2 * i + 1)) * 2 ^ 11 = Y (2 * (8 + i)) + Y (2 * (8 + i) + 1) * 2 ^ 11
    rw [show 16 + 2 * i = 2 * (8 + i) by omega_arith, show 16 + (2 * i + 1) = 2 * (8 + i) + 1 by omega_arith]
  obtain q3 : Lanes (s6.v .v3) fun i => Z (12 + i) := p3.congr fun i _ => by
    show Y (24 + 2 * i) + Y (24 + (2 * i + 1)) * 2 ^ 11 = Y (2 * (12 + i)) + Y (2 * (12 + i) + 1) * 2 ^ 11
    rw [show 24 + 2 * i = 2 * (12 + i) by omega_arith, show 24 + (2 * i + 1) = 2 * (12 + i) + 1 by omega_arith]
  -- level 2: doublewords of 44 bits
  let W : Nat → Nat := fun l => Z (2 * l) + Z (2 * l + 1) * 2 ^ 22
  obtain hW : ∀ l, W l < 2 ^ 44 := fun l => by have := hZ (2 * l); have := hZ (2 * l + 1); simp only [W]; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide) q0 fun i _ => hZ i) fun s7 ⟨c7, d0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide) (Lanes.chg c7 (by decide) q1)
    fun i _ => hZ _) fun s8 ⟨c8, d1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide) (Lanes.chg c8 (by decide) (Lanes.chg c7 (by decide) q2))
    fun i _ => hZ _) fun s9 ⟨c9, d2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dpairV_ok (b := 22) (by decide) (by decide)
    (Lanes.chg c9 (by decide) (Lanes.chg c8 (by decide) (Lanes.chg c7 (by decide) q3)))
    fun i _ => hZ _) fun s10 ⟨c10, d3⟩ => ?_
  obtain e0 : DLanes (s10.v .v0) fun l => W (2 * 0 + l) := fun l hl => by
    rw [c10.get .v0 (by decide), c9.get .v0 (by decide), c8.get .v0 (by decide), d0 l hl]
    simp only [W]; rw [show 2 * (2 * 0 + l) = 2 * l by omega_arith]
  obtain e1 : DLanes (s10.v .v1) fun l => W (2 * 1 + l) := fun l hl => by
    rw [c10.get .v1 (by decide), c9.get .v1 (by decide), d1 l hl]
    simp only [W]; rw [show 2 * (2 * 1 + l) = 4 + 2 * l by omega_arith, show 4 + 2 * l + 1 = 4 + (2 * l + 1) by omega_arith]
  obtain e2 : DLanes (s10.v .v2) fun l => W (2 * 2 + l) := fun l hl => by
    rw [c10.get .v2 (by decide), d2 l hl]
    simp only [W]; rw [show 2 * (2 * 2 + l) = 8 + 2 * l by omega_arith, show 8 + 2 * l + 1 = 8 + (2 * l + 1) by omega_arith]
  obtain e3 : DLanes (s10.v .v3) fun l => W (2 * 3 + l) := fun l hl => by
    rw [d3 l hl]
    simp only [W]; rw [show 2 * (2 * 3 + l) = 12 + 2 * l by omega_arith, show 12 + 2 * l + 1 = 12 + (2 * l + 1) by omega_arith]
  -- level 3: groups of 88 bits
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 0 + l)) (by decide) (by decide) e0 (hW _)) fun s11 ⟨c11, b0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 1 + l)) (by decide) (by decide)
    (fun l hl => by rw [c11.get .v1 (by decide)]; exact e1 l hl)
    (hW _)) fun s12 ⟨c12, b1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 2 + l)) (by decide) (by decide)
    (fun l hl => by rw [c12.get .v2 (by decide), c11.get .v2 (by decide)]; exact e2 l hl) (hW _))
    fun s13 ⟨c13, b2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (merge88_ok (g := fun l => W (2 * 3 + l)) (by decide) (by decide)
    (fun l hl => by rw [c13.get .v3 (by decide), c12.get .v3 (by decide), c11.get .v3 (by decide)]; exact e3 l hl)
    (hW _)) fun s14 ⟨c14, b3⟩ => ?_
  -- the bytes of the four registers: byte `b` of register `r`, of group `r`
  obtain hg : ∀ r < 4, ∀ b < 11, (vbyte (s14.v (Nat.repeat VReg.succ r .v0)) b).toNat =
      grp11 Y r / 2 ^ (8 * b) % 2 ^ 8 := by
    intro r hr b hb
    obtain gr : ∀ r, grp11 Y r = W (2 * r + 0) + W (2 * r + 1) * 2 ^ 44 := fun r => rfl
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [show Nat.repeat VReg.succ 0 .v0 = .v0 from rfl, c14.get .v0 (by decide), c13.get .v0 (by decide),
        c12.get .v0 (by decide), b0 b hb, gr]
    · rw [show Nat.repeat VReg.succ 1 .v0 = .v1 from rfl, c14.get .v1 (by decide), c13.get .v1 (by decide),
        b1 b hb, gr]
    · rw [show Nat.repeat VReg.succ 2 .v0 = .v2 from rfl, c14.get .v2 (by decide), b2 b hb, gr]
    · rw [show Nat.repeat VReg.succ 3 .v0 = .v3 from rfl, b3 b hb, gr]
  obtain cA : VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19, .v23] s s14 :=
    (((((((((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans c9).trans
      c10).trans c11).trans c12).trans c13).trans c14).mono
  obtain tb : ∀ m < 44, (tableByte s14.v .v0 (idx11 m)).toNat = grp11 Y (m / 11) / 2 ^ (8 * (m % 11)) % 2 ^ 8 :=
    fun m hm => by
      unfold tableByte
      rw [show idx11 m / 16 = m / 11 by unfold idx11; omega_arith, show idx11 m % 16 = m % 11 by unfold idx11; omega_arith]
      exact hg (m / 11) (by omega_arith) (m % 11) (by omega_arith)
  obtain tf : ∀ (u u' : State) (d : VReg), (∀ r, r ≠ d → u'.v r = u.v r) → (d = .v4 ∨ d = .v5) →
      ∀ m < 44, tableByte u'.v .v0 (idx11 m) = tableByte u.v .v0 (idx11 m) := by
    intro u u' d hu hd m hm
    unfold tableByte
    rw [show idx11 m / 16 = m / 11 by unfold idx11; omega_arith]
    apply congrArg (fun x => vbyte x _)
    apply hu
    rcases (show m / 11 = 0 ∨ m / 11 = 1 ∨ m / 11 = 2 ∨ m / 11 = 3 by omega_arith) with h | h | h | h <;>
      rw [h] <;> rcases hd with rfl | rfl <;> decide
  refine wp_vop (by simp only [VOp.eval]; rfl) fun s15 h15 => wp_vop (by simp only [VOp.eval]; rfl)
    fun s16 h16 => wp_vop (by simp only [VOp.eval]; rfl) fun t h17 => wp_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (cA.trans ((h15.chg.trans h16.chg).trans h17.chg)).mono
  · intro j hj
    rw [h17.get .v4 (by decide), h16.get .v4 (by decide), h15.v]
    obtain hk : (vbyte (s14.v .v20) j).toNat = idx11 j := by
      rw [cA.get .v20, h20, toNat_idxVec _ (by decide) hj, ce11Idx0_eq j hj]
    rw [vbyte_tblN hj hk (by unfold idx11; omega_arith)]
    exact tb j (by omega_arith)
  · intro j hj
    rw [h17.get .v5 (by decide), h16.v]
    obtain hk : (vbyte (s15.v .v21) j).toNat = idx11 (16 + j) := by
      rw [h15.get .v21 (by decide), cA.get .v21, h21, toNat_idxVec _ (by decide) hj, ce11Idx1_eq j hj]
    rw [vbyte_tblN hj hk (by unfold idx11; omega_arith), tf s14 s15 .v4 h15.other (.inl rfl) (16 + j) (by omega_arith)]
    exact tb (16 + j) (by omega_arith)
  · intro j hj
    rw [h17.v]
    obtain hk : (vbyte (s16.v .v22) j).toNat = idx11 (32 + j) := by
      rw [h16.get .v22 (by decide), h15.get .v22 (by decide), cA.get .v22, h22,
        toNat_idxVec _ (by decide) (by omega_arith), ce11Idx2_eq j hj]
    rw [vbyte_tblN (by omega_arith) hk (by unfold idx11; omega_arith), tf s15 s16 .v5 h16.other (.inr rfl) (32 + j) (by omega_arith),
      tf s14 s15 .v4 h15.other (.inl rfl) (32 + j) (by omega_arith)]
    exact tb (32 + j) (by omega_arith)

end VG.Proof.MlKem1024.AArch64.CodecV

end

end


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
  rw [show 2 * (2 * (2 * g) + 1) + 1 = 8 * g + 3 by omega_arith, show 2 * (2 * (2 * g) + 1) = 8 * g + 2 by omega_arith,
    show 2 * (2 * (2 * g + 1)) + 1 = 8 * g + 5 by omega_arith, show 2 * (2 * (2 * g + 1)) = 8 * g + 4 by omega_arith,
    show 2 * (2 * (2 * g + 1) + 1) + 1 = 8 * g + 7 by omega_arith,
    show 2 * (2 * (2 * g + 1) + 1) = 8 * g + 6 by omega_arith, show 2 * (2 * (2 * g)) + 1 = 8 * g + 1 by omega_arith,
    show 2 * (2 * (2 * g)) = 8 * g by omega_arith]
  omega_arith

/-- The groups of coefficients from `32 k` are the groups from `4 k`. -/
theorem grp11_shift (F : Nat → Nat) (k l : Nat) : grp11 (fun i => F (32 * k + i)) l = grp11 F (4 * k + l) := by
  simp only [grp11, w11, z11]
  rw [show 32 * k + 2 * (2 * (2 * l)) = 2 * (2 * (2 * (4 * k + l))) by omega_arith,
    show 32 * k + (2 * (2 * (2 * l)) + 1) = 2 * (2 * (2 * (4 * k + l))) + 1 by omega_arith,
    show 32 * k + 2 * (2 * (2 * l) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) by omega_arith,
    show 32 * k + (2 * (2 * (2 * l) + 1) + 1) = 2 * (2 * (2 * (4 * k + l)) + 1) + 1 by omega_arith,
    show 32 * k + 2 * (2 * (2 * l + 1)) = 2 * (2 * (2 * (4 * k + l) + 1)) by omega_arith,
    show 32 * k + (2 * (2 * (2 * l + 1)) + 1) = 2 * (2 * (2 * (4 * k + l) + 1)) + 1 by omega_arith,
    show 32 * k + 2 * (2 * (2 * l + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) by omega_arith,
    show 32 * k + (2 * (2 * (2 * l + 1) + 1) + 1) = 2 * (2 * (2 * (4 * k + l) + 1) + 1) + 1 by omega_arith]

theorem step11 {s₀ : State} (hp : Pre width11 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width11 4 K11 s₀ k s) :
    WP isa (.block ce11Body) s fun t =>
      VInv width11 4 K11 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  obtain src := h.src hp
  obtain e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce11Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega_arith)) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega_arith))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  obtain cs2 : CConsts width11 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce11Math_ok cs2 (by rw [c2.get .v20, c1.get .v20]; exact h.K.1)
    (by rw [c2.get .v21, c1.get .v21]; exact h.K.2.1) (by rw [c2.get .v22, c1.get .v22]; exact h.K.2.2)
    (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega_arith)
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega_arith)
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega_arith)
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega_arith)
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega_arith)
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega_arith)
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega_arith)) fun s3 ⟨c3, b4, b5, b6⟩ => ?_
  obtain g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  obtain m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  obtain w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  obtain inO : ∀ o n, o + n ≤ 44 → InRegions s.wr (oP s₀ + BitVec.ofNat 64 (44 * k + o)) n := fun o n hon => by
    rw [h.wr, hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width11]; omega_arith) (by decide))
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
  obtain k4 : k < 256 / (width11.c * 4) := by simp [width11]; omega_arith
  obtain gs : ∀ r, r ≠ .x9 → s9.gpr r = s.gpr r := fun r hr => by
    rw [h9.gpr, o8.gpr r (by simpa using hr), h7.gpr, o6.gpr r (by simpa using hr), h5.gpr, h4.gpr, g3]
  refine WP.mono (tail_ok (w := width11) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  obtain hv : t.v = s3.v := by rw [v, v9, v8, v7, v6, h5.v, h4.v]
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
    obtain hC : C width11 s₀ = fun i => cf width11 ((P s₀)[i]!).val := funext (C_cf width11_ok s₀)
    obtain sh : ∀ l, grp11 (fun i => cf width11 (X i)) l = grp11 (C width11 s₀) (4 * k + l) := fun l => by
      rw [hC]; exact grp11_shift (fun i => cf width11 ((P s₀)[i]!).val) k l
    -- byte `m` of this iteration's output
    obtain byte : ∀ m < 44, ∀ x : BitVec 8,
        x.toNat = grp11 (fun i => cf width11 (X i)) (m / 11) / 2 ^ (8 * (m % 11)) % 2 ^ 8 →
        x = L width11 s₀ (44 * k + m) := fun m hm x hx => by
      rw [show 44 * k + m = 11 * (4 * k + m / 11) + m % 11 by omega_arith, L11 s₀ (by omega_arith) (by omega_arith)]
      apply BitVec.eq_of_toNat_eq
      rw [hx, BitVec.toNat_ofNat, sh]
    rw [o.mem, h9.mem, o8.mem, h7.mem, o6.mem, h5.mem, h4.mem, m3, x8, v7, v6, x6, h5.v, h4.v,
      show width11.nb * 4 * (k + 1) = 44 * k + 16 + 16 + 64 / 8 + 32 / 8 by simp [width11]; omega_arith,
      show 44 * k + 32 = 44 * k + 16 + 16 by omega_arith, show 44 * k + 40 = 44 * k + 16 + 16 + 64 / 8 by omega_arith]
    simp only [Mem.writeW]
    refine bytes_write (n := 32 / 8) (bytes_write (n := 64 / 8) (bytes_write (n := 16)
      (bytes_write (n := 16) out (by decide) (by simp [width11]; omega_arith) fun j hj => byte j (by omega_arith) _ (b4 j hj))
      (by decide) (by simp [width11]; omega_arith) fun j hj => by
        rw [show 44 * k + 16 + j = 44 * k + (16 + j) by omega_arith]; exact byte _ (by omega_arith) _ (b5 j hj))
      (by decide) (by simp [width11]; omega_arith) fun j hj => ?_) (by decide) (by simp [width11]; omega_arith) fun j hj => ?_
    · rw [show 44 * k + 16 + 16 + j = 44 * k + (32 + j) by omega_arith]
      refine byte _ (by omega_arith) _ ?_
      obtain e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v6).extractLsb' (Size.x.bits * 0) Size.x.bits).setWidth 64).setWidth 64).setWidth
          (8 * (64 / 8))) = vbyte (s3.v .v6) j := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp [vbyte, hi, Size.bits, show 8 * j + i < 64 by omega_arith]
      rw [e]
      exact b6 j (by omega_arith)
    · rw [show 44 * k + 16 + 16 + 64 / 8 + j = 44 * k + (32 + (8 + j)) by omega_arith]
      refine byte _ (by omega_arith) _ ?_
      obtain e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v6).extractLsb' (Size.w.bits * 2) Size.w.bits).setWidth 64).setWidth 32).setWidth
          (8 * (32 / 8))) = vbyte (s3.v .v6) (8 + j) := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp [vbyte, hi, Size.bits, show 8 * j + i < 32 by omega_arith, show 32 * 2 + (8 * j + i) = 8 * (8 + j) + i by omega_arith]
      rw [e]
      exact b6 (8 + j) (by omega_arith)
  · rw [o.mem, h9.mem, o8.mem, h7.mem, o6.mem, h5.mem, h4.mem, m3]
    exact (((h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega_arith) (by decide))).write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega_arith) (by decide))).write (n := 64 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega_arith) (by decide))).write (n := 32 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width11]; omega_arith) (by decide))

end VG.Proof.MlKem1024.AArch64.CE
