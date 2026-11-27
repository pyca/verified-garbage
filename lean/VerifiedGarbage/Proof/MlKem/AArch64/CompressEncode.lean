module

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeRun
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce10
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.CeLoop
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec

/-! ### `MlKem.AArch64.CodecV.Ce10Step`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.CodecV.Ce1Step`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.CodecV.Ce4Step`, which this module and modules that import it used -/

section

/-!
# ML-KEM on AArch64: an iteration of `ce4Body`

Coefficients `32 k … 32 k + 31` to bytes `16 k … 16 k + 15` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A compressed coefficient, as the code computes it. -/
theorem C_cf {w : Width} (hw : WOk w) (s₀ : State) (i : Nat) :
    C w s₀ i = cf w ((P s₀)[i]!).val := hw.cmp _

/-- Byte `j` of the output for `d = 4`: two coefficients. -/
theorem L4 (s₀ : State) {g : Nat} (hg : g < 128) :
    L width4 s₀ g = BitVec.ofNat 8 (C width4 s₀ (2 * g) + C width4 s₀ (2 * g + 1) * 2 ^ 4) := by
  have := L_eq width4_ok s₀ (g := g) (j := 0) hg (by decide)
  rw [show width4.nb * g + 0 = g from by simp [width4]] at this
  rw [this]
  congr 1
  rw [show width4.c = 2 from rfl, acc_succ, acc_succ, acc, List.range_zero, List.map_nil, digits_nil]
  simp only [show width4.d = 4 from rfl, show width4.c = 2 from rfl, Nat.add_zero]
  omega_using []

theorem step4 {s₀ : State} (hp : Pre width4 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : VInv width4 16 (fun _ => True) s₀ k s) :
    WP isa (.block ce4Body) s fun t =>
      VInv width4 16 (fun _ => True) s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (32 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[32 * k + i]!).val
  unfold ce4Body ld8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 32 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega_using [hk])) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega_using [hk]))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts width4 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce4Math_ok cs2 (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega_using [])
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega_using [])
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega_using [])
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega_using [])
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega_using [])
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega_using [])
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega_using [])) fun s3 ⟨c3, hb⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (16 * k)) (by decide) (by rw [g3, ptr_zero, h.x2]; rfl)
    (by rw [w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width4]; omega_using [hk]) (by decide)))
    fun s4 h4 => ?_
  have k4 : k < 256 / (width4.c * 16) := by simp [width4]; omega_using [hk]
  refine WP.mono (tail_ok (w := width4) (G := 16) (s₀ := s₀) k4 (by rw [h4.gpr, g3, h.x0])
    (by rw [h4.gpr, g3, h.x2]) (by rw [h4.gpr, g3, h.x11]) (by decide) (by decide)) fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  refine ⟨⟨by rw [o.rd, h4.rd, c3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h4.wr, w3, h.wr],
    by rw [o.sp, h4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, trivial, ?_, ?_⟩,
    by rw [show 256 / (width4.c * 16) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts width4 s3 := cs2.chg c3
    exact ⟨by rw [v, h4.v]; exact cs3.m, by rw [v, h4.v]; exact cs3.a, by rw [v, h4.v]; exact cs3.k⟩
  · rw [o.mem, h4.mem, m3, show width4.nb * 16 * (k + 1) = 16 * k + 16 by simp [width4]; omega_using []]
    have out := h.out
    rw [show width4.nb * 16 * k = 16 * k by simp [width4]] at out
    refine bytes_write (n := 16) out
      (by decide) (by simp [width4]; omega_using [hk]) fun j hj => ?_
    change vbyte _ j = _
    rw [L4 s₀ (by omega_using [hk, hj])]
    apply BitVec.eq_of_toNat_eq
    rw [hb j hj, BitVec.toNat_ofNat, C_cf width4_ok, C_cf width4_ok,
      show 2 * (16 * k + j) = 32 * k + 2 * j by omega_using [], show 32 * k + 2 * j + 1 = 32 * k + (2 * j + 1) by omega_using []]
    have : cf width4 (X (2 * j)) < 2 ^ 4 := cf_lt width4 _
    have : cf width4 (X (2 * j + 1)) < 2 ^ 4 := cf_lt width4 _
    exact (Nat.mod_eq_of_lt (by omega_arith)).symm
  · rw [o.mem, h4.mem, m3]
    exact h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width4]; omega_using [hk]) (by decide))

end VG.Proof.MlKem.AArch64.CE

end

end

/-! ### `MlKem.AArch64.CodecV.Ce1`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `ce1Math`

32 compressed coefficients of one bit, paired three times into four bytes.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The bits `Y (8 j) … Y (8 j + 7)` as a byte. -/
abbrev byte8 (Y : Nat → Nat) (j : Nat) : Nat :=
  Y (8 * j) + Y (8 * j + 1) * 2 + Y (8 * j + 2) * 4 + Y (8 * j + 3) * 8 + Y (8 * j + 4) * 16 +
    Y (8 * j + 5) * 32 + Y (8 * j + 6) * 64 + Y (8 * j + 7) * 128

theorem ce1Math_ok {s : State} (hc : CConsts width1 s) {X : Nat → Nat} (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce1Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s t ∧
      ∀ j < 4, (vbyte (t.v .v0) j).toNat = byte8 (fun i => cf width1 (X i)) j := by
  have hd : WOk width1 := width1_ok
  unfold ce1Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega_using [hi])) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega_using [hi]))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega_using [])
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega_using [])
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega_using []))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  let Y : Nat → Nat := fun i => cf width1 (X i)
  have hY : ∀ i, Y i < 2 ^ 1 := fun i => cf_lt width1 _
  -- level 1: pairs of bits
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 1
  have hZ : ∀ i, Z i < 2 ^ 2 := fun i => by have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega_using [])
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5))
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); congr 1; omega_using [])
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega_using [])
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  -- the registers of pairs: `v0`–`v3` hold `Z 0 …`, `Z 4 …`, `Z 8 …`, `Z 12 …`
  have q0 : Lanes (s6.v .v0) fun i => Z i := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    (Lanes.chg c4 (by decide) p0))
  have q1 : Lanes (s6.v .v1) fun i => Z (4 + i) := (Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    p1)).congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 1 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 1
    rw [show 8 + 2 * i = 2 * (4 + i) by omega_using [], show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega_using []]
  have q2 : Lanes (s6.v .v2) fun i => Z (8 + i) := (Lanes.chg c6 (by decide) p2).congr fun i _ => by
    show Y (16 + 2 * i) + Y (16 + (2 * i + 1)) * 2 ^ 1 = Y (2 * (8 + i)) + Y (2 * (8 + i) + 1) * 2 ^ 1
    rw [show 16 + 2 * i = 2 * (8 + i) by omega_using [], show 16 + (2 * i + 1) = 2 * (8 + i) + 1 by omega_using []]
  have q3 : Lanes (s6.v .v3) fun i => Z (12 + i) := p3.congr fun i _ => by
    show Y (24 + 2 * i) + Y (24 + (2 * i + 1)) * 2 ^ 1 = Y (2 * (12 + i)) + Y (2 * (12 + i) + 1) * 2 ^ 1
    rw [show 24 + 2 * i = 2 * (12 + i) by omega_using [], show 24 + (2 * i + 1) = 2 * (12 + i) + 1 by omega_using []]
  -- level 2: nibbles
  let W : Nat → Nat := fun i => Z (2 * i) + Z (2 * i + 1) * 2 ^ 2
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 2) (f := Z) (by decide) (by decide) (by decide) (by decide)
    q0 q1 fun i _ => hZ i) fun s7 ⟨c7, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 2) (f := fun i => Z (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c7 (by decide) q2)
    ((Lanes.chg c7 (by decide) q3).congr fun i _ => by show Z (12 + i) = Z (8 + (4 + i)); congr 1; omega_using [])
    fun i _ => hZ _) fun s8 ⟨c8, r1⟩ => ?_
  -- level 3: bytes
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 4) (f := W) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c8 (by decide) r0)
    (r1.congr fun i _ => by
      show Z (8 + 2 * i) + Z (8 + (2 * i + 1)) * 2 ^ 2 = Z (2 * (4 + i)) + Z (2 * (4 + i) + 1) * 2 ^ 2
      rw [show 8 + 2 * i = 2 * (4 + i) by omega_using [], show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega_using []])
    fun i _ => by have := hZ (2 * i); have := hZ (2 * i + 1); simp only [W]; omega_arith)
    fun s9 ⟨c9, u0⟩ => ?_
  refine wp_vop rfl fun s10 h10 => wp_vop rfl fun t h11 => wp_nil ⟨?_, ?_⟩
  · exact ((((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans
      (c9.trans (h10.chg.trans h11.chg))).mono
  intro j hj
  rw [h11.v, h10.v]
  rw [narrow1 u0 (fun j _ => by
    have := hZ (2 * (2 * j)); have := hZ (2 * (2 * j) + 1); have := hZ (2 * (2 * j + 1))
    have := hZ (2 * (2 * j + 1) + 1); simp only [W]; omega_arith) hj]
  simp only [W, Z, Y, byte8]
  rw [show 2 * (2 * (2 * j)) + 1 = 8 * j + 1 by omega_using [], show 2 * (2 * (2 * j)) = 8 * j by omega_using [],
    show 2 * (2 * (2 * j) + 1) + 1 = 8 * j + 3 by omega_using [], show 2 * (2 * (2 * j) + 1) = 8 * j + 2 by omega_using [],
    show 2 * (2 * (2 * j + 1)) + 1 = 8 * j + 5 by omega_using [], show 2 * (2 * (2 * j + 1)) = 8 * j + 4 by omega_using [],
    show 2 * (2 * (2 * j + 1) + 1) + 1 = 8 * j + 7 by omega_using [],
    show 2 * (2 * (2 * j + 1) + 1) = 8 * j + 6 by omega_using []]
  omega_using []

end VG.Proof.MlKem.AArch64.CodecV

end

end


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
  omega_using []

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
    (by rw [ptr_zero, e0]) (by omega_using [hk])) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok (src.chg c1) .v4 .v5 .v6 .v7 (o := 64) (j := 32 * k + 16) (by decide)
    (by rw [c1.gpr, e0]; exact coeffAddr_off _ _ 16) (by omega_using [hk]))
    fun s2 ⟨c2, l4, l5, l6, l7⟩ => ?_
  rw [WP.block_append_iff]
  have cs2 : CConsts width1 s2 := (h.cs.chg c1).chg c2
  refine WP.mono (ce1Math_ok cs2 (X := X) (fun i _ => val_lt _)
    (Lanes.chg c2 (by decide) l0)
    ((Lanes.chg c2 (by decide) l1).congr fun e _ => by show _ = X (4 + e); congr 2; omega_using [])
    ((Lanes.chg c2 (by decide) l2).congr fun e _ => by show _ = X (8 + e); congr 2; omega_using [])
    ((Lanes.chg c2 (by decide) l3).congr fun e _ => by show _ = X (12 + e); congr 2; omega_using [])
    (l4.congr fun e _ => by show _ = X (16 + e); congr 2; omega_using [])
    (l5.congr fun e _ => by show _ = X (20 + e); congr 2; omega_using [])
    (l6.congr fun e _ => by show _ = X (24 + e); congr 2; omega_using [])
    (l7.congr fun e _ => by show _ = X (28 + e); congr 2; omega_using [])) fun s3 ⟨c3, hb⟩ => ?_
  have g3 : s3.gpr = s.gpr := by rw [c3.gpr, c2.gpr, c1.gpr]
  have m3 : s3.mem = s.mem := by rw [c3.mem, c2.mem, c1.mem]
  have w3 : s3.wr = s.wr := by rw [c3.wr, c2.wr, c1.wr]
  refine wp_umov_w0 fun s4 o4 v4 x9 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (4 * k)) (by decide)
    (by rw [o4.get .x2, g3, ptr_zero, h.x2]; rfl)
    (by rw [o4.wr, w3, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width1]; omega_using [hk]) (by decide)))
    fun s5 h5 v5 => ?_
  have k4 : k < 256 / (width1.c * 4) := by simp [width1]; omega_using [hk]
  have gs : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, o4.gpr r (by simpa using hr), g3]
  refine WP.mono (tail_ok (w := width1) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  refine ⟨⟨by rw [o.rd, h5.rd, o4.rd, c3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h5.wr, o4.wr, w3, h.wr],
    by rw [o.sp, h5.sp, o4.sp, c3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, trivial, ?_, ?_⟩,
    by rw [show 256 / (width1.c * 4) = 8 from rfl] at tc; exact tc⟩
  · have cs3 : CConsts width1 s3 := cs2.chg c3
    have hv : t.v = s3.v := by rw [v, v5, v4]
    exact ⟨by rw [hv]; exact cs3.m, by rw [hv]; exact cs3.a, by rw [hv]; exact cs3.k⟩
  · rw [o.mem, h5.mem, o4.mem, m3, show width1.nb * 4 * (k + 1) = 4 * k + 4 by simp [width1]; omega_using []]
    have out := h.out
    rw [show width1.nb * 4 * k = 4 * k by simp [width1]] at out
    refine bytes_write (n := 4) out (by decide) (by simp [width1]; omega_using [hk]) fun j hj => ?_
    rw [x9, L1 s₀ (by omega_using [hk, hj])]
    have e : BitVec.extractLsb' (8 * j) 8 (((((s3.v .v0).extractLsb' 0 32).setWidth 64).setWidth 32).setWidth (8 * (32 / 8))) =
        vbyte (s3.v .v0) j := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [vbyte, hi, show 8 * j + i < 32 by omega_using [hj, hi]]
    rw [e]
    apply BitVec.eq_of_toNat_eq
    rw [hb j hj, BitVec.toNat_ofNat]
    simp only [byte8, C_cf width1_ok]
    rw [show 8 * (4 * k + j) = 32 * k + 8 * j by omega_using []]
    simp only [show ∀ e, 32 * k + 8 * j + e = 32 * k + (8 * j + e) from fun e => by omega_using []]
    have b : ∀ i, cf width1 (X i) < 2 ^ 1 := fun i => cf_lt width1 (X i)
    have := b (8 * j); have := b (8 * j + 1); have := b (8 * j + 2); have := b (8 * j + 3)
    have := b (8 * j + 4); have := b (8 * j + 5); have := b (8 * j + 6); have := b (8 * j + 7)
    exact (Nat.mod_eq_of_lt (by simp only [X] at *; omega_arith)).symm
  · rw [o.mem, h5.mem, o4.mem, m3]
    exact h.frame.write (n := 4) (List.mem_singleton_self _) _
      (contains_off (by simp [width1]; omega_using [hk]) (by decide))

end VG.Proof.MlKem.AArch64.CE

end

end

/-!
# ML-KEM on AArch64: an iteration of `ce10Body`

Coefficients `16 k … 16 k + 15` to bytes `20 k … 20 k + 19` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The constants of `ce10Body` besides those of `cmpV`. -/
abbrev K10 (s : State) : Prop := s.v .v20 = idxVec ce10Idx ∧ s.v .v21 = idxVec ce10IdxHi

/-- Byte `b` of group `g` of the output for `d = 10`. -/
theorem L10 (s₀ : State) {g b : Nat} (hg : g < 64) (hb : b < 5) :
    L width10 s₀ (5 * g + b) = BitVec.ofNat 8 (grp10 (C width10 s₀) g / 2 ^ (8 * b)) := by
  have := L_eq width10_ok s₀ (g := g) (j := b) hg hb
  rw [show width10.nb = 5 from rfl] at this
  rw [this]
  congr 2
  rw [show width10.c = 4 from rfl, acc_succ, acc_succ, acc_succ, acc_succ, acc, List.range_zero, List.map_nil,
    digits_nil]
  simp only [show width10.d = 10 from rfl, show width10.c = 4 from rfl, Nat.add_zero, grp10]
  omega_using []

theorem step10 {s₀ : State} (hp : Pre width10 s₀) {k : Nat} (hk : k < 16) {s : State}
    (h : VInv width10 4 K10 s₀ k s) :
    WP isa (.block ce10Body) s fun t =>
      VInv width10 4 K10 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 16) := by
  have src := h.src hp
  have e0 : s.gpr .x0 = coeffAddr (fP s₀) (16 * k) := by rw [h.x0]; rfl
  let X : Nat → Nat := fun i => ((P s₀)[16 * k + i]!).val
  unfold ce10Body
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld4_ok src .v0 .v1 .v2 .v3 (o := 0) (j := 16 * k) (by decide)
    (by rw [ptr_zero, e0]) (by omega_using [hk])) fun s1 ⟨c1, l0, l1, l2, l3⟩ => ?_
  rw [WP.block_append_iff]
  have cs1 : CConsts width10 s1 := h.cs.chg c1
  refine WP.mono (ce10Math_ok cs1 (by rw [c1.get .v20 (by decide)]; exact h.K.1)
    (by rw [c1.get .v21 (by decide)]; exact h.K.2) (X := X) (fun i _ => val_lt _) l0
    (l1.congr fun e _ => by show _ = X (4 + e); congr 2; omega_using [])
    (l2.congr fun e _ => by show _ = X (8 + e); congr 2; omega_using [])
    (l3.congr fun e _ => by show _ = X (12 + e); congr 2; omega_using [])) fun s2 ⟨c2, b6, b7⟩ => ?_
  have g2 : s2.gpr = s.gpr := by rw [c2.gpr, c1.gpr]
  have m2 : s2.mem = s.mem := by rw [c2.mem, c1.mem]
  have w2 : s2.wr = s.wr := by rw [c2.wr, c1.wr]
  refine wp_strq (a := oP s₀ + BitVec.ofNat 64 (20 * k)) (by decide) (by rw [g2, ptr_zero, h.x2]; rfl)
    (by rw [w2, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width10]; omega_using [hk]) (by decide)))
    fun s3 h3 => ?_
  refine wp_umov_w0 fun s4 o4 v4 x9 => ?_
  refine wp_strw' (a := oP s₀ + BitVec.ofNat 64 (20 * k + 16)) (by decide)
    (by rw [o4.get .x2, h3.gpr, g2, h.x2, ptr_add]; rfl)
    (by rw [o4.wr, h3.wr, w2, h.wr, hp.wr]
        exact in_regions (List.mem_singleton_self _) (contains_off (by simp [width10]; omega_using [hk]) (by decide)))
    fun s5 h5 v5 => ?_
  have k4 : k < 256 / (width10.c * 4) := by simp [width10]; omega_using [hk]
  have gs : ∀ r, r ≠ .x9 → s5.gpr r = s.gpr r := fun r hr => by
    rw [h5.gpr, o4.gpr r (by simpa using hr), h3.gpr, g2]
  refine WP.mono (tail_ok (w := width10) (G := 4) (s₀ := s₀) k4 (by rw [gs .x0 (by decide), h.x0])
    (by rw [gs .x2 (by decide), h.x2]) (by rw [gs .x11 (by decide), h.x11]) (by decide) (by decide))
    fun t ⟨o, v, t0, t2, t11, tc⟩ => ?_
  have hv : t.v = s2.v := by rw [v, v5, v4, h3.v]
  refine ⟨⟨by rw [o.rd, h5.rd, o4.rd, h3.rd, c2.rd, c1.rd, h.rd], by rw [o.wr, h5.wr, o4.wr, h3.wr, w2, h.wr],
    by rw [o.sp, h5.sp, o4.sp, h3.sp, c2.sp, c1.sp, h.sp], t0, t2, t11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width10.c * 4) = 16 from rfl] at tc; exact tc⟩
  · have cs2 : CConsts width10 s2 := cs1.chg c2
    exact ⟨by rw [hv]; exact cs2.m, by rw [hv]; exact cs2.a, by rw [hv]; exact cs2.k⟩
  · exact ⟨by rw [hv, c2.get .v20 (by decide), c1.get .v20 (by decide)]; exact h.K.1,
      by rw [hv, c2.get .v21 (by decide), c1.get .v21 (by decide)]; exact h.K.2⟩
  · have out := h.out
    rw [show width10.nb * 4 * k = 20 * k by simp [width10]] at out
    have out1 := bytes_write (n := 16) out (by decide) (by simp [width10]; omega_using [hk]) (x := s2.v .v6)
      fun j hj => by
        change vbyte _ j = _
        rw [show 20 * k + j = 5 * (4 * k + j / 5) + j % 5 by omega_using [], L10 s₀ (by omega_using [hk, hj]) (by omega_using [])]
        apply BitVec.eq_of_toNat_eq
        rw [b6 j hj, BitVec.toNat_ofNat]
        simp only [grp10, C_cf width10_ok]
        rw [show 4 * (4 * k + j / 5) = 16 * k + 4 * (j / 5) by omega_using []]
        simp only [show ∀ e, 16 * k + 4 * (j / 5) + e = 16 * k + (4 * (j / 5) + e) from fun e => by omega_using []]
        rfl
    rw [o.mem, h5.mem, o4.mem, h3.mem, m2, show width10.nb * 4 * (k + 1) = 20 * k + 16 + 4 by
      simp [width10]; omega_using []]
    refine bytes_write (n := 4) out1 (by decide) (by simp [width10]; omega_using [hk]) fun j hj => ?_
    rw [x9, h3.v]
    have e : BitVec.extractLsb' (8 * j) 8 (((((s2.v .v7).extractLsb' 0 32).setWidth 64).setWidth 32).setWidth
        (8 * (32 / 8))) = vbyte (s2.v .v7) j := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [vbyte, hi, show 8 * j + i < 32 by omega_using [hj, hi]]
    rw [e, show 20 * k + 16 + j = 5 * (4 * k + 3) + (1 + j) by omega_using [], L10 s₀ (by omega_using [hk]) (by omega_using [hj])]
    apply BitVec.eq_of_toNat_eq
    rw [b7 j hj, BitVec.toNat_ofNat]
    simp only [grp10, C_cf width10_ok]
    rw [show 4 * (4 * k + 3) = 16 * k + 12 by omega_using []]
  · rw [o.mem, h5.mem, o4.mem, h3.mem, m2]
    exact (h.frame.write (n := 16) (List.mem_singleton_self _) _
      (contains_off (by simp [width10]; omega_using [hk]) (by decide))).write (n := 32 / 8) (List.mem_singleton_self _) _
      (contains_off (by simp [width10]; omega_using [hk]) (by decide))

end VG.Proof.MlKem.AArch64.CE

end

end

/-!
# ML-KEM on AArch64: `vg_mlkem_compress_encode`

The contract, the dispatch on `len` to the loop of each width (`loop1_ok`, `loop4_ok`,
`loop10_ok`, from `Proof/MlKem/AArch64/CodecV/`), and constant time: every address and branch
depends only on the pointers and `len`.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_compress_encode(f = x0, d = w1, out = x2,
len = x3)`: if `d` is 1, 4 or 10, `len = 32 d` and the polynomial at `f` is
reduced, writes `ByteEncode_d(Compress_d(f))` to the `len` bytes at `out`. The
code may read `f` and write `out`, which do not overlap. -/
def compressEncodeAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 1024⟩] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧
    ((s.gpr .x1).setWidth 32).toNat ∈ compressWidths ∧
    (s.gpr .x3).toNat = 32 * ((s.gpr .x1).setWidth 32).toNat ∧ Reduced s.mem (s.gpr .x0)
  post s s' := bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    compressEncode ((s.gpr .x1).setWidth 32).toNat (polyAt s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.CE

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One width, from the state after the dispatch. -/
theorem width_ok {w : Width} {c : Prog isa} {s₀ s : State} (hs : compressEncodeAArch64.pre s₀)
    (hd : ((s₀.gpr .x1).setWidth 32).toNat = w.d) (hk : Keep [.x9] s₀ s) (hm : s.mem = s₀.mem)
    (hl : ∀ s, Pre w s → WP isa c s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      bytesAt s'.mem (oP s) (32 * w.d) = Spec.MlKem.compressEncode w.d (P s)) :
    WP isa c s fun s' => s'.sp = s₀.sp ∧ compressEncodeAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, -, h5, h6'⟩ := hs
  rw [hd] at h5
  have e0 : fP s = s₀.gpr .x0 := hk.get .x0
  have e2 : oP s = s₀.gpr .x2 := hk.get .x2
  have hp : Pre w s :=
    ⟨by rw [hk.rd, h1, e0], by rw [hk.wr, h2, oR, e2, h5], by rw [e0, oR, e2, ← h5]; exact h3,
      by rw [hm, e0]; exact h6'⟩
  refine WP.mono (hl s hp) fun s' ⟨_, _, sp, e⟩ => ⟨by rw [sp, hk.sp], ?_⟩
  show bytesAt s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = _
  rw [h5, hd, ← hk.get .x2, e, P, fP, hm, hk.get .x0]

theorem loop1_ok {s₀ : State} (hp : Pre width1 s₀) :
    WP isa (ceLoop width1 8 [] ce1Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (oP s₀) (32 * width1.d) = Spec.MlKem.compressEncode width1.d (P s₀) :=
  vloop_ok width1_ok (G := 4) (K := fun _ => True) rfl (by decide) rfl (by decide) (by decide)
    (fun s => wp_nil ⟨GFr.refl s, fun _ _ _ _ => rfl, trivial⟩) (fun _ _ _ _ => trivial)
    fun _ hk _ h => step1 hp hk h

theorem loop4_ok {s₀ : State} (hp : Pre width4 s₀) :
    WP isa (ceLoop width4 8 [] ce4Body) s₀ fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (oP s₀) (32 * width4.d) = Spec.MlKem.compressEncode width4.d (P s₀) :=
  vloop_ok width4_ok (G := 16) (K := fun _ => True) rfl (by decide) rfl (by decide) (by decide)
    (fun s => wp_nil ⟨GFr.refl s, fun _ _ _ _ => rfl, trivial⟩) (fun _ _ _ _ => trivial)
    fun _ hk _ h => step4 hp hk h

theorem idx10_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10Idx.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10Idx.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce10Idx := by decide +kernel

theorem idx10Hi_eq : setLane (ofVDwords (BitVec.ofNat 64 ((List.range 8).foldl
      (fun a i => a + (ce10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10IdxHi.getD (0 + i) 255) * 2 ^ (8 * i)) 0))) 64 1
    (BitVec.ofNat 64 ((List.range 8).foldl (fun a i => a + (ce10IdxHi.getD (8 + i) 255) * 2 ^ (8 * i)) 0)) =
      idxVec ce10IdxHi := by decide +kernel

theorem loop10_ok {s₀ : State} (hp : Pre width10 s₀) :
    WP isa (ceLoop width10 16 (bytesVec .v20 ce10Idx ++ bytesVec .v21 ce10IdxHi) ce10Body) s₀
      fun s' => s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
        bytesAt s'.mem (oP s₀) (32 * width10.d) = Spec.MlKem.compressEncode width10.d (P s₀) :=
  vloop_ok width10_ok (G := 4) (K := K10) rfl (by decide) rfl (by decide) (by decide)
    (fun s => by
      rw [← List.append_nil (bytesVec .v21 _)]
      exact wp_bytesVec fun s1 g1 v1 e1 => wp_bytesVec fun s2 g2 v2 e2 => wp_nil ⟨g1.trans g2,
        fun r a b _ => by rw [v2 r b, v1 r a], by rw [v2 .v20 (by decide), e1, idx10_eq], by rw [e2, idx10Hi_eq]⟩)
    (fun _ _ hv hk => by rw [K10, hv]; exact hk)
    fun _ hk _ h => step10 hp hk h

theorem correct (s : State) (hs : compressEncodeAArch64.pre s) :
    ∃ t s', Exec isa compressEncode s t s' ∧ abiPreserved s s' ∧ compressEncodeAArch64.post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, hd, hlen, -⟩ := hs'
  suffices h : WP isa compressEncode s fun s' => s'.sp = s.sp ∧ compressEncodeAArch64.post s s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  refine wp_subImm (by decide) fun s₂ h₂ e₂ => wp_nil ?_
  have k₂ : Keep [.x9] s s₂ := h₂.keep
  have m₂ : s₂.mem = s.mem := h₂.mem
  have z₂ : isa.eval (.zero .x .x9) s₂ = some (decide ((s.gpr .x3).toNat = 32)) := by
    rw [eval_zero, eq_zero_iff, e₂, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega_using []
  refine WP.ite _ z₂ (fun hb => ?_) (fun hb => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 1 := by simp at hb; omega_using [hlen, hb]
    exact width_ok (w := width1) hs e k₂ m₂ fun _ hp => loop1_ok hp
  refine WP.seq (wp_subImm (by decide) fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ : Keep [.x9] s s₃ := (k₂.trans h₃.keep).mono
  have z₃ : isa.eval (.zero .x .x9) s₃ = some (decide ((s.gpr .x3).toNat = 128)) := by
    rw [eval_zero, eq_zero_iff, e₃, k₂.get .x3, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    congr 1
    apply decide_eq_decide.mpr
    rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega_using []
  refine WP.ite _ z₃ (fun hb' => ?_) (fun hb' => ?_)
  · have e : ((s.gpr .x1).setWidth 32).toNat = 4 := by simp at hb'; omega_using [hlen, hb']
    exact width_ok (w := width4) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop4_ok hp
  · have e : ((s.gpr .x1).setWidth 32).toNat = 10 := by
      simp at hb hb'
      rcases mem_compressWidths hd with h | h | h <;> rw [h] at hlen <;> omega
    exact width_ok (w := width10) hs e k₃ (by rw [h₃.mem, m₂]) fun _ hp => loop10_ok hp

end VG.Proof.MlKem.AArch64.CE
