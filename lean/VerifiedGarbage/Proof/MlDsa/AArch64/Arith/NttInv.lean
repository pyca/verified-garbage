import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit`. -/
section

/-!
# ML-DSA on AArch64: the code of the NTTs as literals

The code of `ntt` and `nttInv`, whose tables of zetas are built by functions,
as literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.MlDsa.AArch64.Arith.ntt
materialize_code Impl.MlDsa.AArch64.Arith.nttInv

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table`. -/
section

/-!
# ML-DSA on AArch64: tables of constants in the working space

`storeTab t n b` leaves the `u32`s `t 0, …, t (n - 1)` at `b` (`Tab`), and
writes nothing else (`storeTab_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (coeffAt)

/-- The first `n` entries of the table `t` are the `u32`s at `p`. -/
def Tab (t : Nat → Nat) (m : Mem) (p : Addr) (n : Nat) : Prop :=
  ∀ k < n, coeffAt m p k = BitVec.ofNat 32 (t k)

theorem tabStep_ok (t : Nat → Nat) (b : Reg) (hb : b ≠ .x9) (i : Nat) (hi : i < 256) (s : State)
    (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (tabStep t b i)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 (4 * i)) (BitVec.ofNat 32 (t i))) ∧
        Keep [.x9] s s' := by
  unfold tabStep
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x9 _ s) fun s₁ ⟨⟨h9, hm⟩, k₁⟩ => ?_
  have hb' : s₁.gpr b = s.gpr b := k₁.get b (by simpa using hb)
  have ho : 4 * i % 4 = 0 ∧ 4 * i < 16384 := ⟨by omega, by omega⟩
  have hw₁ : InRegions s₁.wr (s₁.gpr b + BitVec.ofNat 64 (4 * i)) 4 := by rw [k₁.wr, hb']; exact hw
  refine WP.mono (WP.keep (c := .block [Instr.str .w .x9 b (4 * i)]) (s := s₁) []
    (Q := fun s' => s'.mem = s₁.mem.writeW (s₁.gpr b + BitVec.ofNat 64 (4 * i)) ((s₁.gpr .x9).setWidth 32))
    (by arun [ho, hw₁]) (by rfl) (hv := rfl)) fun s₂ ⟨hm₂, k₂⟩ => ⟨?_, (k₁.trans k₂).mono⟩
  rw [hm₂, hb', hm, h9, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The table, stored in the 1024 bytes at `b`. -/
theorem storeTab_ok (t : Nat → Nat) {b : Reg} (hb : b ≠ .x9) (s : State) (hw : pR (s.gpr b) ∈ s.wr) :
    WP isa (.block (storeTab t 256 b)) s fun s' =>
      VG.Proof.MlDsa.AArch64.Arith.Tab t s'.mem (s.gpr b) 256 ∧ Frame [pR (s.gpr b)] s.mem s'.mem ∧ Keep [.x9] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.x9] s s' ∧
      Frame [pR (s.gpr b)] s.mem s'.mem ∧ VG.Proof.MlDsa.AArch64.Arith.Tab t s'.mem (s.gpr b) k)
    (fun k s' hk ⟨hk', hf, ht⟩ => ?_) 256 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, ht⟩ => ⟨ht, hf, hk⟩
  have hb' : s'.gpr b = s.gpr b := hk'.get b (by simpa using hb)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.tabStep_ok t b hb k hk s' (by
      rw [hk'.wr, hb']; exact ⟨_, hw, coeff_contains _ (show k < 256 by omega)⟩))
    fun s'' ⟨hm', hk''⟩ => ⟨(hk'.trans hk'').mono, ?_, fun j hj => ?_⟩
  · rw [hm', hb']
    exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show k < 256 by omega))
  · rw [hm', hb', ← coeffAddr, coeffAt_writeW _ _ (show j < 256 by omega) (show k < 256 by omega)]
    by_cases e : k = j
    · subst e; rw [ite_eq_left rfl]
    · rw [ite_eq_right e]; exact ht j (by omega)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {p : Addr} {n : Nat} (h : VG.Proof.MlDsa.AArch64.Arith.Tab t m p n) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pR p).Disjoint r) (hn : n ≤ 256) : VG.Proof.MlDsa.AArch64.Arith.Tab t m' p n :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < 256 by omega)]; exact h k hk

end VG.Proof.MlDsa.AArch64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttBfly`. -/
section

/-!
# ML-DSA on AArch64: the butterflies of `NTT` and `NTT⁻¹`

What one butterfly's code stores (`bfly_ok`, `bflyInv_ok`), for any `len`,
from the words it reads and the zeta in `x6`; and that it does what the
butterfly of the specification does (`bfly_spec`, `bflyInv_spec`).
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-! ## The values -/

/-- The sum of two values `x` and `y`, reduced. -/
theorem csubX_add64 {a b : BitVec 64} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((csubX (a + b)).setWidth 32).toNat = (x + y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hq : q = 8380417 := rfl
  have e : (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add]; omega
  rw [csubX32 (by rw [e, ha, hb]; omega), e, ha, hb, val_add']

/-- The difference of two values `x` and `y` (`x + q - y`), reduced. -/
theorem csubX_sub64 {a b : BitVec 64} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    ((csubX (a + Qv - b)).setWidth 32).toNat = (x - y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hq : q = 8380417 := rfl
  have e1 : (a + Qv).toNat = a.toNat + q := by
    rw [VG.Proof.MlKem.AArch64.toNat_add_n (by rw [toNat_Qv]; omega), toNat_Qv]
  have e : (a + Qv - b).toNat = a.toNat + q - b.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [e1, hb]; omega), e1]
  rw [csubX32 (by rw [e, ha, hb]; omega), e, ha, hb, val_sub, condSub_eq (by omega)]

/-- The difference, reduced, as a 64-bit value. -/
theorem csubX_sub64' {a b : BitVec 64} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (csubX (a + Qv - b)).toNat = (x - y).val := by
  have hx : x.val < 8380417 := x.isLt
  have hy : y.val < 8380417 := y.isLt
  have hq : q = 8380417 := rfl
  have e1 : (a + Qv).toNat = a.toNat + q := by
    rw [VG.Proof.MlKem.AArch64.toNat_add_n (by rw [toNat_Qv]; omega), toNat_Qv]
  have e : (a + Qv - b).toNat = a.toNat + q - b.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [e1, hb]; omega), e1]
  rw [csubX_toNat (by rw [e, ha, hb]; omega), e, ha, hb, val_sub]

/-- The product of values `x` and `z`, reduced, as a 64-bit value. -/
theorem redX_mul64 {a b : BitVec 64} {x z : Zq} (ha : a.toNat = x.val) (hb : b.toNat = z.val) :
    (redX (a * b)).toNat = (x * z).val := by
  have hxz : x.val * z.val < q * q := Nat.mul_lt_mul_of_lt_of_lt x.isLt z.isLt
  have e : (a * b).toNat = x.val * z.val := by
    rw [BitVec.toNat_mul, ha, hb]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hxz (by decide))
  rw [redX_toNat (by rw [e]; exact hxz), e, val_mul]

/-- A reduced 64-bit value, stored as a word. -/
theorem toNat_setWidth32_zq {a : BitVec 64} {x : Zq} (ha : a.toNat = x.val) : (a.setWidth 32).toNat = x.val := by
  have hx : x.val < 8380417 := x.isLt
  rw [toNat_setWidth32 (by rw [ha]; omega), ha]

/-! ## `NTT` -/

/-- The accesses of a butterfly on `[x2]` and `[x2 + 4len]`. -/
structure Acc (s : State) (len : Nat) : Prop where
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .x2) 4
  r1 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 4
  w0 : InRegions s.wr (s.gpr .x2) 4
  w1 : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 4
  off : 4 * len % 4 = 0 ∧ 4 * len < 16384

theorem bfly_ok (len : Nat) (s : State) (hc : Consts s) (ha : VG.Proof.MlDsa.AArch64.Arith.Acc s len) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.bfly len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 (4 * len))
          ((csubX (w64 (s.mem.readW (s.gpr .x2) 32) + Qv -
            redX (w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32) * s.gpr .x6))).setWidth 32)).writeW
          (s.gpr .x2) ((csubX (w64 (s.mem.readW (s.gpr .x2) 32) +
            redX (w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32) * s.gpr .x6))).setWidth 32) ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s' := by
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold Impl.MlDsa.AArch64.Arith.bfly reduce Impl.MlKem.AArch64.csub
  arun [ha.r0, ha.r1, ha.w0, ha.w1, ha.off, hc.x9, hc.x10, hc.x11, redX, csubX]

/-! ## `NTT⁻¹` -/

theorem bflyInv_ok (len : Nat) (s : State) (hc : Consts s) (ha : VG.Proof.MlDsa.AArch64.Arith.Acc s len) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.bflyInv len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .x2) ((csubX (w64 (s.mem.readW (s.gpr .x2) 32) +
          w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32))).setWidth 32)).writeW
          (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) ((redX (csubX (w64 (s.mem.readW (s.gpr .x2) 32) + Qv -
            w64 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (4 * len)) 32)) * s.gpr .x6)).setWidth 32) ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s' := by
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold Impl.MlDsa.AArch64.Arith.bflyInv reduce Impl.MlKem.AArch64.csub
  arun [ha.r0, ha.r1, ha.w0, ha.w1, ha.off, hc.x9, hc.x10, hc.x11, redX, csubX]

/-! ## What they do to a stored polynomial -/

/-- The code `code len` of a butterfly does what `op` does. -/
def BflyOk (code : Nat → List Instr) (op : Poly → Nat → Nat → Zq → Poly) : Prop :=
  ∀ (fP : Addr) (len j : Nat), 0 < len → len ≤ 128 → j + len < 256 → ∀ (z : Zq) (F : Poly) (s : State),
    s.gpr .x2 = coeffAddr fP j → s.gpr .x6 = BitVec.ofNat 64 z.val → Consts s → PolyIs s.mem fP F →
    pR fP ∈ s.wr →
    WP isa (.block (code len)) s fun s' => (PolyIs s'.mem fP (op F j len z) ∧ Frame [pR fP] s.mem s'.mem ∧
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s'

/-- The words a butterfly reads and writes. -/
theorem bfly_acc {fP : Addr} {len j : Nat} (hl : len ≤ 128) (hj : j + len < 256) {s : State}
    (hx2 : s.gpr .x2 = coeffAddr fP j) (hw : pR fP ∈ s.wr) : VG.Proof.MlDsa.AArch64.Arith.Acc s len := by
  have e : s.gpr .x2 + BitVec.ofNat 64 (4 * len) = coeffAddr fP (j + len) := by rw [hx2, coeffAddr_add]
  refine ⟨?_, ?_, ?_, ?_, ⟨by omega, by omega⟩⟩
  · rw [hx2]; exact ⟨_, List.mem_append_right _ hw, coeff_contains _ (show j < 256 by omega)⟩
  · rw [e]; exact ⟨_, List.mem_append_right _ hw, coeff_contains _ hj⟩
  · rw [hx2]; exact ⟨_, hw, coeff_contains _ (show j < 256 by omega)⟩
  · rw [e]; exact ⟨_, hw, coeff_contains _ hj⟩

/-- The two writes of a butterfly are within the polynomial. -/
theorem bfly_frame {fP : Addr} {len j : Nat} (hj : j + len < 256) (m : Mem) (a b : BitVec 32) :
    Frame [pR fP] m ((m.writeW (coeffAddr fP (j + len)) a).writeW (coeffAddr fP j) b) ∧
      Frame [pR fP] m ((m.writeW (coeffAddr fP j) a).writeW (coeffAddr fP (j + len)) b) :=
  ⟨(Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega)),
    (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show j < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)⟩

theorem bfly_spec : VG.Proof.MlDsa.AArch64.Arith.BflyOk Impl.MlDsa.AArch64.Arith.bfly Arith.bfly := by
  intro fP len j hlen hl hj z F s hx2 h6 hc hF hw
  have ha := VG.Proof.MlDsa.AArch64.Arith.bfly_acc hl hj hx2 hw
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.bfly_ok len s hc ha) fun s' ⟨⟨hm, hx2', hx5⟩, hk⟩ => ⟨⟨?_, ?_, hx2', hx5⟩, hk⟩
  · rw [hm, h6, hx2, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    show PolyIs _ _ ((F.set! (j + len) (F[j]! - z * F[j + len]!)).set! j
      ((F.set! (j + len) (F[j]! - z * F[j + len]!))[j]! + z * F[j + len]!))
    rw [getElem!_set!_ne _ hj' (by omega)]
    have hT' : (redX (w64 (coeffAt s.mem fP (j + len)) * BitVec.ofNat 64 z.val)).toNat = (z * F[j + len]!).val := by
      rw [VG.Proof.MlDsa.AArch64.Arith.redX_mul64 (by rw [toNat_setWidth64]; exact polyIs_toNat hF hj)
        (BitVec.toNat_ofNat .. |>.trans (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le z.isLt (by decide)))), Fin.mul_comm]
    exact polyIs_writeW (polyIs_writeW hF hj _ (VG.Proof.MlDsa.AArch64.Arith.csubX_sub64 (by rw [toNat_setWidth64]; exact ha) hT')) hj' _
      (VG.Proof.MlDsa.AArch64.Arith.csubX_add64 (by rw [toNat_setWidth64]; exact ha) hT')
  · rw [hm, hx2, coeffAddr_add]
    exact (VG.Proof.MlDsa.AArch64.Arith.bfly_frame hj _ _ _).1

theorem bflyInv_spec : VG.Proof.MlDsa.AArch64.Arith.BflyOk Impl.MlDsa.AArch64.Arith.bflyInv Arith.bflyInv := by
  intro fP len j hlen hl hj z F s hx2 h6 hc hF hw
  have ha := VG.Proof.MlDsa.AArch64.Arith.bfly_acc hl hj hx2 hw
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.bflyInv_ok len s hc ha) fun s' ⟨⟨hm, hx2', hx5⟩, hk⟩ => ⟨⟨?_, ?_, hx2', hx5⟩, hk⟩
  · rw [hm, h6, hx2, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq]
    have hj' : j < 256 := by omega
    have ha := polyIs_toNat hF hj'
    have hu := polyIs_toNat hF hj
    have hne : j ≠ j + len := by omega
    show PolyIs _ _ (((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
      (F[j]! - (F.set! j (F[j]! + F[j + len]!))[j + len]!)).set! (j + len)
      (z * ((F.set! j (F[j]! + F[j + len]!)).set! (j + len)
        (F[j]! - (F.set! j (F[j]! + F[j + len]!))[j + len]!))[j + len]!))
    rw [getElem!_set!_ne _ hj hne, getElem!_set!_self _ hj]
    have e : ∀ (G : Poly) (x y : Zq), (G.set! (j + len) x).set! (j + len) y = G.set! (j + len) y := fun G x y =>
      ext_getElem! fun i hi => by
        by_cases h : i = j + len
        · subst h; rw [getElem!_set!_self _ hi, getElem!_set!_self _ hi]
        · rw [getElem!_set!_ne _ hi (Ne.symm h), getElem!_set!_ne _ hi (Ne.symm h), getElem!_set!_ne _ hi (Ne.symm h)]
    rw [e]
    have hd := VG.Proof.MlDsa.AArch64.Arith.csubX_sub64' (x := F[j]!) (y := F[j + len]!) (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hu)
    have hT : ((redX (csubX (w64 (coeffAt s.mem fP j) + Qv - w64 (coeffAt s.mem fP (j + len))) *
        BitVec.ofNat 64 z.val)).setWidth 32).toNat = (z * (F[j]! - F[j + len]!)).val := by
      rw [VG.Proof.MlDsa.AArch64.Arith.toNat_setWidth32_zq (VG.Proof.MlDsa.AArch64.Arith.redX_mul64 hd
        (BitVec.toNat_ofNat .. |>.trans (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le z.isLt (by decide))))),
        Fin.mul_comm]
    exact polyIs_writeW (polyIs_writeW hF hj' _ (VG.Proof.MlDsa.AArch64.Arith.csubX_add64 (by rw [toNat_setWidth64]; exact ha)
      (by rw [toNat_setWidth64]; exact hu))) hj _ hT
  · rw [hm, hx2, coeffAddr_add]
    exact (VG.Proof.MlDsa.AArch64.Arith.bfly_frame hj _ _ _).2

end VG.Proof.MlDsa.AArch64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttLoop`. -/
section

/-!
# ML-DSA on AArch64: the blocks and layers of `NTT` and `NTT⁻¹`

The loops of `nttBlk` and `nttLay`, for any butterfly code that does what a
butterfly `op` of the specification does (`BflyOk`): a block runs `len`
butterflies (`blockN`), and a layer its `128 / len` blocks (`layerN`), with
the zetas `Z (zi c)`, whose values `tab` the table at `zP` holds.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

/-- The table `tab` holds the values of the zetas `Z`. -/
def TabOf (tab : Nat → Nat) (Z : Nat → Zq) : Prop := ∀ k < 256, tab k = (Z k).val

/-- Where the zeta pointer moves: up or down by 4 bytes. -/
def zstep (up : Bool) (a : Addr) : Addr := if up then a + BitVec.ofNat 64 4 else a - BitVec.ofNat 64 4

/-! ## A block -/

section
variable {code : Nat → List Instr} {op : Poly → Nat → Nat → Zq → Poly} (hb : VG.Proof.MlDsa.AArch64.Arith.BflyOk code op)
include hb

/-- The `len` butterflies of a block. -/
theorem bflys_ok {fP : Addr} {len start : Nat} (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256)
    (z : Zq) (G : Poly) (s : State) (hx2 : s.gpr .x2 = coeffAddr fP start)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 z.val) (hc : Consts s) (hG : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block (code len)) (.nonzero .x .x5)) s fun s' =>
      PolyIs s'.mem fP (blockN op G len z start len) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = coeffAddr fP (start + len) ∧ Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s' := by
  refine wp_countdown (cnt := .x5) (N := len) (by omega) hlen (fun t s' =>
      PolyIs s'.mem fP (blockN op G len z start t) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = coeffAddr fP (start + t) ∧ Keep [.x2, .x5, .x12, .x13, .x14, .x15] s s')
    (fun t ht s' ⟨hP, hf, hs', hk⟩ _ => ?_) ⟨hG, Frame.refl _ _, hx2, Keep.refl _ _⟩ h5
  refine WP.mono (hb fP len (start + t) hlen hl (by omega) z _ s' hs' (by rw [hk.get .x6, h6])
    ⟨by rw [hk.get .x9, hc.x9], by rw [hk.get .x10, hc.x10], by rw [hk.get .x11, hc.x11]⟩ hP
    (by rw [hk.wr]; exact hw)) fun s'' ⟨⟨hP', hf', hx2', hx5⟩, hk'⟩ =>
      ⟨⟨?_, hf.trans hf', by rw [hx2', hs', coeffAddr_next, Nat.add_assoc], (hk.trans hk').mono⟩, hx5⟩
  rw [blockN_succ]; exact hP'

omit hb in
theorem blkPre_ok (len : Nat) (up : Bool) (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .x3) 4) :
    WP isa (.block [.ldr .w .x6 .x3 0, if up then .addImm .x .x3 .x3 4 else .subImm .x .x3 .x3 4,
      .movz .x .x5 (BitVec.ofNat 16 len) 0]) s fun s' =>
      (s'.gpr .x6 = w64 (s.mem.readW (s.gpr .x3) 32) ∧ s'.gpr .x3 = VG.Proof.MlDsa.AArch64.Arith.zstep up (s.gpr .x3) ∧
        s'.gpr .x5 = (BitVec.ofNat 16 len).setWidth 64 ∧ s'.mem = s.mem) ∧ Keep [.x6, .x3, .x5] s s' := by
  cases up
  · refine WP.keep _ ?_ (by rfl) (hv := rfl)
    arun [h, VG.Proof.MlDsa.AArch64.Arith.zstep]
  · refine WP.keep _ ?_ (by rfl) (hv := rfl)
    arun [h, VG.Proof.MlDsa.AArch64.Arith.zstep]

omit hb in
theorem blkPost_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 (4 * len), .subImm .x .x4 .x4 1]) s fun s' =>
      (s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (4 * len) ∧ s'.gpr .x4 = s.gpr .x4 - BitVec.ofNat 64 1 ∧
        s'.mem = s.mem) ∧ Keep [.x2, .x4] s s' := by
  have h : 4 * len < 4096 := by omega
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [h]

/-- A block, with the zeta `Z k` at `x3`. -/
theorem blk_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : VG.Proof.MlDsa.AArch64.Arith.TabOf tab Z) {fP zP : Addr} {len start k : Nat}
    (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256)
    (hk : k < 256) (up : Bool) (G : Poly) (s : State) (hx2 : s.gpr .x2 = coeffAddr fP start)
    (h3 : s.gpr .x3 = coeffAddr zP k) (hc : Consts s) (hG : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (hz : pR zP ∈ s.rd ++ s.wr) (ht : VG.Proof.MlDsa.AArch64.Arith.Tab tab s.mem zP 256) :
    WP isa (nttBlk (code len) len up) s fun s' =>
      (PolyIs s'.mem fP (blockN op G len (Z k) start len) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = coeffAddr fP (start + 2 * len) ∧ s'.gpr .x3 = VG.Proof.MlDsa.AArch64.Arith.zstep up (s.gpr .x3) ∧
        s'.gpr .x4 = s.gpr .x4 - BitVec.ofNat 64 1) ∧
      Keep [.x6, .x3, .x5, .x2, .x5, .x12, .x13, .x14, .x15, .x2, .x4] s s' := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.blkPre_ok len up s (by rw [h3]; exact ⟨_, hz, coeff_contains _ hk⟩))
    fun s1 ⟨⟨h6, h3', h5, hm⟩, k1⟩ => ?_)
  have hz6 : s1.gpr .x6 = BitVec.ofNat 64 (Z k).val := by
    rw [h6, h3, ← coeffAt_eq, ht k hk, ← hZ k hk]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := (Z k).isLt
    rw [hZ k hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (by decide))]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.bflys_ok hb (fP := fP) hlen hl hs (Z k) G s1 (by rw [k1.get .x2, hx2]) hz6
    ⟨by rw [k1.get .x9, hc.x9], by rw [k1.get .x10, hc.x10], by rw [k1.get .x11, hc.x11]⟩
    (by rw [hm]; exact hG) (by rw [k1.wr]; exact hw) (by rw [h5]; exact imm16 (by omega)))
    fun s2 ⟨hP, hf, hx22, k2⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.blkPost_ok len hl s2) fun s3 ⟨⟨hx23, hx4, hm3⟩, k3⟩ =>
    ⟨⟨by rw [hm3]; exact hP, by rw [hm3, ← hm]; exact hf, ?_, ?_, ?_⟩, ((k1.trans k2).trans k3).mono⟩
  · rw [hx23, hx22, coeffAddr_add, show start + len + len = start + 2 * len by omega]
  · rw [k3.get .x3, k2.get .x3, h3']
  · rw [hx4, k2.get .x4, k1.get .x4]

/-! ## A layer -/

omit hb in
theorem layPre_ok (c : Nat) (hc : c < 65536) (s : State) :
    WP isa (.block [.movz .x .x4 (BitVec.ofNat 16 c) 0]) s fun s' =>
      (s'.gpr .x4 = BitVec.ofNat 64 c ∧ s'.mem = s.mem) ∧ Keep [.x4] s s' := by
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [imm16 hc]

omit hb in
theorem layPost_ok (s : State) :
    WP isa (.block [.subImm .x .x2 .x2 1024]) s fun s' =>
      (s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1024 ∧ s'.mem = s.mem) ∧ Keep [.x2] s s' := by
  refine WP.keep _ ?_ (by rfl) (hv := rfl)
  arun

omit hb in
/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ VG.Proof.MlDsa.Arith.nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len := by
  decide

/-- A layer, from `x2` = `f` and the zeta of its first block at `x3`. -/
theorem lay_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : VG.Proof.MlDsa.AArch64.Arith.TabOf tab Z) {fP zP : Addr} {len : Nat}
    (hlen : len ∈ VG.Proof.MlDsa.Arith.nttLens) (up : Bool) (zi : Nat → Nat)
    (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, VG.Proof.MlDsa.AArch64.Arith.zstep up (coeffAddr zP (zi c)) = coeffAddr zP (zi (c + 1)))
    (F : Poly) (s : State) (hx2 : s.gpr .x2 = fP) (h3 : s.gpr .x3 = coeffAddr zP (zi 0)) (hc : Consts s)
    (hF : PolyIs s.mem fP F) (hw : pR fP ∈ s.wr) (hz : pR zP ∈ s.rd ++ s.wr)
    (hd : (pR zP).Disjoint (pR fP)) (ht : VG.Proof.MlDsa.AArch64.Arith.Tab tab s.mem zP 256) :
    WP isa (nttLay (code len) len up) s fun s' =>
      (PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.gpr .x2 = fP ∧ s'.gpr .x3 = coeffAddr zP (zi (128 / len))) ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s' := by
  obtain ⟨hl0, hl1, hl2, hl3⟩ := VG.Proof.MlDsa.AArch64.Arith.lens_facts len hlen
  have h128 : 128 / len ≤ 128 := Nat.div_le_self 128 len
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.layPre_ok (128 / len) (by omega) s) fun s1 ⟨⟨hx4, hm⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s' : State) =>
      PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
      Frame [pR fP] s.mem s'.mem ∧ s'.gpr .x2 = coeffAddr fP 256 ∧
      s'.gpr .x3 = coeffAddr zP (zi (128 / len)) ∧ Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s') ?_
    fun s2 ⟨hP, hf, hx22, h32, k2⟩ => ?_)
  · refine WP.mono (wp_countdown (cnt := .x4) (N := 128 / len) (Nat.lt_of_le_of_lt h128 (by decide)) hl3
      (fun c (s' : State) =>
        PolyIs s'.mem fP (layerN op F len (fun c => Z (zi c)) c) ∧ Frame [pR fP] s.mem s'.mem ∧
          s'.gpr .x2 = coeffAddr fP (2 * len * c) ∧ s'.gpr .x3 = coeffAddr zP (zi c) ∧
          Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s')
      (fun c hc' s' ⟨hP, hf, hs', h3', hk⟩ _ => ?_)
      ⟨by rw [hm]; exact hF, by rw [hm]; exact Frame.refl _ _,
        by rw [k1.get .x2, hx2, coeffAddr, Nat.mul_zero, Nat.mul_zero, BitVec.add_zero],
        by rw [k1.get .x3, h3], k1.mono⟩ hx4)
      fun s' ⟨hP, hf, hs', h3', hk⟩ => ⟨hP, hf, by rw [hs', hl2], h3', hk⟩
    have hcm : 2 * len * c + 2 * len ≤ 256 := by
      have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.blk_ok hb hZ hl0 hl1 hcm (hzi c hc') up _ s' hs' h3'
      ⟨by rw [hk.get .x9, hc.x9], by rw [hk.get .x10, hc.x10], by rw [hk.get .x11, hc.x11]⟩ hP
      (by rw [hk.wr]; exact hw) (by rw [hk.rd, hk.wr]; exact hz) (ht.frame hf (by simpa using hd) (by decide)))
      fun s'' ⟨⟨hP', hf', hx2', h3'', hx4'⟩, hk'⟩ => ⟨⟨by rw [layerN_succ]; exact hP',
        hf.trans hf', ?_, ?_, (hk.trans hk').mono⟩, hx4'⟩
    · rw [hx2', Nat.mul_succ]
    · rw [h3'', h3', hstep c hc']
  · refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.layPost_ok s2) fun s3 ⟨⟨hx23, hm3⟩, k3⟩ =>
      ⟨⟨by rw [hm3]; exact hP, by rw [hm3]; exact hf, ?_, by rw [k3.get .x3, h32]⟩,
        (k2.trans k3).mono⟩
    rw [hx23, hx22, coeffAddr]
    exact BitVec.add_sub_cancel _ _

end

end VG.Proof.MlDsa.AArch64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Ntt`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_ntt`

The butterfly's code does what `bfly` does (`bfly_spec`), so each layer is
`nttLayer` (`lay_ok`), and the eight layers are `NTT` (`ntt_eq_layers`).
`Ntt.LI`, `Ntt.pro_ok` and `inPlaceSat` serve `NTT⁻¹` too.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas ntt)

namespace Ntt

/-- The registers the NTTs write. -/
abbrev clob : List Reg := [.x2, .x3, .x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- Between layers: the polynomial `F` at `fP`, the table `tab` at `zP`, and
entry `k` of the table at `x3`. -/
structure LI (tab : Nat → Nat) (s₀ : State) (fP zP : Addr) (F : Poly) (k : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = fP
  x3 : s.gpr .x3 = coeffAddr zP k
  consts : Consts s
  poly : PolyIs s.mem fP F
  tab : VG.Proof.MlDsa.AArch64.Arith.Tab tab s.mem zP 256
  frame : Frame [pR fP, pR zP] s₀.mem s.mem
  keep : Keep VG.Proof.MlDsa.AArch64.Arith.Ntt.clob s₀ s

theorem LI.step {tab : Nat → Nat} {s₀ : State} {fP zP : Addr} {F F' : Poly} {k k' : Nat} {s s' : State}
    (hI : VG.Proof.MlDsa.AArch64.Arith.Ntt.LI tab s₀ fP zP F k s) (hP : PolyIs s'.mem fP F') (hf : Frame [pR fP] s.mem s'.mem)
    (hx2 : s'.gpr .x2 = fP) (h3 : s'.gpr .x3 = coeffAddr zP k')
    (hk : Keep [.x2, .x3, .x4, .x5, .x6, .x12, .x13, .x14, .x15] s s')
    (hd : (pR zP).Disjoint (pR fP)) : VG.Proof.MlDsa.AArch64.Arith.Ntt.LI tab s₀ fP zP F' k' s' :=
  ⟨hx2, h3, ⟨by rw [hk.get .x9, hI.consts.x9], by rw [hk.get .x10, hI.consts.x10],
      by rw [hk.get .x11, hI.consts.x11]⟩, hP, hI.tab.frame hf (by simpa using hd) (by decide),
    hI.frame.trans (hf.mono (by simp)), (hI.keep.trans hk).mono⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ VG.Proof.MlDsa.AArch64.Arith.Ntt.Chain (256 / len) ls

theorem lens_fwd : ∀ len ∈ VG.Proof.MlDsa.Arith.nttLens, 2 * (128 / len) ≤ 256 ∧ 128 / len + 128 / len = 256 / len := by decide

theorem zetaTab_of : VG.Proof.MlDsa.AArch64.Arith.TabOf zetaTab VG.Spec.MlDsa.zetas := fun k _ => zetaNat_eq k

theorem lays_ok {s₀ : State} {fP zP : Addr} (hw : pR fP ∈ s₀.wr) (hz : pR zP ∈ s₀.rd ++ s₀.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    ∀ (ls : List Nat) (F : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ VG.Proof.MlDsa.Arith.nttLens) → VG.Proof.MlDsa.AArch64.Arith.Ntt.Chain k ls →
      VG.Proof.MlDsa.AArch64.Arith.Ntt.LI zetaTab s₀ fP zP F k s →
      WP isa (nttLays ls) s fun s' => ∃ k', VG.Proof.MlDsa.AArch64.Arith.Ntt.LI zetaTab s₀ fP zP (ls.foldl VG.Proof.MlDsa.Arith.nttLayer F) k' s'
  | [], F, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, F, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := VG.Proof.MlDsa.AArch64.Arith.Ntt.lens_fwd len hlen
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.lay_ok VG.Proof.MlDsa.AArch64.Arith.bfly_spec VG.Proof.MlDsa.AArch64.Arith.Ntt.zetaTab_of hlen true (fun c => 128 / len + c)
      (fun c hc => by omega) (fun c _ => by rw [VG.Proof.MlDsa.AArch64.Arith.zstep, ite_eq_left rfl, coeffAddr_next]; rfl)
      F s hI.x2 (by rw [hI.x3, hk]; rfl) hI.consts hI.poly (by rw [hI.keep.wr]; exact hw)
      (by rw [hI.keep.rd, hI.keep.wr]; exact hz) hd hI.tab) fun s' ⟨⟨hP, hf, hx2, h3⟩, hk'⟩ => ?_)
    exact VG.Proof.MlDsa.AArch64.Arith.Ntt.lays_ok hw hz hd ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hx2 (by rw [h3, h2]) hk' hd)

/-- The table `tab` to `scratch`, the constants, `x2` = `f` and `x3` at entry `k`. -/
theorem pro_ok {s₀ : State} {t : Poly → Poly} (hp : (inPlaceK t).pre s₀) (tab : Nat → Nat) (k : Nat)
    (hk : 4 * k < 4096) :
    WP isa (.block (nttPro tab k)) s₀
      (VG.Proof.MlDsa.AArch64.Arith.Ntt.LI tab s₀ (s₀.gpr .x0) (s₀.gpr .x1) (polyAt s₀.mem (s₀.gpr .x0)) k) := by
  unfold nttPro
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.storeTab_ok tab (b := .x1) (by decide) s₀ (by rw [hp.2.1]; simp))
    fun s1 ⟨ht, hf, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s1) fun s2 ⟨⟨hc, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (WP.keep [.x2, .x3] (Q := fun s => s.mem = s2.mem ∧ s.gpr .x2 = s2.gpr .x0 ∧
    s.gpr .x3 = s2.gpr .x1 + BitVec.ofNat 64 (4 * k)) (by arun [Impl.MlKem.AArch64.mov, hk]) (by rfl) (hv := rfl))
    fun s3 ⟨⟨hm3, hx2, hx3⟩, k3⟩ => ?_
  have hd' : (pR (s₀.gpr .x0)).Disjoint (pR (s₀.gpr .x1)) := hp.2.2.1
  refine ⟨by rw [hx2, k12.get .x0], by rw [hx3, k12.get .x1],
    ⟨by rw [k3.get .x9, hc.x9], by rw [k3.get .x10, hc.x10], by rw [k3.get .x11, hc.x11]⟩, ?_,
    by rw [hm3, hm2]; exact ht, by rw [hm3, hm2]; exact hf.mono (by simp), (k12.trans k3).mono⟩
  rw [hm3, hm2]
  exact ⟨reduced_frame hf (by simpa using hd') hp.2.2.2, polyAt_frame hf (by simpa using hd')⟩

end Ntt

theorem chain_fwd : Ntt.Chain 1 VG.Proof.MlDsa.Arith.nttLens := by
  simp only [VG.Proof.MlDsa.Arith.nttLens, Ntt.Chain]; decide

theorem ntt_noCalls : Impl.MlDsa.AArch64.Arith.ntt.noCalls = true := by lit_decide

theorem ntt_correct (s : State) (hs : (inPlaceK VG.Spec.MlDsa.ntt).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.ntt s t s' ∧ abiPreserved s s' ∧ (inPlaceK VG.Spec.MlDsa.ntt).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, ⟨k, hI⟩⟩ := WP.seq (M := isa) (WP.mono (Ntt.pro_ok hs zetaTab 1 (by decide))
    fun s1 hI => Ntt.lays_ok hw hz hs.2.2.1.symm VG.Proof.MlDsa.Arith.nttLens _ 1 s1 (fun _ h => h) VG.Proof.MlDsa.AArch64.Arith.chain_fwd hI)
  refine ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of VG.Proof.MlDsa.AArch64.Arith.ntt_noCalls (by lit_decide) he, ?_⟩
  show PolyIs _ _ _
  rw [VG.Proof.MlDsa.Arith.ntt_eq_layers]
  exact hI.poly

/-- The pointers are public. -/
theorem inPlace_agree {t : Poly → Poly} (s₁ s₂ : State) (_ : (inPlaceK t).pre s₁) (_ : (inPlaceK t).pre s₂)
    (hp : (inPlaceK t).pub s₁ s₂) : VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1]) s₁ s₂ :=
  agree_regs hp.2.2 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.1, hp.2.1]

theorem ntt_ct : ConstantTime isa (inPlaceK VG.Spec.MlDsa.ntt).pre (inPlaceK VG.Spec.MlDsa.ntt).pub Impl.MlDsa.AArch64.Arith.ntt :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1]) VG.Proof.MlDsa.AArch64.Arith.inPlace_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def inPlaceSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.ntt (Spec.MlDsa.nttContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Arith.ntt_correct VG.Proof.MlDsa.AArch64.Arith.ntt_ct (by
    mldsa_implies [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      AArch64.abi, AArch64.argRegs] [inPlaceSat] using VG.Proof.MlDsa.AArch64.Arith.inPlaceSat)

end VG.Proof.MlDsa.AArch64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttInv`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_inv_ntt`

The butterfly's code does what `bflyInv` does (`bflyInv_spec`), with the
negated zetas of the table (`negZetaTab_of`), so each layer is `nttInvLayer`,
the eight layers are those of `NTT⁻¹` (`nttInv_eq_layers`), and the last loop
multiplies each coefficient by `8347681 = 256⁻¹ mod q`.
-/

namespace VG.Proof.MlDsa.AArch64.Arith

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas nttInv)

namespace NttInv

open Ntt (LI)

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ VG.Proof.MlDsa.AArch64.Arith.NttInv.Chain (256 / len - 1 - 128 / len) ls

theorem lens_inv : ∀ len ∈ VG.Proof.MlDsa.Arith.nttLens, 128 / len + 1 ≤ 256 / len ∧ 256 / len ≤ 256 := by decide

theorem step_down (zP : Addr) (m : Nat) : VG.Proof.MlDsa.AArch64.Arith.zstep false (coeffAddr zP (m + 1)) = coeffAddr zP m := by
  rw [VG.Proof.MlDsa.AArch64.Arith.zstep, ite_eq_right Bool.false_ne_true, ← coeffAddr_next, BitVec.add_sub_cancel]

theorem negZetaTab_of : VG.Proof.MlDsa.AArch64.Arith.TabOf negZetaTab fun k => -VG.Spec.MlDsa.zetas k := fun k _ => negZetaNat_eq k

theorem lays_ok {s₀ : State} {fP zP : Addr} (hw : pR fP ∈ s₀.wr) (hz : pR zP ∈ s₀.rd ++ s₀.wr)
    (hd : (pR zP).Disjoint (pR fP)) :
    ∀ (ls : List Nat) (F : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ VG.Proof.MlDsa.Arith.nttLens) → VG.Proof.MlDsa.AArch64.Arith.NttInv.Chain k ls →
      VG.Proof.MlDsa.AArch64.Arith.Ntt.LI negZetaTab s₀ fP zP F k s →
      WP isa (nttInvLays ls) s fun s' => ∃ k', VG.Proof.MlDsa.AArch64.Arith.Ntt.LI negZetaTab s₀ fP zP (ls.foldl VG.Proof.MlDsa.Arith.nttInvLayer F) k' s'
  | [], F, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, F, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := VG.Proof.MlDsa.AArch64.Arith.NttInv.lens_inv len hlen
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.lay_ok VG.Proof.MlDsa.AArch64.Arith.bflyInv_spec VG.Proof.MlDsa.AArch64.Arith.NttInv.negZetaTab_of hlen false (fun c => 256 / len - 1 - c)
      (fun c hc => by omega)
      (fun c hc => by
        rw [show 256 / len - 1 - c = (256 / len - 1 - (c + 1)) + 1 by omega]
        exact VG.Proof.MlDsa.AArch64.Arith.NttInv.step_down zP _)
      F s hI.x2 (by rw [hI.x3, hk]; rfl) hI.consts hI.poly (by rw [hI.keep.wr]; exact hw)
      (by rw [hI.keep.rd, hI.keep.wr]; exact hz) hd hI.tab) fun s' ⟨⟨hP, hf, hx2, h3⟩, hk'⟩ => ?_)
    exact VG.Proof.MlDsa.AArch64.Arith.NttInv.lays_ok hw hz hd ls _ _ s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf hx2 h3 hk' hd)

theorem chain_inv : VG.Proof.MlDsa.AArch64.Arith.NttInv.Chain 255 VG.Proof.MlDsa.Arith.nttInvLens := by
  simp only [VG.Proof.MlDsa.Arith.nttInvLens, VG.Proof.MlDsa.AArch64.Arith.NttInv.Chain]; decide

/-! ## The multiplication by 8347681 -/

theorem scaleBody_ok (s : State) (hc : Consts s) (h : InRegions (s.rd ++ s.wr) (s.gpr .x2) 4)
    (w : InRegions s.wr (s.gpr .x2) 4) :
    WP isa (.block scaleBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x2) ((redX (w64 (s.mem.readW (s.gpr .x2) 32) * s.gpr .x6)).setWidth 32) ∧
        s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 4 ∧ s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1) ∧
      Keep [.x2, .x5, .x12, .x13] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold scaleBody reduce Impl.MlKem.AArch64.csub
  arun [h, w, hc.x9, hc.x10, hc.x11, redX, csubX]

/-- After `i` coefficients of `G` multiplied by 8347681, from the state `sL`. -/
structure SInv (sL : State) (fP : Addr) (G : Poly) (i : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = coeffAddr fP i
  x6 : s.gpr .x6 = BitVec.ofNat 64 (8347681 : Zq).val
  consts : Consts s
  frame : Frame [pR fP] sL.mem s.mem
  coeff : ∀ k < 256, (coeffAt s.mem fP k).toNat = if k < i then (G[k]! * 8347681).val else (G[k]!).val
  keep : Keep [.x2, .x5, .x6, .x12, .x13] sL s

theorem scale_step {sL : State} {fP : Addr} {G : Poly} (hw : pR fP ∈ sL.wr) {i : Nat} (hi : i < 256)
    {s : State} (hI : VG.Proof.MlDsa.AArch64.Arith.NttInv.SInv sL fP G i s) :
    WP isa (.block scaleBody) s fun s' => VG.Proof.MlDsa.AArch64.Arith.NttInv.SInv sL fP G (i + 1) s' ∧
      s'.gpr .x5 = s.gpr .x5 - BitVec.ofNat 64 1 := by
  have hw' : pR fP ∈ s.wr := by rw [hI.keep.wr]; exact hw
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.NttInv.scaleBody_ok s hI.consts
    (by rw [hI.x2]; exact ⟨_, List.mem_append_right _ hw', coeff_contains _ hi⟩)
    (by rw [hI.x2]; exact ⟨_, hw', coeff_contains _ hi⟩)) fun s' ⟨⟨hm, hx2, hx5⟩, hk⟩ => ⟨?_, hx5⟩
  have hv : ((redX (w64 (coeffAt s.mem fP i) * s.gpr .x6)).setWidth 32).toNat = (G[i]! * 8347681).val := by
    rw [hI.x6]
    exact redX_mul (x := G[i]!) (by rw [hI.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]) |>.trans
      (by rw [val_mul, val_mul, Nat.mul_comm])
  rw [hI.x2, ← coeffAt_eq] at hm
  refine ⟨by rw [hx2, hI.x2, coeffAddr_next], by rw [hk.get .x6, hI.x6],
    ⟨by rw [hk.get .x9, hI.consts.x9], by rw [hk.get .x10, hI.consts.x10], by rw [hk.get .x11, hI.consts.x11]⟩,
    by rw [hm]; exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hi),
    fun k hk' => ?_, (hI.keep.trans hk).mono⟩
  rw [hm, coeffAt_writeW _ _ hk' hi]
  by_cases e : i = k
  · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]; exact hv
  · rw [ite_eq_right e, hI.coeff k hk']
    by_cases h : k < i
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem scalePro_ok (s : State) :
    WP isa (.block (movW .x6 (BitVec.ofNat 32 8347681) ++ ([.movz .x .x5 256 0] : List Instr))) s fun s' =>
      (s'.gpr .x6 = BitVec.ofNat 64 (8347681 : Zq).val ∧ s'.gpr .x5 = BitVec.ofNat 64 256 ∧ s'.mem = s.mem) ∧
        Keep [.x6, .x5] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (movW_ok .x6 _ s) fun s₁ ⟨⟨h6, hm⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x5] (Q := fun s => s.gpr .x5 = BitVec.ofNat 64 256 ∧ s.mem = s₁.mem) (by arun)
    (by decide)) fun s₂ ⟨⟨h5, hm₂⟩, k₂⟩ => ⟨⟨?_, h5, by rw [hm₂, hm]⟩, (k₁.trans k₂).mono⟩
  rw [k₂.get .x6, h6]
  decide

/-- The multiplication of every coefficient by 8347681. -/
theorem scale_ok {fP : Addr} {G : Poly} (sL : State) (hx2 : sL.gpr .x2 = fP) (hc : Consts sL)
    (hG : PolyIs sL.mem fP G) (hw : pR fP ∈ sL.wr) :
    WP isa (.seq (.block (movW .x6 (BitVec.ofNat 32 8347681) ++ ([.movz .x .x5 256 0] : List Instr)))
        (.loop (.block scaleBody) (.nonzero .x .x5))) sL fun s' =>
      PolyIs s'.mem fP (G.map (· * 8347681)) ∧ Frame [pR fP] sL.mem s'.mem ∧
        Keep [.x6, .x5, .x2, .x5, .x6, .x12, .x13] sL s' := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Arith.NttInv.scalePro_ok sL) fun s3 ⟨⟨h63, h53, hm3⟩, k3⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x5) (N := 256) (by decide) (by decide) (VG.Proof.MlDsa.AArch64.Arith.NttInv.SInv s3 fP G)
    (fun i hi s hI _ => VG.Proof.MlDsa.AArch64.Arith.NttInv.scale_step (by rw [k3.wr]; exact hw) hi hI)
    ⟨by rw [k3.get .x2, hx2, coeffAddr, Nat.mul_zero, BitVec.add_zero], h63,
      ⟨by rw [k3.get .x9, hc.x9], by rw [k3.get .x10, hc.x10], by rw [k3.get .x11, hc.x11]⟩,
      Frame.refl _ _, fun k hk => by rw [ite_eq_right (Nat.not_lt_zero _), hm3]; exact polyIs_toNat hG hk,
      Keep.refl _ _⟩ h53) fun s' hI => ⟨?_, by rw [← hm3]; exact hI.frame, (k3.trans hI.keep).mono⟩
  refine polyIs_of_toNat fun k hk => ?_
  rw [hI.coeff k hk, ite_eq_left hk, VG.Proof.MlDsa.Arith.map_mul_get _ _ hk]

end NttInv

theorem nttInv_noCalls : Impl.MlDsa.AArch64.Arith.nttInv.noCalls = true := by lit_decide

theorem nttInv_correct (s : State) (hs : (inPlaceK VG.Spec.MlDsa.nttInv).pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Arith.nttInv s t s' ∧ abiPreserved s s' ∧
      (inPlaceK VG.Spec.MlDsa.nttInv).post s s' := by
  have hw : pR (s.gpr .x0) ∈ s.wr := by rw [hs.2.1]; simp
  have hz : pR (s.gpr .x1) ∈ s.rd ++ s.wr := by rw [hs.1, hs.2.1]; simp
  obtain ⟨t, s', he, hP⟩ := WP.seq (M := isa) (Q := fun s' =>
      PolyIs s'.mem (s.gpr .x0) (VG.Spec.MlDsa.nttInv (polyAt s.mem (s.gpr .x0))))
    (WP.mono (Ntt.pro_ok hs negZetaTab 255 (by decide)) fun s1 hI =>
      WP.seq (WP.mono (NttInv.lays_ok hw hz hs.2.2.1.symm VG.Proof.MlDsa.Arith.nttInvLens _ 255 s1 (fun _ h => by
        simp only [VG.Proof.MlDsa.Arith.nttInvLens, VG.Proof.MlDsa.Arith.nttLens, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)
          NttInv.chain_inv hI) fun s2 ⟨k, hI2⟩ =>
      WP.mono (NttInv.scale_ok s2 hI2.x2 hI2.consts hI2.poly (by rw [hI2.keep.wr]; exact hw))
        fun s' ⟨hP, _, _⟩ => by rw [VG.Proof.MlDsa.Arith.nttInv_eq_layers]; exact hP))
  exact ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of VG.Proof.MlDsa.AArch64.Arith.nttInv_noCalls (by lit_decide) he, hP⟩

theorem nttInv_ct :
    ConstantTime isa (inPlaceK VG.Spec.MlDsa.nttInv).pre (inPlaceK VG.Spec.MlDsa.nttInv).pub Impl.MlDsa.AArch64.Arith.nttInv :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1]) VG.Proof.MlDsa.AArch64.Arith.inPlace_agree (by taint_decide)

theorem nttInv_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Arith.nttInv (Spec.MlDsa.nttInvContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Arith.nttInv_correct VG.Proof.MlDsa.AArch64.Arith.nttInv_ct (by
    mldsa_implies [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      AArch64.abi, AArch64.argRegs] [inPlaceSat] using VG.Proof.MlDsa.AArch64.Arith.inPlaceSat)

end VG.Proof.MlDsa.AArch64.Arith

end
