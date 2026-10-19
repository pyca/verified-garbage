module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit

/-!
# ML-KEM on AArch64: `dd10Half`

Two groups of 40 bits, in the doublewords of a register, split into their eight values of ten
bits (`ddSplit_ok`), decompressed and stored (`dd10Half_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.DD (wp_strq2 vword_G)

/-- The value of ten bits `m` of two groups of 40 bits. -/
abbrev dig10 (Gv : Nat → Nat) (m : Nat) : Nat := Gv (m / 4) / 2 ^ (10 * (m % 4)) % 2 ^ 10

theorem dd10Half_ok {s : State} {g : VReg} (hg : g = .v6 ∨ g = .v7) {o : Nat} (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16)
    (hc : DConsts 10 s) (h18 : Lanes (s.v .v18) fun _ => 2 ^ 20 - 1) (h19 : Lanes (s.v .v19) fun _ => 2 ^ 10 - 1)
    {Gv : Nat → Nat} (hG : DLanes (s.v g) Gv) (hGv : ∀ l < 2, Gv l < 2 ^ 40)
    {p : Addr} {m₀ : Mem} {t : Nat} {Gf old : Nat → BitVec 32} {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ht : t + 8 ≤ 256) (hcu : CoeffsUpTo s.mem p t Gf old)
    (hf : Frame [polyRegion p] m₀ s.mem)
    (hval : ∀ m < 8, Gf (t + m) = BitVec.ofNat 32 (df 10 (dig10 Gv m)))
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r, r ≠ g → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) →
      CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (dd10Half g o ++ is)) s Q := by
  have g1 : g ≠ .v1 := by rcases hg with rfl | rfl <;> decide
  have g2 : g ≠ .v2 := by rcases hg with rfl | rfl <;> decide
  have g16 : g ≠ .v16 := by rcases hg with rfl | rfl <;> decide
  have g17 : g ≠ .v17 := by rcases hg with rfl | rfl <;> decide
  have g18 : g ≠ .v18 := by rcases hg with rfl | rfl <;> decide
  have g19 : g ≠ .v19 := by rcases hg with rfl | rfl <;> decide
  unfold dd10Half
  simp only [List.append_assoc]
  refine ddSplit_ok (b := 10) (.inl rfl) h18 h19 hG hGv g1 g2 g18 g19 fun a7 c7 L6 L7 => ?_
  have cs7 : DConsts 10 a7 := hc.chg c7 (by simp [g16.symm]) (by simp [g17.symm])
  have dig_lt : ∀ m, dig 10 Gv m < 2 ^ 10 := fun m => Nat.mod_lt _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v2) (by decide) (by decide) cs7.q cs7.h (by decide) L6
    fun e _ => dig_lt e) fun b1 ⟨d1, r2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decV_ok (v := .v3) (by decide) (by decide) (cs7.chg d1).q (cs7.chg d1).h (by decide)
    (Lanes.chg d1 (by decide) L7) fun e _ => dig_lt _) fun b2 ⟨d2, r3⟩ => ?_
  have c := c7.trans (d1.trans d2)
  simp only [List.cons_append, List.nil_append]
  refine wp_strq2 (by rw [c.wr]; exact hw) (by rw [c.gpr]; exact h3) ho ht (by rw [c.mem]; exact hcu)
    (by rw [c.mem]; exact hf)
    (vword_G (Lanes.chg d2 (by decide) r2) fun e he => by rw [hval e (by omega)])
    (vword_G r3 fun e he => by rw [Nat.add_assoc, hval (4 + e) (by omega)])
    fun s' st o f => k s' (by rw [st.gpr, c.gpr]) (by rw [st.rd, c.rd]) (by rw [st.wr, c.wr])
      (by rw [st.sp, c.sp]) (fun r a b d e => by rw [st.v, c.v r (by simp [a, b, d, e])]) o f

end VG.Proof.MlKem.AArch64.CodecV
