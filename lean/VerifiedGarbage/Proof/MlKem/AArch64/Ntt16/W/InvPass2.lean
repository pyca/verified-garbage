module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvPass2
public import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass1
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM's 16-bit inverse NTT on AArch64, of a polynomial stored with 16 bits: pass 2

`invPass2BodyW` (chunks `c < 4`): the rows of chunk `c` from `scratch`
(`i2_loadsOf`), the last three layers of the inverse (`ip2_arith`), and each
row times 3303, reduced to `[0, q)` (`scale_ok`) and stored into `f` as eight
16-bit coefficients (`scale_rowsW`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16
open Impl.MlKem.AArch64.Ntt16

section
variable {rest : List Instr} {Q : State → Prop}

/-- The rows of chunk `c` (lanes `X (32r + 8c + e)`) times 3303, reduced to `[0, q)` and
stored into `f` with 16-bit coefficients. -/
theorem scale_rowsW {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < 4) {s : State} (st : St s₀ s)
    (hx3 : s.gpr .x3 = fP s₀ + BitVec.ofNat 64 (16 * c)) {X : Nat → Zq}
    (hrows : ∀ r < 8, Rep (s.v (row r)) (fun e => X (32 * r + 8 * c + e)) (2 * 3329))
    (hz : Cst (s.v .v22) fun _ => 3303) (ht : Cst (s.v .v23) fun _ => tw 3303)
    (hq : Cst (s.v .v31) fun _ => 3329) {old : Nat → BitVec 16}
    (hout : CoeffsInW s.mem (fP s₀) (fun i => i % 32 < 8 * c)
      (fun i => BitVec.ofNat 16 (X i * 3303).val) old)
    (k : ∀ s', s'.gpr = s.gpr → St s₀ s' → (∀ r, r ≠ .v16 → r ≠ .v17 → s'.v r = s.v r) →
      Frame [fR s₀] s.mem s'.mem →
      CoeffsInW s'.mem (fP s₀) (fun i => i % 32 < 8 * (c + 1))
        (fun i => BitVec.ofNat 16 (X i * 3303).val) old → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).flatMap fun r =>
      [.vop (.mulH .mul .v16 (row r) .v22), .vop (.mulH .sqrdmulh .v17 (row r) .v23),
       .vop (.mulH .mls .v16 .v17 .v31), .vop (.shift .sshr .h8 .v17 .v16 15),
       .vop (.logic .and .v17 .v17 .v31), .vop (.add .h8 .v16 .v16 .v17),
       .strq .v16 .x3 (64 * r)]) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun n w => w.gpr = s.gpr ∧ w.rd = s.rd ∧
      w.wr = s.wr ∧ w.sp = s.sp ∧ (∀ r, r ≠ .v16 → r ≠ .v17 → w.v r = s.v r) ∧
      Frame [fR s₀] s.mem w.mem ∧
      CoeffsInW w.mem (fP s₀) (fun i => i % 32 < 8 * c ∨ (i / 32 < n ∧ i % 32 < 8 * c + 8))
        (fun i => BitVec.ofNat 16 (X i * 3303).val) old)
    (fun r w hr ⟨g, rd, wr, sp, v, fr, co⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _, hout.congr fun i _ => by omega⟩)
    fun w ⟨g, rd, wr, sp, v, fr, co⟩ =>
      k w g ⟨by rw [rd, st.rd], by rw [wr, st.wr], by rw [sp, st.sp], by rw [g, st.x0],
        by rw [g, st.x1]⟩ v fr (co.congr fun i hi => by omega)
  have st' : St s₀ w := ⟨by rw [rd, st.rd], by rw [wr, st.wr], by rw [sp, st.sp],
    by rw [g, st.x0], by rw [g, st.x1]⟩
  have nr := row_ne hr
  refine scale_ok (x := row r) nr.1 (by rw [v _ nr.1 nr.2.1]; exact hrows r hr) (by decide)
    (by rw [v .v22 (by decide) (by decide)]; exact hz)
    (by rw [v .v23 (by decide) (by decide)]; exact ht)
    (by rw [v .v31 (by decide) (by decide)]; exact hq) fun w₀ c₀ hv => ?_
  have st₀ : St s₀ w₀ := st'.vchg c₀
  refine wp_strq (a := fP s₀ + BitVec.ofNat 64 (2 * (32 * r + 8 * c))) (by omega)
    (by rw [c₀.gpr, g, hx3, ptr_add]; congr 2; omega)
    (by rw [c₀.wr]; exact inF hp st' (by omega)) fun w₁ h₁ => wp_nil ?_
  have hvl : ∀ e < 8, (X (32 * r + 8 * c + e) * 3303).val < 2 ^ 16 := fun e _ => by
    have := val_lt (X (32 * r + 8 * c + e) * 3303); omega
  refine ⟨by rw [h₁.gpr, c₀.gpr, g], by rw [h₁.rd, c₀.rd, rd], by rw [h₁.wr, c₀.wr, wr],
    by rw [h₁.sp, c₀.sp, sp], fun x a1 a2 => by rw [h₁.v, c₀.v x (by simp [a1, a2]), v x a1 a2], ?_, ?_⟩
  · rw [h₁.mem, c₀.mem]
    exact fr.write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
  · rw [h₁.mem, c₀.mem]
    refine co.write16 (by omega) (fun e he => ?_) (fun i hi => by omega)
    apply BitVec.eq_of_toNat_eq
    rw [hv e he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hvl e he)]

end

/-! ## A chunk -/

/-- After `c` chunks of pass 2 of the inverse, from the memory `mB` that pass 1 left. -/
structure LI2 (s₀ : State) (mB : Mem) (c : Nat) (s : State) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = sP s₀ + BitVec.ofNat 64 (16 * c)
  x3 : s.gpr .x3 = fP s₀ + BitVec.ofNat 64 (16 * c)
  x5 : (s.gpr .x5).toNat = 4 - c
  frame : Frame [fR s₀] mB s.mem
  scr : ∀ r < 8, ∀ i < 4, Rep (mB.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * i)) 16)
    (fun e => (nttInvL 4 (P₀ s₀))[32 * r + 8 * i + e]!) (2 * 3329)
  out : CoeffsInW s.mem (fP s₀) (fun i => i % 32 < 8 * c)
    (fun i => BitVec.ofNat 16 ((nttInvL 7 (P₀ s₀))[i]! * 3303).val) fun i => coeffAtW 16 mB (fP s₀) i
  z : ∀ k < 8, vhalf (s.v .v18) k = BitVec.ofNat 16 (izc k)
  t : ∀ k < 8, vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (izc k))
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10

theorem ip2_body {s₀ : State} (hp : Pre s₀) {mB : Mem} {c : Nat} (hc : c < 4) {sb : State}
    (h : LI2 s₀ mB c sb) :
    WP isa (.block invPass2BodyW) sb fun s' => LI2 s₀ mB (c + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ c + 1 ≠ 4) := by
  simp only [invPass2BodyW, List.append_assoc]
  refine i2_loadsOf h.x2 (fun r _ => in_rd_wr (inS hp h.st (by omega)))
    (fun r hr => by
      rw [h.frame.read (r := sR s₀) (contains_off (by omega) (by decide))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)]
      exact h.scr r hr c hc)
    fun s₁ c₁ R₁ => ?_
  refine ip2_arith hc R₁ (fun k hk => by rw [c₁.get .v18]; exact h.z k hk)
    (fun k hk => by rw [c₁.get .v19]; exact h.t k hk) (by rw [c₁.get .v31]; exact h.q)
    (by rw [c₁.get .v30]; exact h.c10) fun s₁₁ C' rows z22 t23 => ?_
  have C₁₁ : VChg p2Regs sb s₁₁ := ((c₁.mono (rs' := p2Regs) (by decide)).trans C').mono (by decide)
  have st₁₁ : St s₀ s₁₁ := h.st.vchg C₁₁
  refine scale_rowsW hp hc st₁₁ (by rw [C₁₁.gpr]; exact h.x3)
    (X := fun i => (nttInvL 7 (P₀ s₀))[i]!) rows z22 t23
    (by rw [C₁₁.v .v31 (by decide)]; exact h.q) (by rw [C₁₁.mem]; exact h.out)
    fun w g₁ stw vw fr co => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x5] w w' ∧ w'.mem = w.mem ∧
      w'.gpr .x2 = w.gpr .x2 + BitVec.ofNat 64 16 ∧ w'.gpr .x3 = w.gpr .x3 + BitVec.ofNat 64 16 ∧
      w'.gpr .x5 = w.gpr .x5 - BitVec.ofNat 64 1)
    (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_subImm (by decide) fun w₃ k₃ e₃ =>
        wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono,
          by rw [k₃.mem, k₂.mem, k₁.mem],
          by rw [k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
          by rw [k₃.gpr .x3 (by decide), e₂, k₁.gpr .x3 (by decide)],
          by rw [e₃, k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w' ⟨⟨kw, mw, e2, e3, e5⟩, hv⟩ => ?_
  have gw : w.gpr = sb.gpr := by rw [g₁, C₁₁.gpr]
  have x5' : (w'.gpr .x5).toNat = 4 - (c + 1) := by
    rw [e5, gw, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have vv : ∀ r ∈ [VReg.v18, .v19, .v30, .v31], w'.v r = sb.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hv, vw _ (by decide) (by decide), C₁₁.v _ (by decide)]
  refine ⟨⟨stw.keep kw, by rw [e2, gw, h.x2, ptr_add]; congr 2,
    by rw [e3, gw, h.x3, ptr_add]; congr 2, x5',
    by rw [mw]; exact h.frame.trans (by rw [← C₁₁.mem]; exact fr), h.scr, by rw [mw]; exact co,
    fun k hk => by rw [vv .v18 (by decide)]; exact h.z k hk,
    fun k hk => by rw [vv .v19 (by decide)]; exact h.t k hk,
    by rw [vv .v31 (by decide)]; exact h.q, by rw [vv .v30 (by decide)]; exact h.c10⟩, by rw [x5']; omega⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
