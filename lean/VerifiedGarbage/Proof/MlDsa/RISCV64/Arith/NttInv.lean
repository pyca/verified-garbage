module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic

/-!
# ML-DSA on RISC-V: `vg_mldsa_inv_ntt`

As `vg_mldsa_ntt` (`Ntt.lean`) and PPC64LE's (`Proof/MlDsa/PPC64LE/Arith/NttInv.lean`),
with the inverse butterflies (`ibfly_ok`, `polyIs_ibfly`), the table of the
negated zetas read from `m = 255` down, and the layers with `len = 2^ℓ`;
then the loop multiplying every coefficient by `8347681 = 256⁻¹ mod q`
(`scaleN`, `SInv`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Arith.NttInv

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Arith
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.RISCV64.Arith
open VG.Proof.MlDsa.RISCV64.Arith.Ntt (F S P Pre Env Env.inW Env.inR Env.inRS bpost_ok lpre_ok sub_low satState)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ ptr_add ptr_ne lsr2 align4_add
  toNat_setWidth64 setWidth64_ofNat kept preserved_sub)

/-! ## Values -/

theorem ibfly_vals (a b z : Zq) :
    ((fixd (BitVec.ofNat 64 a.val + BitVec.ofNat 64 b.val - 8380417)).setWidth 32).toNat = (a + b).val ∧
    ((red (BitVec.ofNat 64 z.val * fixd (BitVec.ofNat 64 a.val - BitVec.ofNat 64 b.val))).setWidth 32).toNat =
      (z * (a - b)).val := by
  have ha := (toNat_val64 a).symm ▸ val_lt a
  have hb := (toNat_val64 b).symm ▸ val_lt b
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_setWidth, fixd_add ha hb, toNat_val64, toNat_val64, ← val_add',
      Nat.mod_eq_of_lt (by have := val_lt (a + b); omega_arith)]
  · have e : fixd (BitVec.ofNat 64 a.val - BitVec.ofNat 64 b.val) = BitVec.ofNat 64 (a - b).val := by
      apply BitVec.eq_of_toNat_eq
      rw [fixd_sub ha hb, toNat_val64, toNat_val64, toNat_val64, val_sub', Nat.add_sub_assoc (Nat.le_of_lt (val_lt b))]
    rw [e, BitVec.toNat_setWidth, red_mul, Nat.mod_eq_of_lt (by have := val_lt (z * (a - b)); omega_arith)]

/-- An inverse butterfly writes `f[j]`, then `f[j + len]`. -/
theorem polyIs_ibfly {m : Mem} {F : Addr} {f : Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) {v₁ v₂ : BitVec 32} (h₁ : v₁.toNat = (f[j]! + f[j + len]!).val)
    (h₂ : v₂.toNat = (z * (f[j]! - f[j + len]!)).val) :
    PolyIs ((m.writeW (coeffAddr F j) v₁).writeW (coeffAddr F (j + len)) v₂) F (bflyInv f j len z) := by
  refine polyIs_of_toNat fun i hi => ?_
  rw [bflyInv_get f hl hj z hi, coeffAt_writeW _ _ hi hj, coeffAt_writeW _ _ hi (by omega_arith)]
  by_cases e2 : j + len = i
  · subst e2; rw [ite_eq_left rfl, ite_eq_right (by omega_arith), ite_eq_left rfl, h₂]
  · rw [ite_eq_right e2, ite_eq_right (Ne.symm e2)]
    by_cases e1 : j = i
    · subst e1; rw [ite_eq_left rfl, ite_eq_left rfl, h₁]
    · rw [ite_eq_right e1, ite_eq_right (Ne.symm e1), polyIs_toNat h hi]

/-! ## The inverse butterfly -/

section
variable {s : State} {x y z c : BitVec 64}

/-- The first part of the inverse butterfly: `f[j] + f[j + len]` stored, and
`f[j] - f[j + len]` reduced in `t0`. -/
def ibfly1 : List Instr :=
  [.load .w .t2 .a2 0, .load .w .t0 .a3 0, .add .t3 .t2 .t0, .sub .t3 .t3 .a6] ++
  fixup .t3 .t4 .a6 ++ [.store .w .t3 .a2 0, .sub .t0 .t2 .t0] ++ fixup .t0 .t4 .a6

/-- The rest: `z · t0` reduced, stored to `f[j + len]`, and on. -/
def ibfly2 : List Instr :=
  [.mul .t0 .a4 .t0] ++ reduce .t0 .t3 ++
  [.store .w .t0 .a3 0, .addi .a2 .a2 4, .addi .a3 .a3 4, .addi .t1 .t1 (-1)]

theorem ibflyBody_eq : ibflyBody = ibfly1 ++ ibfly2 := by
  simp only [ibflyBody, ibfly1, ibfly2, List.append_assoc, List.cons_append, List.nil_append]

theorem ibfly1_ok (h5 : s.gpr .a2 = x) (h6 : s.gpr .a3 = y) (h9 : s.gpr .a6 = 8380417)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4) (oa : InRegions s.wr x 4)
    (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) :
    WP isa (.block ibfly1) s fun s' =>
      s'.gpr .t0 = fixd ((s.mem.readW x 32).setWidth 64 - (s.mem.readW y 32).setWidth 64) ∧
      s'.gpr .a2 = x ∧ s'.gpr .a3 = y ∧ s'.gpr .t1 = s.gpr .t1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = s.gpr .a4 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = 8380417 ∧
      s'.gpr .a7 = s.gpr .a7 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((fixd ((s.mem.readW x 32).setWidth 64 + (s.mem.readW y 32).setWidth 64 -
            8380417)).setWidth 32) := by
  crun [ibfly1, fixup, fixd, kept, h5, h6, h9, ia, ib, oa, ax, ay,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

theorem ibfly2_ok {w : BitVec 64} (h0 : s.gpr .t0 = w) (h5 : s.gpr .a2 = x) (h6 : s.gpr .a3 = y)
    (h7 : s.gpr .a4 = z) (h8 : s.gpr .a5 = 2201172575745) (h9 : s.gpr .a6 = 8380417) (h11 : s.gpr .t1 = c)
    (ob : InRegions s.wr y 4) (ay : y.toNat % 4 = 0) :
    WP isa (.block ibfly2) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = y + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧
      s'.gpr .a7 = s.gpr .a7 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW y ((red (z * w)).setWidth 32) := by
  rw [ibfly2, List.append_assoc]
  refine WP.block_append ?_
  crun [h0, h7]
  refine reduce_ok (by decide) (by decide) (by decide) (by simp [h8]) (by simp [h9])
    fun s' k => ?_
  have g := k.other
  crun [kept, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h0, h5, h6, h7, h8, h9, h11, ob, ay,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW]

theorem ibfly_ok (h5 : s.gpr .a2 = x) (h6 : s.gpr .a3 = y) (h7 : s.gpr .a4 = z) (h8 : s.gpr .a5 = 2201172575745)
    (h9 : s.gpr .a6 = 8380417) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr y 4) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) :
    WP isa (.block ibflyBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = y + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧
      s'.gpr .a7 = s.gpr .a7 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW x ((fixd ((s.mem.readW x 32).setWidth 64 + (s.mem.readW y 32).setWidth 64 -
            8380417)).setWidth 32)).writeW y
          ((red (z * fixd ((s.mem.readW x 32).setWidth 64 - (s.mem.readW y 32).setWidth 64))).setWidth 32) := by
  rw [ibflyBody_eq, WP.block_append_iff]
  refine WP.mono (ibfly1_ok h5 h6 h9 ia ib oa ax ay)
    fun s₁ ⟨r0, r5, r6, r11, r3, r4, r7, r8, r9, r10, kp, rd, wr, sp, m⟩ => ?_
  refine WP.mono (ibfly2_ok r0 r5 r6 (r7.trans h7) (r8.trans h8) r9 (r11.trans h11) (by rw [wr]; exact ob) ay)
    fun s' ⟨q5, q6, q11, q3, q4, q7, q8, q9, q10, qk, qrd, qwr, qsp, qm⟩ =>
      ⟨q5, q6, q11, q3.trans r3, q4.trans r4, q7, q8, q9, q10.trans r10,
        fun r hr => (qk r hr).trans (kp r hr), qrd.trans rd, qwr.trans wr, qsp.trans sp, by
          rw [qm, m]⟩

end

/-! ## Loops -/

/-- What the setup leaves in memory `m₁`. -/
structure Setup (s₀ : State) (m₁ : Mem) : Prop where
  tab : ∀ j < 256, m₁.readW (S s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (negZetaTab j)
  poly : PolyIs m₁ (F s₀) (P s₀)

/-- After `t` inverse butterflies of the block from `st` with the zeta
`-zetas k` of the layer with `len`, from `Q`: the zeta pointer is at
`k - 1`. -/
structure FInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len k st : Nat) (t : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (k - 1))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  a3 : s.gpr .a3 = F s₀ + BitVec.ofNat 64 (4 * (st + len + t))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (-zetas k).val
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (len - t)
  poly : PolyIs s.mem (F s₀) (blockN bflyInv Q len (-zetas k) st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {Q : Poly} {len k st t : Nat} (hl : 0 < len)
    (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ Q len k st t s) :
    WP isa (.block ibflyBody) s fun s' =>
      FInv s₀ m₁ Q len k st (t + 1) s' ∧ (s'.gpr .t1 != 0) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + len + t)) = coeffAddr (F s₀) (st + t + len) := by
    rw [show st + len + t = st + t + len by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := polyIs_toNat h.poly (i := st + t) (by rw [n_eq]; omega_arith)
  have vb := polyIs_toNat h.poly (i := st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (ibfly_ok h.a2 h.a3 h.a4 h.env.a5 h.env.a6 h.t1
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb)
    (align4_add hp.alF _) (align4_add hp.alF _))
    fun s' ⟨r5, r6, r11, r3, r4, r7, r8, r9, r10, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, fun r hr => (kp r hr).trans (h.env.kept r hr),
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, ?_, r7,
        r10.trans h.a7, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ ca).writeW (List.mem_singleton_self _) _ cb
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r6, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub ht
  · have hv : ∀ {v : BitVec 32} {x : Zq}, v.toNat = x.val → v.setWidth 64 = BitVec.ofNat 64 x.val := fun hv => by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_setWidth64, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt ‹Zq›; omega_arith)]
    rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, hv va, hv vb, blockN_succ]
    exact polyIs_ibfly h.poly hl (by rw [n_eq]; omega_arith) _ (ibfly_vals _ _ (-zetas k)).1 (ibfly_vals _ _ (-zetas k)).2
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub ht]
    exact count_nz ht (by omega_arith)

/-! ## Blocks -/

section
variable {s : State} {x4 x5 x10 : BitVec 64}

/-- The start of a block: its zeta, the pointer to the second half, the count. -/
theorem bpre_ok (h4 : s.gpr .a1 = x4) (h5 : s.gpr .a2 = x5) (h10 : s.gpr .a7 = x10)
    (i4 : InRegions (s.rd ++ s.wr) x4 4) (a4 : x4.toNat % 4 = 0) :
    WP isa (.block [.load .w .a4 .a1 0, .addi .a1 .a1 (-4), .add .a3 .a2 .a7, .shift .srl .d .t1 .a7 2]) s
      fun s' => s'.gpr .a4 = (s.mem.readW x4 32).setWidth 64 ∧ s'.gpr .a1 = x4 - 4 ∧
        s'.gpr .a3 = x5 + x10 ∧ s'.gpr .t1 = x10 >>> 2 ∧ s'.gpr .a2 = x5 ∧ s'.gpr .a7 = x10 ∧
        s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h4, h5, h10, i4, a4, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.readW, Mem.read]

end

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (2 * nb - 1 - c))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  poly : PolyIs s.mem (F s₀) (layerN bflyInv Q len (fun c => -zetas (256 / len - 1 - c)) c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (hl : 0 < len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttInvBlockCode s fun s' =>
      BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .t0 != 0) = decide (c + 1 ≠ nb) := by
  have hdiv : 256 / len = 2 * nb := by
    rw [show 256 = len * (2 * nb) by rw [Nat.mul_left_comm, hnb], Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  have hnb1 : nb ≤ 128 := by
    have : nb ≤ len * nb := Nat.le_mul_of_pos_left nb hl
    omega_arith
  have hk : 2 * nb - 1 - c < 256 := by omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (2 * nb - 1 - c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (2 * nb - 1 - c))) 32).setWidth 64 =
      BitVec.ofNat 64 (-zetas (256 / len - 1 - c)).val := by
    have ez : negZetaTab (2 * nb - 1 - c) = (-zetas (2 * nb - 1 - c)).val := negZetaNat_eq _
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, hdiv, ez, setWidth64_ofNat (by have := val_lt (-zetas (2 * nb - 1 - c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok h.a1 h.a2 h.a7 (h.env.inRS hp cS)
    (align4_add (by have := hp.alS; omega) _))
    fun s₁ ⟨r7, r4, r6, r11, r5, r10, r3, r8, r9, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : FInv s₀ m₁ (layerN bflyInv Q len (fun c => -zetas (256 / len - 1 - c)) c) len
      (256 / len - 1 - c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6,
      fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, ?_, ?_, ?_, r10, ?_,
      m ▸ h.poly⟩
    · rw [r4, hdiv, show 4 * (2 * nb - 1 - c) = 4 * (2 * nb - 1 - c - 1) + 4 by omega_arith, BitVec.ofNat_add,
        ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [r7, vz]
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_nz (FInv s₀ m₁ (layerN bflyInv Q len (fun c => -zetas (256 / len - 1 - c)) c) len
    (256 / len - 1 - c) (2 * len * c)) hl (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.a3) fun s' ⟨r5, r0, r3, r4, r8, r9, r10, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, r10.trans h₂.a7, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, hdiv, show 2 * nb - 1 - c - 1 = 2 * nb - 1 - (c + 1) by omega_arith]
  · rw [r5]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, layerN_succ]; exact h₂.poly
  · rw [r0, h₂.env.a0, ptr_ne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- The first `ℓ` layers of `NTT⁻¹`. -/
def nttInvL (ℓ : Nat) (w : Poly) : Poly := (nttInvLens.take ℓ).foldl nttInvLayer w

theorem nttInvL_succ (w : Poly) {ℓ : Nat} (hℓ : ℓ < 8) :
    nttInvL (ℓ + 1) w = nttInvLayer (nttInvL ℓ w) (2 ^ ℓ) := by
  have e : nttInvLens[ℓ]'(by simp [nttInvLens]; omega_arith) = 2 ^ ℓ := by
    revert ℓ; decide
  unfold nttInvL
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simp [nttInvLens]; omega_arith), e]
  rfl

theorem nttInv_eq_nttInvL (w : Poly) : nttInv w = (nttInvL 8 w).map (· * 8347681) := by
  rw [nttInv_eq_layers]; rfl

/-- What the layers' loop counters are: layer `ℓ` has `len = 2^ℓ` and
`128 >>> ℓ` blocks. -/
theorem layer_facts : ∀ ℓ < 8, 0 < 2 ^ ℓ ∧ 2 ^ ℓ * (128 >>> ℓ) = 128 ∧ 0 < 128 >>> ℓ ∧
    2 * (128 >>> ℓ) - 1 - (128 >>> ℓ) = 256 >>> (ℓ + 1) - 1 ∧ 2 * (128 >>> ℓ) = 256 >>> ℓ ∧
    128 / 2 ^ ℓ = 128 >>> ℓ ∧
    BitVec.ofNat 64 (4 * 2 ^ ℓ) <<< 1 = BitVec.ofNat 64 (4 * 2 ^ (ℓ + 1)) ∧
    (BitVec.ofNat 64 (4 * 2 ^ (ℓ + 1)) - 1024 != 0) = decide (ℓ + 1 ≠ 8) := by
  decide

section
variable {s : State} {x10 : BitVec 64}

theorem lpost_ok (h10 : s.gpr .a7 = x10) :
    WP isa (.block [.shift .sll .d .a7 .a7 1, .addi .t0 .a7 (-1024)]) s fun s' =>
      s'.gpr .a7 = x10 <<< 1 ∧ s'.gpr .t0 = x10 <<< 1 - 1024 ∧ s'.gpr .a0 = s.gpr .a0 ∧
        s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .a6 = s.gpr .a6 ∧
        (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  crun [kept, h10, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

end

/-- After `ℓ` layers. -/
structure LInv (s₀ : State) (m₁ : Mem) (ℓ : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (256 >>> ℓ - 1))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * 2 ^ ℓ)
  poly : PolyIs s.mem (F s₀) (nttInvL ℓ (P s₀))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 8) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttInvLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .t0 != 0) = decide (ℓ + 1 ≠ 8) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.a0)
    fun s₁ ⟨r5, r3, r4, r8, r9, r10, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (nttInvL ℓ (P s₀)) (2 ^ ℓ) (128 >>> ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.a5, r9.trans h.env.a6, fun r hr => (kp r hr).trans (h.env.kept r hr),
      rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.a1, Nat.sub_zero, f5], ?_, r10.trans h.a7, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_nz (BInv s₀ m₁ (nttInvL ℓ (P s₀)) (2 ^ ℓ) (128 >>> ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.a7) fun s' ⟨r10, r0, r3, r4, r8, r9, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, f4]
  · rw [r10, f7]
  · rw [m, nttInvL_succ _ hℓ]
    exact (congrArg (fun b => PolyIs s₂.mem (F s₀) (layerN bflyInv (nttInvL ℓ (P s₀)) (2 ^ ℓ)
      (fun c => -zetas (256 / 2 ^ ℓ - 1 - c)) b)) f6).mpr h₂.poly
  · rw [r0, f7, f8]

/-! ## The scaling by `256⁻¹` -/

/-- The first `i` coefficients of `w` multiplied by `8347681`. -/
def scaleN (w : Poly) (i : Nat) : Poly := (List.range i).foldl (fun w j => w.set! j (w[j]! * 8347681)) w

theorem scaleN_get (w : Poly) : ∀ i ≤ n, ∀ j < n, (scaleN w i)[j]! = if j < i then w[j]! * 8347681 else w[j]!
  | 0, _, j, _ => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | i + 1, hi, j, hj => by
    have ih := scaleN_get w i (by omega_arith)
    rw [show scaleN w (i + 1) = (scaleN w i).set! i ((scaleN w i)[i]! * 8347681) from foldl_range_succ _ _ _]
    by_cases e : i = j
    · subst e; rw [getElem!_set!_self _ hj, ih i hj, ite_eq_right (Nat.lt_irrefl i), ite_eq_left (Nat.lt_succ_self i)]
    · rw [getElem!_set!_ne _ hj e, ih j hj]
      by_cases hji : j < i
      · rw [ite_eq_left hji, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hji, ite_eq_right (by omega_arith)]

theorem scaleN_full (w : Poly) : scaleN w 256 = w.map (· * 8347681) :=
  ext_getElem! fun j hj => by rw [scaleN_get w 256 (by rw [n_eq]) j hj, ite_eq_left (by rw [n_eq] at hj; exact hj),
    map_mul_get _ _ hj]

theorem scaleN_zero (w : Poly) : scaleN w 0 = w := rfl

/-- A reduced value times `8347681`, reduced. -/
theorem scale_val (a : Zq) :
    ((red (BitVec.ofNat 64 a.val * BitVec.ofNat 64 8347681)).setWidth 32).toNat = (a * 8347681).val := by
  have e : (BitVec.ofNat 64 8347681 : BitVec 64) = BitVec.ofNat 64 (ofNat 8347681 : Zq).val := by
    rw [ofNat_of_lt (by decide)]
  rw [e, BitVec.toNat_setWidth, red_mul]
  exact Nat.mod_eq_of_lt (by have := val_lt (a * ofNat 8347681); omega_arith)

/-- After `i` coefficients of `w` scaled. -/
structure SInv (s₀ : State) (m₁ : Mem) (w : Poly) (i : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * i)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8347681
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  poly : PolyIs s.mem (F s₀) (scaleN w i)

section
variable {s : State} {x c : BitVec 64}

theorem scale_ok {k : BitVec 64} (h5 : s.gpr .a2 = x) (h7 : s.gpr .a4 = k) (h8 : s.gpr .a5 = 2201172575745)
    (h9 : s.gpr .a6 = 8380417) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (oa : InRegions s.wr x 4) (ax : x.toNat % 4 = 0) :
    WP isa (.block scaleBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a4 = s.gpr .a4 ∧
      s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((red ((s.mem.readW x 32).setWidth 64 * k)).setWidth 32) := by
  rw [show scaleBody = ([.load .w .t2 .a2 0, .mul .t2 .t2 .a4] : List Instr) ++ (reduce .t2 .t3 ++
      ([.store .w .t2 .a2 0, .addi .a2 .a2 4, .addi .t1 .t1 (-1)] : List Instr)) by
    simp only [scaleBody, List.cons_append, List.nil_append]]
  refine WP.block_append ?_
  crun [h5, h7, ia, ax]
  refine reduce_ok (by decide) (by decide) (by decide) (by simp [h8]) (by simp [h9])
    fun s' k => ?_
  have g := k.other
  crun [kept, k.gpr, g, k.mem, k.rd, k.wr, k.sp, h5, h7, h8, h9, h11, oa, ax,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

theorem sstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {w : Poly} {i : Nat} (hi : i < 256) {s : State}
    (h : SInv s₀ m₁ w i s) :
    WP isa (.block scaleBody) s fun s' => SInv s₀ m₁ w (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have ca := coeff_contains (F s₀) (i := i) (by rw [n_eq]; omega_arith)
  have va := polyIs_toNat h.poly (i := i) (by rw [n_eq]; omega_arith)
  refine WP.mono (scale_ok h.a2 h.a4 h.env.a5 h.env.a6 h.t1 (h.env.inR hp ca) (h.env.inW hp ca)
    (align4_add hp.alF _))
    fun s' ⟨r5, r11, r3, r7, r8, r9, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, fun r hr => (kp r hr).trans (h.env.kept r hr), 
        rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, ?_, r7.trans h.a4, ?_, ?_⟩, ?_⟩
  · rw [m]; exact h.env.frame.writeW (List.mem_singleton_self _) _ ca
  · rw [r5]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub hi
  · have hv : (s.mem.readW (coeffAddr (F s₀) i) 32).setWidth 64 = BitVec.ofNat 64 ((scaleN w i)[i]!).val := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_setWidth64, ← coeffAt_eq, va, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := val_lt (scaleN w i)[i]!; omega_arith)]
    rw [m, show F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i from rfl, hv,
      show scaleN w (i + 1) = (scaleN w i).set! i ((scaleN w i)[i]! * 8347681) from foldl_range_succ _ _ _]
    exact polyIs_writeW h.poly (by rw [n_eq]; omega_arith) _ (scale_val ((scaleN w i)[i]!))
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by omega_arith)

/-! ## Setup -/

/-- The table stored in `scratch`. -/
theorem setup_base {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table negZetaTab .a1)) s₀ fun s =>
      Setup s₀ s.mem ∧ (∀ r, r ≠ .t2 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
        s.sp = s₀.sp := by
  have fS := hp.fitS
  have wS : ∀ {o k : Nat}, o + k ≤ 1024 → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 o) k := fun h => by
    rw [hp.wr]; exact ⟨_, by simp, Offset.contains_base _ h (by omega_arith)⟩
  have a8 : (s₀.gpr .a1).toNat % 8 = 0 := hp.alS
  refine WP.mono (table_ok negZetaTab negZetaTab_lt (b := .a1) (by decide) rfl
    (by omega) fun k hk => wS (by omega_arith)) fun s₂ h₂ => ?_
  have fr : Frame [polyRegion (S s₀)] s₀.mem s₂.mem := by
    refine h₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    rw [List.mem_singleton] at hr; subst hr
    exact sub_low _ (by omega_arith)
  exact ⟨⟨fun j hj => h₂.tab j hj, polyIs_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.disj) ⟨hp.red, rfl⟩⟩,
    h₂.gpr, h₂.rd, h₂.wr, h₂.sp⟩

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ ([.addi .a0 .a0 1024, .addi .a1 .a1 1020, .li .a7 4] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1024 ∧ s'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 1020 ∧
        s'.gpr .a5 = 2201172575745 ∧ s'.gpr .a6 = 8380417 ∧ s'.gpr .a7 = 4 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [consts, loadM_eq, loadImm_q, List.cons_append, List.nil_append]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table negZetaTab .a1 ++ consts ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 1020, .li .a7 4] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r10, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .a0 (by decide)], r8, r9, fun r hr => ?_, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩,
    by rw [r4, e .a1 (by decide)]; rfl, r10, m ▸ hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide)]

/-- The block between the layers and the scaling: `a4 = 8347681`, `a2 = f`, the count. -/
theorem mid_ok {s : State} :
    WP isa (.block (loadImm .a4 8347681 ++ ([.addi .a2 .a0 (-1024), .li .t1 256] : List Instr))) s
      fun s' => s'.gpr .a4 = BitVec.ofNat 64 8347681 ∧ s'.gpr .a2 = s.gpr .a0 - 1024 ∧
        s'.gpr .t1 = BitVec.ofNat 64 256 ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a5 = s.gpr .a5 ∧
        s'.gpr .a6 = s.gpr .a6 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [loadImm_inv, List.cons_append, List.nil_append]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

/-! ## Correctness -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (F s₀) (Spec.MlDsa.nttInv (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => ?_)
  refine WP.seq (wp_loop_nz (LInv s₀ s₁.mem) (N := 8) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s h => ?_) h₁)
  refine WP.seq (WP.mono mid_ok fun s₂ ⟨r7, r5, r11, r3, r8, r9, kp, m, rd, wr, sp⟩ => ?_)
  refine wp_loop_nz (SInv s₀ s₁.mem (nttInvL 8 (P s₀))) (N := 256) (by decide)
    (fun i hi s h => sstep hp hi h) (fun s' h' => ⟨fun r hr => h'.env.kept r (preserved_sub r hr), h'.env.sp,
      h'.env.kept .ra (by decide), by rw [nttInv_eq_nttInvL, ← scaleN_full]; exact h'.poly⟩) ?_
  refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6,
    fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
    wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, ?_, r7, r11, ?_⟩
  · rw [r5, h.env.a0, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
  · rw [m, scaleN_zero]; exact h.poly

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.nttInvContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem verified : Verified RISCV64.target nttInv (Spec.MlDsa.nttInvContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlKem.RISCV64.Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs]
    exact h
  · sig_pub [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Arith.NttInv
