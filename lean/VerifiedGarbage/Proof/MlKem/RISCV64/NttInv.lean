module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Ntt
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic

/-!
# ML-KEM on RISCV64: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Proof/MlKem/RISCV64/Ntt.lean`), whose setup and
invariant of what every loop keeps (`Ntt.Env`) it shares: the layers of
`nttInvLayer`, `nttInvBlock` and `nttInvBlockN` (`Proof/MlKem/Ntt.lean`),
from the last zeta of the table down, then every coefficient times 3303
(`SInv`). Layer `ℓ` has `len = 2 <<< ℓ` and `64 >>> ℓ` blocks.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.NttInv

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Proof.MlKem.RISCV64.Ntt (F S P Pre Setup Env Env.inR Env.inW Env.inRS bpost_ok lpre_ok setup_base
  satState)

/-! ## Values -/

theorem ibfly_vals (a b z : Zq) :
    (fixq (BitVec.ofNat 64 a.val + BitVec.ofNat 64 b.val - 3329)).setWidth 32 = BitVec.ofNat 32 (a + b).val ∧
    (red (BitVec.ofNat 64 z.val * fixq (BitVec.ofNat 64 b.val - BitVec.ofNat 64 a.val))).setWidth 32 =
      BitVec.ofNat 32 (z * (b - a)).val := by
  have ha := (toNat_val64 a).symm ▸ val_lt a
  have hb := (toNat_val64 b).symm ▸ val_lt b
  have e2 : fixq (BitVec.ofNat 64 b.val - BitVec.ofNat 64 a.val) = BitVec.ofNat 64 (b - a).val := by
    apply BitVec.eq_of_toNat_eq
    rw [fixq_sub hb ha, toNat_val64, toNat_val64, toNat_val64, val_sub', Nat.add_sub_assoc (Nat.le_of_lt a.isLt)]
  refine ⟨setWidth32_ofNat ?_ (by have := val_lt (a + b); omega_arith),
    setWidth32_ofNat ?_ (by have := val_lt (z * (b - a)); omega_arith)⟩
  · rw [fixq_add ha hb, toNat_val64, toNat_val64, val_add']
  · rw [e2, red_mul]

/-- An inverse butterfly writes `f[j]`, then `f[j + len]`. -/
theorem polyIs_ibfly {m : Mem} {F : Addr} {f : Poly} (h : PolyIs m F f) {j len : Nat} (hl : 0 < len)
    (hj : j + len < n) (z : Zq) :
    PolyIs ((m.writeW (coeffAddr F j) (BitVec.ofNat 32 (f[j]! + f[j + len]!).val)).writeW
      (coeffAddr F (j + len)) (BitVec.ofNat 32 (z * (f[j + len]! - f[j]!)).val)) F (bflyInv f j len z) := by
  have h1 := polyIs_writeW h (j := j) (by omega_arith) (f[j]! + f[j + len]!)
  have h2 := polyIs_writeW h1 hj (z * (f[j + len]! - f[j]!))
  simp only [bflyInv]
  rwa [getElem!_set!_ne _ hj (by omega_arith)]

/-! ## The inverse butterfly -/

section
variable {s : State} {x y z c : BitVec 64}

theorem ibfly_ok (h5 : s.gpr .a2 = x) (h6 : s.gpr .a3 = y) (h7 : s.gpr .a4 = z) (h8 : s.gpr .a5 = C)
    (h9 : s.gpr .a6 = 3329) (h11 : s.gpr .t1 = c)
    (ia : InRegions (s.rd ++ s.wr) x 4) (ib : InRegions (s.rd ++ s.wr) y 4)
    (oa : InRegions s.wr x 4) (ob : InRegions s.wr y 4) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) :
    WP isa (.block ibflyBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .a3 = y + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a4 = z ∧ s'.gpr .a5 = C ∧ s'.gpr .a6 = 3329 ∧
      s'.gpr .a7 = s.gpr .a7 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = (s.mem.writeW x ((fixq ((s.mem.readW x 32).setWidth 64 + (s.mem.readW y 32).setWidth 64 -
            3329)).setWidth 32)).writeW y
          ((red (z * fixq ((s.mem.readW y 32).setWidth 64 - (s.mem.readW x 32).setWidth 64))).setWidth 32) := by
  crun [ibflyBody, reduce, barrett, subMulQ, fixup, red, bar, quot, fixq, kept, h5, h6, h7, h8, h9, h11,
    ia, ib, oa, ob, ax, ay,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## Butterflies of a block -/

/-- After `t` inverse butterflies of the block from `st` with the zeta
`zeta k` of the layer with `len`, from `Q`, the zeta pointer at `R4`. -/
structure FInv (s₀ : State) (m₁ : Mem) (R4 : BitVec 64) (Q : Poly) (len k st : Nat) (t : Nat) (s : State) :
    Prop where
  env : Env s₀ m₁ s
  a1 : s.gpr .a1 = R4
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (st + t))
  a3 : s.gpr .a3 = F s₀ + BitVec.ofNat 64 (4 * (st + len + t))
  a4 : s.gpr .a4 = BitVec.ofNat 64 (zeta k).val
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (len - t)
  poly : PolyIs s.mem (F s₀) (nttInvBlockN Q len k st t)

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {R4 : BitVec 64} {Q : Poly} {len k st t : Nat}
    (hl : 0 < len) (hs : st + 2 * len ≤ 256) (ht : t < len) {s : State} (h : FInv s₀ m₁ R4 Q len k st t s) :
    WP isa (.block ibflyBody) s fun s' =>
      FInv s₀ m₁ R4 Q len k st (t + 1) s' ∧ (s'.gpr .t1 != 0) = decide (t + 1 ≠ len) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * (st + t)) = coeffAddr (F s₀) (st + t) := rfl
  have eb : F s₀ + BitVec.ofNat 64 (4 * (st + len + t)) = coeffAddr (F s₀) (st + t + len) := by
    rw [show st + len + t = st + t + len by omega_arith]
  have ca := coeff_contains (F s₀) (i := st + t) (by rw [n_eq]; omega_arith)
  have cb := coeff_contains (F s₀) (i := st + t + len) (by rw [n_eq]; omega_arith)
  have va := polyIs_coeffAt h.poly (i := st + t) (by rw [n_eq]; omega_arith)
  have vb := polyIs_coeffAt h.poly (i := st + t + len) (by rw [n_eq]; omega_arith)
  refine WP.mono (ibfly_ok h.a2 h.a3 h.a4 h.env.a5 h.env.a6 h.t1
    (by rw [ea]; exact h.env.inR hp ca) (by rw [eb]; exact h.env.inR hp cb)
    (by rw [ea]; exact h.env.inW hp ca) (by rw [eb]; exact h.env.inW hp cb)
    (align4_add hp.alF _) (align4_add hp.alF _))
    fun s' ⟨r5, r6, r11, r3, r4, r7, r8, r9, r10, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, ?_, r7,
        r10.trans h.a7, ?_, ?_⟩, ?_⟩
  · rw [m, ea, eb]
    exact (h.env.frame.writeW (List.mem_singleton_self _) _ ca).writeW (List.mem_singleton_self _) _ cb
  · rw [r5, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r6, ← Nat.add_assoc]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub ht
  · have hv : ∀ x : Zq, (BitVec.ofNat 32 x.val).setWidth 64 = BitVec.ofNat 64 x.val := fun x =>
      setWidth64_ofNat (by have := val_lt x; omega_arith)
    rw [m, ea, eb, ← coeffAt_eq, ← coeffAt_eq, va, vb, hv, hv, (ibfly_vals _ _ (zeta k)).1,
      (ibfly_vals _ _ _).2, nttInvBlockN_succ]
    exact polyIs_ibfly h.poly hl (by rw [n_eq]; omega_arith) (zeta k)
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

theorem ptr_sub4 (p : BitVec 64) {a : Nat} (ha : 1 ≤ a) :
    p + BitVec.ofNat 64 (4 * a) - 4 = p + BitVec.ofNat 64 (4 * (a - 1)) := by
  rw [show 4 * a = 4 * (a - 1) + 4 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len nb : Nat) (c : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c))
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * (2 * len * c))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * len)
  poly : PolyIs s.mem (F s₀) (nttInvLayerN Q len c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (hl2 : 2 ≤ len) (hnb : len * nb = 128) (hc : c < nb) {s : State} (h : BInv s₀ m₁ Q len nb c s) :
    WP isa nttInvBlockCode s fun s' =>
      BInv s₀ m₁ Q len nb (c + 1) s' ∧ (s'.gpr .t0 != 0) = decide (c + 1 ≠ nb) := by
  have hl : 0 < len := by omega_arith
  have hdiv : 256 / len = 2 * nb := by
    rw [show 256 = len * (2 * nb) by rw [← Nat.mul_assoc, Nat.mul_comm len 2, Nat.mul_assoc, hnb],
      Nat.mul_div_cancel_left _ hl]
  have hlc : len * (c + 1) ≤ len * nb := Nat.mul_le_mul_left _ hc
  have e2 : 2 * len * c = 2 * (len * c) := Nat.mul_assoc _ _ _
  rw [Nat.mul_add, Nat.mul_one] at hlc
  have hnb64 : 2 * nb ≤ len * nb := Nat.mul_le_mul_right nb hl2
  have hk : 256 / len - 1 - c < 128 := by omega_arith
  have cS : (polyRegion (S s₀)).Contains (S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c))) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have vz : (s.mem.readW (S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - c))) 32).setWidth 64 =
      BitVec.ofNat 64 (zeta (256 / len - 1 - c)).val := by
    rw [h.env.frame.readW cS (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj.symm)
      (by decide), hm.tab _ hk, zetaTable_eq, zetas_getD hk,
      setWidth64_ofNat (by have := val_lt (zeta (256 / len - 1 - c)); omega_arith)]
  refine WP.seq (WP.mono (bpre_ok h.a1 h.a2 h.a7 (h.env.inRS hp cS)
    (align4_add (by have := hp.alS; omega) _))
    fun s₁ ⟨r7, r4, r6, r11, r5, r10, r3, r8, r9, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have R4 : s₁.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - (c + 1))) := by
    rw [r4, ptr_sub4 _ (by omega_arith), Nat.sub_sub]
  have h₁ : FInv s₀ m₁ (S s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - (c + 1)))) (nttInvLayerN Q len c) len
      (256 / len - 1 - c) (2 * len * c) 0 s₁ := by
    refine ⟨⟨r3.trans h.env.a0, r8.trans h.env.a5, r9.trans h.env.a6,
      fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd,
      wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩, R4, ?_, ?_, ?_, r10, ?_, m ▸ h.poly⟩
    · rw [r5, Nat.add_zero]
    · rw [r6, ptr_add, show 4 * (2 * len * c) + 4 * len = 4 * (2 * len * c + len + 0) by omega_arith]
    · rw [r7, vz]
    · rw [r11, lsr2 (by omega_arith)]
  refine wp_loop_nz (FInv s₀ m₁ _ (nttInvLayerN Q len c) len (256 / len - 1 - c) (2 * len * c)) hl
    (fun t ht s h => fstep hp hl (by omega_arith) ht h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (bpost_ok h₂.a3) fun s' ⟨r5, r0, r3, r4, r8, r9, r10, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, r4.trans h₂.a1, ?_, r10.trans h₂.a7, ?_⟩, ?_⟩
  · rw [r5]; congr 2; rw [Nat.mul_succ]; omega_arith
  · rw [m, nttInvLayerN_succ]; exact h₂.poly
  · rw [r0, h₂.env.a0, ptr_ne _ (by omega_arith) (by omega_arith)]
    refine decide_eq_decide.mpr ⟨fun e e' => e ?_, fun e e' => e ?_⟩
    · subst e'; rw [Nat.mul_add, Nat.mul_one] at *; omega_arith
    · have : len * (c + 1) = len * nb := by rw [Nat.mul_add, Nat.mul_one]; omega_arith
      exact Nat.eq_of_mul_eq_mul_left hl this

/-! ## Layers -/

/-- What the layers' loop counters are. -/
theorem layer_facts : ∀ ℓ < 7, 2 ≤ 2 <<< ℓ ∧ (2 <<< ℓ) * (64 >>> ℓ) = 128 ∧ 0 < 64 >>> ℓ ∧
    256 / (2 <<< ℓ) - 1 - 0 = 128 >>> ℓ - 1 ∧
    256 / (2 <<< ℓ) - 1 - (64 >>> ℓ) = 128 >>> (ℓ + 1) - 1 ∧ 128 / (2 <<< ℓ) = 64 >>> ℓ ∧
    BitVec.ofNat 64 (4 * (2 <<< ℓ)) <<< 1 = BitVec.ofNat 64 (4 * (2 <<< (ℓ + 1))) ∧
    (BitVec.ofNat 64 (4 * (2 <<< (ℓ + 1))) - 1024 != 0) = decide (ℓ + 1 ≠ 7) := by
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
  a1 : s.gpr .a1 = S s₀ + BitVec.ofNat 64 (4 * (128 >>> ℓ - 1))
  a7 : s.gpr .a7 = BitVec.ofNat 64 (4 * (2 <<< ℓ))
  poly : PolyIs s.mem (F s₀) (nttInvL ℓ (P s₀))

theorem lstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {ℓ : Nat} (hℓ : ℓ < 7) {s : State}
    (h : LInv s₀ m₁ ℓ s) :
    WP isa nttInvLayerCode s fun s' => LInv s₀ m₁ (ℓ + 1) s' ∧ (s'.gpr .t0 != 0) = decide (ℓ + 1 ≠ 7) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := layer_facts ℓ hℓ
  refine WP.seq (WP.mono (lpre_ok h.env.a0)
    fun s₁ ⟨r5, r3, r4, r8, r9, r10, kp, m, rd, wr, sp⟩ => WP.seq ?_)
  have h₁ : BInv s₀ m₁ (nttInvL ℓ (P s₀)) (2 <<< ℓ) (64 >>> ℓ) 0 s₁ := by
    refine ⟨⟨r3, r8.trans h.env.a5, r9.trans h.env.a6, fun r hr => (kp r hr).trans (h.env.kept r hr),
      rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, m ▸ h.env.frame⟩,
      by rw [r4, h.a1, f4], ?_, r10.trans h.a7, ?_⟩
    · rw [r5, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, BitVec.add_sub_cancel]; simp
    · rw [m]; exact h.poly
  refine wp_loop_nz (BInv s₀ m₁ (nttInvL ℓ (P s₀)) (2 <<< ℓ) (64 >>> ℓ)) f3
    (fun c hc s h => bstep hp hm f1 f2 hc h) (fun s₂ h₂ => ?_) h₁
  refine WP.mono (lpost_ok h₂.a7) fun s' ⟨r10, r0, r3, r4, r8, r9, kp, m, rd, wr, sp⟩ =>
    ⟨⟨⟨r3.trans h₂.env.a0, r8.trans h₂.env.a5, r9.trans h₂.env.a6,
      fun r hr => (kp r hr).trans (h₂.env.kept r hr), rd.trans h₂.env.rd,
      wr.trans h₂.env.wr, sp.trans h₂.env.sp, m ▸ h₂.env.frame⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [r4, h₂.a1, f5]
  · rw [r10, f7]
  · rw [m, nttInvL_succ _ hℓ, nttInvLayer, f6]
    exact h₂.poly
  · rw [r0, f7, f8]

/-! ## Multiplication by 3303 -/

section
variable {s : State} {x y c : BitVec 64}

theorem scale_ok (h5 : s.gpr .a2 = x) (h7 : s.gpr .a4 = y) (h8 : s.gpr .a5 = C) (h9 : s.gpr .a6 = 3329)
    (h11 : s.gpr .t1 = c) (ia : InRegions (s.rd ++ s.wr) x 4) (oa : InRegions s.wr x 4)
    (ax : x.toNat % 4 = 0) :
    WP isa (.block scaleBody) s fun s' =>
      s'.gpr .a2 = x + 4 ∧ s'.gpr .t1 = c - 1 ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.gpr .a1 = s.gpr .a1 ∧
      s'.gpr .a4 = y ∧ s'.gpr .a5 = C ∧ s'.gpr .a6 = 3329 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW x ((red ((s.mem.readW x 32).setWidth 64 * y)).setWidth 32) := by
  crun [scaleBody, reduce, barrett, subMulQ, fixup, red, bar, quot, fixq, kept, h5, h7, h8, h9, h11, ia, oa,
    ax,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-- After `i` coefficients multiplied by 3303, of `R` in `m₂`. -/
structure SInv (s₀ : State) (m₁ m₂ : Mem) (R : Poly) (i : Nat) (s : State) : Prop where
  env : Env s₀ m₁ s
  a1 : s.gpr .a1 = S s₀
  a2 : s.gpr .a2 = F s₀ + BitVec.ofNat 64 (4 * i)
  a4 : s.gpr .a4 = BitVec.ofNat 64 (3303 : Zq).val
  t1 : s.gpr .t1 = BitVec.ofNat 64 (256 - i)
  coeff : ∀ j < 256, coeffAt s.mem (F s₀) j =
    if j < i then BitVec.ofNat 32 ((R.map (· * 3303))[j]!).val else coeffAt m₂ (F s₀) j

theorem sstep {s₀ : State} (hp : Pre s₀) {m₁ m₂ : Mem} {R : Poly} (hR : PolyIs m₂ (F s₀) R) {i : Nat}
    (hi : i < 256) {s : State} (h : SInv s₀ m₁ m₂ R i s) :
    WP isa (.block scaleBody) s fun s' => SInv s₀ m₁ m₂ R (i + 1) s' ∧ (s'.gpr .t1 != 0) = decide (i + 1 ≠ 256) := by
  have ea : F s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (F s₀) i := rfl
  have ca := coeff_contains (F s₀) (i := i) (by rw [n_eq]; omega_arith)
  have va : coeffAt s.mem (F s₀) i = BitVec.ofNat 32 (R[i]!).val := by
    rw [h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]; exact polyIs_coeffAt hR (by rw [n_eq]; omega_arith)
  refine WP.mono (scale_ok h.a2 h.a4 h.env.a5 h.env.a6 h.t1 (by rw [ea]; exact h.env.inR hp ca)
    (by rw [ea]; exact h.env.inW hp ca) (align4_add hp.alF _))
    fun s' ⟨r5, r11, r3, r4, r7, r8, r9, kp, rd, wr, sp, m⟩ =>
      ⟨⟨⟨r3.trans h.env.a0, r8, r9, fun r hr => (kp r hr).trans (h.env.kept r hr), rd.trans h.env.rd, wr.trans h.env.wr, sp.trans h.env.sp, ?_⟩, r4.trans h.a1, ?_, r7, ?_, ?_⟩, ?_⟩
  · rw [m, ea]; exact h.env.frame.writeW (List.mem_singleton_self _) _ ca
  · rw [r5]; exact ptr_succ _ 4 _
  · rw [r11]; exact count_sub hi
  · rw [m, ea, ← coeffAt_eq, va, setWidth64_ofNat (by have := val_lt R[i]!; omega_arith)]
    refine coeff_one (a := i) hi h.coeff ?_
    rw [map_mul_get _ (by rw [n_eq]; exact hi)]
    exact setWidth32_ofNat red_mul (by have := val_lt (R[i]! * 3303); omega_arith)
  · rw [r11, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

/-! ## Setup, the middle and the end -/

theorem tail_ok {s : State} :
    WP isa (.block (consts ++ ([.addi .a0 .a0 1024, .addi .a1 .a1 508, .li .a7 8] : List Instr))) s
      fun s' => s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 1024 ∧ s'.gpr .a1 = s.gpr .a1 + 508 ∧
        s'.gpr .a5 = C ∧ s'.gpr .a6 = 3329 ∧ s'.gpr .a7 = 8 ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [consts, liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun [kept, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  all_goals decide

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (table zetaTable .a1 ++ consts ++
      ([.addi .a0 .a0 1024, .addi .a1 .a1 508, .li .a7 8] : List Instr))) s₀
      fun s => Setup s₀ s.mem ∧ LInv s₀ s.mem 0 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  refine WP.mono tail_ok fun s ⟨r3, r4, r8, r9, r10, kp, m, rd', wr', sp'⟩ => ?_
  rw [m]
  refine ⟨hm, ⟨⟨by rw [r3, e .a0 (by decide) (by decide)], r8, r9, fun r hr => ?_, rd'.trans rd,
    wr'.trans wr, sp'.trans sp, by rw [m]; exact Frame.refl _ _⟩,
    by rw [r4, e .a1 (by decide) (by decide)]; rfl, r10, m ▸ hm.poly⟩⟩
  rw [kp r hr, e r (by revert r hr; decide) (by revert r hr; decide)]

theorem mid_ok {s₀ : State} {m₁ : Mem} {s : State} (h : LInv s₀ m₁ 7 s) :
    WP isa (.block (liq .a4 3303 ++ ([.addi .a2 .a0 (-1024), .li .t1 256] : List Instr))) s
      (SInv s₀ m₁ s.mem (nttInvL 7 (P s₀)) 0) := by
  have e3 := h.env.a0
  have e4 := h.a1
  simp only [liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun [e3, e4, kept]
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, h.env.rd, h.env.wr, h.env.sp, h.env.frame⟩,
    ?_, ?_, by simp; decide, by simp, fun j _ => by simp⟩
  · simp [e3]
  · simp [h.env.a5]
  · simp [h.env.a6]
  · have : r ≠ .a4 ∧ r ≠ .a2 ∧ r ≠ .t1 := by revert r hr; decide
    simp [this.1, this.2.1, this.2.2, h.env.kept r hr]
  · simp [e4]
  · simp only [reduceCtorEq, ite_false, ite_true, Nat.mul_zero, BitVec.add_zero]
    exact BitVec.add_sub_cancel _ _

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .ra = s₀.gpr .ra ∧ PolyIs s.mem (F s₀) (Spec.MlKem.nttInv (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, h₁⟩ => WP.seq ?_)
  refine wp_loop_nz (LInv s₀ s₁.mem) (N := 7) (by decide) (fun ℓ hℓ s h => lstep hp hm hℓ h)
    (fun s₂ h₂ => WP.seq (WP.mono (mid_ok h₂) fun s₃ h₃ => ?_)) h₁
  refine wp_loop_nz (SInv s₀ s₁.mem s₂.mem (nttInvL 7 (P s₀))) (N := 256) (by decide)
    (fun i hi s h => sstep hp h₂.poly hi h) (fun s h => ?_) h₃
  refine ⟨fun r hr => h.env.kept r (preserved_sub r hr), h.env.sp, h.env.kept .ra (by decide), ?_⟩
  rw [nttInv_eq_nttInvL]
  exact polyIs_of_coeffAt fun j hj => by
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; omega_arith)]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.nttInvContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem verified : Verified RISCV64.target Impl.MlKem.RISCV64.nttInv (Spec.MlKem.nttInvContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.a0, .a1] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs]
    exact h
  · sig_pub [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_pub [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, RISCV64.abi,
      RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.RISCV64.NttInv
