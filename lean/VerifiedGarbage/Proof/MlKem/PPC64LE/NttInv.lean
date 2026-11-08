module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
import VerifiedGarbage.Proof.MlKem.PPC64LE.NttVBfly
import VerifiedGarbage.Proof.Framework.PPC64LE.VWords
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: `vg_mlkem_inv_ntt`

The vector inverse NTT (`Impl/MlKem/PPC64LE/Ntt.lean`), on the table and
constant vectors of `vg_mlkem_ntt` (`Ntt.vsetup_ok`) and what its loops keep
(`Ntt.VEnv`): the first layer, `len = 2`, two blocks a step (`QInv`,
`qstep`, from `VBfly.ibody2_ok` and `VBfly.ipair_poly`); then the layers
with `len ≥ 4` as three nested loops of `nttInvLayer`, `nttInvBlock` and
`nttInvBlockN` (`Proof/MlKem/Ntt.lean`), four inverse butterflies a step
(`LInv`, `BInv`, `FInv`); then every coefficient times 3303 (`SInv`). Layer
`ℓ` has `len = 2 <<< ℓ` and `64 >>> ℓ` blocks.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.NttInv

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Proof.MlKem.PPC64LE.VBfly
open VG.Proof.MlKem.PPC64LE.Ntt (F S P Pre VSetup VEnv VEnv.write VEnv.rowR VEnv.rowW VEnv.rowZ VEnv.zrow
  pres_ne toNat_zp add_ofNat sub_nz lsr4 vsetup_ok Consts vconst_ok VC exec_splat1 exec_splat0' exec_splat0
  satState)

theorem sub_ofNat {a b : Nat} (h : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show a = (a - b) + b by omega, ← add_ofNat, BitVec.add_sub_cancel, Nat.add_sub_cancel]

/-- What every loop keeps survives `vconst` into `v4` or `v5`. -/
theorem VEnv.vc {s₀ : State} {m₁ : Mem} {s s' : State} (h : VEnv s₀ m₁ s) {d : VReg} (hd : d = .v4 ∨ d = .v5)
    (hc : VC [d, .v15] s s') : VEnv s₀ m₁ s' := by
  have v : ∀ r, r ≠ d → r ≠ .v15 → s'.vpr r = s.vpr r := fun r h1 h2 => hc.v r (by simp [h1, h2])
  refine ⟨(hc.g _ (by decide) (by decide)).trans h.r3, (hc.g _ (by decide) (by decide)).trans h.r4,
    fun r hr => ?_, ?_, hc.lr.trans h.lr, hc.rd.trans h.rd, hc.wr.trans h.wr, hc.sp.trans h.sp,
    hc.mem ▸ h.frame⟩
  · obtain ⟨-, -, -, -, -, -, n11, n12⟩ := pres_ne r hr
    exact (hc.g r n11 n12).trans (h.kept r hr)
  · rcases hd with rfl | rfl <;>
    exact ⟨(v _ (by decide) (by decide)).trans h.c.v0, (v _ (by decide) (by decide)).trans h.c.v1,
      (v _ (by decide) (by decide)).trans h.c.v2, (v _ (by decide) (by decide)).trans h.c.v3,
      (v _ (by decide) (by decide)).trans h.c.v12, (v _ (by decide) (by decide)).trans h.c.v13⟩

/-! ## The first layer, two blocks at a time -/

/-- After `i` steps of the first layer (`len = 2`), from `P`. -/
structure QInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  env : VEnv s₀ m₁ s
  r5 : s.gpr .r5 = BitVec.ofNat 64 (32 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 64 (8 * (126 - 2 * i))
  r10 : s.gpr .r10 = BitVec.ofNat 64 (32 - i)
  poly : PolyIs s.mem (F s₀) (nttInvLayerN (P s₀) 2 (2 * i))

theorem qstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : VSetup s₀ m₁) {i : Nat} (hi : i < 32) {s : State}
    (h : QInv s₀ m₁ i s) :
    WP isa (.block vibfly2Body) s fun s' => QInv s₀ m₁ (i + 1) s' ∧ (s'.gpr .r10 != 0) = decide (i + 1 ≠ 32) := by
  have ez : s.gpr .r4 + s.gpr .r7 = S s₀ + BitVec.ofNat 64 (8 * (126 - 2 * i)) := by rw [h.env.r4, h.r7]
  have eA : s.gpr .r3 + s.gpr .r5 = coeffAddr (F s₀) (4 * (2 * i)) := by
    rw [h.env.r3, h.r5]; exact congrArg (F s₀ + ·) (congrArg _ (by omega))
  have eB : s.gpr .r3 + (s.gpr .r5 + BitVec.ofNat 64 16) = coeffAddr (F s₀) (4 * (2 * i) + 4) := by
    rw [h.env.r3, h.r5, add_ofNat]; exact congrArg (F s₀ + ·) (congrArg _ (by omega))
  obtain ⟨z1, z0, z3, z2⟩ := h.env.zrow hp hm (k := 126 - 2 * i) (by omega)
  rw [← ez] at z1 z0 z3 z2
  refine WP.mono (ibody2_ok (ez ▸ h.env.rowZ hp (by omega)) (eA ▸ h.env.rowR hp (by omega))
    (eB ▸ h.env.rowR hp (by omega)) (eA ▸ h.env.rowW hp (by omega)) (eB ▸ h.env.rowW hp (by omega)) rfl rfl rfl
    (fun j hj => by rw [eA, row_lane h.poly (by omega) hj, toNat_val32]; exact val_lt _)
    (fun j hj => by rw [eB, row_lane h.poly (by omega) hj, toNat_val32]; exact val_lt _)
    (by rw [z1, toNat_val32]; exact val_lt _) (by rw [z3, toNat_val32]; exact val_lt _)
    (by rw [z0, z1, toNat_zp, toNat_val32]) (by rw [z2, z3, toNat_zp, toNat_val32])
    h.env.c.v0 h.env.c.v1 h.env.c.v2 h.env.c.v3 h.env.c.v12 h.env.c.v13)
    fun s' ⟨A, B, hA, hB, m, r5, r7, r10, kp⟩ => ⟨⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      kp.lr.trans h.env.lr, kp.rd.trans h.env.rd, kp.wr.trans h.env.wr, kp.sp.trans h.env.sp, ?_⟩,
      ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kp.g _ (by decide) (by decide) (by decide) (by decide), h.env.r3]
  · rw [kp.g _ (by decide) (by decide) (by decide) (by decide), h.env.r4]
  · obtain ⟨-, n5, n6, n7, -, n10, -⟩ := pres_ne r hr
    rw [kp.g r n5 n6 n7 n10, h.env.kept r hr]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.env.c.v0]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.env.c.v1]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.env.c.v2]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.env.c.v3]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.env.c.v12]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      h.env.c.v13]
  · rw [m, eA, eB]
    exact (h.env.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).write
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [r5, h.r5, add_ofNat]; exact congrArg _ (by omega)
  · rw [r7, h.r7, sub_ofNat (by omega)]; exact congrArg _ (by omega)
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
  · rw [m, eA, eB, show 2 * (i + 1) = 2 * i + 2 by omega]
    exact ipair_poly (by omega) h.poly (by rw [z1]; exact congrArg _ (congrArg _ (congrArg _ (by omega))))
      (by rw [z3]; exact congrArg _ (congrArg _ (congrArg _ (by omega))))
      (fun p hp => by rw [hA p hp, eB]) (fun p hp => by rw [hB p hp, eA])
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by omega)

/-! ## Groups of four inverse butterflies -/

/-- After `g` groups of four inverse butterflies of the block from `st` with
the zeta `zeta k` of the layer with `len`, from `Q`. -/
structure FInv (s₀ : State) (m₁ : Mem) (R7 : BitVec 64) (Q : Poly) (len k st : Nat) (g : Nat) (s : State) :
    Prop where
  env : VEnv s₀ m₁ s
  r5 : s.gpr .r5 = BitVec.ofNat 64 (4 * (st + 4 * g))
  r6 : s.gpr .r6 = BitVec.ofNat 64 (4 * (st + 4 * g + len))
  r7 : s.gpr .r7 = R7
  r9 : s.gpr .r9 = BitVec.ofNat 64 (4 * len)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (len / 4 - g)
  v4 : ∀ i < 4, vword (s.vpr .v4) i = BitVec.ofNat 32 (zeta k).val
  v5 : ∀ i < 4, vword (s.vpr .v5) i = BitVec.ofNat 32 (zetaPrime (zeta k).val)
  poly : PolyIs s.mem (F s₀) (nttInvBlockN Q len k st (4 * g))

theorem fstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} {R7 : BitVec 64} {Q : Poly} {len k st g : Nat}
    (hs : st + 2 * len ≤ 256) (hg : g < len / 4) {s : State} (h : FInv s₀ m₁ R7 Q len k st g s) :
    WP isa (.block vibflyBody) s fun s' =>
      FInv s₀ m₁ R7 Q len k st (g + 1) s' ∧ (s'.gpr .r10 != 0) = decide (g + 1 ≠ len / 4) := by
  have ht : 4 * g + 4 ≤ len := by omega
  have eA : s.gpr .r3 + s.gpr .r5 = coeffAddr (F s₀) (st + 4 * g) := by rw [h.env.r3, h.r5]
  have eB : s.gpr .r3 + s.gpr .r6 = coeffAddr (F s₀) (st + 4 * g + len) := by rw [h.env.r3, h.r6]
  refine WP.mono (ibody_ok (eA ▸ h.env.rowR hp (by omega)) (eB ▸ h.env.rowR hp (by omega))
    (eA ▸ h.env.rowW hp (by omega)) (eB ▸ h.env.rowW hp (by omega))
    (fun i hi => by rw [eA, row_lane h.poly (by omega) hi, toNat_val32]; exact val_lt _)
    (fun i hi => by rw [eB, row_lane h.poly (by omega) hi, toNat_val32]; exact val_lt _)
    (fun i hi => by rw [h.v4 i hi, toNat_val32]; exact val_lt _)
    (fun i hi => by rw [h.v5 i hi, h.v4 i hi, toNat_zp, toNat_val32]) h.env.c.v0 h.env.c.v1)
    fun s' ⟨A, B, hA, hB, m, r5, r6, r10, kp⟩ => ⟨⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
      kp.lr.trans h.env.lr, kp.rd.trans h.env.rd, kp.wr.trans h.env.wr, kp.sp.trans h.env.sp, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [kp.g _ (by decide) (by decide) (by decide), h.env.r3]
  · rw [kp.g _ (by decide) (by decide) (by decide), h.env.r4]
  · obtain ⟨-, n5, n6, -, -, n10, -⟩ := pres_ne r hr
    rw [kp.g r n5 n6 n10, h.env.kept r hr]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v0]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v1]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v2]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v3]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v12]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.env.c.v13]
  · rw [m, eA, eB]
    exact (h.env.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).write
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [r5, h.r5, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat]; exact congrArg _ (by omega)
  · rw [r6, h.r6, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, add_ofNat]; exact congrArg _ (by omega)
  · rw [kp.g _ (by decide) (by decide) (by decide), h.r7]
  · rw [kp.g _ (by decide) (by decide) (by decide), h.r9]
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.v4 i hi]
  · rw [kp.v _ (by decide) (by decide) (by decide) (by decide) (by decide), h.v5 i hi]
  · rw [m, eA, eB, show 4 * (g + 1) = 4 * g + 4 by omega]
    exact igroup_poly ht hs h.poly (fun p hp => by rw [hA p hp, eA, eB])
      (fun p hp => by rw [hB p hp, eA, eB, h.v4 p hp])
  · rw [r10, h.r10, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hg]
    exact count_nz hg (by omega)

/-! ## Blocks -/

/-- After `c` blocks of the layer with `len` and `nb` blocks, from `Q`. -/
structure BInv (s₀ : State) (m₁ : Mem) (Q : Poly) (len : Nat) (c : Nat) (s : State) : Prop where
  env : VEnv s₀ m₁ s
  r5 : s.gpr .r5 = BitVec.ofNat 64 (4 * (2 * len * c))
  r7 : s.gpr .r7 = BitVec.ofNat 64 (8 * (256 / len - 1 - c))
  r9 : s.gpr .r9 = BitVec.ofNat 64 (4 * len)
  poly : PolyIs s.mem (F s₀) (nttInvLayerN Q len c)

theorem bstep {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : VSetup s₀ m₁) {Q : Poly} {len nb c : Nat}
    (h4 : 4 ≤ len) (hl4 : len % 4 = 0) (hnb : len * nb = 128) (hc : c < nb) {s : State}
    (h : BInv s₀ m₁ Q len c s) :
    WP isa viblockCode s fun s' => BInv s₀ m₁ Q len (c + 1) s' ∧ (s'.gpr .r0 != 0) = decide (c + 1 ≠ nb) := by
  have hl : 0 < len := by omega
  have hdiv : 256 / len = 2 * nb := Nat.div_eq_of_eq_mul_left hl (by rw [Nat.mul_assoc, Nat.mul_comm nb len, hnb])
  have hlen : len ≤ 128 := by have := Nat.le_mul_of_pos_right len (show 0 < nb by omega); omega
  have hnb32 : 4 * nb ≤ 128 := hnb ▸ Nat.mul_le_mul_right nb h4
  have hb : 2 * len * (c + 1) ≤ 256 := by
    have := Nat.mul_le_mul_left len (show c + 1 ≤ nb from hc)
    rw [Nat.mul_assoc]; omega
  have hk : 256 / len - 1 - c + 1 < 128 := by omega
  have ez : s.gpr .r4 + s.gpr .r7 = S s₀ + BitVec.ofNat 64 (8 * (256 / len - 1 - c)) := by rw [h.env.r4, h.r7]
  obtain ⟨z1, z0, -, -⟩ := h.env.zrow hp hm hk
  rw [viblockCode, WP.seq_iff]
  refine WP.cons (exec_lxvd2x .v11 .r4 .r7 s (by decide) (ez ▸ h.env.rowZ hp hk)) ?_
  refine WP.cons (exec_splat1 _ _ _) (WP.cons (exec_splat0' _ _ _) ?_)
  refine WP.cons (exec_subi (by decide) (by decide)) (WP.cons exec_add ?_)
  refine WP.cons (exec_lsr_d (by decide)) (wp_nil ?_)
  rw [WP.seq_iff]
  refine wp_loop_nz (FInv s₀ m₁ (BitVec.ofNat 64 (8 * (256 / len - 1 - (c + 1)))) (nttInvLayerN Q len c) len
    (256 / len - 1 - c) (2 * len * c)) (N := len / 4) (by omega)
    (fun g hg t ht => fstep hp (by omega) hg ht) (fun s₂ h₂ => ?_) ?_
  · refine WP.cons (exec_addi (by decide) (by decide)) (WP.cons (exec_subi (by decide) (by decide)) (wp_nil ?_))
    have e5 : BitVec.ofNat 64 (4 * (2 * len * c + 4 * (len / 4) + len)) + BitVec.ofNat 64 0 =
        BitVec.ofNat 64 (4 * (2 * len * (c + 1))) := by
      rw [add_ofNat]; exact congrArg _ (by rw [Nat.mul_succ]; omega)
    refine ⟨⟨(h₂.env.write (by decide) (by decide) (by decide) _).write (by decide) (by decide) (by decide) _,
      ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h₂.r6, e5]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.r7]
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h₂.r9]
    · have hp2 := h₂.poly
      rw [show 4 * (len / 4) = len by omega] at hp2
      rw [nttInvLayerN_succ, nttInvBlock]; exact hp2
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h₂.r6, e5]
      rw [sub_nz (by omega) (by decide)]
      have e8 : 4 * (2 * len * (c + 1)) = 8 * (len * (c + 1)) := by rw [Nat.mul_assoc 2]; omega
      have key : 4 * (2 * len * (c + 1)) = 1024 ↔ c + 1 = nb := by
        rw [e8]
        constructor
        · intro e; exact Nat.eq_of_mul_eq_mul_left hl (by omega)
        · intro e; subst e; omega
      exact decide_eq_decide.mpr (not_congr key)
  · refine ⟨⟨?_, ?_, fun r hr => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, h.env.lr, h.env.rd, h.env.wr, h.env.sp,
      h.env.frame⟩, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.env.r3]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.env.r4]
    · obtain ⟨-, -, n6, n7, -, n10, -⟩ := pres_ne r hr
      simp only [RegUpd.gpr_write, gpr_writeV, n6, n7, n10, ite_false, h.env.kept r hr]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v0]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v1]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v2]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v3]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v12]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, h.env.c.v13]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.r5, Nat.mul_zero, Nat.add_zero]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, ite_true, h.r5, h.r9, add_ofNat]
      exact congrArg _ (by omega)
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, ite_true, h.r7]
      rw [sub_ofNat (by omega)]; exact congrArg _ (by omega)
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, h.r9]
    · simp only [RegUpd.gpr_write, gpr_writeV, reduceCtorEq, ite_false, ite_true, h.r9, Nat.sub_zero]
      exact lsr4 (by omega)
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, ite_true, vword_ofVWords _ hi, ez, z1]
    · simp only [vpr_write, vpr_writeV, reduceCtorEq, ite_false, ite_true, vword_ofVWords _ hi, ez, z0]
    · rw [Nat.mul_zero, nttInvBlockN_zero]; exact h.poly
