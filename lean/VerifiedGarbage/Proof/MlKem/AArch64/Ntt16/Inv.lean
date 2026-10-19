module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvPass2
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvPass1
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Gs
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: `vg_mlkem_ntt_inv`

The constants (`qConsts_ok`, `invConsts_ok`), pass 1 and pass 2 (`ip1_body`,
`ip2_body`) as loops, and the inverse NTT (`correctInv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Constants -/

/-- What `qConsts` sets. -/
structure QInv (s₀ s : State) : Prop where
  keep : Keep [.x9] s₀ s
  mem : s.mem = s₀.mem
  v : ∀ r, r ∉ [VReg.v31, .v30, .v29] → s.v r = s₀.v r
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

theorem qConsts_ok (s₀ : State) : WP isa (.block qConsts) s₀ (QInv s₀) := by
  simp only [qConsts]
  refine wp_movzV fun s₁ h₁ v₁ e₁ => wp_vop rfl fun s₂ h₂ => wp_movzV fun s₃ h₃ v₃ e₃ => wp_vop rfl fun s₄ h₄ =>
    wp_vop rfl fun s₅ h₅ => wp_nil ?_
  refine ⟨(((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep |>.mono,
    by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], fun r hr => ?_, fun e he => ?_, fun e he => ?_,
    fun e he => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₅.get r hr.2.2, h₄.get r hr.2.1, v₃, h₂.get r hr.1, v₁]
  · rw [h₅.get .v31, h₄.get .v31, v₃, h₂.v, vhalf_ofVHalves _ he, e₁, setWidth16_imm]; rfl
  · rw [h₅.get .v30, h₄.v, vhalf_ofVHalves _ he, e₃, setWidth16_imm]; rfl
  · rw [h₅.v, vhalf_zero]; rfl

/-- What the first `n` lanes of `invConsts` set. -/
structure ZInv (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.x9] s₀ s
  mem : s.mem = s₀.mem
  v : ∀ r, r ∉ [VReg.v18, .v19] → s.v r = s₀.v r
  z : ∀ k < n, vhalf (s.v .v18) k = BitVec.ofNat 16 (izc k) ∧
    vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (izc k))

theorem invConsts_ok (s₀ : State) : WP isa (.block invConsts) s₀ (ZInv s₀ 8) := by
  refine wp_range_flatMap (M := isa) (ZInv s₀) (fun k w hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, rfl, fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  refine wp_movzV fun w₁ h₁ v₁ e₁ => wp_vop (by simp only [VOp.eval, hk, ite_true]; rfl)
    fun w₂ h₂ => wp_movzV fun w₃ h₃ v₃ e₃ =>
      wp_vop (by simp only [VOp.eval, hk, ite_true]; rfl) fun w₄ h₄ => wp_nil ?_
  refine ⟨(h.keep.trans ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep))).mono,
    by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem, h.mem], fun r hr => ?_, fun k' hk' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₄.get r hr.2, v₃, h₂.get r hr.1, v₁]; exact h.v r (by simp [hr])
  · have k8 : k' < 8 := by omega
    refine ⟨?_, ?_⟩
    · rw [h₄.get .v18, v₃, h₂.v, vhalf_setLane _ hk k8, v₁]
      by_cases e : k' = k
      · subst e; rw [ite_eq_left rfl, e₁, setWidth16_imm]; rfl
      · rw [ite_eq_right e]; exact (h.z k' (by omega)).1
    · rw [h₄.v, vhalf_setLane _ hk k8, v₃, h₂.get .v19, v₁]
      by_cases e : k' = k
      · subst e; rw [ite_eq_left rfl, e₃, setWidth16_imm]; rfl
      · rw [ite_eq_right e]; exact (h.z k' (by omega)).2

/-! ## The inverse NTT -/

theorem correctInv (s₀ : State) (hs : (inPlaceAArch64 Spec.MlKem.nttInv).pre s₀) :
    ∃ t s', Exec isa Impl.MlKem.AArch64.Ntt16.nttInv s₀ t s' ∧ abiPreserved s₀ s' ∧
      (inPlaceAArch64 Spec.MlKem.nttInv).post s₀ s' := by
  have hp : Pre s₀ := pre_of (Ntt.pre_of hs)
  suffices h : WP isa Impl.MlKem.AArch64.Ntt16.nttInv s₀ fun s' => s'.sp = s₀.sp ∧
      (inPlaceAArch64 Spec.MlKem.nttInv).post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by lit_decide) he (by lit_decide), hpost⟩
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  have hreg : (⟨s₀.gpr .x1, 1024⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.mono (halves_ok invTableHalves (r := .x1) (by decide) (off := 512)
    (by rw [length_invTableHalves]) (by decide) hreg) fun s₁ h₁ => ?_
  refine WP.mono (qConsts_ok s₁) fun s₂ c₂ => ?_
  refine WP.mono (WP.keepV (Q := fun s₃ => Keep [.x2, .x3, .x6, .x5] s₂ s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x2 = s₂.gpr .x0 ∧ s₃.gpr .x3 = s₂.gpr .x1 + BitVec.ofNat 64 0 ∧
      s₃.gpr .x6 = s₂.gpr .x1 + BitVec.ofNat 64 512 ∧ (s₃.gpr .x5).toNat = 8)
    (by decide) (wp_mov fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_addImm (by decide) fun w₃ k₃ e₃ => wp_movz fun w₄ k₄ e₄ =>
      wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
        by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
        by rw [k₄.get .x2, k₃.get .x2, k₂.get .x2, e₁],
        by rw [k₄.get .x3, k₃.get .x3, e₂, k₁.get .x1],
        by rw [k₄.get .x6, e₃, k₂.get .x1, k₁.get .x1], by rw [e₄]; rfl⟩))
    fun s₃ ⟨⟨k₃, m₃, e2, e3, e6, e5⟩, hv₃⟩ => ?_
  have kk := (h₁.keep.trans c₂.keep).trans k₃
  have st₃ : St s₀ s₃ := ⟨kk.rd, kk.wr, kk.sp, kk.get .x0, kk.get .x1⟩
  have i₀ : LI1 s₀ 0 s₃ := by
    refine ⟨st₃, ?_, ?_, ?_, by rw [e5], ?_,
      (fun o ho => by
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        exact in_rd_wr (in_regions hreg (contains_off (by omega) (by decide)))),
      Or.inl rfl, fun j hj => ?_, fun r hr => absurd hr (Nat.not_lt_zero _),
      by rw [hv₃]; exact c₂.q, by rw [hv₃]; exact c₂.c10, by rw [hv₃]; exact c₂.c0⟩
    · rw [e2, c₂.keep.get .x0, h₁.keep.get .x0]; exact (BitVec.add_zero _).symm
    · rw [e3, c₂.keep.get .x1, h₁.keep.get .x1]
    · rw [e6, c₂.keep.get .x1, h₁.keep.get .x1]; exact (BitVec.add_zero _).symm
    · rw [m₃, c₂.mem]; exact h₁.frame
    · rw [m₃,c₂.mem,BitVec.add_assoc,←BitVec.ofNat_add]; exact h₁.tab j (by rw [length_invTableHalves]; exact hj)
  refine WP.seq (WP.mono (count_loop (n := 8) (by decide) (LI1 s₀) (fun b hb w hw => ip1_body hp hb hw) i₀)
    fun s₄ h₄ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (invConsts_ok s₄) fun s₅ c₅ => ?_
  refine WP.mono (WP.keepV (Q := fun s₆ => Keep [.x2, .x3, .x5] s₅ s₆ ∧ s₆.mem = s₅.mem ∧
      s₆.gpr .x2 = s₅.gpr .x1 + BitVec.ofNat 64 0 ∧ s₆.gpr .x3 = s₅.gpr .x0 ∧ (s₆.gpr .x5).toNat = 4)
    (by decide) (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_mov fun w₂ k₂ e₂ => wp_movz fun w₃ k₃ e₃ =>
      wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono, by rw [k₃.mem, k₂.mem, k₁.mem],
        by rw [k₃.get .x2, k₂.get .x2, e₁], by rw [k₃.get .x3, e₂, k₁.get .x0], by rw [e₃]; rfl⟩))
    fun s₆ ⟨⟨k₆, m₆, e2', e3', e5'⟩, hv₆⟩ => ?_
  have k₅₆ := c₅.keep.trans k₆
  have vv : ∀ r ∈ [VReg.v29, .v30, .v31], s₆.v r = s₄.v r := fun r hr => by
    rw [hv₆, c₅.v r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)]
  have j₀ : LI2 s₀ s₄.mem 0 s₆ := by
    refine ⟨h₄.st.keep k₅₆, ?_, ?_, by rw [e5'], by rw [m₆, c₅.mem]; exact Frame.refl _ _,
      fun r hr i hi => h₄.scr r hr i hi, fun i _ => ?_, fun k hk => by rw [hv₆]; exact (c₅.z k hk).1,
      fun k hk => by rw [hv₆]; exact (c₅.z k hk).2, by rw [vv .v31 (by decide)]; exact h₄.q,
      by rw [vv .v30 (by decide)]; exact h₄.c10, by rw [vv .v29 (by decide)]; exact h₄.c0⟩
    · rw [e2', c₅.keep.get .x1, h₄.st.x1]
    · rw [e3', c₅.keep.get .x0, h₄.st.x0, coeffAddr]; exact (BitVec.add_zero _).symm
    · rw [m₆, c₅.mem, ite_eq_right (Nat.not_lt_zero _)]
  refine WP.mono (count_loop (n := 4) (by decide) (LI2 s₀ s₄.mem) (fun c hc w hw => ip2_body hp hc hw) j₀)
    fun s' h' => ⟨h'.st.sp, ?_⟩
  show PolyIs s'.mem (fP s₀) (Spec.MlKem.nttInv (P₀ s₀))
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [h'.out i hi, ite_eq_left (Nat.mod_lt _ (by decide)), nttInv_eq_nttInvL,
    map_mul_get _ (show i < n from hi)]

theorem ctInv : ConstantTime isa (inPlaceAArch64 Spec.MlKem.nttInv).pre
    (inPlaceAArch64 Spec.MlKem.nttInv).pub Impl.MlKem.AArch64.Ntt16.nttInv :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (VG.AArch64.Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

theorem ntt_inv_verified :
    Verified AArch64.target Impl.MlKem.AArch64.Ntt16.nttInv (Spec.MlKem.nttInvContract AArch64.abi) :=
  Verified.of_correct correctInv ctInv (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig,
      inPlaceAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Ntt16
