module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
meta import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Spec.Gcm.Powers8
meta import VerifiedGarbage.Spec.Gcm.Powers8
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# GHASH with PMULL and the powers in their own buffer

`ghashW_verified` and `ghashS_verified` prove
`Impl.Gcm.AArch64.Pmull.ghashW` (`vg_ghash_with_powers_aes`) and
`Impl.Gcm.AArch64.Pmull.ghashS` (`vg_ghash_store_powers_aes`) against their
AArch64 contracts, `Proof.Gcm.ghashWithAArch64` and
`Proof.Gcm.ghashStoreAArch64`. Both set up all eight powers before the loops
(`Inv s₀ 8 0`, `loopsPart_ok`): `ghashW` loads them from `pw`, where
`x · H'ᵏ = Hᵏ` (`read_pwOff`), and `ghashS` computes them as `ghash` does,
then stores them after its epilogue, where `H'ᵏ = pp H k` (`tReg_pp`).
-/

@[expose] public section

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.AArch64 in
/-- `vg_ghash_with_powers(h = x0, y = x1, data = x2, n = x3, scratch = x4,
pw = x5)`: `ghashAArch64`, with the 8 prepared powers of the hash subkey at
`pw` (`Spec.Gcm.Powers8Repr`), which the code may read (128 bytes). -/
def ghashWithAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    let pw : Region := ⟨s.gpr .x5, 128⟩
    s.rd = [h, data, pw] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    y.Disjoint pw ∧ data.Disjoint scratch ∧ scratch.Disjoint pw ∧
    Powers8Repr s.mem (s.gpr .x5) (blockAt s.mem (s.gpr .x0))
  post := ghashAArch64.post
  pub s₁ s₂ := ghashAArch64.pub s₁ s₂ ∧ s₁.gpr .x5 = s₂.gpr .x5

open VG.AArch64 in
/-- `vg_ghash_store_powers(h = x0, y = x1, data = x2, n = x3, scratch = x4,
pw = x5)`: `ghashAArch64`, and the 8 prepared powers of the hash subkey
written to `pw` (`Spec.Gcm.Powers8Repr`, 128 bytes). -/
def ghashStoreAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    let pw : Region := ⟨s.gpr .x5, 128⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch, pw] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ h.Disjoint pw ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    y.Disjoint pw ∧ data.Disjoint scratch ∧ data.Disjoint pw ∧ scratch.Disjoint pw
  post s s' := ghashAArch64.post s s' ∧
    Powers8Repr s'.mem (s.gpr .x5) (blockAt s.mem (s.gpr .x0))
  pub s₁ s₂ := ghashAArch64.pub s₁ s₂ ∧ s₁.gpr .x5 = s₂.gpr .x5

end VG.Proof.Gcm

namespace VG.Proof.Gcm.AArch64.Pmull

open VG VG.AArch64 VG.Proof.Gcm VG.Proof.Gcm.Poly
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly pwOff)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## The loops, from all eight powers -/

/-- The loops of `ghashAll`, from all eight powers. -/
theorem loopsPart_ok {s₀ : State} (hp : Pm s₀) {s₁ : State} (hI₁ : Inv s₀ 8 0 s₁) :
    WP isa (.ite (.zero .x .x5)
        (.ite (.zero .x .x3) (.block []) (.loop (.block (Impl.Gcm.AArch64.Pmull.body 1)) (.nonzero .x .x3)))
        (.seq (.loop (.block (Impl.Gcm.AArch64.Pmull.body 8)) (.nonzero .x .x5))
          Impl.Gcm.AArch64.Pmull.tail)) s₁ (Inv s₀ 8 (nb s₀)) := by
  have hn := hp.nb_lt
  have hev : eval (.zero .x .x5) s₁ = some (decide (nb s₀ < 8)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI₁.x5, hI₁.x3, Nat.sub_zero,
      shr3_beq (show nb s₀ < 2 ^ 64 by omega)]
  refine WP.ite _ hev (fun _ => ones_ok hp (by decide) le_rfl hI₁) (fun h => ?_)
  simp only [decide_eq_false_iff_not, Nat.not_lt] at h
  refine WP.seq (WP.mono (Q := fun s => ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s) ?_
    fun s₄ ⟨i, hi, hI₄⟩ => tail_ok hp hi hI₄)
  let Inv8 : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i + 8 ≤ nb s₀ ∧ Inv s₀ 8 i s
  have hstep : ∀ m s, Inv8 m s → WP isa (.block (Impl.Gcm.AArch64.Pmull.body 8)) s (fun s' =>
      (eval (.nonzero .x .x5) s' = some false ∧ ∃ i, nb s₀ - i < 8 ∧ Inv s₀ 8 i s') ∨
      (eval (.nonzero .x .x5) s' = some true ∧ ∃ m' < m, Inv8 m' s')) := by
    rintro m s ⟨i, rfl, hi, hI⟩
    refine WP.mono (body_ok hp (by decide) le_rfl le_rfl hi hI) fun s' hI' => ?_
    have hev : eval (.nonzero .x .x5) s' = some (decide (8 ≤ nb s₀ - (i + 8))) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hI'.x5, hI'.x3,
        shr3_bne (show nb s₀ - (i + 8) < 2 ^ 64 by omega)]
    by_cases h8 : 8 ≤ nb s₀ - (i + 8)
    · exact .inr ⟨by rw [hev, decide_eq_true h8], nb s₀ - (i + 8), by omega, i + 8, rfl,
        by omega, hI'⟩
    · exact .inl ⟨by rw [hev, decide_eq_false h8], i + 8, by omega, hI'⟩
  exact WP.loop (M := isa) Inv8 hstep (nb s₀) s₁ ⟨0, rfl, by omega, hI₁⟩

/-- `ghashAll pro []`, from a prologue that sets up all eight powers. -/
theorem loopsAll_ok {s₀ : State} (hp : Pm s₀) {pro : List Instr}
    (hpro : WP isa (.block pro) s₀ (Inv s₀ 8 0)) :
    WP isa (Impl.Gcm.AArch64.Pmull.ghashAll pro []) s₀ fun s' =>
      Proof.Gcm.ghashAArch64.post s₀ s' := by
  refine WP.seq (WP.mono hpro fun s₁ hI₁ => ?_)
  refine WP.seq (WP.mono (loopsPart_ok hp hI₁) fun s₂ hI₂ => ?_)
  rw [List.append_nil]
  exact epilogue_ok hp hI₂

/-! ## Reading the powers -/

theorem pm_of_with {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) : Pm s₀ := by
  obtain ⟨hrd, hwr, -, -, hyd, -⟩ := h
  exact ⟨⟨hR s₀, by simp [hrd], contains_offset (by decide) (by decide)⟩, by simp [hrd],
    by simp [hwr], hyd⟩

theorem pwOff_mod (k : Nat) : pwOff k % 16 = 0 := by
  unfold pwOff; split <;> omega

/-- The power `H'ᵏ` at `pw + pwOff k`, as `tReg k` holds it. -/
theorem read_pwOff {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) {k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ 8) :
    x * φ (s₀.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16) = φ (H₀ s₀) ^ k := by
  have hr := h.2.2.2.2.2.2.2.2.2
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · obtain ⟨hv, -⟩ := hr (j - 1) (by omega)
    have h1 : pwOff (2 * j) = 32 * (j - 1) := by
      simp only [pwOff, Nat.mul_mod_right, ↓reduceIte]; omega
    have h2 : 2 * j = 2 * (j - 1) + 2 := by omega
    have hv' : s₀.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff (2 * j))) 16 =
        Spec.Gcm.preparedPower (Spec.Gcm.hpow (H₀ s₀) (2 * j)) :=
      calc _ = s₀.mem.readW (s₀.gpr .x5 + BitVec.ofNat 64 (32 * (j - 1))) 128 := by
              rw [h1, Mem.readW]; rfl
        _ = _ := hv
        _ = _ := by rw [← h2]
    rw [hv', x_φ_preparedPower_hpow]
  · obtain ⟨-, hv⟩ := hr j (by omega)
    have h1 : pwOff (2 * j + 1) = 16 + 32 * j := by
      simp only [pwOff, show (2 * j + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]; omega
    have hv' : s₀.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff (2 * j + 1))) 16 =
        Spec.Gcm.preparedPower (Spec.Gcm.hpow (H₀ s₀) (2 * j + 1)) :=
      calc _ = s₀.mem.readW (s₀.gpr .x5 + BitVec.ofNat 64 (16 + 32 * j)) 128 := by
              rw [h1, Mem.readW]; rfl
        _ = _ := hv
    rw [hv', x_φ_preparedPower_hpow]

theorem loadPw_ok (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr)
    (s.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16) (hk : k ≤ 8) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPw k)) s fun s' =>
      s'.v (tReg k) = s.mem.read (s.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 ∧
      s'.v (sReg k) = ext8 (s'.v (tReg k)) (s'.v (tReg k)) ∧ VOnly [tReg k, sReg k] s s' := by
  have ho' : pwOff k < 4096 * 16 := by unfold pwOff; split <;> omega
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq (pwOff_mod k) ho' hin, ?_⟩
  refine WP.mono (swap_ok (sReg k) (tReg k) _) fun s' ⟨w, o⟩ => ?_
  have ts : tReg k ∉ [sReg k] := by
    simp only [List.mem_singleton]; exact tReg_ne_sReg _ _
  refine ⟨by rw [o.v _ ts]; simp only [v_setV, ite_true], by rw [w, o.v _ ts], ⟨fun r hr => ?_, o.gpr, o.mem,
    o.rd, o.wr, o.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [o.v r (by simp only [List.mem_singleton]; exact hr.2)]
  simp only [v_setV, hr.1, ite_false]

/-- The powers below `K` loaded, nothing else changed. -/
structure PW (s₀ : State) (K : Nat) (s : State) : Prop where
  t : ∀ k, 1 ≤ k → k ≤ K → x * φ (s.v (tReg k)) = φ (H₀ s₀) ^ k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = ext8 (s.v (tReg k)) (s.v (tReg k))
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `H'ᴷ⁺¹` loaded. -/
theorem loadPwI_ok {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) {K : Nat} (hK8 : K + 1 ≤ 8)
    {s : State} (hP : PW s₀ K s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPw (K + 1))) s (PW s₀ (K + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (pwOff (K + 1))) 16 := by
    rw [hP.rd, hP.wr, hP.gpr]
    refine ⟨⟨s₀.gpr .x5, 128⟩, by simp [h.1], contains_offset ?_ ?_⟩ <;>
      (unfold pwOff; split <;> omega)
  refine WP.mono (loadPw_ok (K + 1) s hin hK8) fun s' ⟨t, w, o⟩ => ?_
  have kv : ∀ r, r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r := fun r h1 h2 =>
    o.v r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
  refine ⟨fun k hk hkK => ?_, fun k hk hkK => ?_, by rw [o.gpr, hP.gpr], by rw [o.mem, hP.mem],
    by rw [o.rd, hP.rd], by rw [o.wr, hP.wr]⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [t, hP.gpr, hP.mem]; exact read_pwOff h hk (by omega)
    · rw [kv _ (tReg_ne hk (by omega) (by omega) hK8 (by omega)) (tReg_ne_sReg _ _),
        hP.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · exact w
    · rw [kv _ (tReg_ne hk (by omega) (by omega) hK8 (by omega)) (tReg_ne_sReg _ _),
        kv _ (fun e => tReg_ne_sReg _ _ e.symm) (sReg_ne hk (by omega) (by omega) hK8 (by omega)),
        hP.sw k hk hkK']

theorem prologueW_ok {s₀ : State} (h : Proof.Gcm.ghashWithAArch64.pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologueW) s₀ (Inv s₀ 8 0) := by
  have hp := pm_of_with h
  simp only [Impl.Gcm.AArch64.Pmull.prologueW, List.append_assoc]
  have h₀ : PW s₀ 0 s₀ := ⟨fun _ _ h => absurd h (by omega), fun _ _ h => absurd h (by omega),
    rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 0) (by decide) h₀) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 1) (by decide) h₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 2) (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 3) (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 4) (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 5) (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 6) (by decide) h₆) fun s₇ h₇ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPwI_ok h (K := 7) (by decide) h₇) fun s₈ h₈ => ?_
  rw [WP.block_append_iff]
  have hcb : WP isa (.block ([.movz .x .x5 0xc200 3, .vop (.dup .d2 C .x5)] : List Instr)) s₈ fun s₉ =>
      s₉.v C = ofVDwords poly poly ∧ (∀ r, r ≠ C → s₉.v r = s₈.v r) ∧
      (∀ r, r ≠ .x5 → s₉.gpr r = s₈.gpr r) ∧ s₉.mem = s₈.mem ∧ s₉.rd = s₈.rd ∧ s₉.wr = s₈.wr := by
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_x (show 16 * 3 < 64 by decide),
        exec_dup_d2]; rfl, ?_⟩
    refine ⟨by simp only [v_setV, ite_true, gpr_write_x]; decide, fun r hr => by simp only [v_setV, hr, ite_false,
      v_write], fun r hr => by simp only [gpr_setV, gpr_write_x, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono hcb fun s₉ ⟨c₉, v₉, g₉, m₉, rd₉, wr₉⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok Y .x1 0 s₉ rfl (by decide)
    (by rw [rd₉, wr₉, h₈.rd, h₈.wr, g₉ .x1 (by decide), h₈.gpr]
        exact ⟨yR s₀, List.mem_append_right _ hp.y_in, contains_offset (by decide) (by decide)⟩))
    fun s₁₀ ⟨l₁₀, o₁₀⟩ => ?_
  refine WP.mono (lsr_ok .x5 .x3 3 (by decide) s₁₀) fun s' ⟨f5, fg, fv, fm, frd, fwr⟩ => ?_
  have g : ∀ r, r ≠ .x5 → s'.gpr r = s₀.gpr r := fun r h5 => by
    rw [fg r h5, o₁₀.gpr, g₉ r h5, h₈.gpr]
  have kv : ∀ r, r ≠ C → r ≠ Y → s'.v r = s₈.v r := fun r hc hy => by
    rw [fv, o₁₀.v _ (by simp only [List.mem_singleton]; exact hy), v₉ _ hc]
  refine ⟨Nat.zero_le _, by rw [fv, o₁₀.v C (by decide), c₉], fun k hk hk8 => ?_, fun k hk hk8 => ?_, ?_,
    by rw [g .x0 (by decide)], by rw [g .x1 (by decide)],
    by rw [g .x2 (by decide)]; simp [blkAddr], by rw [g .x3 (by decide)]; simp [nb],
    by rw [f5, fg .x3 (by decide)], by rw [fm, o₁₀.mem, m₉, h₈.mem],
    by rw [frd, o₁₀.rd, rd₉, h₈.rd], by rw [fwr, o₁₀.wr, wr₉, h₈.wr]⟩
  · rw [kv _ (ne_tReg (r := C) k).symm (ne_tReg (r := Y) k).symm]; exact h₈.t k hk hk8
  · rw [kv _ (ne_sReg (r := C) k).symm (ne_sReg (r := Y) k).symm,
      kv _ (ne_tReg (r := C) k).symm (ne_tReg (r := Y) k).symm]
    exact h₈.sw k hk hk8
  · rw [fv, l₁₀, m₉, h₈.mem, g₉ .x1 (by decide), h₈.gpr, add_ofNat_zero]
    exact congrArg φ (ghashFrom_blocksAt_zero _ _ _ _).symm

theorem correctW {s₀ : State} (hs : Proof.Gcm.ghashWithAArch64.pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghashW s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loopsAll_ok (pm_of_with hs) (prologueW_ok hs))
    (by decide +kernel) (by decide +kernel)) fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghashW_correct (s : State) (hs : Proof.Gcm.ghashWithAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghashW s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashWithAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correctW hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashW_ct : ConstantTime isa Proof.Gcm.ghashWithAArch64.pre Proof.Gcm.ghashWithAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghashW := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3, h4, h5, hsp⟩, h6⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- Zero memory has the eight prepared powers of the zero subkey. -/
theorem powers8Repr_zero (p : Addr) : Spec.Gcm.Powers8Repr (fun _ => 0) p 0 := by
  intro k hk
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  have hz : ∀ k, Spec.Gcm.hpow 0 (k + 1) = 0 := fun k => φ_inj (by
    rw [φ_hpow, φ_zero, zero_pow (Nat.succ_ne_zero k)])
  simp only [hz, w]
  constructor <;> decide

theorem blockAt_zero (q : Addr) : Spec.Gcm.blockAt (fun _ => 0) q = 0 := by
  simp [Spec.Gcm.blockAt, Spec.Aes.bytesAt, Spec.Gcm.ofBytes]

/-- A state satisfying `vg_ghash_with_powers`'s precondition, with zero memory. -/
def satStateW : State :=
  { Proof.Gcm.AArch64.satState with
    gpr := fun r => if r = .x5 then 0x6000 else Proof.Gcm.AArch64.satState.gpr r
    rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩, ⟨0x6000, 128⟩] }

theorem ghashW_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghashW (Spec.Gcm.ghashWithPowersContract AArch64.abi) :=
  Verified.of_correct ghashW_correct ghashW_ct
    { pre := by
        sig_implies_pre [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.withPowersParam, Proof.Gcm.ghashWithAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateW, by
        sig_pre [Spec.Gcm.ghashWithPowersContract, Spec.Gcm.ghashWithPowersSig, Spec.Gcm.ghashSig,
          Spec.Gcm.withPowersParam, AArch64.abi, AArch64.argRegs, satStateW,
          Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | (rw [blockAt_zero]; exact powers8Repr_zero _)
          | exact Region.disjoint_of_sep (by decide)⟩ }


/-! ## Storing the powers -/

theorem pm_of_store {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) : Pm s₀ := by
  obtain ⟨hrd, hwr, -, -, -, hyd, -⟩ := h
  exact ⟨⟨hR s₀, by simp [hrd], contains_offset (by decide) (by decide)⟩, by simp [hrd],
    by simp [hwr], hyd⟩

/-- `Pm` reads only `x0` to `x3` and the regions of its state. -/
theorem Pm.congr {s₀ s₁ : State} (h0 : s₁.gpr .x0 = s₀.gpr .x0) (h1 : s₁.gpr .x1 = s₀.gpr .x1)
    (h2 : s₁.gpr .x2 = s₀.gpr .x2) (h3 : s₁.gpr .x3 = s₀.gpr .x3) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hp : Pm s₀) : Pm s₁ := by
  obtain ⟨hh, hd, hy, hyd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hA, hrd, hwr, h0]; exact hh
  · simp only [dR, dp, nb, hrd, h2, h3]; exact hd
  · simp only [yR, yp, hwr, h1]; exact hy
  · simp only [yR, yp, dR, dp, nb, h1, h2, h3]; exact hyd

/-- `Inv` reads only `x0` to `x3`, the memory and the regions of its initial state. -/
theorem Inv.congr {s₀ s₁ : State} (h0 : s₁.gpr .x0 = s₀.gpr .x0) (h1 : s₁.gpr .x1 = s₀.gpr .x1)
    (h2 : s₁.gpr .x2 = s₀.gpr .x2) (h3 : s₁.gpr .x3 = s₀.gpr .x3) (hm : s₁.mem = s₀.mem)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) {K i : Nat} {s : State} (hI : Inv s₁ K i s) :
    Inv s₀ K i s := by
  have eH : H₀ s₁ = H₀ s₀ := by simp only [H₀, hA, h0, hm]
  have eY : ∀ j, Ys s₁ j = Ys s₀ j := fun j => by
    simp only [Ys, H₀, Y₀, hA, yp, dp, h0, h1, h2, hm]
  refine ⟨?_, hI.c, fun k hk hkK => ?_, hI.sw, ?_, ?_, ?_, ?_, ?_, hI.x5, ?_, ?_, ?_⟩
  · have := hI.le; simp only [nb, h3] at this ⊢; exact this
  · rw [← eH]; exact hI.t k hk hkK
  · rw [← eY]; exact hI.y
  · rw [hI.x0]; simp only [hA, h0]
  · rw [hI.x1]; simp only [yp, h1]
  · rw [hI.x2]; simp only [blkAddr, dp, h2]
  · rw [hI.x3]; simp only [nb, h3]
  · rw [hI.mem, hm]
  · rw [hI.rd, hrd]
  · rw [hI.wr, hwr]

theorem prologueS_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.prologueS) s₀ fun s =>
      Inv s₀ 8 0 s ∧ s.gpr .x8 = s₀.gpr .x5 := by
  have hp := pm_of_store h
  simp only [Impl.Gcm.AArch64.Pmull.prologueS, List.singleton_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addImm (show 0 < 4096 by decide) s₀, ?_⟩
  have g : ∀ r, r ≠ .x8 → (s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0)).gpr r = s₀.gpr r :=
    fun r hr => by simp only [gpr_write_x, hr, ite_false]
  have hp₁ := Pm.congr (s₁ := s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0))
    (g .x0 (by decide)) (g .x1 (by decide)) (g .x2 (by decide)) (g .x3 (by decide)) rfl rfl hp
  have hw : WP isa (.block (Impl.Gcm.AArch64.Pmull.prologue ++ Impl.Gcm.AArch64.Pmull.powers))
      (s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0)) (Inv (s₀.write .x .x8 (s₀.gpr .x5 + BitVec.ofNat 64 0)) 8 0) := by
    rw [WP.block_append_iff]
    exact WP.mono (prologue_ok hp₁) fun _ hI => powers_ok hI
  refine WP.mono (WP.gprs (rs := [.x8]) hw (by decide +kernel) (by decide +kernel))
    fun s ⟨hI, g8⟩ => ⟨Inv.congr (g .x0 (by decide)) (g .x1 (by decide)) (g .x2 (by decide))
      (g .x3 (by decide)) rfl rfl rfl hI, ?_⟩
  rw [g8 .x8 (by simp)]
  simp only [gpr_write_x, ite_true, add_ofNat_zero]

/-- With the eight powers computed, `H'ᵏ` is the prepared power of `Hᵏ`. -/
theorem tReg_pp {s₀ s : State} {i : Nat} (hI : Inv s₀ 8 i s) {k : Nat} (hk1 : 1 ≤ k) (hk8 : k ≤ 8) :
    s.v (tReg k) = pp (H₀ s₀) k :=
  φ_inj (x_cancel (by rw [hI.t k hk1 hk8, x_φ_pp]))

/-- The offsets of distinct powers are 16 bytes apart at least. -/
theorem pwOff_sep : ∀ k < 9, ∀ j < 9, 1 ≤ k → 1 ≤ j → k ≠ j →
    pwOff k + 16 ≤ pwOff j ∨ pwOff j + 16 ≤ pwOff k := by
  intro k hk j hj h1 h2 hne
  unfold Impl.Gcm.AArch64.Pmull.pwOff
  split <;> split <;> omega

theorem pwOff_le : ∀ k < 9, pwOff k + 16 ≤ 128 := by
  intro k hk
  unfold Impl.Gcm.AArch64.Pmull.pwOff
  split <;> omega

/-- The powers below `K` stored at `pw`, the block at `y` kept. -/
structure SW (s₀ : State) (yv : BitVec 128) (K : Nat) (s : State) : Prop where
  x8 : s.gpr .x8 = s₀.gpr .x5
  wr : s.wr = s₀.wr
  t : ∀ k, 1 ≤ k → k ≤ 8 → s.v (tReg k) = pp (H₀ s₀) k
  pw : ∀ k, 1 ≤ k → k ≤ K → s.mem.read (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 = pp (H₀ s₀) k
  y : s.mem.read (yp s₀) 16 = yv

/-- `H'ᴷ⁺¹` stored. -/
theorem storeI_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) {yv : BitVec 128} {K : Nat}
    (hK : K + 1 ≤ 8) {s : State} (hS : SW s₀ yv K s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.storePw (K + 1))) s (SW s₀ yv (K + 1)) := by
  obtain ⟨-, hwr, -, -, -, -, -, hyp, -, -, -⟩ := h
  have hc : ∀ k, k ≤ 8 → Region.Contains ⟨s₀.gpr .x5, 128⟩ (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 16 :=
    fun k hk => contains_offset (by have := pwOff_le k (by omega); omega)
      (by have := pwOff_le k (by omega); omega)
  have hout : InRegions s.wr (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 := by
    rw [hS.wr, hwr, hS.x8]; exact ⟨⟨s₀.gpr .x5, 128⟩, by simp, hc (K + 1) hK⟩
  have ho' : pwOff (K + 1) < 4096 * 16 := by have := pwOff_le (K + 1) (by omega); omega
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (pwOff_mod (K + 1)) ho' hout, WP.block_nil ?_⟩
  refine ⟨hS.x8, hS.wr, hS.t, fun k hk hkK => ?_, ?_⟩
  · show (s.mem.write (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s.v (tReg (K + 1)))).read _ 16 = _
    rw [hS.x8]
    rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [read_write16, hS.t _ hk hK]
    · rw [Mem.read_write_sep (Offset.sep _ (pwOff_sep k (by omega) (K + 1) (by omega) hk (by omega)
          (by omega)) (by have := pwOff_le k (by omega); omega)
          (by have := pwOff_le (K + 1) (by omega); omega)) (by decide),
        hS.pw k hk hkK']
  · show (s.mem.write (s.gpr .x8 + BitVec.ofNat 64 (pwOff (K + 1))) 16 (s.v (tReg (K + 1)))).read _ 16 = _
    have hcy : Region.Contains ⟨s₀.gpr .x1, 16⟩ (s₀.gpr .x1) 16 := by
      have := contains_offset (base := s₀.gpr .x1) (len := 16) (off := 0) (n := 16) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    rw [hS.x8, Mem.read_write_sep (Region.Disjoint.sep hyp hcy (hc (K + 1) hK)) (by decide), hS.y]

/-- The epilogue, then the eight powers stored. -/
theorem epiS_ok {s₀ : State} (h : Proof.Gcm.ghashStoreAArch64.pre s₀) {s : State}
    (hI : Inv s₀ 8 (nb s₀) s) (h8 : s.gpr .x8 = s₀.gpr .x5) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.epilogue ++ Impl.Gcm.AArch64.Pmull.storesS)) s fun s' =>
      Proof.Gcm.ghashAArch64.post s₀ s' ∧ Spec.Gcm.Powers8Repr s'.mem (s₀.gpr .x5) (H₀ s₀) := by
  have hp := pm_of_store h
  have hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 0) 16 := by
    rw [hI.wr, hI.x1]
    exact ⟨yR s₀, hp.y_in, contains_offset (by decide) (by decide)⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (s := s.setV Y _) (by decide) (by decide) hout, ?_⟩
  -- After the epilogue: `Y` at `y`.
  let se : State := { s.setV Y (VRevOp.eval .rev64b (s.v Y)) with
    mem := (s.setV Y (VRevOp.eval .rev64b (s.v Y))).mem.write
      ((s.setV Y (VRevOp.eval .rev64b (s.v Y))).gpr .x1 + BitVec.ofNat 64 0) 16
      ((s.setV Y (VRevOp.eval .rev64b (s.v Y))).v Y) }
  have hye : blockAt se.mem (yp s₀) = Ys s₀ (nb s₀) := by
    apply φ_inj
    simp only [se, mem_setV, gpr_setV, v_setV, ↓reduceIte, hI.x1, add_ofNat_zero, φ_store, hI.y]
  have hS0 : SW s₀ (se.mem.read (yp s₀) 16) 0 se :=
    ⟨by simp only [se, gpr_setV, h8], by simp only [se, wr_setV, hI.wr],
      fun k hk1 hk8 => by
        simp only [se, v_setV, (ne_tReg (r := Y) k).symm, ite_false]; exact tReg_pp hI hk1 hk8,
      fun _ _ h => absurd h (by omega), rfl⟩
  show WP isa (.block Impl.Gcm.AArch64.Pmull.storesS) se _
  simp only [Impl.Gcm.AArch64.Pmull.storesS, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 0) (by decide) hS0) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 1) (by decide) h₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 2) (by decide) h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 3) (by decide) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 4) (by decide) h₄) fun s₅ h₅ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 5) (by decide) h₅) fun s₆ h₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeI_ok h (K := 6) (by decide) h₆) fun s₇ h₇ => ?_
  refine WP.mono (storeI_ok h (K := 7) (by decide) h₇) fun s' h' => ⟨?_, ?_⟩
  · show blockAt s'.mem (yp s₀) = Ys s₀ (nb s₀)
    rw [← hye]
    apply φ_inj
    rw [← ρ_load, ← ρ_load, h'.y]
  · intro j hj
    have e : ∀ k, 1 ≤ k → k ≤ 8 → s'.mem.readW (s₀.gpr .x5 + BitVec.ofNat 64 (pwOff k)) 128 =
        pp (H₀ s₀) k := fun k hk1 hk8 => by rw [Mem.readW, ← h'.pw k hk1 hk8]; rfl
    refine ⟨?_, ?_⟩
    · have := e (2 * j + 2) (by omega) (by omega)
      rw [show pwOff (2 * j + 2) = 32 * j by
        simp only [pwOff, show (2 * j + 2) % 2 = 0 by omega, ↓reduceIte]; omega] at this
      exact this
    · have := e (2 * j + 1) (by omega) (by omega)
      rw [show pwOff (2 * j + 1) = 16 + 32 * j by
        simp only [pwOff, show (2 * j + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]; omega] at this
      exact this

theorem correctS {s₀ : State} (hs : Proof.Gcm.ghashStoreAArch64.pre s₀) :
    WP isa Impl.Gcm.AArch64.Pmull.ghashS s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashStoreAArch64.post s₀ s' := by
  have hp := pm_of_store hs
  have hw : WP isa Impl.Gcm.AArch64.Pmull.ghashS s₀ (Proof.Gcm.ghashStoreAArch64.post s₀) := by
    refine WP.seq (WP.mono (prologueS_ok hs) fun s₁ ⟨hI₁, h8₁⟩ => ?_)
    refine WP.seq (WP.mono (WP.gprs (rs := [.x8]) (loopsPart_ok hp hI₁) (by decide +kernel)
      (by decide +kernel)) fun s₂ ⟨hI₂, g₂⟩ => ?_)
    exact epiS_ok hs hI₂ (by rw [g₂ .x8 (by simp), h8₁])
  exact WP.mono (WP.gprs (rs := preserved) hw (by decide +kernel) (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

theorem ghashS_correct (s : State) (hs : Proof.Gcm.ghashStoreAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.Pmull.ghashS s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashStoreAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correctS hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ghashS_ct : ConstantTime isa Proof.Gcm.ghashStoreAArch64.pre Proof.Gcm.ghashStoreAArch64.pub
    Impl.Gcm.AArch64.Pmull.ghashS := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3, h4, h5, hsp⟩, h6⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- A state satisfying `vg_ghash_store_powers`'s precondition, with zero memory. -/
def satStateS : State :=
  { Proof.Gcm.AArch64.satState with
    gpr := fun r => if r = .x5 then 0x6000 else Proof.Gcm.AArch64.satState.gpr r
    wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩, ⟨0x6000, 128⟩] }

theorem ghashS_verified :
    Verified AArch64.target Impl.Gcm.AArch64.Pmull.ghashS (Spec.Gcm.ghashStorePowersContract AArch64.abi) :=
  Verified.of_correct ghashS_correct ghashS_ct
    { pre := by
        sig_implies_pre [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig,
          Spec.Gcm.ghashSig, Spec.Gcm.storePowersParam, Proof.Gcm.ghashStoreAArch64,
          Proof.Gcm.ghashAArch64, AArch64.abi, AArch64.argRegs]
      sat := ⟨satStateS, by
        sig_pre [Spec.Gcm.ghashStorePowersContract, Spec.Gcm.ghashStorePowersSig, Spec.Gcm.ghashSig,
          Spec.Gcm.storePowersParam, AArch64.abi, AArch64.argRegs, satStateS,
          Proof.Gcm.AArch64.satState]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)⟩ }

end VG.Proof.Gcm.AArch64.Pmull
