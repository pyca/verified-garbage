module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
public import VerifiedGarbage.Proof.Rsa.X86_64.WordCT
import VerifiedGarbage.Proof.Rsa.X86_64.WordNormalize
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordNormalize
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv

/-! # Public state at the word reducer's initialization boundaries -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def CountPre (B : Addr) (Z W : Nat) (s : State) : Prop :=
  Ws s B Z W ∧ WP isa (.block countSetup) s (Ready ⟨B, Z, W, W⟩)

def RecipPre (B : Addr) (Z W : Nat) (s : State) : Prop :=
  (s.gpr .rdi = B ∧ s.gpr .r10 = off B (slot W aM) ∧ s.gpr .r8 = off B (slot W aV) ∧
    s.gpr .r12 = BitVec.ofNat 64 (W / 2)) ∧
    WP isa VG.Impl.Bignum.X86_64.R2Words.recip s (CountPre B Z W)

def SetupPre (B : Addr) (Z W : Nat) (s : State) : Prop :=
  Ws s B Z W ∧ WP isa (.block recipSetup) s (RecipPre B Z W)

theorem stages_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 4 ≤ W)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroA aR) s (SetupPre B Z W) := by
  have hMpos := modulus_pos (n := W / 2) (by omega_using [hW]) hd
  have hn := h.scr.nowrap
  have hw := h.w2
  have hz := window_bound h hZ
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have hD := h.sl (j := aD) (by decide)
  have sepRM := slot_far (w := W) (i := aR) (j := aM) (by decide)
  have sepRD := slot_far (w := W) (i := aR) (j := aD) (by decide)
  refine WP.mono (zeroA_ok h (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_
  have f₁ : Frm B (allRanges W) s.mem s₁.mem := Frm.of_outside o₁ (by simp [allRanges])
  have h₁ := h.congr f₁ (fun _ hr => all_mut hr) k₁ (by decide)
  have M₁ : wv s₁.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) :=
    o₁.wv (by omega_arith) (by omega_arith)
  have top₁ : word s₁.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) :=
    o₁.word (by omega_arith) (by omega_arith)
  have D₁ : wv s₁.mem B (slot W aD) W = wv s.mem B (slot W aD) W :=
    o₁.wv (by omega_arith) (by omega_arith)
  refine ⟨h₁, ?_⟩
  refine WP.mono (recipSetup_ok h₁) fun s₂ ⟨h10, h8, h12, m₂, k₂⟩ => ?_
  refine ⟨⟨(k₂.gpr (by decide)).trans h₁.rdi, h10, h8, h12⟩, ?_⟩
  refine WP.mono (R2w.recip_ok (h₁.scr.congr k₂.2.2) h10 h12 h8
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [m₂, top₁]; exact hd))
    fun s₃ ⟨m₃, k₃⟩ => ?_
  have o₃ : Outside B (slot W aV) 8 s₁.mem s₃.mem := by
    rw [m₃, m₂]; exact writeW_outside _ _ _ (by omega_arith)
  have f₃ : Frm B (allRanges W) s₁.mem s₃.mem := by
    apply cover (Frm.of_outside o₃ (by simp : (slot W aV, 8) ∈ [(slot W aV, 8)]))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, allRanges]
    exact ⟨(slot W aV, 24), by simp, (Nat.le_refl _), by omega_arith⟩
  have k03 := (k₁.trans k₂).trans k₃
  have h₃ := h₁.congr f₃ (fun _ hr => all_mut hr) (k₂.trans k₃) (by decide)
  refine ⟨h₃, ?_⟩
  refine WP.mono (countSetup_ok h₃ hZ) fun s₄ ⟨ha, m₄, k₄⟩ => ?_
  have o₄ : Outside B (slot W aV + 16) 8 s₃.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by omega_arith)
  have f₄ : Frm B (allRanges W) s₃.mem s₄.mem := by
    rw [m₄]
    apply cover (range_store (B := B) (W := W) _ (by omega_arith) (by omega_arith) (by omega_arith))
    intro r hr
    simp only [ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(slot W aR, 8 * (W + 2)), by simp [allRanges], (Nat.le_refl _), by omega_arith⟩
    · exact ⟨(slot W aT, 8 * (W / 2 + 1)), by simp [allRanges], (Nat.le_refl _), (Nat.le_refl _)⟩
    · exact ⟨(slot W aV, 24), by simp [allRanges], by omega_arith, by omega_arith⟩
  have h₄ := h₃.congr f₄ (fun _ hr => all_mut hr) k₄ (by decide)
  have eqM : wv s₄.mem B (slot W aM) (W / 2) = wv s.mem B (slot W aM) (W / 2) := by
    rw [o₄.wv (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), M₁]
  have eqD : wv s₄.mem B (slot W aD) W = wv s.mem B (slot W aD) W := by
    rw [o₄.wv (by simp only [slot, aD, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aD, aV]; omega_arith) (by omega_arith), D₁]
  have eqTop : word s₄.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) := by
    rw [o₄.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), top₁]
  have z₄ : wv s₄.mem B (slot W aR) (W + 2) = 0 := by
    rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
      o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith), z₁]
  have zp := wv_add s₄.mem B (slot W aR) (W / 2) (W + 2 - W / 2)
  rw [show W / 2 + (W + 2 - W / 2) = W + 2 by omega_arith, z₄] at zp
  have zlo : wv s₄.mem B (slot W aR) (W / 2) = 0 := by omega_using [zp]
  have zhi : wv s₄.mem B (slot W aR + 8 * (W / 2)) (W + 2 - W / 2) = 0 := by
    have hp := Nat.two_pow_pos (64 * (W / 2))
    rcases Nat.mul_eq_zero.mp (show 2 ^ (64 * (W / 2)) * wv s₄.mem B (slot W aR + 8 * (W / 2)) (W + 2 - W / 2) = 0 by omega_using [zp]) with he | he
    · omega_using [hp, he]
    · exact he
  refine ⟨h₄, hZ, hW, Nat.le_refl _, by rw [m₄, word_writeW_self], ?_, ?_, ?_⟩
  · rw [eqTop]; exact hd
  · rw [o₄.word (d := slot W aV) (Or.inl (by omega_arith)) (by omega_arith), m₃, m₂,
      word_writeW_self, BitVec.toNat_ofNat, eqTop,
      Nat.mod_eq_of_lt (reciprocal_lt (by rw [top₁]; exact hd)), top₁]
  · rw [zlo, eqM]; exact hMpos

/-- Public workspace, with a normalized secret divisor. -/
def Pre (p : Pub) (s : State) : Prop := Ws s p.B p.Z p.W ∧ slot p.W 17 ≤ p.Z ∧ 4 ≤ p.W ∧
  2 ^ 63 ≤ (word s.mem p.B (slot p.W aM + 8 * (p.W / 2 - 1))).toNat

/-- Initialization pins each workspace reload before the next arithmetic piece. -/
theorem code_ct : RelCT isa (Two Pre) code fun _ _ => True := by
  unfold code
  change RelCT isa _ (.seq (VG.Impl.Rsa.X86_64.Keys.zeroA aR) (.seq (.block recipSetup)
    (.seq VG.Impl.Bignum.X86_64.R2Words.recip (.seq (.block countSetup) (.loop body .ne))))) _
  refine RelCT.seq (R := Two fun (p : Pub) s => SetupPre p.B p.Z p.W s) ?_ ?_
  · unfold VG.Impl.Rsa.X86_64.Keys.zeroA
    exact ws_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide)
      (fun _ _ h => stages_ok h.1 h.2.1 h.2.2.1 h.2.2.2)
  refine RelCT.seq (R := Two fun (p : Pub) s => RecipPre p.B p.Z p.W s) ?_ ?_
  · unfold recipSetup
    rw [List.append_assoc]
    exact ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide) (fun _ _ h => h.2)
  refine RelCT.seq (R := Two fun (p : Pub) s => CountPre p.B p.Z p.W s) ?_ ?_
  · refine two_piece [.r10, .r8, .r12] ?_ (by taint_decide) (fun _ _ h => h.2)
    intro p s₁ s₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2, h₂.1.2.2.2]
  refine RelCT.seq (R := Two fun (p : Pub) s => Ready ⟨p.B, p.Z, p.W, p.W⟩ s) ?_ ?_
  · unfold countSetup
    rw [List.append_assoc]
    exact ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide) (fun _ _ h => h.2)
  exact (two_map (fun p : Pub => p) (fun p s h => ⟨by have hw : 4 ≤ p.W := h.w; omega_using [hw], h⟩) loop_ct).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86_64.WordDivide
