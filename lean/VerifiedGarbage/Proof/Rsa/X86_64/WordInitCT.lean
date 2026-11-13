module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
public import VerifiedGarbage.Proof.Rsa.X86_64.WordCT
import VerifiedGarbage.Proof.Rsa.X86_64.WordNormalize
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordNormalize
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep

/-! # Public state at the word reducer's initialization boundaries -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def CountPre (B : Addr) (Z W : Nat) (st : List Instr) (j : Nat) (s : State) : Prop :=
  Ws s B Z W ∧ WP isa (.block (countSetupWith st)) s (Ready ⟨B, Z, W, j⟩)

def RecipPre (B : Addr) (Z W : Nat) (st : List Instr) (j : Nat) (s : State) : Prop :=
  (s.gpr .rdi = B ∧ s.gpr .r10 = off B (slot W aM) ∧ s.gpr .r8 = off B (slot W aV) ∧
    s.gpr .r12 = BitVec.ofNat 64 (W / 2)) ∧
    WP isa VG.Impl.Bignum.X86_64.R2Words.recip s (CountPre B Z W st j)

def SetupPre (B : Addr) (Z W : Nat) (st : List Instr) (j : Nat) (s : State) : Prop :=
  Ws s B Z W ∧ WP isa (.block recipSetup) s (RecipPre B Z W st j)

def SeedPre (B : Addr) (Z W : Nat) (st : List Instr) (j : Nat) (s : State) : Prop :=
  Ws s B Z W ∧ WP isa (seedWith st) s (SetupPre B Z W st j)

/-- The taint checks of the seed's and the count's setup for the first digit's index `st`,
after `ws`. -/
structure SeedCkW (st : List Instr) : Prop where
  seed : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (st ++ [.shift .shl .rax 3] ++
    VG.Impl.Rsa.X86_64.Keys.base aD .rsi ++ [.alu .add .rsi (.reg .rax)] ++ VG.Impl.Rsa.X86_64.Keys.base aR .rbx ++
    [.alu .sub .r12 (.imm 1)]))
    VG.Impl.Rsa.X86_64.copyWords) hc).isSome = true
  count : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
    (.block (VG.Impl.Rsa.X86_64.Keys.base aV .rbp ++ st ++ [.store (wm 16) .rax])) hc).isSome = true

/-- `SeedCkW` for `start top`. -/
abbrev SeedCk (top : Option Nat) : Prop := SeedCkW (start top)

theorem seedCk_none : SeedCk none := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem seedCk_one : SeedCk (some 1) := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem stages_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 6 ≤ W) {st : List Instr} {j₀ : Nat} (hst : StartOk st W j₀)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroA aR) s (SeedPre B Z W st j₀) := by
  have hn := h.scr.nowrap
  have hw := h.w2
  have hz := window_bound h hZ
  have hM := h.sl (j := aM) (by decide)
  have hR := h.sl (j := aR) (by decide)
  have sepRM := slot_far (w := W) (i := aR) (j := aM) (by decide)
  have hfit := hst.fit
  refine WP.mono (zeroA_ok h (by decide)) fun s₀ ⟨z₀, o₀, k₀⟩ => ?_
  have f₀ : Frm B (allRanges W) s.mem s₀.mem := Frm.of_outside o₀ (by simp [allRanges])
  have h₀ := h.congr f₀ (fun _ hr => all_mut hr) k₀ (by decide)
  refine ⟨h₀, ?_⟩
  refine WP.mono (seedWith_ok h₀ hW hst) fun s₁ ⟨_, oS, kS⟩ => ?_
  have o₁ : Outside B (slot W aR) (8 * (W + 2)) s.mem s₁.mem :=
    o₀.trans (oS.mono (Nat.le_refl _) (by omega_arith))
  have f₁ : Frm B (allRanges W) s.mem s₁.mem := Frm.of_outside o₁ (by simp [allRanges])
  have h₁ := h.congr f₁ (fun _ hr => all_mut hr) (k₀.trans kS) (by decide)
  have top₁ : word s₁.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) :=
    o₁.word (by omega_arith) (by omega_arith)
  have zS : ∀ i, W / 2 - 1 ≤ i → i < W + 2 → word s₁.mem B (slot W aR + 8 * i) = 0 := fun i h1 h2 => by
    rw [oS.word (.inr (by omega_arith)) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mp z₀ i h2
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
  have h₃ := h₁.congr f₃ (fun _ hr => all_mut hr) (k₂.trans k₃) (by decide)
  refine ⟨h₃, ?_⟩
  refine WP.mono (countSetupWith_ok h₃ hZ hst)
    fun s₄ ⟨ha, m₄, k₄⟩ => ?_
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
  have eqTop : word s₄.mem B (slot W aM + 8 * (W / 2 - 1)) = word s.mem B (slot W aM + 8 * (W / 2 - 1)) := by
    rw [o₄.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith),
      o₃.word (by simp only [slot, aM, aV]; omega_arith) (by omega_arith), top₁]
  -- the remainder: the seed's `W / 2 - 1` words, below the divisor
  have Rlt : wv s₄.mem B (slot W aR) (W / 2) < 2 ^ (64 * (W / 2 - 1)) := by
    have e := wv_add s₄.mem B (slot W aR) (W / 2 - 1) 1
    rw [show W / 2 - 1 + 1 = W / 2 by omega_arith] at e
    have z1 : wv s₄.mem B (slot W aR + 8 * (W / 2 - 1)) 1 = 0 := by
      rw [o₄.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith),
        o₃.wv (by simp only [slot, aR, aV]; omega_arith) (by omega_arith)]
      exact wv_zero fun i hi => by
        rw [Nat.add_assoc, ← Nat.mul_add]; exact zS _ (by omega_arith) (by omega_arith)
    rw [e, z1, Nat.mul_zero, Nat.add_zero]; exact wv_lt _ _ _ _
  have Mlo : 2 ^ (64 * (W / 2 - 1)) ≤ wv s₄.mem B (slot W aM) (W / 2) := by
    have t := (R2w.top_half s₄.mem B (slot W aM) (W / 2 - 1)).mpr (by rw [eqTop]; exact hd)
    rw [show W / 2 - 1 + 1 = W / 2 by omega_arith] at t
    have : 2 ^ (64 * (W / 2 - 1)) ≤ 2 ^ (64 * (W / 2)) / 2 := by
      rw [show 64 * (W / 2) = 64 * (W / 2 - 1) + 63 + 1 by omega_arith, Nat.pow_succ, Nat.mul_div_cancel _ (by decide),
        Nat.pow_add]
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    omega_arith
  refine ⟨h₄, hZ, hW, by dsimp only; omega_arith, by rw [m₄, word_writeW_self], ?_, ?_, ?_⟩
  · rw [eqTop]; exact hd
  · rw [o₄.word (d := slot W aV) (Or.inl (by omega_arith)) (by omega_arith), m₃, m₂,
      word_writeW_self, BitVec.toNat_ofNat, eqTop,
      Nat.mod_eq_of_lt (reciprocal_lt (by rw [top₁]; exact hd)), top₁]
  · exact Nat.lt_of_lt_of_le Rlt Mlo

/-- Public workspace, with a normalized secret divisor. -/
def Pre (p : Pub) (s : State) : Prop := Ws s p.B p.Z p.W ∧ slot p.W 17 ≤ p.Z ∧ 6 ≤ p.W ∧
  2 ^ 63 ≤ (word s.mem p.B (slot p.W aM + 8 * (p.W / 2 - 1))).toNat

/-- Initialization pins each workspace reload before the next arithmetic piece, for the first
digit's index `J W` that `st` computes. -/
theorem codeWith_ct {st : List Instr} (ck : SeedCkW st) (J : Nat → Nat)
    (hst : ∀ W, 6 ≤ W → W < 2 ^ 24 → StartOk st W (J W)) :
    RelCT isa (Two Pre) (codeWith st) fun _ _ => True := by
  obtain ⟨_, cs⟩ := ck.seed
  obtain ⟨_, cc⟩ := ck.count
  unfold codeWith
  change RelCT isa _ (.seq (VG.Impl.Rsa.X86_64.Keys.zeroA aR) (.seq (seedWith st) (.seq (.block recipSetup)
    (.seq VG.Impl.Bignum.X86_64.R2Words.recip (.seq (.block (countSetupWith st)) (.loop body .ne)))))) _
  refine RelCT.seq (R := Two fun (p : Pub) s => SeedPre p.B p.Z p.W st (J p.W) s) ?_ ?_
  · unfold VG.Impl.Rsa.X86_64.Keys.zeroA
    exact ws_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide)
      (fun p _ h => stages_ok h.1 h.2.1 h.2.2.1 (hst p.W h.2.2.1 h.1.w2) h.2.2.2)
  refine RelCT.seq (R := Two fun (p : Pub) s => SetupPre p.B p.Z p.W st (J p.W) s) ?_ ?_
  · have e : seedWith st = .seq (.block (VG.Impl.Rsa.X86_64.Keys.ws ++ (st ++ [.shift .shl .rax 3] ++
        VG.Impl.Rsa.X86_64.Keys.base aD .rsi ++ [.alu .add .rsi (.reg .rax)] ++
        VG.Impl.Rsa.X86_64.Keys.base aR .rbx ++ [.alu .sub .r12 (.imm 1)]))) VG.Impl.Rsa.X86_64.copyWords := by
      simp only [seedWith, seedSetupWith, List.append_assoc]
    rw [e]
    exact ws_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) cs (fun _ _ h => by have := h.2; rwa [e] at this)
  refine RelCT.seq (R := Two fun (p : Pub) s => RecipPre p.B p.Z p.W st (J p.W) s) ?_ ?_
  · unfold recipSetup
    rw [List.append_assoc]
    exact ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) (by taint_decide) (fun _ _ h => h.2)
  refine RelCT.seq (R := Two fun (p : Pub) s => CountPre p.B p.Z p.W st (J p.W) s) ?_ ?_
  · refine two_piece [.r10, .r8, .r12] ?_ (by taint_decide) (fun _ _ h => h.2)
    intro p s₁ s₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.2.1, h₂.1.2.1]
    · rw [h₁.1.2.2.1, h₂.1.2.2.1]
    · rw [h₁.1.2.2.2, h₂.1.2.2.2]
  refine RelCT.seq (R := Two fun (p : Pub) s => Ready ⟨p.B, p.Z, p.W, J p.W⟩ s) ?_ ?_
  · have e : countSetupWith st = VG.Impl.Rsa.X86_64.Keys.ws ++ (VG.Impl.Rsa.X86_64.Keys.base aV .rbp ++ st ++
        [.store (wm 16) .rax]) := by
      simp only [countSetupWith, List.append_assoc]
    rw [e]
    exact ws_block_ct Pub.B Pub.Z Pub.W (fun _ _ h => h.1) cc (fun _ _ h => by have := h.2; rwa [e] at this)
  exact (two_map (fun p : Pub => (⟨p.B, p.Z, p.W, J p.W⟩ : Pub)) (fun p s h => ⟨
      (hst p.W h.w h.ws.w2).pos, by simpa only [At, Nat.sub_zero] using h⟩) loop_ct).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

/-- `codeWith_ct` for `code top`. -/
theorem code_ct {top : Option Nat} (ck : SeedCk top) (hk : ∀ (p : Pub) k, 6 ≤ p.W → top = some k → k ≤ p.W / 2) :
    RelCT isa (Two Pre) (code top) fun _ _ => True :=
  codeWith_ct ck (fun W => j0 W top) fun W hW hW' =>
    start_startOk hW (by omega) fun k e => hk ⟨0, 0, W, 0⟩ k hW e

end VG.Proof.Rsa.X86_64.WordDivide
