import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the exponentiation

`Bw` words of 64 bits each, public counts (`expLoop_ct`): the counters in
`sC1` and `sC3` are pinned by correctness, and so is the index of the word
`wordHead` loads.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

namespace Rp

/-- The words of `r`. -/
abbrev bW (p : RpP) : Nat := wk p.k + (p.el + 7) / 8

/-! ## A bit -/

theorem RelCT.seq_assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq ea e' =>
    cases e' with
    | seq eb ec =>
      cases e₂ with
      | seq fa f' =>
        cases f' with
        | seq fb fc =>
          have := h _ _ _ _ _ _ hp (.seq (.seq ea eb) ec) (.seq (.seq fa fb) fc)
          simpa only [List.append_assoc] using this

/-- In a bit: the constants, `Y < n`, `G < n`, and `Xm < n` if `hx`. -/
def BT (hx : Bool) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) < N ∧ wv s.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    (hx = true → wv s.mem p.B (slot (wk p.k) aXm) (wk p.k) < N)

theorem BT.ws {hx : Bool} {p : RpP} {s : State} (h : BT hx p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, hc, -⟩ := h
  exact hc.ws

/-- `bitSel`'s and the selection's registers. -/
def selVal (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r8 => off p.B (slot (wk p.k) aXm)
  | .rsi => off p.B (slot (wk p.k) aG)
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- The bit, and the multiplicand `G` or `R mod n`. -/
theorem bitSel_ct : RelCT isa (Two (BT true)) (.seq (.block bitSel) (wordLoop 0 selBody)) (Two (BT true)) := by
  refine pin_ct [.rdi] [.rdi, .r8, .rsi, .r12] selVal (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi])
    (by taint_decide) (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · have hw := h.ws
    refine WP.mono (bitSel_ok hw (V := (word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (BitVec.isLt _)) fun t ⟨_, h8, hsi, h12, _, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k.gpr (by decide)).trans hw.rdi
    · exact h8
    · exact hsi
    · exact h12
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have h256 := hc.ws.h256
    refine WP.seq (WP.mono (bitSel_ok hc.ws (V := (word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (BitVec.isLt _)) fun u₂ ⟨hbp, h8, hsi, h12, m₂, k₂⟩ => ?_)
    have hf₂ : Frm p.B (rg (wk p.k) [] [sC2]) s.mem u₂.mem := by
      rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) _ _
        (List.mem_singleton_self _)
    have hc₂ := hc.congr hf₂ (by decide) (by decide) k₂ (by decide)
    have sXm := hc₂.ws.sl (j := aXm) (by decide)
    have sG := hc₂.ws.sl (j := aG) (by decide)
    refine WP.mono (sel_ok hc₂.ws.scr h8 hsi hbp h12 (by omega) (by omega) (by omega) (by omega)
      (by have := slot_far (w := wk p.k) (show aXm ≠ aG by decide); omega)) fun u₃ ⟨hx₃, o₃, k₃⟩ => ?_
    have hf₃ : Frm p.B (rg (wk p.k) [aXm] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (by omega) _ _ (by decide)
    have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
    have e₂ : ∀ j, j < 16 → j ≠ aXm →
        wv u₃.mem p.B (slot (wk p.k) j) (wk p.k) = wv s.mem p.B (slot (wk p.k) j) (wk p.k) := fun j hj hne => by
      rw [hf₃.rg_wv hZ16 (by simp) hj (by simpa using hne) (by omega),
        hf₂.rg_wv hZ16 (by decide) hj (by simp) (by omega)]
    refine ⟨minv, N, r, t, hc₃, by rw [e₂ _ (by decide) (by decide)]; exact hY,
      by rw [e₂ _ (by decide) (by decide)]; exact hG, fun _ => ?_⟩
    rw [hx₃, hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega),
      hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]
    split
    · exact hX rfl
    · exact hG

/-- A bit leaks the same in runs that agree on the public data. -/
theorem bitBody_ct (M : Mont) : RelCT isa (Two (BT false)) (bitBody M.mm) fun _ _ => True := by
  have hB : ∀ (hx : Bool) p s, BT hx p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  simp only [bitBody, seqs]
  refine RelCT.seq (R := Two (BT true)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide)
    fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, hc, hY, hG, -⟩ := h
    have hZ16 := hc.hZ16
    have hN : 0 < N := by have := hc.n1; omega
    refine WP.mono (copyA_ok hc.ws (o := aXm) (a := aO) (by decide) (by decide) (by decide))
      fun u ⟨hx, o, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aXm] []) s.mem u.mem := Frm.rg_of_out o (by omega) _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), ?_, ?_, fun _ => ?_⟩
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hY
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hG
    · rw [hx, hc.ho]; exact Nat.mod_lt _ hN
  refine RelCT.seq_assoc (RelCT.seq bitSel_ct (RelCT.seq (R := Two (BT true)) (mm_gct RpP.B RpP.Z (fun p => wk p.k)
    (hB true) M (o := aY) (a := aY) (b := aY) (by unfold MmUse; decide) fun p s h => ?_)
    (RelCT.seq (R := Two (BT false)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) M (o := aY) (a := aY)
      (b := aXm) (by unfold MmUse; decide) fun p s h => ?_)
    (two_taint [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]) (by taint_decide)))))
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hY)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun _ => ?_⟩
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hG
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hX rfl
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega) (o := aY) (a := aY) (b := aXm) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hX rfl)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun e => by cases e⟩
    rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact hG

/-- The bits' invariant: `j` bits of the word `V` from `t₀`. -/
def BI (p : RpP) (j : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t g e V : Nat), Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧ V = e % 2 ^ 64 ∧
    BitInv t₀ p.B (wk p.k) N g e V j u

theorem bitLoop_ct (M : Mont) : RelCT isa (Two fun (p : RpP) s => 0 < 64 ∧ BI p 0 s) (.loop (bitBody M.mm) .ne)
    (Two fun p s => BI p 64 s) :=
  two_loop (fun _ => 64) (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨-, t₀, minv, N, r, t, g, e, V, hc, hGlt, -, -, hI⟩ := hq
      have hZ16 := hc.hZ16
      have hcu := hc.congr hI.frm (by decide) bit_hs hI.keep (by decide)
      refine ⟨minv, N, r, t, hcu, hI.ylt, ?_, fun e => by cases e⟩
      rw [hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hGlt) (bitBody_ct M))
    fun p j s hj ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI⟩ =>
      WP.mono (bitBody_ok M hc hGlt hG hV hj hI) fun s' ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hj hz, fun _ => ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI'⟩,
          fun h => h ▸ ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI'⟩⟩

/-! ## A word -/

/-- The words' invariant: `k` words of `r` from `t₀`. -/
def WI (p : RpP) (k : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t g : Nat), Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧
    WordInv t₀ p.B (wk p.k) N g r (bW p) k u

theorem wordHead_eq : wordHead = (ws ++ (base aM .rbx ++ ([.mov .rax (.mem (hdr sC1)), .alu .sub .rax (.imm 1)] :
    List Instr))) ++ ([.mov .rax (.mem (ix .rbx .rax)), .store (hdr sC2) .rax, .mov32 .rax (.imm 64),
      .store (hdr sC3) .rax] : List Instr) := by
  simp only [wordHead, List.append_assoc, List.cons_append, List.nil_append]

/-- `wordHead`'s registers before its load of the word. -/
def headVal (q : RpP × Nat) : Reg → BitVec 64
  | .rdi => q.1.B
  | .rbx => off q.1.B (slot (wk q.1.k) aM)
  | .rax => BitVec.ofNat 64 (bW q.1 - q.2 - 1)
  | _ => 0

theorem wordHead_ct : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < bW q.1 ∧ WI q.1 q.2 s) (.block wordHead)
    (Two fun (q : RpP × Nat) s => 0 < 64 ∧ BI q.1 0 s) := by
  rw [wordHead_eq]
  refine RelCT.block_append (ws_pin_ct (fun q : RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun (q : RpP × Nat) s ⟨_, t₀, minv, N, r, t, g, hc, _, _, hI⟩ => (hc.congr hI.frm (by decide) word_hs hI.keep
      (by decide)).ws) (by taint_decide) [.rdi, .rbx, .rax] headVal (fun q s h => ?_) (by taint_decide)
    fun q s h => ?_)
  · obtain ⟨hk, t₀, minv, N, r, t, g, hc, _, _, hI⟩ := h
    have hcu := hc.congr hI.frm (by decide) word_hs hI.keep (by decide)
    have h256 := hcu.ws.h256
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    rw [WP.block_append_iff]
    refine WP.mono hcu.ws.ws_ok fun u₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
    refine WP.mono (base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hcu.ws.rdi) h9)
      fun u₂ ⟨hbx, m₂, k₂⟩ => ?_
    have k12 := k₁.trans k₂
    have hs₂ := hcu.ws.scr.congr k12.2.2
    have hdi₂ : u₂.gpr .rdi = q.1.B := (k12.gpr (by decide)).trans hcu.ws.rdi
    have hc1 := hI.c1
    have hk' : q.2 < wk q.1.k + (q.1.el + 7) / 8 := hk
    have e1 : BitVec.ofNat 64 (bW q.1 - q.2) - 1 = BitVec.ofNat 64 (bW q.1 - q.2 - 1) :=
      ofNat64_pred (by simp only [bW]; omega) (by simp only [bW]; unfold wk at *; omega)
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (bW q.1 - q.2 - 1)) (by
      xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), m₂, m₁,
        hc1, e1]) rfl) fun u ⟨hax, k₃⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k₃.gpr (by decide)).trans hdi₂
    · exact (k₃.gpr (by decide)).trans hbx
    · exact hax
  · obtain ⟨hk, t₀, minv, N, r, t, g, hc, hGlt, hG, hI⟩ := h
    have hZ16 := hc.hZ16
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    have hm := hc.hm
    have hk' : q.2 < wk q.1.k + (q.1.el + 7) / 8 := hk
    have hBw2 : wk q.1.k + (q.1.el + 7) / 8 ≤ 2 * (wk q.1.k + 2) := by unfold wk at *; omega
    have hcu := hc.congr hI.frm (by decide) word_hs hI.keep (by decide)
    obtain ⟨i, hi₀⟩ : ∃ i, wk q.1.k + (q.1.el + 7) / 8 - q.2 = i + 1 := ⟨wk q.1.k + (q.1.el + 7) / 8 - q.2 - 1, by omega⟩
    have hi : bW q.1 - q.2 = i + 1 := hi₀
    have hc1 : word s.mem q.1.B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by rw [← hi]; exact hI.c1
    have sM := slot_lt (w := wk q.1.k) (show aM + 1 < 16 by decide)
    have eM1 : slot (wk q.1.k) (aM + 1) = slot (wk q.1.k) aM + 8 * (wk q.1.k + 2) := by
      simp only [slot, hdrBytes, aM]; omega
    have hZ := hcu.ws.hZ
    rw [WP.seq_iff, ← WP.block_append_iff, ← wordHead_eq]
    refine WP.mono (wordHead_ok hcu.ws hc1 (by omega) (by omega)) fun u₁ ⟨m₁, k₁⟩ => ⟨by decide, ?_⟩
    have hW : (word s.mem q.1.B (slot (wk q.1.k) aM + 8 * i)).toNat = r / 2 ^ (64 * i) % 2 ^ 64 := by
      have := word_of_wv s.mem q.1.B (slot (wk q.1.k) aM) (bW q.1) (q := i) (by omega)
      rw [hcu.hm] at this
      exact this
    have hf₁ : Frm q.1.B (rg (wk q.1.k) [] [sC2, sC3]) s.mem u₁.mem := by
      rw [m₁]
      exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega)) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega)) [] [sC2, sC3]
          (by decide))
    have hc₁ := hcu.congr hf₁ (by decide) (by decide) k₁ (by decide)
    have hGu : wv u₁.mem q.1.B (slot (wk q.1.k) aG) (wk q.1.k) = wv t₀.mem q.1.B (slot (wk q.1.k) aG) (wk q.1.k) := by
      rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega),
        hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]
    have hpow : r / 2 ^ (64 * i) / 2 ^ (64 - 0) = r / 2 ^ (64 * (bW q.1 - q.2)) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hi, Nat.sub_zero, Nat.mul_succ]
    have hW' : word s.mem q.1.B (slot (wk q.1.k) aM + 8 * i) =
        BitVec.ofNat 64 (r / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ 0 % 2 ^ 64) := by
      rw [← hW, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    refine ⟨u₁, minv, N, r, t, g, r / 2 ^ (64 * i), r / 2 ^ (64 * i) % 2 ^ 64, hc₁, by rw [hGu]; exact hGlt,
      by rw [hGu]; exact hG, rfl, Frm.refl _ _ _, Keep.refl _ _, ?_, ?_, ?_, ?_⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hI.ylt
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hpow]; exact hI.y
    · rw [m₁, (writeW_outside _ q.1.B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega)).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega)) (by simp only [sC2, sFn]; omega), word_writeW_self, hW']
    · rw [m₁, word_writeW_self]

theorem pins_BI : Pins (fun (p : RpP) s => BI p 64 s) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  obtain ⟨_, _, _, _, _, _, _, _, hc₁, _, _, _, hI₁⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _, _, hc₂, _, _, _, hI₂⟩ := h₂
  simp only [List.mem_singleton] at hr; subst hr
  rw [(hc₁.congr hI₁.frm (by decide) bit_hs hI₁.keep (by decide)).ws.rdi,
    (hc₂.congr hI₂.frm (by decide) bit_hs hI₂.keep (by decide)).ws.rdi]

/-- A word leaks the same in runs that agree on the public data. -/
theorem wordBody_ct (M : Mont) : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < bW q.1 ∧ WI q.1 q.2 s)
    (.seq (.block wordHead) (.seq (.loop (bitBody M.mm) .ne) (.block wordNext))) fun _ _ => True :=
  RelCT.seq wordHead_ct (RelCT.seq (two_map (fun q => q.1) (fun _ _ h => h) (bitLoop_ct M))
    (two_taint [.rdi] pins_BI (by taint_decide)))

theorem wordLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < bW p ∧ WI p 0 s)
    (.loop (.seq (.block wordHead) (.seq (.loop (bitBody M.mm) .ne) (.block wordNext))) .ne)
    (Two fun p s => WI p (bW p) s) :=
  two_loop bW (wordBody_ct M) fun _ _ _ hk ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI⟩ =>
    WP.mono (wordStep_ok M hc hGlt hG hk hI) fun _ ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hk hz, fun _ => ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI'⟩,
        fun h => h ▸ ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI'⟩⟩

/-- `expLoop`'s hypotheses. -/
def EX (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    wv s.mem p.B (slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = 2 ^ (64 * wk p.k) % N

/-- The exponentiation leaks the same in runs that agree on the public data. -/
theorem expLoop_ct (M : Mont) : RelCT isa (Two EX) (expLoop M.mm) (Two fun p s => WI p (bW p) s) := by
  unfold expLoop
  refine RelCT.seq (blk_gct RpP.B RpP.Z (fun p => wk p.k) (fun p s ⟨_, _, _, _, _, hc, _⟩ => hc.ws)
    (by taint_decide) fun p s h => ?_) (wordLoop_ct M)
  obtain ⟨minv, N, r, t, g, hc, hGlt, hG, hY⟩ := h
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hN : 0 < N := by have := hc.n1; omega
  unfold expInit
  refine WP.block_append_iff.mpr (WP.mono (bw_ok hc.ws hc.hel (by omega)) fun s₁ ⟨hax, m₁, k₁⟩ => ?_)
  have hs₁ := hc.ws.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hc.ws.rdi
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off p.B (8 * sC1))
      (BitVec.ofNat 64 (bW p))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hs₁.st (d := 8 * sC1) (by simp only [sC1, sCnt, sFn]; omega), hax, m₁])
    rfl) fun u ⟨mu, k₂⟩ => ⟨by simp only [bW]; unfold wk at *; omega, s, minv, N, r, t, g, hc, hGlt, hG, ?_⟩
  have hf₁ : Frm p.B (rg (wk p.k) [] [sC1]) s.mem u.mem := by
    rw [mu]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sCnt, sFn]; omega)) _ _
      (List.mem_singleton_self _)
  have hr : r < 2 ^ (64 * bW p) := hc.hm ▸ wv_lt _ _ _ _
  refine ⟨hf₁.rg_mono (by decide) (by decide), (k₁.trans k₂).mono (by decide), ?_, ?_, ?_⟩
  · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY]; exact Nat.mod_lt _ hN
  · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega), hY, Nat.sub_zero,
      Nat.div_eq_of_lt hr, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
  · rw [mu, word_writeW_self, Nat.sub_zero]

end Rp

end VG.Proof.Rsa.X86_64
