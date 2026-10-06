import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, Montgomery form

`mont` computes only from `n`, which is public: `R² mod n` leaks only
`n` (`r2_ct`, with `-n⁻¹`, a function of `n`, the same in both runs), and
the other pieces' loops count `w` words (`mont_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Spec.Rsa (splitTwos)

namespace Rp

/-- Before `R² mod n`. -/
def MR (q : R2Pub) (s : State) : Prop :=
  R2Pre q s ∧ Ws s q.L.B q.L.Z q.L.w ∧ word s.mem q.L.B (8 * sMinv) = q.L.minv

/-- Between `mont`'s pieces after `R² mod n`. -/
def MW (q : R2Pub) (s : State) : Prop :=
  Ws s q.L.B q.L.Z q.L.w ∧ word s.mem q.L.B (8 * sMinv) = q.L.minv ∧
    wv s.mem q.L.B (slot q.L.w aN) q.L.w = q.N ∧
    ((word s.mem q.L.B (slot q.L.w aN)).toNat * q.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧ 1 < q.N

/-- Before `setWord aOne`. -/
def MB (q : R2Pub) (s : State) : Prop :=
  MW q s ∧ s.gpr .r12 = BitVec.ofNat 64 q.L.w ∧ s.gpr .rcx = BitVec.ofNat 64 0 ∧ s.gpr .rdx = BitVec.ofNat 64 1

/-- After `setWord aOne`. -/
def MW1 (q : R2Pub) (s : State) : Prop := MW q s ∧ wv s.mem q.L.B (slot q.L.w aOne) q.L.w = 1

theorem pins_MW : Pins MW [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi]

theorem pins_MB : Pins MB [.rdi, .r12, .rcx] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.1.1.rdi, h₂.1.1.rdi]
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]

/-- `MW` after a piece that changes only arrays other than `n`. -/
theorem MW.step {q : R2Pub} {s t : State} (h : MW q s) {js : List Nat}
    (hf : Frm q.L.B (rg q.L.w js []) s.mem t.mem) (hN : aN ∉ js)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : MW q t := by
  obtain ⟨hw, hmv, hn, hi, h1⟩ := h
  have hZ16 : slot q.L.w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  refine ⟨hw.congrG hf (by simp) k hr, by rw [hf.rg_word (by decide) (by simp)]; exact hmv, ?_, ?_, h1⟩
  · rw [hf.rg_wv hZ16 (by simp) (by decide) hN (by omega)]; exact hn
  · rw [hf.rg_word0 hZ16 (by simp) (by decide) hN]; exact hi

theorem mr_bind (p : RpP) (s₁ s₂ : State)
    (h₁ : ∃ minv, MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s₁)
    (h₂ : ∃ minv, MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s₂) : ∃ q, MR q s₁ ∧ MR q s₂ := by
  obtain ⟨mi₁, h₁⟩ := h₁
  obtain ⟨mi₂, h₂⟩ := h₂
  have e : ∀ {s : State} {mi : BitVec 64}, MR ⟨⟨p.B, p.Z, wk p.k, mi⟩, Spec.Rsa.os2ip p.nb⟩ s →
      (word s.mem p.B (slot (wk p.k) aN)).toNat = Spec.Rsa.os2ip p.nb % 2 ^ 64 := fun h => by
    rw [← wv_mod64 _ _ _ (show 1 ≤ wk p.k by have : 2 ≤ wk p.k := h.1.2.1; omega), h.1.2.2.2.1]
  have i₁ := h₁.1.2.2.2.2.1
  have i₂ := h₂.1.2.2.2.2.1
  rw [e h₁] at i₁
  rw [e h₂] at i₂
  obtain rfl := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.1.2.2.2.2.2.2.2.1) i₁ i₂
  exact ⟨_, h₁, h₂⟩

/-- The loads of `w` and `n`'s base, and `R² mod n`. -/
theorem montR2_ct (M : Mont) :
    RelCT isa (Two GR1) (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))])
      (seqs (r2Steps M))) (Two MW) := by
  refine RelCT.seq (R := Two MR) ((two_piece (Ψ := fun p s => ∃ minv,
      MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s) [.rdi]
    (fun _ _ _ ⟨_, _, e₁, h₁, _⟩ ⟨_, _, e₂, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]
      exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ h => two_bind mr_bind h) ?_
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hodd, hlo, hn, hinv, -⟩ := h
    dsimp only [RpIn.pub]
    have hw := S.ws
    have hn0 := hw.scr.nowrap
    have h256 := hw.h256
    have hZ := hw.hZ
    have hw1 := hw.w1
    have hw2 := hw.w2
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega)
    refine WP.mono (WP.keep [.r12, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (wk I.k) ∧
        t.gpr .r10 = off I.B (slot (wk I.k) aN) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl _ (show sW < 32 by decide), hl _ (show sArr aN < 32 by decide),
        hw.hw, hw.harr aN (by decide)]) rfl) fun t ⟨⟨h12, h10, m₁⟩, k₁⟩ => ⟨word t.mem I.B (8 * sMinv), ?_⟩
    have hw₁ : Ws t I.B I.Z (wk I.k) :=
      hw.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
    exact ⟨⟨hw₁.good, hw1, show wk I.k < 2 ^ 30 by omega, by rw [m₁]; exact hn, by rw [m₁]; exact hinv, h12, h10, hodd, hlo⟩, hw₁, rfl⟩
  · refine two_post ((two_map id (fun _ _ h => h.1) (r2_ct M)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun q s ⟨⟨hg, hw1, hw30, hn, hinv, h12, h10, hodd, hlo⟩, hw, hmv⟩ => ?_
    have hZ16 : slot q.L.w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    have hN1 : 1 < q.N := by
      have : 2 ^ 64 ≤ 2 ^ (64 * (q.L.w - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine WP.mono (r2_ok M hg.1 hg.2 hw1 hw30 hn hinv h12 h10 hodd hlo) fun t ⟨hg₂, _, _, hf₂, k₂⟩ => ?_
    have hf₂' : Frm q.L.B (rg q.L.w [aAcc, aTmp, aR2] [sCnt]) s.mem t.mem := hf₂
    exact ⟨hw.congrG hf₂' (by decide) k₂ (by decide), hg₂.hdr.hminv,
      by rw [hf₂'.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hn,
      by rw [hf₂'.rg_word0 hZ16 (by decide) (by decide) (by decide)]; exact hinv, hN1⟩

/-- `setWord`'s registers after its load. -/
def swVal (q : R2Pub) : Reg → BitVec 64
  | .r8 => off q.L.B (slot q.L.w aOne)
  | .r12 => BitVec.ofNat 64 q.L.w
  | .rcx => BitVec.ofNat 64 0
  | _ => 0

/-- 1, 0 and `w`. -/
theorem montB_ct : RelCT isa (Two MW) (.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0),
    .mov .r12 (.mem (hdr sW))]) (Two MB) :=
  two_piece [.rdi] pins_MW (by taint_decide) fun q s h => by
    have hw := h.1
    refine WP.mono (WP.keep [.rdx, .rcx, .r12] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 1 ∧
        t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.gpr .r12 = BitVec.ofNat 64 q.L.w ∧ t.mem = s.mem) (by
      have := hw.h256
      xrun [State.ea, hdr, hw.rdi, hdrOff, hw.scr.ld (d := 8 * sW) (by simp only [sW]; omega), hw.hw]) rfl)
      fun t ⟨⟨hdx, hcx, h12, m⟩, k⟩ => ⟨h.step (js := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) k (by decide), h12, hcx, hdx⟩

/-- 1 into its array. -/
theorem montSet_ct : RelCT isa (Two MB) (setWord aOne .rcx) (Two MW1) := by
  rw [setWord_eq]
  refine pin_ct [.rdi, .r12, .rcx] [.r8, .r12, .rcx] swVal pins_MB (by taint_decide) (fun q s h => ?_)
    (by taint_decide) fun q s h => ?_
  · have hw := h.1.1
    have := hw.h256
    have hl : InRegions (s.rd ++ s.wr) (off q.L.B (8 * sArr aOne)) 8 :=
      hw.scr.ld (by have := hw.hZ; have := hdr_lt_slot q.L.w 16 (show sArr aOne < 32 by decide); omega)
    refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off q.L.B (slot q.L.w aOne)) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl, hw.harr aOne (by decide)]) rfl) fun t ⟨h8, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h8
    · exact (k.gpr (by decide)).trans h.2.1
    · exact (k.gpr (by decide)).trans h.2.2.1
  · rw [← setWord_eq]
    obtain ⟨hM, h12, hcx, hdx⟩ := h
    have hw := hM.1
    have hw1 := hw.w1
    have hw2 := hw.w2
    have hH : Hdr s.mem q.L.B q.L.w q.L.minv := ⟨hw.hw, hM.2.1, fun j hj => hw.harr j hj⟩
    refine WP.mono (setWord_ok hw.scr hw.rdi hH hw.good.2 h12 (by omega) (by omega) (o := aOne) (by decide)
      (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t ⟨hv, o, k⟩ => ?_
    rw [hdx, BitVec.toNat_ofNat] at hv
    have hf : Frm q.L.B (rg q.L.w [aOne] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    exact ⟨hM.step hf (by decide) k (by decide), by rw [hv]⟩

/-- `Y = R mod n`. -/
theorem montY_ct (M : Mont) : RelCT isa (Two MW1) (M.mm aY aR2 aOne) (Two MW) :=
  two_post (two_map (fun q => (⟨q.L.B, q.L.Z, q.L.w⟩ : Bignum.X86_64.Ws)) (fun _ _ h => ⟨_, h.1.1.good⟩)
    (M.ct (by unfold MmUse; decide))) fun q s ⟨hM, h1⟩ => by
    have hw := hM.1
    have hg := hw.good
    rw [hM.2.1] at hg
    exact WP.mono (M.mm_ok hg.1 hg.2 hw.w1 (by have := hw.w2; omega) (o := aY) (a := aR2) (b := aOne) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hM.2.2.2.1
      (by rw [h1, hM.2.2.1]; exact hM.2.2.2.2)) fun t ⟨_, _, _, ha, k⟩ =>
      hM.step (Frm.rg_of_arrays ha [aAcc, aTmp, aY] [] (by decide)) (by decide) k (by decide)

/-- `R mod n` into its array. -/
theorem montO_ct : RelCT isa (Two MW) (copyA aO aY) (Two fun (q : R2Pub) s => Ws s q.L.B q.L.Z q.L.w) := by
  have e : copyA aO aY = .seq (.block (ws ++ (base aY .rsi ++ base aO .rbx))) VG.Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact ws_ct (Φ := MW) (Ψ := fun q s => Ws s q.L.B q.L.Z q.L.w) (fun q : R2Pub => q.L.B) (fun q => q.L.Z) (fun q => q.L.w) (fun _ _ h => h.1) (by taint_decide)
    fun q s h => by
      rw [← e]
      exact WP.mono (copyA_ok h.1 (o := aO) (a := aY) (by decide) (by decide) (by decide)) fun t ⟨_, o, k⟩ =>
        h.1.congrG (Frm.rg_of_out o (by omega) [aO] [] (by decide)) (by simp) k (by decide)

/-- `n - R mod n`. -/
theorem montNg_ct : RelCT isa (Two fun (q : R2Pub) s => Ws s q.L.B q.L.Z q.L.w)
    (.seq (.block (ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))
      (wordLoop 0 subBody)) fun _ _ => True := by
  have e : (.seq (.block (ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]))
      (wordLoop 0 subBody) : Prog isa) = .seq (.block (ws ++ (base aN .r8 ++ (base aO .r10 ++
        (base aNg .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subBody) := by
    simp only [List.append_assoc]
  rw [e]
  refine (ws_ct (Ψ := fun _ _ => True) (fun q : R2Pub => q.L.B) (fun q => q.L.Z) (fun q => q.L.w)
    (fun _ _ h => h) (by taint_decide) fun q s hw => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  rw [← e]
  have hn0 := hw.scr.nowrap
  have hZ := hw.hZ
  have hw1 := hw.w1
  have hw2 := hw.w2
  refine WP.seq (WP.mono (subSet_ok hw aN aO aNg) fun t ⟨h12, h8, h10, hsi, hbp, _, k⟩ => ?_)
  exact WP.mono (sub_ok (hw.scr.congr k.2.2) h8 h10 hsi h12 hbp (by omega) (by omega)
    (by have := hw.sl (j := aN) (by decide); omega) (by have := hw.sl (j := aO) (by decide); omega)
    (by have := hw.sl (j := aNg) (by decide); omega)
    (by have := slot_far (w := q.L.w) (show aNg ≠ aN by decide); omega)
    (by have := slot_far (w := q.L.w) (show aNg ≠ aO by decide); omega)) fun _ _ => trivial

/-- `mont` leaks only `n`. -/
theorem montT_ct (M : Mont) : RelCT isa (Two GR1) (seqs (mont M.mm)) fun _ _ => True := by
  rw [show mont M.mm = ([.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))]] ++ r2Steps M) ++
    [.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))],
      setWord aOne .rcx, M.mm aY aR2 aOne, copyA aO aY,
      .block (ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody] from rfl]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (montR2_ct M) ?_)
  simp only [seqs]
  exact RelCT.seq montB_ct (RelCT.seq montSet_ct (RelCT.seq (montY_ct M) (RelCT.seq montO_ct montNg_ct)))

/-- After Montgomery form: what the candidates need. -/
def GR2 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) (word s.mem I.B (8 * sMinv)) I.N I.el (splitTwos (I.D * I.E - 1)).2
      (splitTwos (I.D * I.E - 1)).1 ∧ 0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0

theorem mont_ct (M : Mont) : RelCT isa (Two GR1) (seqs (mont M.mm)) (Two GR2) :=
  two_post (montT_ct M) fun p s h => by
    obtain ⟨I, m₀, rfl, S₁, L, O, hv, hodd, hlo, hn₁, hi₁, hr₁, ht₁, hm0, heven, hmlt⟩ := h
    have hk1 := L.k1
    have hel1 := L.el1
    have hel2 := L.el2
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S₁.ws.scr.nowrap; have := S₁.ws.hZ; omega
    refine WP.mono (mont_ok M S₁.ws hi₁ hn₁ hodd hlo)
      fun s₂ ⟨_, hr2lt, hr2, hone, ho, hng, hf₂, k₂⟩ => ⟨I, m₀, rfl, ?_⟩
    have S₂ := S₁.step hf₂ (by decide) (by decide) k₂ (by decide)
    have hspl := VG.Proof.Rsa.splitTwos_spec hm0
    have hrlt : (splitTwos (I.D * I.E - 1)).2 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := by
      have : (splitTwos (I.D * I.E - 1)).2 ≤ I.D * I.E - 1 :=
        calc (splitTwos (I.D * I.E - 1)).2
            ≤ 2 ^ (splitTwos (I.D * I.E - 1)).1 * (splitTwos (I.D * I.E - 1)).2 :=
              Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
          _ = I.D * I.E - 1 := hspl.1.symm
      omega
    have ht1 : 1 ≤ (splitTwos (I.D * I.E - 1)).1 := by
      rcases Nat.eq_zero_or_pos (splitTwos (I.D * I.E - 1)).1 with h0 | h0
      · have := hspl.1; rw [h0, Nat.pow_zero, Nat.one_mul] at this; have := hspl.2; omega
      · exact h0
    have ht2 := VG.Proof.Rsa.splitTwos_lt hm0 hmlt
    refine ⟨S₂, L, O, hv, ⟨S₂.ws, rfl, ?_, ?_, hr2lt, hr2, hone, ho, hng, S₂.args.el, ?_, ?_, hodd, hlo, hel1,
      by unfold wk; omega, ht1, ht2⟩, hm0, heven⟩
    · rw [hf₂.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₂.rg_word (by decide) (by decide)]; exact hi₁
    · rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact hn₁
    · rw [hf₂.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by unfold wk; omega)]
      rw [wv_low_of_lt (v := wk I.k + (I.el + 7) / 8) (w := 2 * (wk I.k + 2)) (by unfold wk; omega)
        (by rw [hr₁]; exact hrlt), hr₁]
    · rw [hf₂.rg_word (by decide) (by decide)]; exact ht₁

end Rp

end VG.Proof.Rsa.X86_64
