import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the halvings

`64 Bw` halvings, a public count (`halving_ct`): the counter in `r13` and
its bound in `r11` are pinned by correctness, and so are the bases and `Bw`
after each halving's head.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)
open VG.Spec.Rsa (splitTwos)

namespace Rp

/-- On entry to `rest`. -/
def GR0 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RestPre I m₀ I.N (I.D * I.E - 1) s ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

/-- The halvings' count, `64 Bw`. -/
abbrev hN (p : RpP) : Nat := 64 * (wk p.k + (p.el + 7) / 8)

/-- After `j` halvings, from `s₁`. -/
def HL (p : RpP) (j : Nat) (s : State) : Prop :=
  ∃ (s₁ : State) (m : Nat), Bignum.X86_64.word s₁.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) =
    BitVec.ofNat 64 p.el ∧ 1 ≤ p.el ∧ p.el ≤ 8 * wk p.k ∧ m < 2 ^ (64 * (wk p.k + (p.el + 7) / 8)) ∧
    s₁.gpr .r11 = BitVec.ofNat 64 (hN p) ∧ HalfInv s₁ p.B p.Z (wk p.k) m j s

theorem halfHead_eq : halfHead = ws ++ (base aM .r8 ++ base aH .rsi ++ bw ++
    ([.mov .r12 (.reg .rax), .mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1), .mov32 .rbp (.imm 0),
      .alu .sub .rbp (.reg .rax)] : List Instr)) := by
  simp only [halfHead, List.append_assoc]

/-- The registers a halving needs pinned after its head. -/
def halfVal (q : RpP × Nat) : Reg → BitVec 64
  | .rdi => q.1.B
  | .r8 => off q.1.B (slot (wk q.1.k) aM)
  | .rsi => off q.1.B (slot (wk q.1.k) aH)
  | .r12 => BitVec.ofNat 64 (wk q.1.k + (q.1.el + 7) / 8)
  | .r13 => BitVec.ofNat 64 q.2
  | .r11 => BitVec.ofNat 64 (hN q.1)
  | _ => 0

theorem halfBody_ct : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < hN q.1 ∧ HL q.1 q.2 s)
    (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 selBody, .block halfNext]) fun _ _ => True := by
  simp only [seqs]
  rw [halfHead_eq]
  refine (ws_pin_ct (Ψ := fun _ _ => True) (fun q : RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun q s h => by obtain ⟨-, s₁, m, -, -, -, -, -, hI⟩ := h; exact hI.ws) (by taint_decide)
    [.rdi, .r8, .rsi, .r12, .r13, .r11] halfVal (fun q s h => ?_) (by taint_decide) fun q s h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · rw [← halfHead_eq]
    obtain ⟨-, s₁, m, hel, he1, he2, -, h11, hI⟩ := h
    have hel₀ : Bignum.X86_64.word s.mem q.1.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 q.1.el := by
      have hT0 := hdr_lt_slot (wk q.1.k) aM (show Impl.Bignum.X86_64.Public.sElen < 32 by decide)
      have hT1 := hdr_lt_slot (wk q.1.k) aH (show Impl.Bignum.X86_64.Public.sElen < 32 by decide)
      have hZ := hI.ws.hZ
      rw [hI.frm.word_eq (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT] at * <;> omega)
        (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]
      exact hel
    exact WP.mono (halfHead_ok hI.ws hel₀ (by have := hI.ws.w2; omega))
      fun t ⟨h8, hsi, h12, _, hdi, _, k⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hdi
        · exact h8
        · exact hsi
        · exact h12
        · exact (k.gpr (by decide)).trans hI.r13
        · exact (k.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h11)
  · rw [← halfHead_eq]
    obtain ⟨hj, s₁, m, hel, he1, he2, hm, h11, hI⟩ := h
    have := halfStep_ok hI hel he1 he2 hm h11 hj
    simp only [seqs] at this
    exact WP.mono this fun _ _ => trivial

/-- After the halvings: `r` and `t`, and what Montgomery form needs. -/
def GR1 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ I.N % 2 = 1 ∧ 2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧
    wv s.mem I.B (slot (wk I.k) aN) (wk I.k) = I.N ∧
    ((word s.mem I.B (slot (wk I.k) aN)).toNat * (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = (splitTwos (I.D * I.E - 1)).2 ∧
    word s.mem I.B (8 * sT) = BitVec.ofNat 64 (splitTwos (I.D * I.E - 1)).1 ∧
    0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0 ∧ I.D * I.E - 1 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem halfInit_ct : RelCT isa (Two GR0) (.block halfInit) (Two fun p s => 0 < hN p ∧ HL p 0 s) :=
  two_piece [.rdi] (fun _ _ _ ⟨_, _, e₁, h₁, _⟩ ⟨_, _, e₂, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.S.ws.rdi, h₂.S.ws.rdi]
      exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm)
    (by taint_decide) fun p s h => by
      obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
      dsimp only [RpIn.pub]
      have hw := h.S.ws
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      have hZ := hw.hZ
      have hT0 := hdr_lt_slot (wk I.k) aM (show sT < 32 by decide)
      have L := h.L
      refine WP.mono (halfInit_ok hw h.S.args.el (by have := L.el2; have := L.k2; omega))
        fun t ⟨h11, h13, m₁, k₁⟩ => ⟨by show 0 < 64 * (wk I.k + (I.el + 7) / 8); unfold wk; have := L.k1; omega, t, I.D * I.E - 1, ?_, L.el1,
          by show I.el ≤ 8 * wk I.k; have := L.el2; unfold wk; omega, h.mlt, h11, ?_⟩
      · have o₁ := writeW_outside s.mem I.B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega)
        rw [← m₁] at o₁
        rw [o₁.word (Or.inl (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn, sT]; omega))
          (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega)]
        exact h.S.args.el
      · have o₁ := writeW_outside s.mem I.B (0 : BitVec 64) (d := 8 * sT) (by simp only [sT, sFn]; omega)
        rw [← m₁] at o₁
        have hf₁ : Frm I.B (rg (wk I.k) [] [sT]) s.mem t.mem := Frm.rg_of_hdr o₁ _ _ (List.mem_singleton_self _)
        dsimp only
        have hs₁ := slot_add (wk I.k) aM 2
        have hs₂ := slot_mono (w := wk I.k) (show aM + 2 ≤ 16 by decide)
        have hs₃ := hdr_lt_slot (wk I.k) aM (show sT < 32 by decide)
        exact ⟨hw.congrG hf₁ (by decide) k₁ (by decide), Keep.refl _ _, h13, Frm.refl _ _ _,
          by rw [o₁.wv (Or.inr (by omega)) (by omega), h.M]; rfl, by rw [m₁, word_writeW_self]; rfl⟩

theorem halfLoop_ct : RelCT isa (Two fun p s => 0 < hN p ∧ HL p 0 s)
    (.loop (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 selBody, .block halfNext]) .ne)
    (Two fun (_ : RpP) (_ : State) => True) :=
  two_loop hN halfBody_ct fun p j s hj h => by
    obtain ⟨s₁, m, hel, he1, he2, hm, h11, hI⟩ := h
    exact WP.mono (halfStep_ok hI hel he1 he2 hm h11 hj) fun s' ⟨hz, hI'⟩ =>
      ⟨eval_ne_count hj hz,
        fun _ => ⟨s₁, m, hel, he1, he2, hm, h11, hI'⟩, fun _ => trivial⟩

theorem halving_ct : RelCT isa (Two GR0) halving (Two GR1) :=
  two_post ((RelCT.seq halfInit_ct halfLoop_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
    have L := h.L
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := h.S.ws.scr.nowrap; have := h.S.ws.hZ; omega
    refine WP.mono (halving_ok h.S.ws h.S.args.el L.el1 (by have := L.el2; unfold wk; omega) h.M h.m0 h.mlt)
      fun t ⟨_, hr₁, ht₁, hf₁', k₁⟩ => ?_
    have hf₁ := frm_halving hf₁'
    refine ⟨I, m₀, rfl, h.S.step hf₁ (by decide) (by decide) k₁ (by decide), L, O, hv, h.odd, h.lo, ?_, ?_, hr₁, ht₁,
      h.m0, h.even, h.mlt⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega)]; exact h.n
    · rw [hf₁.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₁.rg_word (by decide) (by decide)]; exact h.inv

end Rp

end VG.Proof.Rsa.X86_64
