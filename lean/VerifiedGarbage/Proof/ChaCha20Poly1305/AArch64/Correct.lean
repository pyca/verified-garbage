import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# ChaCha20-Poly1305 on AArch64: correctness

`seal` and `open`, from their parts: the code up to the tag (`sealMain`,
`openMain`, and their stitched forms), which leaves what `MainS` and `MainO`
say, and then the tag (`sealTail`, `openTail`), the same for every backend.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_movz wp_ldr)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the additional data, the data and the tag. (Matching
only reducibly, so that a lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by lit_omega) (by lit_omega) (by lit_omega)
  | with_reducible exact (‹APre _ _›).c_d.sub_left (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).c_d.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).c_a.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).a_d
  | with_reducible exact (‹APre _ _›).c_t.sub_left (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).c_t.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).d_t
  | with_reducible exact (‹APre _ _›).d_t.symm)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem hRDX (s₀ : State) : s₀.gpr .x3 = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .x3).isLt, hp.wrap_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.a_rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .x5).isLt, hp.wrap_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.d_wr], hc⟩⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The callee-saved registers on return: those saved in the context are
restored, and the others were never changed. -/
theorem preserved_split : ∀ r ∈ preserved, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30, .x6] →
    r ∈ untouched ∧ r ≠ .x30 := by decide

theorem abi_of0 {s₀ s s₁ s' : State} (h : Inv0 s₀ s)
    (hk : ∀ r ∈ preserved, r ≠ .x30 → s₁.gpr r = s.gpr r)
    (hr : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s₀.gpr r)
    (hg : ∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30, .x6] → s'.gpr r = s₁.gpr r)
    (hsp : s'.sp = s.sp) : GprAbi s₀ s' := by
  refine ⟨fun r hr' => ?_, by rw [hsp, h.sp]⟩
  by_cases hm : r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30]
  · exact hr r hm
  · have hm' : r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30, .x6] := by
      intro h'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h' hm
      rcases h' with h' | h' | h' | h' | h' | h' | rfl
      · exact hm (.inl h')
      · exact hm (.inr (.inl h'))
      · exact hm (.inr (.inr (.inl h')))
      · exact hm (.inr (.inr (.inr (.inl h'))))
      · exact hm (.inr (.inr (.inr (.inr (.inl h')))))
      · exact hm (.inr (.inr (.inr (.inr (.inr h')))))
      · exact absurd hr' (by decide)
    have hu := preserved_split r hr' hm'
    rw [hg r hm', hk r hr' hu.2, h.un r hu.1]

/-! ## The tag -/

/-- What holds after `seal`'s code but the tag (`sealTail`). -/
structure MainS (s₀ s : State) : Prop where
  inv : Inv0 s₀ s
  vec : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀)
    (macData (A s₀) (Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)))
  ct : bytesAt s.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

/-- What holds after `open`'s code but the comparison of the tags
(`openTail`). -/
structure MainO (s₀ s : State) : Prop where
  inv : Inv0 s₀ s
  vec : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  tag : bytesAt s.mem (off (cx s₀) 48) 16 = mac (otk s₀) (macData (A s₀) (D s₀))
  pt : bytesAt s.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

/-- The address of `tag`, loaded from the context into `r`. -/
theorem tagPtr_ok {r : Reg} {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀)
    (hsv : Saved s₀ s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ([Instr.ldr .x r .x21 624].all fun i => preserved.all fun r' => dstOf i != some r') = true) :
    WP isa (.block [.ldr .x r .x21 624]) s fun s' => s'.gpr r = tp s₀ ∧ Kept [] s s' := by
  have hs : s.mem.readW (off (cx s₀) 624) 64 = tp s₀ := hsv (.x6, 624) (by decide)
  have h : WP isa (.block [.ldr .x r .x21 624]) s fun s' =>
      s'.gpr r = tp s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_ldr (a := off (cx s₀) 624) (by decide) (by rw [hx21]) (by rw [hrd, hwr]; exact hp.in_ctx' (by lit_omega))
      fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, hs], u₁.rd, u₁.wr, u₁.mem⟩
  exact WP.mono (WP.kept h hk) fun s' ⟨⟨h0, hrd', hwr', hm⟩, hg, hsp⟩ =>
    ⟨h0, Kept.of hg hsp hrd' hwr' (by rw [hm]; exact Frame.refl _ _)⟩

/-- `x0 = x21 + 448`, `x1 = 0` and `x3 = x21 + 632`. -/
theorem ftptrs_ok (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x3 .x21 632]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = s.gpr .x2 ∧ Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x3 .x21 632]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = s.gpr .x2 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ =>
      wp_addImm (by decide) fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr]; rfl,
        by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- The tag written to `tag` (its address in `x2`). -/
theorem finalizeTag_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : Inv0 s₀ s)
    (hx2 : s.gpr .x2 = tp s₀) :
    WP isa finalizeTag s fun s' => Kept [sub s₀ 448 128, tR s₀] s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (tp s₀) 16 = mac key msg := by
  unfold finalizeTag
  refine WP.seq (WP.mono (ftptrs_ok s) fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0
  rw [hx2] at h2
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  have hw : Covers [sub s₀ 448 128, tR s₀] s₁.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁]; exact hp.ctx_wr, 448, rfl, by show 448 + 128 ≤ 760; omega⟩
    · exact ⟨tR s₀, by rw [wr₁]; exact hp.t_wr, 0, by simp, by simp⟩
  refine finalize_call h0 h1 h2 (hp.c_t.sub_left (sub_ctx s₀ (by lit_omega))) (Covers.right hw) hw
    fun s₂ k₂ tag₂ => ?_
  exact ⟨(k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂,
    fun key msg hr => tag₂ key msg (by rw [m₁]; exact hr)⟩

theorem sealTail_ok {s₀ s : State} (hp : APre true s₀) (h : MainS s₀ s) :
    WP isa sealTail s fun s' => abiPreserved s₀ s' ∧ sealAArch64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold sealTail
  refine WP.seq (WP.mono (WP.preservedV (tagPtr_ok (r := .x2) hp h.inv.x21 h.inv.saved h.inv.rd h.inv.wr
    (by decide)) (by lit_decide)) fun s₁ ⟨⟨x2₁, k₁⟩, v₁⟩ => ?_)
  have i₁ : Inv0 s₀ s₁ := h.inv.step k₁ (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)
  refine WP.seq (WP.mono (WP.preservedV (finalizeTag_ok hp i₁ x2₁) (by lit_decide)) fun s₂ ⟨⟨k₂, tag₂⟩, v₂⟩ => ?_)
  refine WP.mono (WP.preservedV (restore_ok hp (by rw [k₂.cs _ (pres .x21) (pres30 .x21), i₁.x21])
    (i₁.saved.frame k₂.frame (by rdisj_all)) (by rw [k₂.rd, i₁.rd]) (by rw [k₂.wr, i₁.wr])) (by lit_decide))
    fun s₃ ⟨⟨⟨rs₃, g₃, m₃⟩, sp₃⟩, v₃⟩ => ?_
  have hg := abi_of0 i₁ k₂.cs rs₃ g₃ (by rw [sp₃, k₂.sp])
  refine ⟨⟨hg.1, hg.2, fun r hr => (v₃ r hr).trans ((v₂ r hr).trans ((v₁ r hr).trans (h.vec r hr)))⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₃.mem (dp s₀) (L s₀), bytesAt s₃.mem (tp s₀) 16)
  rw [m₃, tag₂ _ _ (by rw [k₁.mem_eq]; exact h.poly), bytesAt_frame k₂.frame (by rdisj_all) hL', k₁.mem_eq, h.ct]
  rfl

theorem openTail_ok {s₀ s : State} (hp : APre false s₀) (h : MainO s₀ s) :
    WP isa openTail s fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' := by
  unfold openTail
  refine WP.seq (WP.mono (WP.preservedV (tagPtr_ok (r := .x12) hp h.inv.x21 h.inv.saved h.inv.rd h.inv.wr
    (by decide)) (by lit_decide)) fun s₁ ⟨⟨x12₁, k₁⟩, v₁⟩ => ?_)
  have m₁ := k₁.mem_eq
  have x21₁ : s₁.gpr .x21 = cx s₀ := by rw [k₁.cs _ (pres .x21) (pres30 .x21), h.inv.x21]
  refine WP.block_append (WP.mono (WP.preservedV (compare_ok hp x21₁ x12₁ (by rw [k₁.rd, h.inv.rd])
    (by rw [k₁.wr, h.inv.wr])) (by lit_decide)) fun s₂ ⟨⟨rax₂, g₂, sp₂, m₂, rd₂, wr₂⟩, v₂⟩ => ?_)
  refine WP.mono (WP.preservedV (restore_ok hp (by rw [g₂ _ (pres .x21), x21₁])
    (by rw [m₂, m₁]; exact h.inv.saved) (by rw [rd₂, k₁.rd, h.inv.rd]) (by rw [wr₂, k₁.wr, h.inv.wr])) (by lit_decide))
    fun s₃ ⟨⟨⟨rs₃, g₃, m₃⟩, sp₃⟩, v₃⟩ => ?_
  have hg := abi_of0 h.inv (fun r hr h30 => by rw [g₂ r hr, k₁.cs r hr h30]) rs₃
    (fun r hr => by rw [g₃ r hr]) (by rw [sp₃, sp₂, k₁.sp])
  refine ⟨⟨hg.1, hg.2, fun r hr => (v₃ r hr).trans ((v₂ r hr).trans ((v₁ r hr).trans (h.vec r hr)))⟩, ?_⟩
  have T0₁ : bytesAt s₁.mem (tp s₀) 16 = T0 s₀ := by
    rw [m₁, bytesAt_frame h.inv.frame (by rdisj_all) (by lit_omega)]
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₁.mem (off (cx s₀) 48) 16 := by
    rw [m₁, h.tag]
  rw [openAArch64, Contract.post_mk]
  rw [g₃ .x0 (by decide), rax₂]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₁.symm)), by rw [m₃, m₂, m₁, h.pt]⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₁)

/-! ## The scalar backend -/

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealMain v.callee) s₀ (MainS s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold sealMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.x21
    h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (crypt_ok v hp i₃ st₃) fun s₄ ⟨v₄, i₄, k₄, ct₄⟩ => ?_)
  rw [D₃] at ct₄
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄.x21
    i₄.rd i₄.wr i₄.x22 (by rw [i₄.x23]; exact hL s₀)) (by lit_decide))
    fun s₅ ⟨⟨k₅, r₅⟩, v₅⟩ => ?_)
  have i₅ := mac_inv i₄ k₅
  refine WP.mono (WP.preservedV (absorbLengths_ok hp i₅) (by lit_decide)) fun s₆ ⟨⟨i₆, k₆, r₆⟩, v₆⟩ => ?_
  have R₄ := Repr.frame k₄.frame (by rdisj_all) (Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have R₆ := r₆ _ _ (r₅ _ _ R₄)
  have L₅ : bytesAt s₅.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega), bytesAt_frame k₄.frame (by rdisj_all) (by lit_omega),
      len₃]
  rw [L₅, ct₄, hA] at R₆
  refine ⟨i₆.inv0, fun r hr => (v₆ r hr).trans ((v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans
      ((v₂ r hr).trans (v₁ r hr))))), ?_, ?_⟩
  · refine (congrArg (Repr s₆.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₆
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₆.frame (by rdisj_all) hL', bytesAt_frame k₅.frame (by rdisj_all) hL', ct₄]

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openMain v.callee) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold openMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.x21
    h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₂.x21
    i₂.rd i₂.wr i₂.x22 (by rw [i₂.x23]; exact hL s₀)) (by lit_decide))
    fun s₃ ⟨⟨k₃, r₃⟩, v₃⟩ => ?_)
  have i₃ := mac_inv i₂ k₃
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₃) (by lit_decide)) fun s₄ ⟨⟨i₄, k₄, len₄⟩, v₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok hp i₄) (by lit_decide)) fun s₅ ⟨⟨i₅, k₅, r₅⟩, v₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₅.frame (by rdisj_all), stateAt_frame k₄.frame (by rdisj_all),
      stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono (crypt_ok v hp i₅ st₅) fun s₆ ⟨v₆, i₆, k₆, pt₆⟩ => ?_)
  refine WP.mono (WP.preservedV (finalizeTo_ok hp i₆ (out := 48) (by omega)) (by lit_decide))
    fun s₇ ⟨⟨k₇, tag₇⟩, v₇⟩ => ?_
  have R₃ := r₃ _ _ (r₂ (otk s₀) [] h₁.poly)
  have T₇ := tag₇ _ _ (Repr.frame k₆.frame (by rdisj_all) (r₅ _ _ (Repr.frame k₄.frame (by rdisj_all) R₃)))
  rw [len₄, D₂, hA] at T₇
  refine ⟨i₆.inv0.step k₇ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₇ r hr).trans ((v₆ r hr).trans
      ((v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', pt₆, bytesAt_frame k₅.frame (by rdisj_all) hL',
      bytesAt_frame k₄.frame (by rdisj_all) hL', bytesAt_frame k₃.frame (by rdisj_all) hL', D₂]

theorem seal_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sealAArch64.post s₀ s' :=
  WP.seq (WP.mono (sealMain_ok v hp) fun _ h => sealTail_ok hp h)

theorem open_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' :=
  WP.seq (WP.mono (openMain_ok v hp) fun _ h => openTail_ok hp h)

end VG.Proof.ChaCha20Poly1305.AArch64

end
