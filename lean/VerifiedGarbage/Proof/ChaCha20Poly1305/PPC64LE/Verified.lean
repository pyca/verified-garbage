module

import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Tail
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Tail
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Mac
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Prologue
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Prologue

/-!
# ChaCha20-Poly1305 on PPC64LE: `Verified`

`seal` and `open`, from their parts: up to the arguments of
`vg_poly1305_finalize_scratch` (`sealMain`, `openMain`), the call, and the
rest. Constant time is the taint analysis of the whole of each function,
through its callees: the values it keeps in `r24`–`r29`, which no callee
writes, stay public across the calls. Then the functions, which allocate the
working space in a frame of 688 bytes on the stack and wipe it after the
code (`Verified.stackScratchWiped`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The ciphertext `seal` computes. -/
abbrev Ct (s₀ : State) : List Byte := Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .r6).isLt, hp.fit_a, hp.a_c.symm, hp.b_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hp.a_rd, hc⟩⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .r8).isLt, hp.fit_d, hp.d_c.symm, hp.b_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ hp.d_wr, hc⟩⟩

theorem hAL (s₀ : State) : s₀.gpr .r6 = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem hL (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_c
    · exact hp.a_d
    · exact hp.b_a.symm) (Nat.le_of_lt (s₀.gpr .r6).isLt)

/-- `tag` is unchanged while the invariant holds. -/
theorem tag_eq0 {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (tp s₀) 16 = T0 s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.t_c
    · exact hp.d_t.symm
    · exact hp.b_t.symm) (by decide)

/-- The data is unchanged by a frame of parts of the context and the stack below. -/
theorem data_frame {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∃ k n, (k + n ≤ 648 ∧ Region.Sub r (sub s₀ k n)) ∨ r = belR s₀) :
    bytesAt m' (dp s₀) (L s₀) = bytesAt m (dp s₀) (L s₀) :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨k, n, h⟩ := hd r hr
    rcases h with ⟨hk, hs⟩ | rfl
    · exact (hp.d_c.sub_right (sub_ctx s₀ hk)).sub_right hs
    · exact hp.b_d.symm) (Nat.le_of_lt (s₀.gpr .r8).isLt)

theorem sub_self' (s₀ : State) (k n : Nat) : Region.Sub (sub s₀ k n) (sub s₀ k n) := fun _ h => h

/-- What `macPad` writes, as `data_frame` wants it. -/
theorem macR_hd (s₀ : State) : ∀ r ∈ macR s₀, ∃ k n, (k + n ≤ 648 ∧ Region.Sub r (sub s₀ k n)) ∨ r = belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨0, 128, .inl ⟨by decide, sub_self' _ _ _⟩⟩
  · exact ⟨padOff, 16, .inl ⟨by decide, sub_self' _ _ _⟩⟩
  · exact ⟨0, 0, .inr rfl⟩

/-- What `lengths` writes, as `data_frame` wants it. -/
theorem lenR_hd (s₀ : State) :
    ∀ r ∈ macR s₀ ++ [sub s₀ lenOff 16], ∃ k n, (k + n ≤ 648 ∧ Region.Sub r (sub s₀ k n)) ∨ r = belR s₀ := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact macR_hd s₀ r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨lenOff, 16, .inl ⟨by decide, sub_self' _ _ _⟩⟩

theorem macData_eq (a c : List Byte) :
    macData a c = [] ++ (a ++ pad16 a) ++ (c ++ pad16 c) ++ (leBytes 8 a.length ++ leBytes 8 c.length) := by
  simp [macData, List.append_assoc]

/-- The MAC so far, from the Poly1305 state for the one-time key: the
additional data and the text `x`, padded, and the lengths. -/
theorem mac_parts {s₀ s₁ s₂ s₃ s₄ : State} {x : List Byte} (hx : x.length = L s₀)
    (hr₁ : Repr s₁.mem (cx s₀) (otk s₀) [])
    (ha : ∀ key msg, Repr s₁.mem (cx s₀) key msg → Repr s₂.mem (cx s₀) key (msg ++
      (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))))
    (hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀)
    (hd : ∀ key msg, Repr s₂.mem (cx s₀) key msg → Repr s₃.mem (cx s₀) key (msg ++ (x ++ pad16 x)))
    (hl : ∀ key msg, Repr s₃.mem (cx s₀) key msg →
      Repr s₄.mem (cx s₀) key (msg ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀)))) :
    Repr s₄.mem (cx s₀) (otk s₀) (macData (A s₀) x) := by
  have := hl _ _ (hd _ _ (ha _ _ hr₁))
  rw [hA] at this
  rwa [macData_eq, show (A s₀).length = AL s₀ from VG.Proof.Poly1305.length_bytesAt _ _ _, hx]

/-! ## Seal -/

/-- Before `vg_poly1305_finalize_scratch` in `seal`. -/
structure PreFs (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  r3 : s.gpr .r3 = cx s₀
  r4 : (s.gpr .r4).toNat % 16 = 0
  r5 : s.gpr .r5 = tp s₀
  r6 : s.gpr .r6 = off (cx s₀) scrOff
  repr : Repr s.mem (cx s₀) (otk s₀) (macData (A s₀) (Ct s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = Ct s₀

theorem sealMain_ok {s₀ : State} (hp : APre true s₀) : WP isa sealMain s₀ (PreFs s₀) := by
  unfold sealMain
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = D s₀ :=
    data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 648, .inl ⟨Nat.le_refl _, by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 256, .inl ⟨by decide, sub_self' _ _ _⟩⟩
      · exact ⟨keyOff, 32, .inl ⟨by decide, sub_self' _ _ _⟩⟩, d₁]
  refine WP.seq (WP.mono (crypt_ok hp h₂.inv h₂.st) fun s₃ ⟨i₃, k₃, c₃⟩ => ?_)
  rw [d₂] at c₃
  have key₃ : bytesAt s₃.mem (off (cx s₀) keyOff) 32 = otk s₀ := by
    rw [bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (by decide) (by decide) (by decide)
        · exact (hp.d_c.sub_right (sub_ctx s₀ (by decide))).symm) (by decide), h₂.key]
  refine WP.seq (WP.mono (polyInit_ok hp i₃ key₃) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Ct s₀ := by
    rw [data_frame hp k₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by decide, sub_self' _ _ _⟩⟩, c₃]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r25) (n := .r26) (.inl ⟨rfl, rfl⟩) (srcA hp) i₄ i₄.regs.r25
    (by rw [i₄.regs.r26]; exact hAL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have c₅ : bytesAt s₅.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₅.frame (macR_hd s₀), c₄]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r27) (n := .r28) (.inr ⟨rfl, rfl⟩) (srcD hp) i₅ i₅.regs.r27
    (by rw [i₅.regs.r28]; exact hL s₀)) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have c₆ : bytesAt s₆.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₆.frame (macR_hd s₀), c₅]
  refine WP.seq (WP.mono (lengths_ok hp i₆) fun s₇ ⟨i₇, k₇, r₇⟩ => ?_)
  have c₇ : bytesAt s₇.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₇.frame (lenR_hd s₀), c₆]
  refine WP.mono (finArgs_ok i₇ (out_seal i₇)) fun s₈ ⟨i₈, k₈, h3, h5, h6, h4⟩ => ?_
  have hlen : (Ct s₀).length = L s₀ := by
    rw [length_encrypt, VG.Proof.Poly1305.length_bytesAt]
  refine ⟨i₈, h3, h4, h5, h6, ?_, by rw [k₈.mem_eq, c₇]⟩
  rw [k₈.mem_eq]
  refine mac_parts hlen r₄ r₅ (aad_eq hp i₄) ?_ r₇
  rw [c₅] at r₆
  exact r₆

/-- After `vg_poly1305_finalize_scratch` in `seal`: the tag written, and what
restoring the registers needs. -/
structure PostFs (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  pres : ∀ r ∈ preserved, (∀ i < 6, r ≠ saved i) → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  tag : bytesAt s.mem (tp s₀) 16 = mac (otk s₀) (macData (A s₀) (Ct s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = Ct s₀

theorem finalize_seal_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : PreFs s₀ s) :
    WP isa finalize s (PostFs s₀) :=
  WP.mono (fin_ok hp h.inv (outOk_tP hp) h.r3 h.r4 h.r5 h.r6) fun s' ⟨k', t'⟩ =>
    ⟨h.inv.regs.kept k'.cs, fun r hr hne => by rw [k'.cs r hr, h.inv.pres r hr hne],
      by rw [k'.sp, h.inv.sp], by rw [k'.rd, h.inv.rd], by rw [k'.wr, h.inv.wr],
      h.inv.saved.frame k'.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by decide) (by decide) (by decide)
        · exact (outOk_tP hp).dSv
        · exact sub_disj s₀ (by decide) (by decide) (by decide)),
      t' _ _ h.repr, by
      rw [bytesAt_frame k'.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.d_c.sub_right (sub_ctx s₀ (by decide))
        · exact hp.d_t
        · exact hp.d_c.sub_right (sub_ctx s₀ (by decide))) (Nat.le_of_lt (s₀.gpr .r8).isLt), h.data]⟩

/-- The callee-saved registers, from the restored ones and those never written. -/
theorem pres_of {s₀ s s' : State} (hpres : ∀ r ∈ preserved, (∀ i < 6, r ≠ saved i) → s.gpr r = s₀.gpr r)
    (hg : ∀ i < 6, s'.gpr (saved i) = s₀.gpr (saved i))
    (ho : ∀ r, (∀ i < 6, r ≠ saved i) → r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  by_cases hs : ∃ i < 6, r = saved i
  · obtain ⟨i, hi, rfl⟩ := hs; exact hg i hi
  · have hne : ∀ i < 6, r ≠ saved i := fun i hi e => hs ⟨i, hi, e⟩
    rw [ho r hne (ne_of_pres hr) (ne_of_pres hr), hpres r hr hne]

theorem sealEnd_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : PostFs s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' := by
  refine WP.mono (restore_ok hp h.regs.r24 h.saved h.rd h.wr) fun s₂ ⟨g₂, lr₂, o₂, m₂, sp₂, _, _⟩ =>
    ⟨⟨pres_of h.pres g₂ o₂, by rw [sp₂, h.sp], lr₂⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₂.mem (dp s₀) (L s₀), bytesAt s₂.mem (tp s₀) 16)
  rw [m₂, h.data, h.tag]
  simp only [Spec.ChaCha20Poly1305.encrypt]

theorem seal_correct {s₀ : State} (hp : APre true s₀) :
    WP isa Impl.ChaCha20Poly1305.PPC64LE.«seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealPPC64LE.post s₀ s' :=
  WP.seq (WP.mono (sealMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_seal_ok hp h)
    fun _ h' => sealEnd_ok hp h'))

/-! ## Open -/

/-- The ChaCha20 state is unchanged by a frame of parts of the context
outside it, the data and the stack below. -/
theorem ctx_state {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ stOff 64).Disjoint r) :
    stateAt m' (off (cx s₀) stOff) = stateAt m (off (cx s₀) stOff) :=
  stateAt_frame hf hd

theorem macR_st {s₀ : State} (hp : APre e s₀) : ∀ r ∈ macR s₀, (sub s₀ stOff 64).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by decide) (by decide) (by decide)
  · exact sub_disj s₀ (by decide) (by decide) (by decide)
  · exact (hp.b_c.sub_right (sub_ctx s₀ (by decide))).symm

/-- Before `vg_poly1305_finalize_scratch` in `open`. -/
structure PreFo (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  r3 : s.gpr .r3 = cx s₀
  r4 : (s.gpr .r4).toNat % 16 = 0
  r5 : s.gpr .r5 = off (cx s₀) tagOff
  r6 : s.gpr .r6 = off (cx s₀) scrOff
  repr : Repr s.mem (cx s₀) (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = D s₀
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem openMain_ok {s₀ : State} (hp : APre false s₀) : WP isa openMain s₀ (PreFo s₀) := by
  unfold openMain
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = D s₀ :=
    data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 648, .inl ⟨Nat.le_refl _, by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 256, .inl ⟨by decide, sub_self' _ _ _⟩⟩
      · exact ⟨keyOff, 32, .inl ⟨by decide, sub_self' _ _ _⟩⟩, d₁]
  refine WP.seq (WP.mono (polyInit_ok hp h₂.inv h₂.key) fun s₃ ⟨i₃, k₃, r₃⟩ => ?_)
  have d₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp k₃.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by decide, sub_self' _ _ _⟩⟩, d₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state k₃.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by decide) (by decide) (by decide),
      h₂.st]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r25) (n := .r26) (.inl ⟨rfl, rfl⟩) (srcA hp) i₃ i₃.regs.r25
    (by rw [i₃.regs.r26]; exact hAL s₀)) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have d₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₄.frame (macR_hd s₀), d₃]
  have st₄ : stateAt s₄.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state k₄.frame (macR_st hp), st₃]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r27) (n := .r28) (.inr ⟨rfl, rfl⟩) (srcD hp) i₄ i₄.regs.r27
    (by rw [i₄.regs.r28]; exact hL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have d₅ : bytesAt s₅.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₅.frame (macR_hd s₀), d₄]
  have st₅ : stateAt s₅.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state k₅.frame (macR_st hp), st₄]
  refine WP.seq (WP.mono (lengths_ok hp i₅) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have d₆ : bytesAt s₆.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₆.frame (lenR_hd s₀), d₅]
  have st₆ : stateAt s₆.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state k₆.frame fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact macR_st hp r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by decide) (by decide) (by decide),
      st₅]
  refine WP.mono (finArgs_ok i₆ out_open) fun s₇ ⟨i₇, k₇, h3, h5, h6, h4⟩ => ?_
  have hlen : (D s₀).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₇ := k₇.mem_eq
  refine ⟨i₇, h3, h4, h5, h6, ?_, by rw [m₇, d₆], by rw [m₇, st₆]⟩
  rw [m₇]
  refine mac_parts hlen r₃ r₄ (aad_eq hp i₃) ?_ r₆
  rw [d₄] at r₅
  exact r₅

/-- After `vg_poly1305_finalize_scratch` in `open`. -/
structure PostFo (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  tag : bytesAt s.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = D s₀
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem finalize_open_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PreFo s₀ s) :
    WP isa finalize s (PostFo s₀) := by
  refine WP.mono (fin_ok hp h.inv (outOk_tag hp) h.r3 h.r4 h.r5 h.r6) fun s' ⟨k', t'⟩ => ?_
  refine ⟨h.inv.step k' (fun r hr => ?_) (fun r hr => ?_), t' _ _ h.repr, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
    · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (k := tagOff) (n := 16) (by decide)⟩
    · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by decide) (by decide) (by decide)
    · exact sub_disj s₀ (b := tagOff) (m := 16) (by decide) (by decide) (by decide)
    · exact sub_disj s₀ (by decide) (by decide) (by decide)
  · rw [data_frame hp k'.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨0, 128, .inl ⟨by decide, sub_self' _ _ _⟩⟩
      · exact ⟨tagOff, 16, .inl ⟨by decide, sub_self' _ _ _⟩⟩
      · exact ⟨scrOff, 128, .inl ⟨by decide, sub_self' _ _ _⟩⟩, h.data]
  · rw [ctx_state k'.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact sub_disj s₀ (b := tagOff) (m := 16) (by decide) (by decide) (by decide)
      · exact sub_disj s₀ (by decide) (by decide) (by decide), h.st]

theorem openEnd_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PostFo s₀ s) :
    WP isa openEnd s fun s' => abiPreserved s₀ s' ∧ openPPC64LE.post s₀ s' := by
  unfold openEnd
  refine WP.seq (WP.mono (crypt_ok hp h.inv h.st) fun s₁ ⟨i₁, k₁, c₁⟩ => ?_)
  have t₁ : bytesAt s₁.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀)) := by
    rw [bytesAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (a := tagOff) (n := 16) (by decide) (by decide) (by decide)
        · exact (hp.d_c.sub_right (sub_ctx s₀ (k := tagOff) (n := 16) (by decide))).symm) (by decide), h.tag]
  rw [h.data] at c₁
  refine compare_ok hp i₁ fun s₂ r3₂ g₂ sp₂ lr₂ m₂ rd₂ wr₂ => ?_
  have i₂ : Inv s₀ s₂ := i₁.step0 ⟨g₂, sp₂, rd₂, wr₂, by rw [m₂]; exact Frame.refl _ _⟩
  refine WP.mono (restore_ok hp i₂.regs.r24 i₂.saved i₂.rd i₂.wr) fun s₃ ⟨g₃, lr₃, o₃, m₃, sp₃, _, _⟩ =>
    ⟨⟨pres_of i₂.pres g₃ o₃, by rw [sp₃, i₂.sp], lr₃⟩, ?_⟩
  have r3₃ : s₃.gpr .r3 = if mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0 := by
    rw [o₃ .r3 (by decide) (by decide) (by decide), r3₂, t₁, tag_eq0 hp i₁]
  have d₃ : bytesAt s₃.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₃, m₂, c₁]
  dsimp only [openPPC64LE]
  rw [r3₃]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left hmac, d₃⟩
  next hn => exact ite_eq_right (decrypt_eq_none hn)

theorem open_correct {s₀ : State} (hp : APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.PPC64LE.«open» s₀ fun s' => abiPreserved s₀ s' ∧ openPPC64LE.post s₀ s' :=
  WP.seq (WP.mono (openMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_open_ok hp h)
    fun _ h' => openEnd_ok hp h'))

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : pubPPC64LE s₁ s₂) :
    VG.PPC64LE.Taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) s₁ s₂ := by
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub Impl.ChaCha20Poly1305.PPC64LE.«seal» :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem open_ct : ConstantTime isa openPPC64LE.pre openPPC64LE.pub Impl.ChaCha20Poly1305.PPC64LE.«open» :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data): `key` at `0x1000`, `nonce` at `0x1100`, `aad` at `0x2000`, `data` at 0,
`tag` at `0x3000` and `work` at `0x4000`. -/
def sealSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x1100 | .r5 => 0x2000 | .r9 => 0x3000 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 648⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩, ⟨0x4000, 648⟩] }

theorem seal_ok (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.PPC64LE.«seal» s t s' ∧ abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_correct (APre.of s hs)

theorem open_ok (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.PPC64LE.«open» s t s' ∧ abiPreserved s s' ∧ openPPC64LE.post s s' :=
  open_correct (APre.of s hs)

theorem seal_verified :
    Verified PPC64LE.target Impl.ChaCha20Poly1305.PPC64LE.«seal» (sealScratchContract PPC64LE.abi 81 160) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
      Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.ChaCha20Poly1305.PPC64LE.sealSat]
      using Proof.ChaCha20Poly1305.PPC64LE.sealSat)

/-- The postconditions match on `decrypt`; the result is the low word of `r3`. -/
theorem open_verified :
    Verified PPC64LE.target Impl.ChaCha20Poly1305.PPC64LE.«open» (openScratchContract PPC64LE.abi 81 160) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
          Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, PPC64LE.abi, PPC64LE.argRegs]
        simp only [Proof.ChaCha20Poly1305.openPPC64LE] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨by rw [h.1]; rfl, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => rw [h]; rfl
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
          Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
          Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
          [Proof.ChaCha20Poly1305.PPC64LE.openSat, Proof.ChaCha20Poly1305.PPC64LE.sealSat]
          using Proof.ChaCha20Poly1305.PPC64LE.openSat }

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, PPC64LE.abi, PPC64LE.argRegs]
    [sealFrameSat, sealSat]
    using sealFrameSat

theorem seal_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 81 Impl.ChaCha20Poly1305.PPC64LE.«seal»)
      (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 81) (post := Spec.ChaCha20Poly1305.sealPost PPC64LE.abi.ptrBits) (wa := true) (stack := 160)
    (bytes := 688) (words := 81) seal_verified (by decide) (by decide) (by decide)
    (pre_local _ _) (sealPost_local _) (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract PPC64LE.abi 848).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, PPC64LE.abi, PPC64LE.argRegs]
    [openFrameSat, sealSat]
    using openFrameSat

theorem open_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 81 Impl.ChaCha20Poly1305.PPC64LE.«open»)
      (Spec.ChaCha20Poly1305.openContract PPC64LE.abi 848) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 81) (post := Spec.ChaCha20Poly1305.openPost PPC64LE.abi.ptrBits) (wa := true) (stack := 160)
    (bytes := 688) (words := 81) open_verified (by decide) (by decide) (by decide)
    (pre_local _ _) (openPost_local _) (openPost_out _) openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.PPC64LE
