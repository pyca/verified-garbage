module

import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Tail
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Tail
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgsWipe
public import VerifiedGarbage.Proof.Zeroize.Common
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

One body serves in place and out of place: `seal` and `open` run it with
the destination the source (`inPlace`, `r11 = r7`), and
`vg_chacha20_poly1305_open_to` runs `open`'s after `toEntry`, which takes
`dst` from `r9` and `tag` and `work` from its stack arguments, in a frame of
768 bytes wiped after the code (`Verified.stackScratchArgsWiped`). The
constant-time proof of the body (`open_rel`) serves both entries.
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
    simp only [List.mem_singleton] at hr; subst hr; exact hp.d_in, hc⟩⟩

/-- `seal`'s data is apart from its tag. -/
theorem APre.d_t {s₀ : State} (hp : APre true s₀) : (dR s₀).Disjoint (tR s₀) := by
  have h := hp.o_t
  simp only [oR, dR] at h ⊢
  rwa [hp.inPlace] at h

theorem hAL (s₀ : State) : s₀.gpr .r6 = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem hL (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_c
    · exact hp.a_o
    · exact hp.b_a.symm) (Nat.le_of_lt (s₀.gpr .r6).isLt)

/-- `tag` is unchanged while the invariant holds. -/
theorem tag_eq0 {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (tp s₀) 16 = T0 s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.t_c
    · exact hp.o_t.symm
    · exact hp.b_t.symm) (by decide)

/-- The data is unchanged by a frame of parts of the context and the stack below. -/
theorem data_frame {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∃ k n, (k + n ≤ 656 ∧ Region.Sub r (sub s₀ k n)) ∨ r = belR s₀) :
    bytesAt m' (dp s₀) (L s₀) = bytesAt m (dp s₀) (L s₀) :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨k, n, h⟩ := hd r hr
    rcases h with ⟨hk, hs⟩ | rfl
    · exact (hp.d_c.sub_right (sub_ctx s₀ hk)).sub_right hs
    · exact hp.b_d.symm) (Nat.le_of_lt (s₀.gpr .r8).isLt)

theorem sub_self' (s₀ : State) (k n : Nat) : Region.Sub (sub s₀ k n) (sub s₀ k n) := fun _ h => h

/-- What `macPad` writes, as `data_frame` wants it. -/
theorem macR_hd (s₀ : State) : ∀ r ∈ macR s₀, ∃ k n, (k + n ≤ 656 ∧ Region.Sub r (sub s₀ k n)) ∨ r = belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨0, 128, .inl ⟨by decide, sub_self' _ _ _⟩⟩
  · exact ⟨padOff, 16, .inl ⟨by decide, sub_self' _ _ _⟩⟩
  · exact ⟨0, 0, .inr rfl⟩

/-- What `lengths` writes, as `data_frame` wants it. -/
theorem lenR_hd (s₀ : State) :
    ∀ r ∈ macR s₀ ++ [sub s₀ lenOff 16], ∃ k n, (k + n ≤ 656 ∧ Region.Sub r (sub s₀ k n)) ∨ r = belR s₀ := by
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
      exact ⟨0, 656, .inl ⟨Nat.le_refl _, by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 256, .inl ⟨by decide, sub_self' _ _ _⟩⟩
      · exact ⟨keyOff, 32, .inl ⟨by decide, sub_self' _ _ _⟩⟩, d₁]
  refine WP.seq (WP.mono (crypt_ok hp h₂.inv h₂.st) fun s₃ ⟨i₃, k₃, c₃⟩ => ?_)
  rw [d₂, hp.inPlace] at c₃
  have key₃ : bytesAt s₃.mem (off (cx s₀) keyOff) 32 = otk s₀ := by
    rw [bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (by decide) (by decide) (by decide)
        · exact (hp.o_c.sub_right (sub_ctx s₀ (by decide))).symm) (by decide), h₂.key]
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
  pres : ∀ r ∈ preserved, (∀ i < 7, r ≠ saved i) → s.gpr r = s₀.gpr r
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
theorem pres_of {s₀ s s' : State} (hpres : ∀ r ∈ preserved, (∀ i < 7, r ≠ saved i) → s.gpr r = s₀.gpr r)
    (hg : ∀ i < 7, s'.gpr (saved i) = s₀.gpr (saved i))
    (ho : ∀ r, (∀ i < 7, r ≠ saved i) → r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  by_cases hs : ∃ i < 7, r = saved i
  · obtain ⟨i, hi, rfl⟩ := hs; exact hg i hi
  · have hne : ∀ i < 7, r ≠ saved i := fun i hi e => hs ⟨i, hi, e⟩
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
      exact ⟨0, 656, .inl ⟨Nat.le_refl _, by rw [sub_zero]; exact fun _ h => h⟩⟩
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

/-- Everything but the epilogue: `r3` is whether the tag is right, the
plaintext is at the destination. -/
theorem body_ok {s₀ : State} (hp : APre false s₀) :
    WP isa openBody s₀ fun s₂ => Inv s₀ s₂ ∧
      s₂.gpr .r3 = (if mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0) ∧
      bytesAt s₂.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  unfold openBody
  refine WP.seq (WP.mono (openMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_open_ok hp h) fun s h => ?_))
  refine WP.seq (WP.mono (crypt_ok hp h.inv h.st) fun s₁ ⟨i₁, k₁, c₁⟩ => ?_)
  have t₁ : bytesAt s₁.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀)) := by
    rw [bytesAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (a := tagOff) (n := 16) (by decide) (by decide) (by decide)
        · exact (hp.o_c.sub_right (sub_ctx s₀ (k := tagOff) (n := 16) (by decide))).symm) (by decide), h.tag]
  rw [h.data] at c₁
  rw [show Impl.ChaCha20Poly1305.PPC64LE.compare = Impl.ChaCha20Poly1305.PPC64LE.compare ++ [] from
    (List.append_nil _).symm]
  refine compare_ok hp i₁ fun s₂ r3₂ g₂ sp₂ lr₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  have i₂ : Inv s₀ s₂ := i₁.step0 ⟨g₂, sp₂, rd₂, wr₂, by rw [m₂]; exact Frame.refl _ _⟩
  exact ⟨i₂, by rw [r3₂, t₁, tag_eq0 hp i₁], by rw [m₂, c₁]⟩

theorem ofNat_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat_ne_zero {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  exact Nat.ne_of_gt h this

/-- A write of a temporary register (not one we keep) is kept. -/
theorem kept_upd {s s' : State} {d : Reg} {v : BitVec 64} (rs : List Region) (u : Upd s s' d v)
    (hd : d ∉ preserved := by decide) : Kept rs s s' :=
  ⟨fun r hr => u.other r fun e => hd (e ▸ hr), u.sp, u.rd, u.wr, by rw [u.mem]; exact Frame.refl _ _⟩

/-- One step of `zeroData`'s loop: the byte at `op + j` zeroed, with `r3`
zero and `r4` at it. -/
theorem zeroStep_ok {s₀ : State} (hp : APre false s₀) {u : State} (hu : Inv s₀ u) {j : Nat}
    (hj : j < L s₀) (h3 : u.gpr .r3 = 0) (h4 : u.gpr .r4 = op s₀ + BitVec.ofNat 64 j)
    (hz : Proof.Zeroize.Prefix u.mem (op s₀) j) :
    WP isa (.block [.stb .r3 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]) u fun u' =>
      Inv s₀ u' ∧ u'.gpr .r3 = 0 ∧ u'.gpr .r4 = op s₀ + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .r5 = u.gpr .r5 - 1 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → u'.gpr r = u.gpr r) ∧ u'.lr = u.lr ∧
      Proof.Zeroize.Prefix u'.mem (op s₀) (j + 1) := by
  have hfit := hp.fit_o
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have hc : (oR s₀).Contains (op s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_stb (off := 0) (a := op s₀ + BitVec.ofNat 64 j) (by decide) (by decide)
    (by rw [h4, BitVec.add_zero]) ⟨oR s₀, by rw [hu.wr]; exact hp.o_wr, hc⟩ fun u₁ m₁ => ?_
  refine wp_addi (imm := 1) (by decide) (by decide) fun u₂ v₂ =>
    wp_subi (imm := 1) (by decide) (by decide) fun u₃ v₃ => WP.block_nil ?_
  have st₁ : Kept [oR s₀] u u₁ :=
    ⟨fun r _ => by rw [m₁.gpr], m₁.sp, m₁.rd, m₁.wr,
      by rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc⟩
  have st : Kept [oR s₀] u u₃ := (st₁.trans (kept_upd _ v₂)).trans (kept_upd _ v₃)
  have o : ∀ r, r ≠ .r4 → r ≠ .r5 → u₃.gpr r = u.gpr r := fun r a b => by
    rw [v₃.other r b, v₂.other r a, m₁.gpr]
  refine ⟨hu.step st (fun r hr => ⟨oR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_c.sub_right (sub_ctx s₀ (by decide))).symm),
    by rw [o _ (by decide) (by decide), h3], ?_, by rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr]; rfl, o,
    by rw [v₃.lr, v₂.lr, m₁.lr], ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, h4, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [v₃.mem, v₂.mem, m₁.mem, h3, show BitVec.setWidth 8 (0 : BitVec 64) = 0 by decide]
    exact Proof.Zeroize.prefix_writeW hz (by omega)

/-- `zeroData`, with `r3` zero: zeros at the destination, and only `r4` and `r5`
written. -/
theorem zeroData_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (h3 : s.gpr .r3 = 0) :
    WP isa zeroData s fun s' => Inv s₀ s' ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧ s'.lr = s.lr := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  unfold zeroData
  refine WP.seq (wp_mov fun u₁ v₁ => wp_mov fun u₂ v₂ => WP.block_nil ?_)
  have r4₂ : u₂.gpr .r4 = op s₀ := by rw [v₂.other _ (by decide), v₁.gpr, h.regs.r31]
  have r5₂ : u₂.gpr .r5 = BitVec.ofNat 64 (L s₀) := by
    rw [v₂.gpr, v₁.other _ (by decide), h.regs.r28, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have i₂ : Inv s₀ u₂ := h.step0 ((kept_upd [] v₁).trans (kept_upd [] v₂))
  have o₂ : ∀ r, r ≠ .r4 → r ≠ .r5 → u₂.gpr r = s.gpr r := fun r a b => by
    rw [v₂.other r b, v₁.other r a]
  have l₂ : u₂.lr = s.lr := by rw [v₂.lr, v₁.lr]
  by_cases hz : L s₀ = 0
  · refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, r5₂, hz]; rfl)
      (fun _ => WP.block_nil ⟨i₂, ?_, o₂, l₂⟩) (by simp)
    rw [hz]; rfl
  · have hne := ofNat_ne_zero (n := L s₀) (by omega) hL
    refine WP.ite false (by
        show some ((u₂.gpr .r5).setWidth 64 == 0) = some false
        rw [r5₂, BitVec.setWidth_eq, beq_false_of_ne hne])
      (by simp) fun _ => ?_
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < L s₀ ∧ rem = L s₀ - j ∧ Inv s₀ u ∧ u.gpr .r3 = 0 ∧
      u.gpr .r4 = op s₀ + BitVec.ofNat 64 j ∧ u.gpr .r5 = BitVec.ofNat 64 (L s₀ - j) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → u.gpr r = s.gpr r) ∧ u.lr = s.lr ∧
      Proof.Zeroize.Prefix u.mem (op s₀) j) ?_ (L s₀) u₂
      ⟨0, by omega, by omega, i₂, by rw [o₂ _ (by decide) (by decide), h3],
        by rw [r4₂]; exact (BitVec.add_zero _).symm, by rw [r5₂, Nat.sub_zero], o₂, l₂,
        fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem u ⟨j, hj, hr, hu, e3, e4, e5, ho, hl, hpz⟩
    refine WP.mono (zeroStep_ok hp hu hj e3 e4 hpz) fun u' ⟨i', r3', r4', r5', o', l', z'⟩ => ?_
    have r5'' : u'.gpr .r5 = BitVec.ofNat 64 (L s₀ - (j + 1)) := by
      rw [r5', e5, ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
    have o'' : ∀ r, r ≠ .r4 → r ≠ .r5 → u'.gpr r = s.gpr r := fun r a b => by rw [o' r a b, ho r a b]
    by_cases he : j + 1 = L s₀
    · left
      refine ⟨by simp only [VG.PPC64LE.eval, State.read, r5'', he, Nat.sub_self]; rfl, i', ?_, o'',
        by rw [l', hl]⟩
      rw [he] at z'
      exact Proof.Zeroize.prefix_spec z'
    · right
      have hne := ofNat_ne_zero (n := L s₀ - (j + 1)) (by omega) (by omega)
      refine ⟨by
          show some ((u'.gpr .r5).setWidth 64 != 0) = some true
          rw [r5'', BitVec.setWidth_eq, bne, beq_false_of_ne hne]; rfl,
        L s₀ - (j + 1), by omega, j + 1, by omega, rfl, i', r3', r4', r5'', o'', by rw [l', hl], z'⟩

/-- The epilogue: our caller's registers restored. -/
theorem tail_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' =>
      abiPreserved s₀ s' ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem :=
  WP.mono (restore_ok hp h.regs.r24 h.saved h.rd h.wr) fun _ ⟨g₃, lr₃, o₃, m₃, sp₃, _, _⟩ =>
    ⟨⟨pres_of h.pres g₃ o₃, by rw [sp₃, h.sp], lr₃⟩, o₃ .r3 (by decide) (by decide) (by decide), m₃⟩

/-- What `open`'s body leaves, from the source to the destination: the
result in `r3`, and the plaintext or zeros at the destination. -/
def CorePost (s₀ s' : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
  | some pt => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (op s₀) (L s₀) = pt
  | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0

theorem open_correct {s₀ : State} (hp : APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.PPC64LE.«open» s₀ fun s' => abiPreserved s₀ s' ∧ CorePost s₀ s' := by
  unfold «open»
  refine WP.seq (WP.mono (body_ok hp) fun s₂ ⟨i₂, ok₂, d₂⟩ => ?_)
  unfold CorePost
  refine WP.seq ?_
  by_cases hc : mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀
  · simp only [hc, ↓reduceIte] at ok₂
    refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, ok₂]; rfl) (by simp) fun _ => WP.block_nil ?_
    refine WP.mono (tail_ok hp i₂) fun s₃ ⟨ha, r3₃, m₃⟩ => ⟨ha, ?_⟩
    split
    next pt hpt =>
      obtain ⟨-, rfl⟩ := decrypt_eq_some hpt
      exact ⟨by rw [r3₃, ok₂], by rw [m₃, d₂]⟩
    next hn => exact absurd hc (decrypt_eq_none hn)
  · simp only [hc, ↓reduceIte] at ok₂
    refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, ok₂]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (zeroData_ok hp i₂ ok₂) fun s₃ ⟨i₃, z₃, o₃, _⟩ => ?_
    refine WP.mono (tail_ok hp i₃) fun s₄ ⟨ha, r3₄, m₄⟩ => ⟨ha, ?_⟩
    split
    next pt hpt => exact absurd (decrypt_eq_some hpt).1 hc
    next hn => exact ⟨by rw [r3₄, o₃ _ (by decide) (by decide), ok₂], by rw [m₄, z₃]⟩

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : pubPPC64LE s₁ s₂) :
    VG.PPC64LE.Taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]) s₁ s₂ := by
  obtain ⟨p3, p4, p5, p6, p7, p8, p9, p10, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub
    (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«seal») :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

/-! `open` branches on whether the tag is right, which its contract lets it
leak: the taint analysis checks the parts around the branch, which
`open_rel` composes, with the public data that `body_ok` and `zeroData_ok`
give them in both runs. Each entry then reaches that body with the same
public data in both runs (`open_ct`, `openTo_ct`). -/

theorem openBody_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11])
    Impl.ChaCha20Poly1305.PPC64LE.openBody h).isSome = true := ⟨_, by taint_decide⟩

theorem inPlace_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    (.block [Impl.ChaCha20.PPC64LE.Xor.mov .r11 .r7]) h).isSome = true := ⟨_, by taint_decide⟩

theorem toEntry_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10])
    (.block Impl.ChaCha20Poly1305.PPC64LE.toEntry) h).isSome = true := ⟨_, by taint_decide⟩

theorem zeroData_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.r31, .r28])
    Impl.ChaCha20Poly1305.PPC64LE.zeroData h).isSome = true := ⟨_, by taint_decide⟩

theorem tail_taint : ∃ h, (VG.Taint.check taint (Taint.ofRegs [.r24])
    (.block Impl.ChaCha20Poly1305.PPC64LE.restore) h).isSome = true := ⟨_, by taint_decide⟩

/-- Both states satisfy `I`. -/
abbrev Both (I : State → Prop) : State → State → Prop := fun s₁ s₂ => I s₁ ∧ I s₂

theorem ct_seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : RelCT isa (Both I) c₁ fun _ _ => True)
    (w : ∀ s, I s → WP isa c₁ s J) (h₂ : RelCT isa (Both J) c₂ fun _ _ => True) :
    RelCT isa (Both I) (.seq c₁ c₂) fun _ _ => True :=
  ((h₁.wp fun s₁ s₂ h => ⟨w s₁ h.1, w s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2).seq h₂

theorem ct_taint {I : State → Prop} {c : Prog isa} (rs : List Reg) (v : Reg → BitVec 64) (sp : Addr)
    (hp : ∀ s, I s → s.sp = sp ∧ ∀ r ∈ rs, s.gpr r = v r) {h : VG.Taint.Hint VG.PPC64LE.taint.T}
    (hc : (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Both I) c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun _ _ hh => ⟨(hp _ hh.1).1.trans (hp _ hh.2).1.symm, fun r h' =>
      ((hp _ hh.1).2 r (Taint.mem_ofRegs.mp h')).trans ((hp _ hh.2).2 r (Taint.mem_ofRegs.mp h')).symm⟩) hc

/-- `ct_taint` for code with vector instructions. -/
theorem ct_vtaint {I : State → Prop} {c : Prog isa} (rs : List Reg) (v : Reg → BitVec 64) (sp : Addr)
    (hp : ∀ s, I s → s.sp = sp ∧ ∀ r ∈ rs, s.gpr r = v r) {h : VG.Taint.Hint vectorTaint.T}
    (hc : (VG.Taint.check vectorTaint (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Both I) c fun _ _ => True :=
  RelCT.taint (A := vectorTaint) (Taint.ofRegs rs)
    (fun _ _ hh => ⟨(hp _ hh.1).1.trans (hp _ hh.2).1.symm, fun r h' =>
      ((hp _ hh.1).2 r (Taint.mem_ofRegs.mp h')).trans ((hp _ hh.2).2 r (Taint.mem_ofRegs.mp h')).symm⟩) hc

theorem ok_iff (s₀ : State) :
    okPPC64LE s₀ = true ↔ mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ := by
  unfold okPPC64LE
  constructor
  · intro h
    obtain ⟨pt, hpt⟩ := Option.isSome_iff_exists.mp h
    exact (decrypt_eq_some hpt).1
  · intro h
    cases hd : Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | none => exact absurd h (decrypt_eq_none hd)
    | some _ => rfl

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The registers the body reads as public on entry. -/
abbrev pubRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- What two runs of the body agree on: the public registers (`v`), the
stack pointer and whether the tag is right. -/
def Core (v : Reg → BitVec 64) (sp : Addr) (b : Bool) (s : State) : Prop :=
  APre false s ∧ (∀ r ∈ pubRegs, s.gpr r = v r) ∧ s.sp = sp ∧ okPPC64LE s = b

theorem open_rel (v : Reg → BitVec 64) (sp : Addr) (bo : Bool) :
    RelCT isa (Both (Core v sp bo)) Impl.ChaCha20Poly1305.PPC64LE.«open» fun _ _ => True := by
  let b : BitVec 64 := if bo then 1 else 0
  let J : State → Prop := fun s => s.sp = sp ∧ s.gpr .r24 = v .r10 ∧ s.gpr .r3 = b ∧
    s.gpr .r31 = v .r11 ∧ s.gpr .r28 = v .r8 ∧ ∃ t₀, Core v sp bo t₀ ∧ Inv t₀ s
  let J' : State → Prop := fun s => s.sp = sp ∧ s.gpr .r24 = v .r10
  unfold «open»
  refine ct_seq (J := J) ?_ ?_ ?_
  · obtain ⟨_, hc⟩ := openBody_taint
    exact ct_vtaint _ v sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
  · intro s ⟨hp, e, esp, eok⟩
    refine WP.mono (body_ok hp) fun s' ⟨i, r3, _⟩ => ⟨by rw [i.sp, esp], ?_, ?_,
      by rw [i.regs.r31, e .r11 (by decide)], by rw [i.regs.r28, e .r8 (by decide)], s, ⟨hp, e, esp, eok⟩, i⟩
    · rw [i.regs.r24]; exact e .r10 (by decide)
    · rw [r3]; show _ = if bo = true then _ else _
      rw [← eok]; simp only [ok_iff]
  · refine ct_seq (J := J') ?_ ?_ ?_
    · refine RelCT.ite (fun _ _ h => by simp only [VG.PPC64LE.eval, State.read, h.1.2.2.1, h.2.2.2.1]) ?_ ?_
      · obtain ⟨_, hc⟩ := zeroData_taint
        refine RelCT.mono (ct_taint (I := J) _ (fun r => match r with | .r31 => v .r11 | _ => v .r8)
          sp (fun s hs => ⟨hs.1, ?_⟩) hc) (fun _ _ h => h.1) fun _ _ h => h
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.2.2.2.1
        · exact hs.2.2.2.2.1
      · intro _ _ _ _ _ _ _ x₁ x₂
        cases x₁ with
        | block h₁ =>
          cases x₂ with
          | block h₂ =>
            simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
            exact ⟨h₁.2.symm.trans h₂.2, trivial⟩
    · rintro s ⟨esp, e24, e3, -, -, t₀, ⟨hp, -⟩, i⟩
      by_cases hb : bo = true
      · have : s.gpr .r3 = 1 := by rw [e3]; simp only [b, hb, ↓reduceIte]
        exact WP.ite (M := isa) (c := .zero .d .r3) false
          (by simp only [VG.PPC64LE.eval, State.read, this]; rfl) (by simp)
          fun _ => WP.block_nil ⟨esp, e24⟩
      · have : s.gpr .r3 = 0 := by rw [e3]; simp only [b, hb, Bool.false_eq_true, ↓reduceIte]
        exact WP.ite (M := isa) (c := .zero .d .r3) true
          (by simp only [VG.PPC64LE.eval, State.read, this]; rfl)
          (fun _ => WP.mono (zeroData_ok hp i this) fun s' ⟨i', _, o', _⟩ =>
            ⟨by rw [i'.sp, ← i.sp, esp], by rw [o' _ (by decide) (by decide), e24]⟩) (by simp)
    · obtain ⟨_, hc⟩ := tail_taint
      exact ct_taint _ (fun _ => v .r10) sp (fun s hs => ⟨hs.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.2⟩) hc

/-! ## In place -/

/-- After `mr r11, r7`, from the precondition of `seal` or `open`: the
destination is the source. -/
theorem apre_inPlace {enc : Bool} {s s₁ : State} (hs : prePPC64LE enc s)
    (u : Upd s s₁ .r11 (s.gpr .r7)) : APre enc s₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := hs
  have e : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s₁.gpr r = s.gpr r := fun r hr =>
    u.other r (by revert r; decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e3, e4, e5, e6, e7, e8, e9, e10⟩ := e
  have g11 : s₁.gpr .r11 = s.gpr .r7 := u.gpr
  have rd : s₁.rd = s.rd := u.rd
  have wr : s₁.wr = s.wr := u.wr
  have sp : s₁.sp = s.sp := u.sp
  refine {
    sp160 := ?_, k_rd := ?_, n_rd := ?_, a_rd := ?_, d_in := ?_, o_wr := ?_, ctx_wr := ?_, t_in := ?_,
    k_c := ?_, n_c := ?_, a_c := ?_, d_c := ?_, t_c := ?_, k_o := ?_, n_o := ?_, a_o := ?_, o_t := ?_,
    o_c := ?_, alias := ?_, enc_t := ?_, b_k := ?_, b_n := ?_, b_a := ?_, b_d := ?_, b_o := ?_,
    b_t := ?_, b_c := ?_, fit_k := ?_, fit_n := ?_, fit_a := ?_, fit_d := ?_, fit_o := ?_,
    fit_t := ?_, fit_c := ?_ } <;>
  simp only [kR, kp, nR, np, aR, ad, AL, dR, dp, L, tR, tp, ctxR, cx, oR, op, belR, e3, e4, e5, e6, e7,
    e8, e9, e10, g11, rd, wr, sp, h2, h3] <;>
  first
    | with_reducible assumption
    | (cases enc <;> simp)

theorem abi_inPlace {s s₁ s' : State} (u : Upd s s₁ .r11 (s.gpr .r7)) (h : abiPreserved s₁ s') :
    abiPreserved s s' :=
  ⟨fun r hr => by rw [h.1 r hr, u.other r (ne_of_pres hr)], by rw [h.2.1, u.sp], by rw [h.2.2, u.lr]⟩

theorem inPlace_ok {enc : Bool} {c : Prog isa} {s : State} (hs : prePPC64LE enc s) {Q : State → Prop}
    (k : ∀ s₁, Upd s s₁ .r11 (s.gpr .r7) → APre enc s₁ → WP isa c s₁ Q) :
    WP isa (Impl.ChaCha20Poly1305.PPC64LE.inPlace c) s Q :=
  WP.seq (wp_mov fun s₁ u => WP.block_nil (k s₁ u (apre_inPlace hs u)))

theorem ok_inPlace {s s₁ : State} (u : Upd s s₁ .r11 (s.gpr .r7)) : okPPC64LE s₁ = okPPC64LE s := by
  simp only [okPPC64LE, u.mem, u.other .r3 (by decide), u.other .r4 (by decide), u.other .r5 (by decide),
    u.other .r6 (by decide), u.other .r7 (by decide), u.other .r8 (by decide), u.other .r9 (by decide)]

theorem open_ct : ConstantTime isa openPPC64LE.pre openPPC64LE.pub
    (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«open») := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩, ql⟩ := hq
  have qok : okPPC64LE σ₁ = okPPC64LE σ₂ := leak_bool ql
  let v : Reg → BitVec 64 := fun r => if r = .r11 then σ₁.gpr .r7 else σ₁.gpr r
  let I₀ : State → Prop := fun s => prePPC64LE false s ∧ (∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10],
    s.gpr r = σ₁.gpr r) ∧ s.sp = σ₁.sp ∧ okPPC64LE s = okPPC64LE σ₁
  have hc : RelCT isa (Both I₀)
      (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«open») fun _ _ => True := by
    unfold Impl.ChaCha20Poly1305.PPC64LE.inPlace
    refine ct_seq (J := Core v σ₁.sp (okPPC64LE σ₁)) ?_ ?_ (open_rel v σ₁.sp _)
    · obtain ⟨_, hc⟩ := inPlace_taint
      exact ct_taint _ σ₁.gpr σ₁.sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
    · intro s ⟨hpre, e, esp, eok⟩
      refine wp_mov fun s₁ u => WP.block_nil ⟨apre_inPlace hpre u, fun r hr => ?_, by rw [u.sp, esp],
        by rw [ok_inPlace u, eok]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .r3 = σ₁.gpr .r3; rw [u.other _ (by decide)]; exact e .r3 (by simp)
      · show s₁.gpr .r4 = σ₁.gpr .r4; rw [u.other _ (by decide)]; exact e .r4 (by simp)
      · show s₁.gpr .r5 = σ₁.gpr .r5; rw [u.other _ (by decide)]; exact e .r5 (by simp)
      · show s₁.gpr .r6 = σ₁.gpr .r6; rw [u.other _ (by decide)]; exact e .r6 (by simp)
      · show s₁.gpr .r7 = σ₁.gpr .r7; rw [u.other _ (by decide)]; exact e .r7 (by simp)
      · show s₁.gpr .r8 = σ₁.gpr .r8; rw [u.other _ (by decide)]; exact e .r8 (by simp)
      · show s₁.gpr .r9 = σ₁.gpr .r9; rw [u.other _ (by decide)]; exact e .r9 (by simp)
      · show s₁.gpr .r10 = σ₁.gpr .r10; rw [u.other _ (by decide)]; exact e .r10 (by simp)
      · show s₁.gpr .r11 = σ₁.gpr .r7; rw [u.gpr]; exact e .r7 (by simp)
  exact (hc _ _ _ _ _ _ ⟨⟨h₁, fun r _ => rfl, rfl, rfl⟩,
    ⟨h₂, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm],
      qsp.symm, qok.symm⟩⟩ e₁ e₂).1

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
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 656⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩, ⟨0x4000, 656⟩] }

theorem seal_ok (s : State) (hs : sealPPC64LE.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«seal») s t s' ∧
      abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  inPlace_ok hs fun s₁ u hp => WP.mono (seal_correct hp) fun s' ⟨ha, hpost⟩ => ⟨abi_inPlace u ha, by
    simpa only [sealPPC64LE, u.mem, u.other .r3 (by decide), u.other .r4 (by decide), u.other .r5 (by decide),
      u.other .r6 (by decide), u.other .r7 (by decide), u.other .r8 (by decide), u.other .r9 (by decide)]
      using hpost⟩

theorem open_ok (s : State) (hs : openPPC64LE.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«open») s t s' ∧
      abiPreserved s s' ∧ openPPC64LE.post s s' :=
  inPlace_ok hs fun s₁ u hp => WP.mono (open_correct hp) fun s' ⟨ha, hpost⟩ => ⟨abi_inPlace u ha, by
    have ed : Spec.ChaCha20Poly1305.decrypt (K s₁) (N s₁) (A s₁) (D s₁) (T0 s₁) =
        Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
          (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
          (bytesAt s.mem (s.gpr .r9) 16) := by
      simp only [K, N, A, D, T0, kp, np, ad, AL, dp, L, tp, u.mem, u.other .r3 (by decide),
        u.other .r4 (by decide), u.other .r5 (by decide), u.other .r6 (by decide), u.other .r7 (by decide),
        u.other .r8 (by decide), u.other .r9 (by decide)]
    have eo : op s₁ = s.gpr .r7 := u.gpr
    have eL : L s₁ = (s.gpr .r8).toNat := by simp only [L, u.other .r8 (by decide)]
    unfold CorePost at hpost
    rw [ed, eo, eL] at hpost
    simp only [openPPC64LE]
    split at hpost <;> rename_i heq <;> simp only [heq] <;> exact hpost⟩

theorem seal_verified :
    Verified PPC64LE.target (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«seal»)
      (sealScratchContract PPC64LE.abi 82 160) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
      Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.ChaCha20Poly1305.PPC64LE.sealSat]
      using Proof.ChaCha20Poly1305.PPC64LE.sealSat)

/-- The postconditions match on `decrypt`; the result is the low word of `r3`. -/
theorem open_verified :
    Verified PPC64LE.target (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«open»)
      (openZeroScratchContract PPC64LE.abi 82 160) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openPPC64LE,
          Proof.ChaCha20Poly1305.openLeakPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
          Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, PPC64LE.abi, PPC64LE.argRegs]
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
          next _ e₂ => exact ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openPPC64LE,
          Proof.ChaCha20Poly1305.openLeakPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
          Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openPPC64LE,
          Proof.ChaCha20Poly1305.openLeakPPC64LE, Proof.ChaCha20Poly1305.prePPC64LE,
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
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 82
        (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«seal»))
      (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 82) (post := Spec.ChaCha20Poly1305.sealPost PPC64LE.abi.ptrBits) (wa := true) (stack := 160)
    (bytes := 688) (words := 82) seal_verified (by decide) (by decide) (by decide)
    (pre_local _ _) (sealPost_local _) (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract PPC64LE.abi 848).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, PPC64LE.abi, PPC64LE.argRegs]
    [openFrameSat, sealSat]
    using openFrameSat

theorem open_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 688 .r10 82
        (Impl.ChaCha20Poly1305.PPC64LE.inPlace Impl.ChaCha20Poly1305.PPC64LE.«open»))
      (Spec.ChaCha20Poly1305.openZeroContract PPC64LE.abi 848) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 82) (post := Spec.ChaCha20Poly1305.openZeroPost PPC64LE.abi.ptrBits) (wa := true) (stack := 160)
    (leak := some (Spec.ChaCha20Poly1305.openLeak PPC64LE.abi.ptrBits))
    (bytes := 688) (words := 82) open_verified (by decide) (by decide) (by decide)
    (pre_local _ _) (openZeroPost_local _) (openZeroPost_out _) openFrameSat_pre
    (hleak := openLeak_local _)

/-! ## Out of place

`vg_chacha20_poly1305_open_to` is `open`'s body after `toEntry`: `dst` into
`r11`, and `tag` and `work` from the stack into `r9` and `r10`, where the
body expects them. -/

theorem wp_addSp0 {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Nat}
    (h : imm < 2 ^ 15) (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (by simp [exec, show imm < 32768 from h]) (k _ (Upd.write _ _ _))

/-- After `toEntry`. -/
structure ToEntered (s s₄ : State) : Prop where
  gpr : ∀ r, r ≠ .r11 → r ≠ .r12 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r
  r11 : s₄.gpr .r11 = s.gpr .r9
  r9 : s₄.gpr .r9 = stackArg s 0
  r10 : s₄.gpr .r10 = stackArg s 1
  mem : s₄.mem = s.mem
  sp : s₄.sp = s.sp
  lr : s₄.lr = s.lr
  rd : s₄.rd = s.rd
  wr : s₄.wr = s.wr

theorem toEntry_ok {s : State} (hs : openToPrePPC64LE s) : WP isa (.block toEntry) s (ToEntered s) := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfa,
    -, -⟩ := hs
  have hin : ∀ j, j < 2 → InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := fun j hj => by
    refine ⟨toArgs s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨stackArgAddr s 0, 16⟩ : Region).Contains (stackArgAddr s j) 8
    rw [stackArgAddr_eq, stackArgAddr_eq]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  unfold toEntry
  refine wp_mov fun s₁ u₁ => wp_addSp0 (imm := 0) (by decide) fun s₂ u₂ => ?_
  have p₂ : s₂.gpr .r12 = s.sp := by rw [u₂.gpr, u₁.sp, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by decide) (by rw [p₂, stackArgAddr_eq])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), p₂, stackArgAddr_eq])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 1 (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact ⟨fun r h11 h12 h9 h10 => by rw [u₄.other r h10, u₃.other r h9, u₂.other r h12, u₁.other r h11],
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]; rfl,
    by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]; rfl, hm,
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.lr, u₃.lr, u₂.lr, u₁.lr],
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩

theorem apre_openTo {s s₄ : State} (hs : openToPrePPC64LE s) (h : ToEntered s s₄) : APre false s₄ := by
  obtain ⟨h1, h2, h3, dk, dn, da, ds, dt, dw, -, wk', wn, wa, ws, wt, -, bk, bn, ba, bs, bd, bt, bw,
    f3, f4, f5, f7, f9, ft, fw, -, hl, -⟩ := hs
  have e3 := h.gpr .r3 (by decide) (by decide) (by decide) (by decide)
  have e4 := h.gpr .r4 (by decide) (by decide) (by decide) (by decide)
  have e5 := h.gpr .r5 (by decide) (by decide) (by decide) (by decide)
  have e6 := h.gpr .r6 (by decide) (by decide) (by decide) (by decide)
  have e7 := h.gpr .r7 (by decide) (by decide) (by decide) (by decide)
  have e8 := h.gpr .r8 (by decide) (by decide) (by decide) (by decide)
  simp only [hl] at h3 dk dn da ds dt dw bd f9
  refine {
    sp160 := ?_, k_rd := ?_, n_rd := ?_, a_rd := ?_, d_in := ?_, o_wr := ?_, ctx_wr := ?_, t_in := ?_,
    k_c := ?_, n_c := ?_, a_c := ?_, d_c := ?_, t_c := ?_, k_o := ?_, n_o := ?_, a_o := ?_, o_t := ?_,
    o_c := ?_, enc_t := trivial,
    alias := by
      refine .inr ⟨rfl, ?_⟩
      simp only [dR, dp, L, oR, op, e7, e8, h.r11]
      exact ds.symm,
    b_k := ?_, b_n := ?_, b_a := ?_, b_d := ?_, b_o := ?_, b_t := ?_, b_c := ?_,
    fit_k := ?_, fit_n := ?_, fit_a := ?_, fit_d := ?_, fit_o := ?_, fit_t := ?_, fit_c := ?_ } <;>
  simp only [kR, kp, nR, np, aR, ad, AL, dR, dp, L, tR, tp, ctxR, cx, oR, op, belR, e3, e4, e5, e6, e7, e8,
    h.r11, h.r9, h.r10, h.rd, h.wr, h.sp, h2, h3, Bool.false_eq_true, ↓reduceIte] <;>
  first
    | with_reducible assumption
    | (apply Region.Disjoint.symm; with_reducible assumption)
    | simp

theorem abi_openTo {s s₄ s' : State} (h : ToEntered s s₄) (ha : abiPreserved s₄ s') : abiPreserved s s' :=
  ⟨fun r hr => by
    rw [ha.1 r hr, h.gpr r (ne_of_pres hr) (ne_of_pres hr) (ne_of_pres hr) (ne_of_pres hr)],
    by rw [ha.2.1, h.sp], by rw [ha.2.2, h.lr]⟩

theorem ok_openTo {s s₄ : State} (h : ToEntered s s₄) : okPPC64LE s₄ = (openToRes s).isSome := by
  simp only [okPPC64LE, openToRes, h.mem, h.r9, h.gpr .r3 (by decide) (by decide) (by decide) (by decide),
    h.gpr .r4 (by decide) (by decide) (by decide) (by decide),
    h.gpr .r5 (by decide) (by decide) (by decide) (by decide),
    h.gpr .r6 (by decide) (by decide) (by decide) (by decide),
    h.gpr .r7 (by decide) (by decide) (by decide) (by decide),
    h.gpr .r8 (by decide) (by decide) (by decide) (by decide)]

theorem openTo_ok (s : State) (hs : openToPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.PPC64LE.openTo s t s' ∧ abiPreserved s s' ∧
      openToPPC64LE.post s s' :=
  WP.seq (WP.mono (toEntry_ok hs) fun s₄ h₄ => WP.mono (open_correct (apre_openTo hs h₄))
    fun s' ⟨ha, hpost⟩ => ⟨abi_openTo h₄ ha, by
      have ed : Spec.ChaCha20Poly1305.decrypt (K s₄) (N s₄) (A s₄) (D s₄) (T0 s₄) = openToRes s := by
        simp only [K, N, A, D, T0, kp, np, ad, AL, dp, L, tp, openToRes, h₄.mem, h₄.r9,
          h₄.gpr .r3 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .r4 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .r5 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .r6 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .r7 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .r8 (by decide) (by decide) (by decide) (by decide)]
      have eo : op s₄ = s.gpr .r9 := h₄.r11
      have eL : L s₄ = (s.gpr .r8).toNat := by
        simp only [L, h₄.gpr .r8 (by decide) (by decide) (by decide) (by decide)]
      unfold CorePost at hpost
      rw [ed, eo, eL] at hpost
      simp only [openToPPC64LE]
      split at hpost <;> rename_i heq <;> simp only [heq] <;> exact hpost⟩)

theorem openTo_ct : ConstantTime isa openToPPC64LE.pre openToPPC64LE.pub Impl.ChaCha20Poly1305.PPC64LE.openTo := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩, qa, ql⟩ := hq
  have qok : (openToRes σ₁).isSome = (openToRes σ₂).isSome := leak_bool ql
  let v : Reg → BitVec 64 := fun r =>
    if r = .r11 then σ₁.gpr .r9 else if r = .r9 then stackArg σ₁ 0 else if r = .r10 then stackArg σ₁ 1
    else σ₁.gpr r
  let I₀ : State → Prop := fun s => openToPrePPC64LE s ∧
    (∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], s.gpr r = σ₁.gpr r) ∧ s.sp = σ₁.sp ∧
    (∀ i < 2, stackArg s i = stackArg σ₁ i) ∧ (openToRes s).isSome = (openToRes σ₁).isSome
  have hc : RelCT isa (Both I₀) Impl.ChaCha20Poly1305.PPC64LE.openTo fun _ _ => True := by
    unfold Impl.ChaCha20Poly1305.PPC64LE.openTo
    refine ct_seq (J := Core v σ₁.sp (openToRes σ₁).isSome) ?_ ?_ (open_rel v σ₁.sp _)
    · obtain ⟨_, hc⟩ := toEntry_taint
      exact ct_taint _ σ₁.gpr σ₁.sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
    · intro s ⟨hpre, e, esp, ea, eok⟩
      refine WP.mono (toEntry_ok hpre) fun s₄ h₄ => ⟨apre_openTo hpre h₄, fun r hr => ?_,
        by rw [h₄.sp, esp], by rw [ok_openTo h₄, eok]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have g : ∀ r, r ≠ .r11 → r ≠ .r12 → r ≠ .r9 → r ≠ .r10 →
          r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] → s₄.gpr r = σ₁.gpr r :=
        fun r a b c d hm => (h₄.gpr r a b c d).trans (e r hm)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact g .r3 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .r4 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .r5 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .r6 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .r7 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .r8 (by decide) (by decide) (by decide) (by decide) (by simp)
      · show s₄.gpr .r9 = stackArg σ₁ 0; rw [h₄.r9]; exact ea 0 (by decide)
      · show s₄.gpr .r10 = stackArg σ₁ 1; rw [h₄.r10]; exact ea 1 (by decide)
      · show s₄.gpr .r11 = σ₁.gpr .r9; rw [h₄.r11]; exact e .r9 (by simp)
  exact (hc _ _ _ _ _ _ ⟨⟨h₁, fun r _ => rfl, rfl, fun i _ => rfl, rfl⟩,
    ⟨h₂, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm],
      qsp.symm, fun i hi => (qa i hi).symm, qok.symm⟩⟩ e₁ e₂).1

/-- A state satisfying `open_to`'s precondition (with no additional data and
no data): `key`, `nonce` and `aad` as in `sealSat`, `src` at `0x5000`, `dst`
at 0, `tag` at `0x3000` and `work` at `0x4000`, both on the stack at
`sp + 96`. -/
def openToSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x1100 | .r5 => 0x2000 | .r7 => 0x5000 | _ => 0
  lr := 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8061 then 0x30 else bif Nat.beq a.toNat 0x8069 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8060, 16⟩]
  wr := [⟨0, 0⟩, ⟨0x4000, 656⟩]

/-- The postconditions match on `decrypt`; the result is the low word of `r3`. -/
theorem openTo_verified :
    Verified PPC64LE.target Impl.ChaCha20Poly1305.PPC64LE.openTo (openToScratchContract PPC64LE.abi 82 160) :=
  Verified.of_correct openTo_ok openTo_ct
    { pre := by
        intro s h
        sig_pre [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToPPC64LE, Proof.ChaCha20Poly1305.openToPrePPC64LE,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakPPC64LE,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToPPC64LE, Proof.ChaCha20Poly1305.openToPrePPC64LE,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakPPC64LE,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_and_intros
        sig_close
        all_goals first
          | omega
          | bv_omega_arith
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPost, PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg,
          PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [Proof.ChaCha20Poly1305.openToPPC64LE, Proof.ChaCha20Poly1305.openToRes] at h
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
          next _ e₂ => exact ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToPPC64LE, Proof.ChaCha20Poly1305.openToPrePPC64LE,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakPPC64LE,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToPPC64LE, Proof.ChaCha20Poly1305.openToPrePPC64LE,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakPPC64LE,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubPPC64LE, PPC64LE.abi, PPC64LE.argRegs,
            PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range, List.range.loop]
          [Proof.ChaCha20Poly1305.PPC64LE.openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
          using Proof.ChaCha20Poly1305.PPC64LE.openToSat }

/-- A state satisfying `open_to`'s precondition, without the working space:
`tag`, its one stack argument. -/
def openToFrameSat : State :=
  { openToSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8060, 8⟩],
                   wr := [⟨0, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract PPC64LE.abi 928).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
    PPC64LE.abi, PPC64LE.argRegs, PPC64LE.stackArg, PPC64LE.stackArgAddr, List.getD, List.range,
    List.range.loop] [openToFrameSat, openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using openToFrameSat

/-- `open_to` with its working space in a frame of 768 bytes on the stack
(after the frame's header, the copy of `tag` and the working space's
address), wiped after the code. -/
theorem openTo_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchArgsWiped 768 1 82 Impl.ChaCha20Poly1305.PPC64LE.openTo)
      (Spec.ChaCha20Poly1305.openToContract PPC64LE.abi 928) :=
  PPC64LE.Verified.stackScratchArgsWiped (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 82) (pre := Spec.ChaCha20Poly1305.openToPre PPC64LE.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost PPC64LE.abi.ptrBits) (wa := true) (stack := 160) (bytes := 768)
    (m := 1) (words := 82) (leak := some (Spec.ChaCha20Poly1305.openToLeak PPC64LE.abi.ptrBits))
    openTo_verified (by decide) (by decide) (by decide) (openToPre_local _) (openToPost_local _)
    (openToPost_out _) openToFrameSat_pre (hleak := openToLeak_local _)

end VG.Proof.ChaCha20Poly1305.PPC64LE
