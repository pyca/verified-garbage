import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Stages
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch

section

/-!
# ChaCha20-Poly1305 on ARMv7: correctness

`seal` and `open`, from their parts: up to the arguments of
`vg_poly1305_finalize_scratch` (`sealMain`, `openMain`), the frame around it
(`finalize`), and the rest (`sealEnd`, `openEnd`). The constant-time proof
runs the taint analysis on the first and the last, and relates the two runs of
the frame by what these theorems say of the states between them.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The ciphertext `seal` computes. -/
abbrev Ct (s₀ : State) : List Byte := Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (aP s₀) (AL s₀) :=
  ⟨(s₀.gpr .r3).isLt, hp.fit_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hp.a_rd, hc⟩⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (dP s₀) (L s₀) :=
  ⟨(stackArg s₀ 1).isLt, hp.fit_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ hp.d_wr, hc⟩⟩

theorem hAL (s₀ : State) : s₀.gpr .r3 = BitVec.ofNat 32 (AL s₀) := by simp [AL]

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.a_d
    · exact hp.b_a.symm) (by have := (s₀.gpr .r3).isLt; simp only [AL]; omega)

/-- The data is unchanged by a frame of the context and the stack below. -/
theorem data_frame {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀) :
    bytesAt m' (dp s₀) (L s₀) = bytesAt m (dp s₀) (L s₀) :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨k, n, h⟩ := hd r hr
    rcases h with ⟨hk, hs⟩ | rfl
    · exact (hp.c_d.sub_left (sub_ctx s₀ hk)).symm.sub_right hs
    · exact hp.b_d.symm) (by have := (stackArg s₀ 1).isLt; simp only [L]; omega)

theorem sub_self' (s₀ : State) (k n : Nat) : Region.Sub (sub s₀ k n) (sub s₀ k n) := fun _ h => h

theorem macData_eq (a c : List Byte) :
    macData a c = [] ++ (a ++ pad16 a) ++ (c ++ pad16 c) ++ (leBytes 8 a.length ++ leBytes 8 c.length) := by
  simp [macData, List.append_assoc]

/-! ## Up to the frame -/

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

theorem count_eq {s₀ : State} {x : List Byte} (hx : x.length = L s₀) :
    BitVec.ofNat 64 (16 * ((AL s₀ + 15) / 16 + (L s₀ + 15) / 16 + 1)) =
      BitVec.ofNat 64 (macData (A s₀) x).length := by
  rw [length_macData, hx, show (A s₀).length = AL s₀ from VG.Proof.Poly1305.length_bytesAt _ _ _]

/-- Before the frame in `seal`. -/
structure PreFs (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  r0 : s.gpr .r0 = cP s₀
  r1 : s.gpr .r1 = tP s₀
  r12 : s.gpr .r12 = ptr s₀ scrOff
  cnt : Proof.Poly1305.countArm s = BitVec.ofNat 64 (macData (A s₀) (Ct s₀)).length
  repr : Repr s.mem (cx s₀) (otk s₀) (macData (A s₀) (Ct s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = Ct s₀

theorem sealMain_ok {s₀ : State} (hp : APre true s₀) : WP isa sealMain s₀ (PreFs s₀) := by
  unfold sealMain
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = D s₀ :=
    data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 632, .inl ⟨(Nat.le_refl _), by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 256, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨keyOff, 32, .inl ⟨by simp [keyOff], sub_self' _ _ _⟩⟩, d₁]
  refine WP.seq (WP.mono (crypt_ok hp h₂.inv h₂.st) fun s₃ ⟨i₃, k₃, c₃⟩ => ?_)
  rw [d₂] at c₃
  have key₃ : bytesAt s₃.mem (off (cx s₀) keyOff) 32 = otk s₀ := by
    rw [bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (by simp [keyOff, stOff]) (by simp [keyOff]) (by simp [stOff])
        · exact hp.c_d.sub_left (sub_ctx s₀ (by simp [keyOff]))) (by lit_omega), h₂.key]
  refine WP.seq (WP.mono (polyInit_ok hp i₃ key₃) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Ct s₀ := by
    rw [data_frame hp k₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩, c₃]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r8) (n := .r9) ⟨.inl rfl, .inl rfl⟩ (srcA hp) i₄ i₄.regs.r8
    (by rw [i₄.regs.r9]; exact hAL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have hmac : ∀ r ∈ macR s₀, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
    · exact ⟨padOff, 16, .inl ⟨by simp [padOff], sub_self' _ _ _⟩⟩
  have c₅ : bytesAt s₅.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₅.frame hmac, c₄]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r10) (n := .r11) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₅ i₅.regs.r10
    (by rw [i₅.regs.r11]; exact hL s₀)) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have c₆ : bytesAt s₆.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₆.frame hmac, c₅]
  refine WP.seq (WP.mono (lengths_ok hp i₆) fun s₇ ⟨i₇, k₇, r₇⟩ => ?_)
  have c₇ : bytesAt s₇.mem (dp s₀) (L s₀) = Ct s₀ := by
    rw [data_frame hp k₇.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨lenOff, 16, .inl ⟨by simp [lenOff], sub_self' _ _ _⟩⟩, c₆]
  refine WP.mono (finArgs_ok i₇ (by decide) (out_seal hp i₇)) fun s₈ ⟨i₈, k₈, h0, h1, h12, hc⟩ => ?_
  have hlen : (Ct s₀).length = L s₀ := by
    rw [length_encrypt, VG.Proof.Poly1305.length_bytesAt]
  refine ⟨i₈, h0, h1, h12, by rw [hc, count_eq hlen], ?_, by rw [k₈.mem_eq, c₇]⟩
  rw [k₈.mem_eq]
  refine mac_parts hlen r₄ r₅ (aad_eq hp i₄) ?_ r₇
  rw [c₅] at r₆
  exact r₆

/-! ## The frame -/

/-- After the frame in `seal`: the tag written, and what restoring the
registers needs. -/
structure PostFs (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  tag : bytesAt s.mem (tp s₀) 16 = mac (otk s₀) (macData (A s₀) (Ct s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = Ct s₀

theorem finalize_seal_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : PreFs s₀ s) :
    WP isa finalize s (PostFs s₀) :=
  WP.mono (fin_ok hp h.inv (outOk_tP hp) h.r0 h.r1 h.r12) fun s' ⟨k', rg', sv', t'⟩ =>
    ⟨rg', by rw [k'.sp, h.inv.sp], by rw [k'.rd, h.inv.rd], by rw [k'.wr, h.inv.wr], sv',
      t' _ _ h.repr h.cnt, by
      rw [bytesAt_frame k'.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm
        · exact hp.d_t
        · exact (hp.c_d.sub_left (sub_ctx s₀ (by simp [scrOff]))).symm
        · exact hp.b_d.symm) (by have := (stackArg s₀ 1).isLt; simp only [L]; omega), h.data]⟩

/-! ## After the frame -/

/-- The callee-saved registers restored, and the stack pointer as on entry. -/
theorem abi_of {s₀ s' : State} (hr : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r) (hsp : s'.sp = s₀.sp) :
    abiPreserved s₀ s' := ⟨hr, hsp⟩

theorem sealEnd_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : PostFs s₀ s) :
    WP isa (.block sealEnd) s fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  unfold sealEnd
  refine WP.mono (restore_ok hp h.regs.r7 h.saved h.rd h.wr) fun s₂ ⟨g₂, _, m₂, sp₂, _, _⟩ =>
    ⟨abi_of g₂ (by rw [sp₂, h.sp]), ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₂.mem (dp s₀) (L s₀), bytesAt s₂.mem (tp s₀) 16)
  rw [m₂, h.data, h.tag]
  simp only [Spec.ChaCha20Poly1305.encrypt]

theorem seal_correct {s₀ : State} (hp : APre true s₀) :
    WP isa Impl.ChaCha20Poly1305.Arm.«seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' :=
  WP.seq (WP.mono (sealMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_seal_ok hp h)
    fun _ h' => sealEnd_ok hp h'))

/-! ## Open -/

/-- A part of the context is unchanged by a frame of other parts of it, the
data and the stack below. -/
theorem ctx_disj {s₀ : State} (hp : APre e s₀) {rs : List Region} {a n : Nat} (ha : a + n ≤ 632)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀) :
    ∀ r ∈ rs, (sub s₀ a n).Disjoint r := by
  intro r hr
  rcases hd r hr with ⟨k, l, hk, hkl, rfl⟩ | rfl | rfl
  · exact sub_disj s₀ (by lit_omega) ha hk
  · exact hp.c_d.sub_left (sub_ctx s₀ ha)
  · exact (hp.b_c.sub_right (sub_ctx s₀ ha)).symm

theorem ctx_bytes {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a n : Nat}
    (ha : a + n ≤ 632)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀) :
    bytesAt m' (off (cx s₀) a) n = bytesAt m (off (cx s₀) a) n :=
  bytesAt_frame hf (ctx_disj hp ha hd) (by lit_omega)

theorem ctx_state {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ stOff ∨ stOff + 64 ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨
      r = belR s₀) :
    stateAt m' (off (cx s₀) stOff) = stateAt m (off (cx s₀) stOff) :=
  stateAt_frame hf (ctx_disj hp (a := stOff) (n := 64) (by simp [stOff]) hd)

/-- Before the frame in `open`. -/
structure PreFo (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  r0 : s.gpr .r0 = cP s₀
  r1 : s.gpr .r1 = ptr s₀ tagOff
  r12 : s.gpr .r12 = ptr s₀ scrOff
  cnt : Proof.Poly1305.countArm s = BitVec.ofNat 64 (macData (A s₀) (D s₀)).length
  repr : Repr s.mem (cx s₀) (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = D s₀
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

/-- The regions `macPad` writes, as `ctx_bytes` wants them. -/
theorem macR_hd (s₀ : State) {a n : Nat} (h : 128 ≤ a) (h' : padOff + 16 ≤ a ∨ a + n ≤ padOff) :
    ∀ r ∈ macR s₀, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨
      r = belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  · exact .inl ⟨padOff, 16, by simp [padOff], h', rfl⟩

theorem openMain_ok {s₀ : State} (hp : APre false s₀) : WP isa openMain s₀ (PreFo s₀) := by
  unfold openMain
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = D s₀ :=
    data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 632, .inl ⟨(Nat.le_refl _), by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have hd₂ : ∀ r ∈ [sub s₀ 0 256, sub s₀ keyOff 32], ∃ k n, k + n ≤ 632 ∧ Region.Sub r (sub s₀ k n) ∨
      r = belR s₀ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 256, .inl ⟨by omega, sub_self' _ _ _⟩⟩
    · exact ⟨keyOff, 32, .inl ⟨by simp [keyOff], sub_self' _ _ _⟩⟩
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp f₂ hd₂, d₁]
  refine WP.seq (WP.mono (polyInit_ok hp h₂.inv h₂.key) fun s₃ ⟨i₃, k₃, r₃⟩ => ?_)
  have hd₀ : ∀ {a n : Nat}, 128 ≤ a → ∀ r ∈ [sub s₀ 0 128],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ :=
    fun ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  have d₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp k₃.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩, d₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₃.frame (hd₀ (by simp [stOff])), h₂.st]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r8) (n := .r9) ⟨.inl rfl, .inl rfl⟩ (srcA hp) i₃ i₃.regs.r8
    (by rw [i₃.regs.r9]; exact hAL s₀)) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have hmac : ∀ r ∈ macR s₀, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
    · exact ⟨padOff, 16, .inl ⟨by simp [padOff], sub_self' _ _ _⟩⟩
  have d₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₄.frame hmac, d₃]
  have st₄ : stateAt s₄.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₄.frame (macR_hd s₀ (by simp [stOff]) (by simp [stOff, padOff])), st₃]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r10) (n := .r11) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄ i₄.regs.r10
    (by rw [i₄.regs.r11]; exact hL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have d₅ : bytesAt s₅.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₅.frame hmac, d₄]
  have st₅ : stateAt s₅.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₅.frame (macR_hd s₀ (by simp [stOff]) (by simp [stOff, padOff])), st₄]
  refine WP.seq (WP.mono (lengths_ok hp i₅) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have hl : ∀ {a n : Nat}, 128 ≤ a → (lenOff + 16 ≤ a ∨ a + n ≤ lenOff) → ∀ r ∈ [sub s₀ 0 128, sub s₀ lenOff 16],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ :=
    fun ha ha' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
      · exact .inl ⟨lenOff, 16, by simp [lenOff], ha', rfl⟩
  have d₆ : bytesAt s₆.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp k₆.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨lenOff, 16, .inl ⟨by simp [lenOff], sub_self' _ _ _⟩⟩, d₅]
  have st₆ : stateAt s₆.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₆.frame (hl (by simp [stOff]) (by simp [stOff, lenOff])), st₅]
  refine WP.mono (finArgs_ok i₆ (by decide) (out_open i₆)) fun s₇ ⟨i₇, k₇, h0, h1, h12, hc⟩ => ?_
  have hlen : (D s₀).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₇ := k₇.mem_eq
  refine ⟨i₇, h0, h1, h12, by rw [hc, count_eq hlen], ?_, by rw [m₇, d₆], by rw [m₇, st₆]⟩
  rw [m₇]
  refine mac_parts hlen r₃ r₄ (aad_eq hp i₃) ?_ r₆
  rw [d₄] at r₅
  exact r₅

/-- After the frame in `open`. -/
structure PostFo (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  tag : bytesAt s.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = D s₀
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem fin_hd (s₀ : State) {a n : Nat} (h : 128 ≤ a) (h' : tagOff + 16 ≤ a ∨ a + n ≤ tagOff)
    (h'' : scrOff + 128 ≤ a ∨ a + n ≤ scrOff) :
    ∀ r ∈ [sub s₀ 0 128, sub s₀ tagOff 16, sub s₀ scrOff 128, belR s₀],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  · exact .inl ⟨tagOff, 16, by simp [tagOff], h', rfl⟩
  · exact .inl ⟨scrOff, 128, by simp [scrOff], h'', rfl⟩
  · exact .inr (.inr rfl)

theorem finalize_open_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PreFo s₀ s) :
    WP isa finalize s (PostFo s₀) := by
  have et := hp.addr_ptr (k := tagOff) (by simp [tagOff])
  refine WP.mono (fin_ok hp h.inv (outOk_tag hp) h.r0 h.r1 h.r12) fun s' ⟨k', _, _, t'⟩ => ?_
  rw [et] at k' t'
  refine ⟨h.inv.step k' (fun r hr => ?_) (fun r hr => ?_), t' _ _ h.repr h.cnt, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_inv s₀ (by lit_omega)
    · exact sub_inv s₀ (by simp [tagOff])
    · exact sub_inv s₀ (by simp [scrOff])
    · exact ⟨belR s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_disj s₀ (by simp [savOff]) (by simp [savOff]) (by lit_omega)
    · exact sub_disj s₀ (by simp [savOff, tagOff]) (by simp [savOff]) (by simp [tagOff])
    · exact sub_disj s₀ (by simp [savOff, scrOff]) (by simp [savOff]) (by simp [scrOff])
    · exact (hp.b_c.sub_right (sub_ctx s₀ (by simp [savOff]))).symm
  · rw [data_frame hp k'.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨tagOff, 16, .inl ⟨by simp [tagOff], sub_self' _ _ _⟩⟩
      · exact ⟨scrOff, 128, .inl ⟨by simp [scrOff], sub_self' _ _ _⟩⟩
      · exact ⟨0, 0, .inr rfl⟩, h.data]
  · rw [ctx_state hp k'.frame (fin_hd s₀ (by simp [stOff]) (by simp [stOff, tagOff])
      (by simp [stOff, scrOff])), h.st]

/-- `tag` is unchanged while the invariant holds. -/
theorem tag_eq0 {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (tp s₀) 16 = T0 s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_t.symm
    · exact hp.d_t.symm
    · exact hp.b_t.symm) (by omega)

theorem openEnd_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PostFo s₀ s) :
    WP isa openEnd s fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  unfold openEnd
  refine WP.seq (WP.mono (crypt_ok hp h.inv h.st) fun s₁ ⟨i₁, k₁, c₁⟩ => ?_)
  have hc : ∀ {a n : Nat}, stOff + 64 ≤ a → a + n ≤ 632 → ∀ r ∈ [sub s₀ 0 (stOff + 64), dR s₀],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ :=
    fun ha _ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, stOff + 64, by simp [stOff], by omega, rfl⟩
      · exact .inr (.inl rfl)
  have t₁ : bytesAt s₁.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀)) := by
    rw [ctx_bytes hp k₁.frame (by simp [tagOff]) (hc (by simp [stOff, tagOff]) (by simp [tagOff])), h.tag]
  rw [h.data] at c₁
  refine WP.block_append (WP.mono (compare_ok hp i₁)
    fun s₂ ⟨r0₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : Inv s₀ s₂ := i₁.step0 ⟨fun r hr _ => g₂ r hr, sp₂, rd₂, wr₂, by rw [m₂]; exact Frame.refl _ _⟩
  refine WP.mono (restore_ok hp i₂.regs.r7 i₂.saved i₂.rd i₂.wr) fun s₃ ⟨g₃, o₃, m₃, sp₃, _, _⟩ =>
    ⟨abi_of g₃ (by rw [sp₃, i₂.sp]), ?_⟩
  have r0₃ : s₃.gpr .r0 = if mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0 := by
    rw [o₃ .r0 (by decide) (by decide), r0₂, t₁, tag_eq0 hp i₁]
  have d₃ : bytesAt s₃.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₃, m₂, c₁]
  rw [openArm, Contract.post_mk]
  rw [r0₃]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left hmac, d₃⟩
  next hn => exact ite_eq_right (decrypt_eq_none hn)

theorem open_correct {s₀ : State} (hp : APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.Arm.«open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' :=
  WP.seq (WP.mono (openMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_open_ok hp h)
    fun _ h' => openEnd_ok hp h'))

end VG.Proof.ChaCha20Poly1305.Arm

end


/-!
# ChaCha20-Poly1305 on ARMv7: `Verified`

Correctness (above), constant time, and a state satisfying the precondition,
of the code with its working space as its last argument
(`sealScratchContract`, `openScratchContract`), and then of the functions,
which allocate it in a frame of 656 bytes on the stack and wipe it after the
code (`Verified.stackScratchWiped`).

Constant time relates two runs from states that agree on the public data
(`RelCT`), part by part. The taint analysis does not analyse frames, so it
runs on the code before the frame around `vg_poly1305_finalize_scratch`
(`sealMain`, `openMain`) and after it (`sealEnd`, `openEnd`), through the
callees' code: it knows `r7`–`r11` for public after each call because every
callee saves them in memory at known offsets of the context, which it
tracks, and restores them, and `r7` for the base of the context once it is
set from the callee's pointer that the callee keeps. The stack arguments
are public, and the one at `sp + 12` is the base of the context. The frame
itself leaks only addresses computed from the stack pointer, and
`vg_poly1305_finalize_scratch` is constant time (`RelCT.frame`,
`RelCT.call`), given what the correctness proof shows of the states on
either side of it in each run (`RelCT.wp`): the same stack pointer and
arguments, whose values are computed from public data only.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (macData)

variable {e : Bool}

/-! ## The writable regions -/

/-- The index of the context among the writable regions. -/
abbrev ci (enc : Bool) : Nat := if enc then 2 else 1

/-- Lower bounds on the lengths of the writable regions. -/
abbrev lensOf (enc : Bool) : List Nat := if enc then [0, 16, 632] else [0, 632]

theorem APre.wr_cases {s : State} (hp : APre e s) {r : Region} (hr : r ∈ s.wr) :
    r = dR s ∨ r = ctxR s ∨ (e = true ∧ r = tR s) := by
  cases e
  · have hw : s.wr = [dR s, ctxR s] := hp.wr
    rw [hw] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
  · have hw : s.wr = [dR s, tR s, ctxR s] := hp.wr
    rw [hw] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨rfl, rfl⟩)
    · exact .inr (.inl rfl)

theorem wr_facts {s : State} (hp : APre e s) :
    List.Forall₂ (fun r l => l ≤ r.len) s.wr (lensOf e) ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32 := by
  have hc := hp.fit_c; have hd := hp.fit_d; have ht := hp.fit_t
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · cases e
    · have hw : s.wr = [dR s, ctxR s] := hp.wr
      rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · have hw : s.wr = [dR s, tR s, ctxR s] := hp.wr
      rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · cases e
    · have hw : s.wr = [dR s, ctxR s] := hp.wr
      rw [hw]
      exact List.Pairwise.cons (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.symm) (List.pairwise_singleton _ _)
    · have hw : s.wr = [dR s, tR s, ctxR s] := hp.wr
      rw [hw]
      refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_) (List.pairwise_singleton _ _))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.d_t
        · exact hp.c_d.symm
      · simp only [List.mem_singleton] at hr; subst hr; exact hp.c_t.symm
  · rcases hp.wr_cases hr with rfl | rfl | ⟨-, rfl⟩ <;> simp only [addr_toNat] <;> omega

/-- The stack arguments are outside the writable regions. -/
theorem arg_wr {s : State} (hp : APre e s) : ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 16⟩ r := by
  have e' : (⟨State.addr s.sp, 16⟩ : Region) = argR s := by simp [stackArgAddr]
  intro r hr
  rw [e']
  rcases hp.wr_cases hr with rfl | rfl | ⟨he, rfl⟩
  · exact hp.d_arg.symm
  · exact hp.c_arg.symm
  · cases he; exact (show (tR s).Disjoint (argR s) from hp.t_arg).symm

theorem wr_eq {s₁ s₂ : State} (h₁ : APre e s₁) (h₂ : APre e s₂) (hpub : pubArm s₁ s₂) : s₁.wr = s₂.wr := by
  obtain ⟨-, -, -, -, -, a0, a1, a2, a3⟩ := hpub
  rw [h₁.wr, h₂.wr]
  simp only [ctxR, dR, tR, cx, dp, tp, cP, dP, tP, L, a0, a1, a2, a3]

theorem stackArgs_eq {s₁ s₂ : State} (hpub : pubArm s₁ s₂) : ∀ i < 4, stackArg s₁ i = stackArg s₂ i := by
  obtain ⟨-, -, -, -, -, a0, a1, a2, a3⟩ := hpub
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3

/-- The stack arguments, from a state where the invariant holds. -/
theorem Inv.argEq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) {i : Nat} (hi : i < 4) :
    stackArg s i = stackArg s₀ i := by
  rw [show stackArg s i = s.mem.readW (stackArgAddr s₀ i) 32 by simp only [stackArg, stackArgAddr, h.sp]]
  exact h.arg hp hi

/-! ## The taint on entry -/

/-- The initial taint: `r0`–`r3` (`key`, `nonce`, `aad`, `aad_len`) and the
stack arguments (`data`, `len`, `tag`, `work`) are public, and the last is
the base of the context. -/
def τ₀ (enc : Bool) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := lensOf enc, argLen := 16,
    argBases := [(12, ci enc)] }

theorem wf₀ {s : State} (hp : APre e s) : VG.Arm.Taint.Wf (τ₀ e) s := by
  refine ⟨fun _ => wr_facts hp, fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.spfit, arg_wr hp⟩,
    fun p hp' => ?_⟩
  simp only [τ₀, List.mem_singleton] at hp'
  subst hp'
  refine ⟨Nat.le_refl _, ?_⟩
  cases e
  · have hw : s.wr = [dR s, ctxR s] := hp.wr
    rw [VG.Arm.Taint.region, hw]; rfl
  · have hw : s.wr = [dR s, tR s, ctxR s] := hp.wr
    rw [VG.Arm.Taint.region, hw]; rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : APre e s₁) (h₂ : APre e s₂) (hpub : pubArm s₁ s₂) :
    VG.Arm.Taint.Agree (τ₀ e) s₁ s₂ := by
  have hw := wr_eq h₁ h₂ hpub
  have ha := stackArgs_eq hpub
  obtain ⟨psp, p0, p1, p2, p3, -⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => hw, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    argMem_of (j := 4) psp h₁.spfit ha⟩
  simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The frame -/

theorem push_eq' {s a : State} (h : isa.push (.push [.r1, .r12]) s = some a) : a = pushed [.r1, .r12] s := by
  rw [push_pushed rfl (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

/-- `vg_poly1305_finalize_scratch`'s view of the state after the push, with the
regions given in terms of the stack pointer `sp`. -/
theorem finView_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) (P O Sc : BitVec 32) :
    (pushed [.r1, .r12] s).callEntry.withRegions [⟨State.addr sp - 8, 8⟩] (finWr P O Sc) = finView s P O Sc := by
  rw [← h]

/-- The frame around `vg_poly1305_finalize_scratch`, in two runs whose states before
it are `x₁` and `x₂`, with the same stack pointer, pointers (`out` is `O`)
and message length. -/
theorem frame_ct {s₁ s₂ : State} (hp₁ : APre e s₁) (hp₂ : APre e s₂) (hpub : pubArm s₁ s₂)
    {O : State → BitVec 32} (ho₁ : OutOk s₁ (O s₁)) (ho₂ : OutOk s₂ (O s₂)) (hO : O s₂ = O s₁)
    {F : State → State → Prop}
    (hF : ∀ x₁ x₂, F x₁ x₂ → Inv s₁ x₁ ∧ Inv s₂ x₂ ∧ x₁.gpr .r0 = cP s₁ ∧ x₁.gpr .r1 = O s₁ ∧
      x₁.gpr .r12 = ptr s₁ scrOff ∧ x₂.gpr .r0 = cP s₂ ∧ x₂.gpr .r1 = O s₂ ∧
      x₂.gpr .r12 = ptr s₂ scrOff ∧ Proof.Poly1305.countArm x₁ = Proof.Poly1305.countArm x₂) :
    RelCT isa F finalize fun _ _ => True := by
  obtain ⟨psp, -, -, -, -, -, -, -, a3⟩ := hpub
  refine RelCT.frame (fun x₁ x₂ h => by
    obtain ⟨i₁, i₂, -⟩ := hF x₁ x₂ h
    rw [i₁.sp, i₂.sp, psp]) ?_
  refine RelCT.call (k := Proof.Poly1305.finalizeArm) Proof.Poly1305.Arm.Fin.finalize_ok
    Proof.Poly1305.Arm.Fin.finalize_ct [⟨State.addr s₁.sp - 8, 8⟩]
    (finWr (cP s₁) (O s₁) (ptr s₁ scrOff)) fun a b ⟨x₁, x₂, h, pa, pb⟩ => ?_
  obtain ⟨i₁, i₂, a0, a1, a12, b0, b1, b12, hc⟩ := hF x₁ x₂ h
  rw [push_eq' pa, push_eq' pb]
  have f₁ := fin_args hp₁ i₁ ho₁ a0 a1 a12
  have f₂ := fin_args hp₂ i₂ ho₂ b0 b1 b12
  have e2 : cP s₂ = cP s₁ := a3.symm
  have ep : ∀ k, ptr s₂ k = ptr s₁ k := fun k => by simp only [ptr, e2]
  rw [ep, e2, hO] at f₂
  rw [finView_eq i₁.sp, finView_eq (i₂.sp.trans psp.symm)]
  refine ⟨f₁.pre, f₂.pre, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [fin_nsp, fin_nsp, i₁.sp, i₂.sp, psp]
  · rw [fin_ng _ _ _ _ .r0 (by decide), fin_ng _ _ _ _ .r0 (by decide), a0, b0, e2]
  · have := (BitVec.append_32_inj hc).2
    rw [fin_ng _ _ _ _ .r2 (by decide), fin_ng _ _ _ _ .r2 (by decide), this]
  · have := (BitVec.append_32_inj hc).1
    rw [fin_ng _ _ _ _ .r3 (by decide), fin_ng _ _ _ _ .r3 (by decide), this]
  · rw [f₁.arg0 _ (fin_nsp _ _ _ _) rfl, f₂.arg0 _ (fin_nsp _ _ _ _) rfl]
  · rw [f₁.arg1 _ (fin_nsp _ _ _ _) rfl, f₂.arg1 _ (fin_nsp _ _ _ _) rfl]
  · have e : finRd x₁ = [⟨State.addr s₁.sp - 8, 8⟩] := by simp [finRd, i₁.sp]
    rw [← e]; exact f₁.cov
  · exact f₁.covW
  · have e : finRd x₂ = [⟨State.addr s₁.sp - 8, 8⟩] := by simp [finRd, i₂.sp, psp]
    rw [← e]; exact f₂.cov
  · exact f₂.covW

/-! ## After the frame -/

/-- `open`'s taint after the frame: the context (the base of the second
writable region), the data, its length and the stack arguments are public. -/
def τB : VG.Arm.Taint.T :=
  { regs := .ofList [.r7, .r10, .r11], flags := false, lens := lensOf false, bases := [(.r7, 1)],
    argLen := 16 }

theorem wfB {s₀ s : State} (hp : APre false s₀) (h : Inv s₀ s) : VG.Arm.Taint.Wf τB s := by
  refine ⟨fun _ => by rw [h.wr]; exact wr_facts hp, fun p hp' => ?_,
    fun _ => ⟨by rw [h.sp]; exact hp.spfit, by rw [h.sp, h.wr]; exact arg_wr hp⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [τB, List.mem_singleton] at hp'
  subst hp'
  have hw : s₀.wr = [dR s₀, ctxR s₀] := hp.wr
  rw [h.regs.r7, VG.Arm.Taint.region, h.wr, hw]; rfl

theorem agreeB {s₁ s₂ a b : State} (hp₁ : APre false s₁) (hp₂ : APre false s₂) (hpub : pubArm s₁ s₂)
    (ha : Inv s₁ a) (hb : Inv s₂ b) : VG.Arm.Taint.Agree τB a b := by
  have hw := wr_eq hp₁ hp₂ hpub
  have hs := stackArgs_eq hpub
  obtain ⟨psp, -, -, -, -, a0, a1, -, a3⟩ := hpub
  have hsp : a.sp = b.sp := by rw [ha.sp, hb.sp, psp]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => by rw [ha.wr, hb.wr, hw], wfB hp₁ ha, wfB hp₂ hb,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    argMem_of (j := 4) hsp (by rw [ha.sp]; exact hp₁.spfit) fun i hi => by
      rw [ha.argEq hp₁ hi, hb.argEq hp₂ hi]; exact hs i hi⟩
  simp only [τB, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [ha.regs.r7, hb.regs.r7, cP, cP, a3]
  · rw [ha.regs.r10, hb.regs.r10, dP, dP, a0]
  · rw [ha.regs.r11, hb.regs.r11, a1]

/-! ## Seal -/

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub Impl.ChaCha20Poly1305.Arm.«seal» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp₁ := APre.of s₁ h₁
  have hp₂ := APre.of s₂ h₂
  have hlen : (macData (A s₁) (Ct s₁)).length = (macData (A s₂) (Ct s₂)).length := by
    obtain ⟨-, -, -, -, p3, -, a1, -, -⟩ := hpub
    rw [length_macData, length_macData, length_encrypt, length_encrypt]
    simp only [VG.Proof.Poly1305.length_bytesAt, AL, L, p3, a1]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sealMain fun a b => True ∧ PreFs s₁ a ∧ PreFs s₂ b :=
    (RelCT.taint (A := taint) (τ₀ true) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact agree₀ hp₁ hp₂ hpub) (by taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨sealMain_ok hp₁, sealMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ PreFs s₁ a ∧ PreFs s₂ b) finalize
      fun a b => True ∧ PostFs s₁ a ∧ PostFs s₂ b :=
    (frame_ct hp₁ hp₂ hpub (O := tP) (outOk_tP hp₁) (outOk_tP hp₂) hpub.2.2.2.2.2.2.2.1.symm
      fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨finalize_seal_ok hp₁ h.2.1, finalize_seal_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ PostFs s₁ a ∧ PostFs s₂ b) (.block sealEnd) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r7]) (fun a b h => VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.2.1.regs.r7, h.2.2.regs.r7, cP, cP, hpub.2.2.2.2.2.2.2.2]) (by taint_decide)
  exact ((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Open -/

theorem open_ct : ConstantTime isa openArm.pre openArm.pub Impl.ChaCha20Poly1305.Arm.«open» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp₁ := APre.of s₁ h₁
  have hp₂ := APre.of s₂ h₂
  have hlen : (macData (A s₁) (D s₁)).length = (macData (A s₂) (D s₂)).length := by
    obtain ⟨-, -, -, -, p3, -, a1, -, -⟩ := hpub
    rw [length_macData, length_macData]
    simp only [VG.Proof.Poly1305.length_bytesAt, AL, L, p3, a1]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) openMain fun a b => True ∧ PreFo s₁ a ∧ PreFo s₂ b :=
    (RelCT.taint (A := taint) (τ₀ false) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact agree₀ hp₁ hp₂ hpub) (by taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨openMain_ok hp₁, openMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ PreFo s₁ a ∧ PreFo s₂ b) finalize
      fun a b => True ∧ PostFo s₁ a ∧ PostFo s₂ b :=
    (frame_ct hp₁ hp₂ hpub (O := fun s => ptr s tagOff) (outOk_tag hp₁) (outOk_tag hp₂)
      (by simp only [ptr, cP, hpub.2.2.2.2.2.2.2.2])
      fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨finalize_open_ok hp₁ h.2.1, finalize_open_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ PostFo s₁ a ∧ PostFo s₂ b) openEnd fun _ _ => True :=
    RelCT.taint (A := taint) τB (fun a b h => agreeB hp₁ hp₂ hpub h.2.1.inv h.2.2.inv) (by taint_decide)
  exact ((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data): `key` at `0x1000`, `nonce` at `0x1100`, `aad` at `0x2000`, the stack
arguments at `0x5000`: `data` and `work` at 0, `tag` at `0x3000`. -/
def sealSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x1100 | .r2 => 0x2000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := bif Nat.beq a.toNat 0x5009 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 16⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 632⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩, ⟨0x5000, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0, 632⟩] }

theorem seal_ok (s : State) (hs : sealArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.Arm.«seal» s t s' ∧ abiPreserved s s' ∧
      sealArm.post s s' :=
  seal_correct (APre.of s hs)

theorem open_ok (s : State) (hs : openArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.Arm.«open» s t s' ∧ abiPreserved s s' ∧
      openArm.post s s' :=
  open_correct (APre.of s hs)

theorem seal_verified :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«seal» (sealScratchContract Arm.abi 79 8) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealArm, Proof.ChaCha20Poly1305.preArm,
      Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.ChaCha20Poly1305.Arm.sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.ChaCha20Poly1305.Arm.sealSat)

/-- The postconditions match on `decrypt`; the result is the low word of
`r1:r0`. -/
theorem open_verified :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«open» (openScratchContract Arm.abi 79 8) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        simp only [Proof.ChaCha20Poly1305.openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨(e _ _).trans h.1, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact (e _ _).trans h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, Proof.ChaCha20Poly1305.openArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
          [Proof.ChaCha20Poly1305.Arm.openSat, Proof.ChaCha20Poly1305.Arm.sealSat, Arm.stackArg,
            Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.ChaCha20Poly1305.Arm.openSat }

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 12⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«seal»)
      (Spec.ChaCha20Poly1305.sealContract Arm.abi 664) :=
  Arm.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 79) (post := Spec.ChaCha20Poly1305.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 656) (m := 3) (words := 158) seal_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (pre_local _ _) (sealPost_local _) (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩, ⟨0x5000, 12⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract Arm.abi 664).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«open»)
      (Spec.ChaCha20Poly1305.openContract Arm.abi 664) :=
  Arm.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 79) (post := Spec.ChaCha20Poly1305.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 656) (m := 3) (words := 158) open_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (pre_local _ _) (openPost_local _) (openPost_out _) openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.Arm
