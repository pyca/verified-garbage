module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Stages
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Arm.Finalize
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Stages
meta import VerifiedGarbage.Proof.Framework.ContractPost
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
meta import VerifiedGarbage.Proof.Poly1305.Arm.Finalize
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

@[expose] public section

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
open VG.Proof.MdStream.Arm (Upd wp_cmp wp_strb wp_mov wp_add wp_subs op2_imm op2_reg)

variable {e : Bool}

/-- The ciphertext `seal` computes. -/
abbrev Ct (s₀ : State) : List Byte := Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (aP s₀) (AL s₀) :=
  ⟨(s₀.gpr .r9).isLt, hp.fit_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hp.a_rd, hc⟩⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (dP s₀) (L s₀) :=
  ⟨(s₀.gpr .r11).isLt, hp.fit_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.d_in, hc⟩⟩

theorem hAL (s₀ : State) : s₀.gpr .r9 = BitVec.ofNat 32 (AL s₀) := by simp [AL]

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.o_a.symm
    · exact hp.b_a.symm) (by have := (s₀.gpr .r9).isLt; simp only [AL]; omega)

/-- The data is unchanged by a frame of the context and the stack below. -/
theorem data_frame {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∃ k n, k + n ≤ 632 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀) :
    bytesAt m' (dp s₀) (L s₀) = bytesAt m (dp s₀) (L s₀) :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨k, n, h⟩ := hd r hr
    rcases h with ⟨hk, hs⟩ | rfl
    · exact (hp.c_d.sub_left (sub_ctx s₀ hk)).symm.sub_right hs
    · exact hp.b_d.symm) (by have := (s₀.gpr .r11).isLt; simp only [L]; omega)

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
  rw [d₂, show op s₀ = dp s₀ by simp only [op, dp, hp.inPlace]] at c₃
  have key₃ : bytesAt s₃.mem (off (cx s₀) keyOff) 32 = otk s₀ := by
    rw [bytesAt_frame k₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (by simp [keyOff, stOff]) (by simp [keyOff]) (by simp [stOff])
        · exact hp.c_o.sub_left (sub_ctx s₀ (by simp [keyOff]))) (by lit_omega), h₂.key]
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
  refine WP.mono (finArgs_ok i₇ (by decide) (out_seal i₇)) fun s₈ ⟨i₈, k₈, h0, h1, h12, hc⟩ => ?_
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
        · exact hp.b_d.symm) (by have := (s₀.gpr .r11).isLt; simp only [L]; omega), h.data]⟩

/-! ## After the frame -/

/-- What `seal`'s body computes, from its entry state `s₀`. -/
def SealB (s₀ s' : State) : Prop :=
  Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) = (bytesAt s'.mem (dp s₀) (L s₀), bytesAt s'.mem (tp s₀) 16)

theorem sealEnd_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : PostFs s₀ s) :
    WP isa (.block sealEnd) s fun s' => Restored s₀ s' ∧ s'.sp = s₀.sp ∧ SealB s₀ s' := by
  unfold sealEnd
  refine WP.mono (restore_ok hp h.regs.r7 h.saved h.rd h.wr) fun s₂ ⟨g₂, _, m₂, sp₂, _, _⟩ =>
    ⟨g₂, by rw [sp₂, h.sp], ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₂.mem (dp s₀) (L s₀), bytesAt s₂.mem (tp s₀) 16)
  rw [m₂, h.data, h.tag]
  simp only [Spec.ChaCha20Poly1305.encrypt]

theorem sealBody_correct {s₀ : State} (hp : APre true s₀) :
    WP isa sealBody s₀ fun s' => Restored s₀ s' ∧ s'.sp = s₀.sp ∧ SealB s₀ s' :=
  WP.seq (WP.mono (sealMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_seal_ok hp h)
    fun _ h' => sealEnd_ok hp h'))

/-! ## Open -/

/-- A part of the context is unchanged by a frame of other parts of it, the
destination and the stack below. -/
theorem ctx_disj {s₀ : State} (hp : APre e s₀) {rs : List Region} {a n : Nat} (ha : a + n ≤ 632)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨ r = belR s₀) :
    ∀ r ∈ rs, (sub s₀ a n).Disjoint r := by
  intro r hr
  rcases hd r hr with ⟨k, l, hk, hkl, rfl⟩ | rfl | rfl
  · exact sub_disj s₀ (by lit_omega) ha hk
  · exact hp.c_o.sub_left (sub_ctx s₀ ha)
  · exact (hp.b_c.sub_right (sub_ctx s₀ ha)).symm

theorem ctx_bytes {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a n : Nat}
    (ha : a + n ≤ 632)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨ r = belR s₀) :
    bytesAt m' (off (cx s₀) a) n = bytesAt m (off (cx s₀) a) n :=
  bytesAt_frame hf (ctx_disj hp ha hd) (by lit_omega)

theorem ctx_state {s₀ : State} (hp : APre e s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ stOff ∨ stOff + 64 ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨
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
    ∀ r ∈ macR s₀, (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨
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
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨ r = belR s₀ :=
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
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨ r = belR s₀ :=
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
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨ r = belR s₀ := by
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
    · exact hp.o_t.symm
    · exact hp.b_t.symm) (by omega)

/-- After the source is decrypted to the destination in `open`. -/
structure PostC (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  tag : bytesAt s.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

/-- The source decrypted to the destination. -/
theorem cryptOpen_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PostFo s₀ s) :
    WP isa crypt s (PostC s₀) := by
  refine WP.mono (crypt_ok hp h.inv h.st) fun s₁ ⟨i₁, k₁, c₁⟩ => ?_
  have hc : ∀ {a n : Nat}, stOff + 64 ≤ a → a + n ≤ 632 → ∀ r ∈ [sub s₀ 0 (stOff + 64), oR s₀],
      (∃ k l, k + l ≤ 632 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = oR s₀ ∨ r = belR s₀ :=
    fun ha _ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, stOff + 64, by simp [stOff], by omega, rfl⟩
      · exact .inr (.inl rfl)
  rw [h.data] at c₁
  exact ⟨i₁, by rw [ctx_bytes hp k₁ (by simp [tagOff]) (hc (by simp [stOff, tagOff]) (by simp [tagOff])), h.tag],
    c₁⟩

/-- What `cmp_ok` gives, from the body's entry state `s₀`. -/
def EB (s₀ s₃ : State) : Prop := Inv s₀ s₃ ∧
  s₃.gpr .r0 = (if mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0) ∧
  s₃.z = (s₃.gpr .r0 == 0) ∧
  bytesAt s₃.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

/-- The tags compared: `r0` is whether the tag is right, and `Z` whether it
is not. -/
theorem cmp_ok {s₀ : State} (hp : APre false s₀) {s₁ : State} (h : PostC s₀ s₁) :
    WP isa (.block (Impl.ChaCha20Poly1305.Arm.compare ++ ([.cmp .r0 (.imm 0)] : List Instr))) s₁ (EB s₀) := by
  have i₁ := h.inv
  refine WP.block_append (WP.mono (compare_ok hp i₁)
    fun s₂ ⟨r0₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : Inv s₀ s₂ := i₁.step0 ⟨fun r hr _ => g₂ r hr, sp₂, rd₂, wr₂, by rw [m₂]; exact Frame.refl _ _⟩
  refine wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_
  have i₃ : Inv s₀ s₃ := i₂.step0 ⟨fun r _ _ => by rw [f₃.gpr], f₃.sp, f₃.rd, f₃.wr,
    by rw [f₃.mem]; exact Frame.refl _ _⟩
  refine ⟨i₃, by rw [f₃.gpr, r0₂, h.tag, tag_eq0 hp i₁],
    by rw [z₃, f₃.gpr, show (s₂.gpr .r0 - 0 : BitVec 32) = s₂.gpr .r0 from BitVec.sub_zero _],
    by rw [f₃.mem, m₂, h.data]⟩

/-- The source decrypted to the destination and the tags compared. -/
theorem endBody_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PostFo s₀ s) :
    WP isa (.seq crypt (.block (Impl.ChaCha20Poly1305.Arm.compare ++ ([.cmp .r0 (.imm 0)] : List Instr)))) s
      (EB s₀) :=
  WP.seq (WP.mono (cryptOpen_ok hp h) fun _ h' => cmp_ok hp h')

/-- A write of a temporary register (not one we keep) is kept. -/
theorem kept_upd {s s' : State} {d : Reg} {v : BitVec 32} (rs : List Region) (u : Upd s s' d v)
    (hd : d ∉ preserved := by decide) : Kept rs s s' :=
  ⟨fun r hr _ => u.other r fun e => hd (e ▸ hr), u.sp, u.rd, u.wr, by rw [u.mem]; exact Frame.refl _ _⟩

theorem ofNat32_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

theorem ofNat32_ne_zero {n : Nat} (h : 0 < n) (hn : n < 2 ^ 32) : BitVec.ofNat 32 n ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  exact Nat.ne_of_gt h this

/-- One step of `zeroData`'s loop: the byte at `op + j` zeroed, with `r0`
zero and `r2` at it. -/
theorem zeroStep_ok {s₀ : State} (hp : APre false s₀) {u : State} (hu : Inv s₀ u) {j : Nat}
    (hj : j < L s₀) (h0 : u.gpr .r0 = 0) (h2 : u.gpr .r2 = oP s₀ + BitVec.ofNat 32 j)
    (hz : Proof.Zeroize.Prefix u.mem (op s₀) j) :
    WP isa (.block [.strb .r0 .r2 0, .dp .add .r2 .r2 (.imm 1), .subs .r3 .r3 (.imm 1)]) u fun u' =>
      Inv s₀ u' ∧ u'.gpr .r0 = 0 ∧ u'.gpr .r2 = oP s₀ + BitVec.ofNat 32 (j + 1) ∧
      u'.gpr .r3 = u.gpr .r3 - 1 ∧ u'.z = (u.gpr .r3 - 1 == 0) ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → u'.gpr r = u.gpr r) ∧ Proof.Zeroize.Prefix u'.mem (op s₀) (j + 1) := by
  have hfit := hp.fit_o
  have h2' : u.gpr .r2 + BitVec.ofNat 32 0 = oP s₀ + BitVec.ofNat 32 j := by
    rw [h2]; exact BitVec.add_zero _
  have ha : State.addr (u.gpr .r2 + BitVec.ofNat 32 0) = op s₀ + BitVec.ofNat 64 j := by
    rw [h2', addr_add (by omega)]
  have hd : (op s₀).toNat = (oP s₀).toNat := addr_toNat _
  have hc : (oR s₀).Contains (op s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_strb (by decide) ha ⟨oR s₀, by rw [hu.wr]; exact hp.o_wr, hc⟩ fun u₁ m₁ => ?_
  refine wp_add (op2_imm (by decide)) fun u₂ v₂ =>
    wp_subs (op2_imm (by decide)) fun u₃ v₃ z₃ => WP.block_nil ?_
  have st₁ : Kept [oR s₀] u u₁ :=
    ⟨fun r _ _ => by rw [m₁.gpr], m₁.sp, m₁.rd, m₁.wr,
      by rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc⟩
  have st : Kept [oR s₀] u u₃ := (st₁.trans (kept_upd _ v₂)).trans (kept_upd _ v₃)
  have o : ∀ r, r ≠ .r2 → r ≠ .r3 → u₃.gpr r = u.gpr r := fun r a b => by
    rw [v₃.other r b, v₂.other r a, m₁.gpr]
  have e3 : u₂.gpr .r3 = u.gpr .r3 := by rw [v₂.other _ (by decide), m₁.gpr]
  refine ⟨hu.step st (fun r hr => ⟨oR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.c_o.sub_left (sub_ctx s₀ (by decide))),
    by rw [o _ (by decide) (by decide), h0], ?_, by rw [v₃.gpr, e3], by rw [z₃, e3], o, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, h2, BitVec.add_assoc, BitVec.ofNat_add]; rfl
  · rw [v₃.mem, v₂.mem, m₁.mem, h0, show BitVec.setWidth 8 (0 : BitVec 32) = 0 by decide]
    exact Proof.Zeroize.prefix_writeW hz (by omega)

/-- `zeroData`, with `r0` zero: zeros at the destination, and only `r2`,
`r3` and the flags written. -/
theorem zeroData_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (h0 : s.gpr .r0 = 0) :
    WP isa zeroData s fun s' => Inv s₀ s' ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0 ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) := by
  have hL : L s₀ < 2 ^ 32 := (s₀.gpr .r11).isLt
  unfold zeroData
  refine WP.seq (wp_mov (op2_reg _ _) fun u₁ v₁ => wp_mov (op2_reg _ _) fun u₂ v₂ =>
    wp_cmp (op2_imm (by decide)) fun u₃ f₃ z₃ => WP.block_nil ?_)
  have r2₃ : u₃.gpr .r2 = oP s₀ := by rw [f₃.gpr, v₂.other _ (by decide), v₁.gpr, h.regs.r6]
  have r3₃ : u₃.gpr .r3 = BitVec.ofNat 32 (L s₀) := by
    rw [f₃.gpr, v₂.gpr, v₁.other _ (by decide), h.regs.r11, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have z₃' : u₃.z = (BitVec.ofNat 32 (L s₀) == 0) := by
    rw [z₃, show u₂.gpr .r3 = u₃.gpr .r3 by rw [f₃.gpr], r3₃,
      show (BitVec.ofNat 32 (L s₀) - 0 : BitVec 32) = BitVec.ofNat 32 (L s₀) from BitVec.sub_zero _]
  have i₃ : Inv s₀ u₃ := h.step0 (((kept_upd [] v₁).trans (kept_upd [] v₂)).trans
    ⟨fun r _ _ => by rw [f₃.gpr], f₃.sp, f₃.rd, f₃.wr, by rw [f₃.mem]; exact Frame.refl _ _⟩)
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → u₃.gpr r = s.gpr r := fun r a b => by
    rw [f₃.gpr, v₂.other r b, v₁.other r a]
  by_cases hz : L s₀ = 0
  · refine WP.ite true (by show some u₃.z = some true; rw [z₃', hz]; rfl)
      (fun _ => WP.block_nil ⟨i₃, ?_, o₃⟩) (by simp)
    rw [hz]; rfl
  · have hne := ofNat32_ne_zero (n := L s₀) (by omega) hL
    refine WP.ite false (by show some u₃.z = some false; rw [z₃', beq_false_of_ne hne])
      (by simp) fun _ => ?_
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < L s₀ ∧ rem = L s₀ - j ∧ Inv s₀ u ∧ u.gpr .r0 = 0 ∧
      u.gpr .r2 = oP s₀ + BitVec.ofNat 32 j ∧ u.gpr .r3 = BitVec.ofNat 32 (L s₀ - j) ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → u.gpr r = s.gpr r) ∧ Proof.Zeroize.Prefix u.mem (op s₀) j) ?_ (L s₀) u₃
      ⟨0, by omega, by omega, i₃, by rw [o₃ _ (by decide) (by decide), h0],
        by rw [r2₃]; exact (BitVec.add_zero _).symm, by rw [r3₃, Nat.sub_zero], o₃,
        fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem u ⟨j, hj, hr, hu, e0, e2, e3, ho, hpz⟩
    refine WP.mono (zeroStep_ok hp hu hj e0 e2 hpz) fun u' ⟨i', r0', r2', r3', z', o', p'⟩ => ?_
    have hsub : BitVec.ofNat 32 (L s₀ - j) - 1 = BitVec.ofNat 32 (L s₀ - (j + 1)) := by
      rw [ofNat32_sub_one (by omega) (by omega), Nat.sub_sub]
    rw [e3, hsub] at r3' z'
    have o'' : ∀ r, r ≠ .r2 → r ≠ .r3 → u'.gpr r = s.gpr r := fun r a b => by rw [o' r a b, ho r a b]
    by_cases he : j + 1 = L s₀
    · left
      refine ⟨by show some (!u'.z) = some false; rw [z', he, Nat.sub_self]; rfl, i', ?_, o''⟩
      rw [he] at p'
      exact Proof.Zeroize.prefix_spec p'
    · right
      have hne := ofNat32_ne_zero (n := L s₀ - (j + 1)) (by omega) (by omega)
      refine ⟨by show some (!u'.z) = some true; rw [z', beq_false_of_ne hne]; rfl,
        L s₀ - (j + 1), by omega, j + 1, by omega, rfl, i', r0', r2', r3', o'', p'⟩

/-- The epilogue, from the invariant: our caller's registers restored. -/
theorem restoreEnd_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => (Restored s₀ s' ∧ s'.sp = s₀.sp) ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.mem = s.mem :=
  WP.mono (restore_ok hp h.regs.r7 h.saved h.rd h.wr) fun _ ⟨g, o, m, sp, _, _⟩ =>
    ⟨⟨g, by rw [sp, h.sp]⟩, o .r0 (by decide) (by decide), m⟩

/-- What `open`'s body computes, from its entry state `s₀`. -/
def OpenB (s₀ s' : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
  | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (op s₀) (L s₀) = pt
  | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0

theorem openEnd_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : PostFo s₀ s) :
    WP isa openEnd s fun s' => (Restored s₀ s' ∧ s'.sp = s₀.sp) ∧ OpenB s₀ s' := by
  unfold openEnd
  refine WP.seq (WP.mono (endBody_ok hp h) fun s₃ ⟨i₃, r0₃, z₃, d₃⟩ => ?_)
  unfold openTail
  refine WP.seq ?_
  by_cases hc : mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀
  · simp only [hc, ↓reduceIte] at r0₃
    refine WP.ite false (by show some s₃.z = some false; rw [z₃, r0₃]; rfl) (by simp)
      fun _ => WP.block_nil ?_
    refine WP.mono (restoreEnd_ok hp i₃) fun s₄ ⟨ha, r0₄, m₄⟩ => ⟨ha, ?_⟩
    unfold OpenB
    split
    next pt hpt =>
      obtain ⟨-, rfl⟩ := decrypt_eq_some hpt
      exact ⟨by rw [r0₄, r0₃], by rw [m₄, d₃]⟩
    next hn => exact absurd hc (decrypt_eq_none hn)
  · simp only [hc, ↓reduceIte] at r0₃
    refine WP.ite true (by show some s₃.z = some true; rw [z₃, r0₃]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (zeroData_ok hp i₃ r0₃) fun s₄ ⟨i₄, z₄, o₄⟩ => ?_
    refine WP.mono (restoreEnd_ok hp i₄) fun s₅ ⟨ha, r0₅, m₅⟩ => ⟨ha, ?_⟩
    unfold OpenB
    split
    next pt hpt => exact absurd (decrypt_eq_some hpt).1 hc
    next hn => exact ⟨by rw [r0₅, o₄ _ (by decide) (by decide), r0₃], by rw [m₅, z₄]⟩

theorem openBody_correct {s₀ : State} (hp : APre false s₀) :
    WP isa openBody s₀ fun s' => (Restored s₀ s' ∧ s'.sp = s₀.sp) ∧ OpenB s₀ s' :=
  WP.seq (WP.mono (openMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_open_ok hp h)
    fun _ h' => openEnd_ok hp h'))

/-! ## The entries -/

/-- Setting the destination keeps what the prologue gives. -/
theorem Entered.upd6 {s b b' : State} {w t : Nat} (he : Entered s w t b) {v : BitVec 32}
    (u : VG.Proof.MdStream.Arm.Upd b b' .r6 v) : Entered s w t b' := by
  have h7 : b'.gpr .r7 = b.gpr .r7 := u.other _ (by decide)
  have hcx : cx b' = cx b := by simp only [cx, cP, h7]
  have hsub : sub b' savOff 36 = sub b savOff 36 := by simp only [sub, hcx]
  refine ⟨by rw [u.other _ (by decide), he.r0], by rw [u.other _ (by decide), he.r1],
    by rw [u.other _ (by decide), he.r4], by rw [h7, he.r7], by rw [u.other _ (by decide), he.r8],
    by rw [u.other _ (by decide), he.r9], by rw [u.other _ (by decide), he.r10],
    by rw [u.other _ (by decide), he.r11], by rw [u.sp, he.sp], by rw [u.rd, he.rd], by rw [u.wr, he.wr],
    by rw [hsub, u.mem]; exact he.frame, fun p hp' => by rw [hcx, u.mem]; exact he.saved p hp'⟩

/-- `seal` and `open`'s prologue: the destination the data. -/
theorem inPlace_ok {s : State} (hs : EntryOk s 4 3) :
    WP isa (.block inPlace) s fun b => Entered s 3 2 b ∧ b.gpr .r6 = stackArg s 0 := by
  show WP isa (.block (entry (4 * 3) ++ save ++ moves (4 * 2) ++ [.mov .r6 (.reg .r10)])) s _
  exact prologueA_ok hs (by decide) (by decide) (by decide) (by decide) fun b he _ =>
    wp_mov (op2_reg _ _) fun b' u => WP.block_nil ⟨he.upd6 u, by rw [u.gpr, he.r10]⟩

/-- `open_to`'s prologue: the destination from the stack. -/
theorem toEntry_ok {s : State} (hs : EntryOk s 6 5) :
    WP isa (.block toEntry) s fun b => Entered s 5 4 b ∧ b.gpr .r6 = stackArg s 2 := by
  show WP isa (.block (entry (4 * 5) ++ save ++ moves (4 * 4) ++ [.ldrSp .r6 8])) s _
  exact prologueA_ok hs (by decide) (by decide) (by decide) (by decide) fun b he hm =>
    VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [he.sp]; rfl)
      (hs.arg_in (by decide) he.rd) fun b' u => WP.block_nil ⟨he.upd6 u, by rw [u.gpr]; exact hs.arg_eq hm (by decide)⟩

/-- The callee-saved registers restored, and the stack pointer as on entry. -/
theorem Entered.abi {s b s' : State} {w t : Nat} (he : Entered s w t b) (hr : Restored b s')
    (hsp : s'.sp = b.sp) : abiPreserved s s' := by
  refine ⟨fun r hr' => ?_, hsp.trans he.sp⟩
  rw [preserved_eq] at hr'
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
  rw [hr p hp', he.saved p hp']

/-- What the body reads, from what the function reads on entry: the
prologue writes only the saved registers' slots of the context. -/
theorem Entered.inputs {s b : State} {w t : Nat} (he : Entered s w t b) (hp : APre e b) :
    K b = bytesAt s.mem (State.addr (s.gpr .r0)) 32 ∧ N b = bytesAt s.mem (State.addr (s.gpr .r1)) 12 ∧
    A b = bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat ∧
    D b = bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat ∧
    T0 b = bytesAt s.mem (State.addr (stackArg s t)) 16 ∧
    dp b = State.addr (stackArg s 0) ∧ L b = (stackArg s 1).toNat ∧ tp b = State.addr (stackArg s t) := by
  have hb : ∀ {p : Addr} {n : Nat}, (ctxR b).Disjoint ⟨p, n⟩ → n ≤ 2 ^ 64 →
      bytesAt b.mem p n = bytesAt s.mem p n := fun hd hn =>
    bytesAt_frame he.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_left (sub_ctx b (by decide))).symm) hn
  refine ⟨(hb hp.c_k (by decide)).trans (by simp only [kp, kP, he.r0]),
    (hb hp.c_n (by decide)).trans (by simp only [np, nP, he.r1]),
    (hb hp.c_a (by have := (b.gpr .r9).isLt; simp only [AL]; omega)).trans (by simp only [ad, aP, AL, he.r8, he.r9]),
    (hb hp.c_d (by have := (b.gpr .r11).isLt; simp only [L]; omega)).trans (by simp only [dp, dP, L, he.r10, he.r11]),
    (hb hp.c_t (by decide)).trans (by simp only [tp, tP, he.r4]),
    by simp only [dp, dP, he.r10], by simp only [L, he.r11], by simp only [tp, tP, he.r4]⟩

/-! ## The functions -/

theorem EntryOk.ofIn {enc : Bool} {s : State} (h : preArm enc s) : EntryOk s 4 3 := by
  obtain ⟨hrd, hwr, -, -, -, -, -, c_arg, -, -, -, -, -, -, -, -, -, -, f_c, -, -, -, -, -, -, spfit⟩ := h
  exact ⟨spfit, by rw [hrd]; cases enc <;> simp, by rw [hwr]; cases enc <;> simp, f_c, c_arg⟩

theorem EntryOk.ofTo {s : State} (h : preToArm s) : EntryOk s 6 5 := by
  obtain ⟨hrd, hwr, -, -, -, -, -, -, c_arg, -, -, -, -, -, -, -, -, -, -, -, f_c, -, -, -, -, -, -, -,
    spfit, -⟩ := h
  exact ⟨spfit, by rw [hrd]; simp, by rw [hwr]; simp, f_c, c_arg⟩

/-- The body's precondition, from `seal`'s or `open`'s. -/
theorem APre.ofIn {enc : Bool} {s b : State} (h : preArm enc s) (he : Entered s 3 2 b)
    (h6 : b.gpr .r6 = stackArg s 0) : APre enc b := by
  obtain ⟨hrd, hwr, c_k, c_n, c_a, c_d, c_t, -, -, -, d_a, d_t, -, -, b_c, b_a, b_d, b_t,
    f_c, f_a, f_d, f_t, f_k, f_n, sp8, -⟩ := h
  have eK : kR b = ⟨State.addr (s.gpr .r0), 32⟩ := by simp only [kR, kp, kP, he.r0]
  have eN : nR b = ⟨State.addr (s.gpr .r1), 12⟩ := by simp only [nR, np, nP, he.r1]
  have eA : aR b = ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ := by simp only [aR, ad, aP, AL, he.r8, he.r9]
  have eD : dR b = ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by
    simp only [dR, dp, dP, L, he.r10, he.r11]
  have eO : oR b = ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by simp only [oR, op, oP, L, h6, he.r11]
  have eT : tR b = ⟨State.addr (stackArg s 2), 16⟩ := by simp only [tR, tp, tP, he.r4]
  have eC : ctxR b = ⟨State.addr (stackArg s 3), 632⟩ := by simp only [ctxR, cx, cP, he.r7]
  have eB : belR b = ⟨State.addr s.sp - 8, 8⟩ := by simp only [belR, he.sp]
  refine ⟨by rw [he.wr, hwr, eD, eT, eC, eO], by rw [eK, he.rd, hrd]; cases enc <;> simp,
    by rw [eN, he.rd, hrd]; cases enc <;> simp, by rw [eA, he.rd, hrd]; cases enc <;> simp,
    fun he' => by subst he'; rw [eT, he.rd, hrd]; simp, by rw [eD, he.rd, he.wr, hwr]; cases enc <;> simp,
    .inl (by simp only [oP, dP, h6, he.r10]), by rw [eC, eK]; exact c_k, by rw [eC, eN]; exact c_n,
    by rw [eC, eA]; exact c_a, by rw [eC, eD]; exact c_d, by rw [eC, eT]; exact c_t,
    by rw [eC, eO]; exact c_d, by rw [eO, eA]; exact d_a, by rw [eO, eT]; exact d_t,
    by rw [eB, eC]; exact b_c, by rw [eB, eA]; exact b_a, by rw [eB, eD]; exact b_d,
    by rw [eB, eO]; exact b_d, by rw [eB, eT]; exact b_t, by simp only [cP, he.r7]; exact f_c,
    by simp only [aP, AL, he.r8, he.r9]; exact f_a, by simp only [dP, L, he.r10, he.r11]; exact f_d,
    by simp only [oP, L, h6, he.r11]; exact f_d, by simp only [tP, he.r4]; exact f_t,
    by simp only [kP, he.r0]; exact f_k, by simp only [nP, he.r1]; exact f_n, by rw [he.sp]; exact sp8⟩

/-- The body's precondition, from `open_to`'s. -/
theorem APre.ofTo {s b : State} (h : preToArm s) (he : Entered s 5 4 b) (h6 : b.gpr .r6 = stackArg s 2) :
    APre false b := by
  obtain ⟨hrd, hwr, w_k, w_n, w_a, w_s, w_d, w_t, -, d_k, d_n, d_a, d_s, d_t, -, b_w, b_a, b_s, b_d, b_t,
    f_w, f_a, f_s, f_d, f_t, f_k, f_n, sp8, -, hdl⟩ := h
  have eK : kR b = ⟨State.addr (s.gpr .r0), 32⟩ := by simp only [kR, kp, kP, he.r0]
  have eN : nR b = ⟨State.addr (s.gpr .r1), 12⟩ := by simp only [nR, np, nP, he.r1]
  have eA : aR b = ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ := by simp only [aR, ad, aP, AL, he.r8, he.r9]
  have eD : dR b = ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ := by
    simp only [dR, dp, dP, L, he.r10, he.r11]
  have eO : oR b = ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩ := by
    simp only [oR, op, oP, L, h6, he.r11, hdl]
  have eT : tR b = ⟨State.addr (stackArg s 4), 16⟩ := by simp only [tR, tp, tP, he.r4]
  have eC : ctxR b = ⟨State.addr (stackArg s 5), 632⟩ := by simp only [ctxR, cx, cP, he.r7]
  have eB : belR b = ⟨State.addr s.sp - 8, 8⟩ := by simp only [belR, he.sp]
  refine ⟨by rw [he.wr, hwr, eO, eC]; rfl, by rw [eK, he.rd, hrd]; simp, by rw [eN, he.rd, hrd]; simp,
    by rw [eA, he.rd, hrd]; simp, fun _ => by rw [eT, he.rd, hrd]; simp, by rw [eD, he.rd, hrd]; simp,
    .inr ⟨rfl, by rw [eD, eO]; exact d_s.symm⟩, by rw [eC, eK]; exact w_k, by rw [eC, eN]; exact w_n,
    by rw [eC, eA]; exact w_a, by rw [eC, eD]; exact w_s, by rw [eC, eT]; exact w_t,
    by rw [eC, eO]; exact w_d, by rw [eO, eA]; exact d_a, by rw [eO, eT]; exact d_t,
    by rw [eB, eC]; exact b_w, by rw [eB, eA]; exact b_a, by rw [eB, eD]; exact b_s,
    by rw [eB, eO]; exact b_d, by rw [eB, eT]; exact b_t, by simp only [cP, he.r7]; exact f_w,
    by simp only [aP, AL, he.r8, he.r9]; exact f_a, by simp only [dP, L, he.r10, he.r11]; exact f_s,
    by simp only [oP, L, h6, he.r11]; rw [← hdl]; exact f_d, by simp only [tP, he.r4]; exact f_t,
    by simp only [kP, he.r0]; exact f_k, by simp only [nP, he.r1]; exact f_n, by rw [he.sp]; exact sp8⟩

theorem seal_correct {s : State} (h : sealArm.pre s) :
    WP isa Impl.ChaCha20Poly1305.Arm.«seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' := by
  refine WP.seq (WP.mono (inPlace_ok (EntryOk.ofIn h)) fun b ⟨he, h6⟩ => ?_)
  have hp := APre.ofIn h he h6
  refine WP.mono (sealBody_correct hp) fun s' ⟨hr, hsp, hq⟩ => ⟨he.abi hr hsp, ?_⟩
  obtain ⟨eK, eN, eA, eD, -, edp, eL, etp⟩ := he.inputs hp
  unfold SealB at hq
  rw [eK, eN, eA, eD, edp, eL, etp] at hq
  exact hq

theorem open_correct {s : State} (h : openArm.pre s) :
    WP isa Impl.ChaCha20Poly1305.Arm.«open» s fun s' => abiPreserved s s' ∧ openArm.post s s' := by
  refine WP.seq (WP.mono (inPlace_ok (EntryOk.ofIn h)) fun b ⟨he, h6⟩ => ?_)
  have hp := APre.ofIn h he h6
  refine WP.mono (openBody_correct hp) fun s' ⟨⟨hr, hsp⟩, hq⟩ => ⟨he.abi hr hsp, ?_⟩
  obtain ⟨eK, eN, eA, eD, eT, -, eL, -⟩ := he.inputs hp
  have eo : op b = State.addr (stackArg s 0) := by simp only [op, oP, h6]
  unfold OpenB at hq
  rw [eK, eN, eA, eD, eT, eo, eL] at hq
  exact hq

theorem openTo_correct {s : State} (h : openToArm.pre s) :
    WP isa Impl.ChaCha20Poly1305.Arm.openTo s fun s' => abiPreserved s s' ∧ openToArm.post s s' := by
  refine WP.seq (WP.mono (toEntry_ok (EntryOk.ofTo h)) fun b ⟨he, h6⟩ => ?_)
  have hp := APre.ofTo h he h6
  refine WP.mono (openBody_correct hp) fun s' ⟨⟨hr, hsp⟩, hq⟩ => ⟨he.abi hr hsp, ?_⟩
  obtain ⟨eK, eN, eA, eD, eT, -, eL, -⟩ := he.inputs hp
  have eo : op b = State.addr (stackArg s 2) := by simp only [op, oP, h6]
  unfold OpenB at hq
  rw [eK, eN, eA, eD, eT, eo, eL] at hq
  exact hq

end VG.Proof.ChaCha20Poly1305.Arm

end


/-!
# ChaCha20-Poly1305 on ARMv7: `Verified`

Correctness (above), constant time, and a state satisfying the precondition,
of the code with its working space as its last argument
(`sealScratchContract`, `openZeroScratchContract`, `openToScratchContract`),
and then of the functions, which allocate it in a frame on the stack and wipe
it after the code (`Verified.stackScratchWiped`).

Constant time relates two runs from states that agree on the public data
(`RelCT`), part by part. The prologue reads only the arguments, which are
public (`τP`), and sets the registers the body keeps from them, so the body
runs from states that agree on those registers (`BPub`): `open`'s body is
proven once (`openBody_ct`), for `open` and `open_to`. The taint analysis
does not analyse frames, so it runs on the body before the frame around
`vg_poly1305_finalize_scratch` (`sealMain`, `openMain`) and after it
(`sealEnd`, `openEnd`), through the callees' code: it knows `r4` and
`r6`–`r11` for public after each call because every callee saves them in
memory at known offsets of the context, which it tracks, and restores them,
and `r7` for the base of the context once it is set from the callee's
pointer that the callee keeps. The frame itself leaks only addresses
computed from the stack pointer, and `vg_poly1305_finalize_scratch` is
constant time (`RelCT.frame`, `RelCT.call`), given what the correctness
proof shows of the states on either side of it in each run (`RelCT.wp`): the
same stack pointer and arguments, whose values are computed from public data
only.
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

theorem wr_facts {s : State} (hp : APre e s) :
    List.Forall₂ (fun r l => l ≤ r.len) s.wr (lensOf e) ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.base.toNat + r.len ≤ 2 ^ 32 := by
  have hc := hp.fit_c; have hd := hp.fit_d; have ho := hp.fit_o; have ht := hp.fit_t
  cases e
  · have hw : s.wr = [oR s, ctxR s] := hp.wr
    rw [hw]
    refine ⟨.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil), List.Pairwise.cons (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_o.symm) (List.pairwise_singleton _ _),
      fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [addr_toNat] <;> omega
  · have hw : s.wr = [dR s, tR s, ctxR s] := hp.wr
    rw [hw]
    refine ⟨.cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)),
      List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_) (List.pairwise_singleton _ _)),
      fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.d_t
      · exact hp.c_d.symm
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.c_t.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [addr_toNat] <;> omega

/-- The context is the writable region `ci e`. -/
theorem region_ctx {s₀ s : State} (hp : APre e s₀) (h : s.wr = s₀.wr) :
    (VG.Arm.Taint.region s (ci e)).base = cx s₀ := by
  rw [VG.Arm.Taint.region, h]
  cases e
  · have hw : s₀.wr = [oR s₀, ctxR s₀] := hp.wr
    rw [hw]; rfl
  · have hw : s₀.wr = [dR s₀, tR s₀, ctxR s₀] := hp.wr
    rw [hw]; rfl

/-! ## The body's taint on entry -/

/-- What two runs of a body agree on: the stack pointer and the registers
the prologue set. -/
def BPub (b₁ b₂ : State) : Prop :=
  b₁.sp = b₂.sp ∧ b₁.gpr .r0 = b₂.gpr .r0 ∧ b₁.gpr .r1 = b₂.gpr .r1 ∧ b₁.gpr .r4 = b₂.gpr .r4 ∧
  b₁.gpr .r6 = b₂.gpr .r6 ∧ b₁.gpr .r7 = b₂.gpr .r7 ∧ b₁.gpr .r8 = b₂.gpr .r8 ∧
  b₁.gpr .r9 = b₂.gpr .r9 ∧ b₁.gpr .r10 = b₂.gpr .r10 ∧ b₁.gpr .r11 = b₂.gpr .r11

theorem wr_eq {b₁ b₂ : State} (h₁ : APre e b₁) (h₂ : APre e b₂) (hpub : BPub b₁ b₂) : b₁.wr = b₂.wr := by
  obtain ⟨-, -, -, a4, a6, a7, -, -, a10, a11⟩ := hpub
  rw [h₁.wr, h₂.wr]
  simp only [ctxR, dR, tR, oR, cx, dp, tp, op, cP, dP, tP, oP, L, a4, a6, a7, a10, a11]

/-- The body's taint on entry: the registers the prologue set are public,
and `r7` is the base of the context. -/
def τM (enc : Bool) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r4, .r6, .r7, .r8, .r9, .r10, .r11], flags := false, lens := lensOf enc,
    bases := [(.r7, ci enc)] }

theorem wfM {b : State} (hp : APre e b) : VG.Arm.Taint.Wf (τM e) b := by
  refine ⟨fun _ => wr_facts hp, fun p hp' => ?_, fun h => (Nat.lt_irrefl 0 h).elim,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [τM, List.mem_singleton] at hp'
  subst hp'
  exact (region_ctx hp rfl).symm

theorem agreeM {b₁ b₂ : State} (h₁ : APre e b₁) (h₂ : APre e b₂) (hpub : BPub b₁ b₂) :
    VG.Arm.Taint.Agree (τM e) b₁ b₂ := by
  have hw := wr_eq h₁ h₂ hpub
  obtain ⟨psp, a0, a1, a4, a6, a7, a8, a9, a10, a11⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => hw, wfM h₁, wfM h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => (Nat.not_lt_zero k hk).elim⟩
  simp only [τM, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

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
theorem frame_ct {s₁ s₂ : State} (hp₁ : APre e s₁) (hp₂ : APre e s₂) (hpub : BPub s₁ s₂)
    {O : State → BitVec 32} (ho₁ : OutOk s₁ (O s₁)) (ho₂ : OutOk s₂ (O s₂)) (hO : O s₂ = O s₁)
    {F : State → State → Prop}
    (hF : ∀ x₁ x₂, F x₁ x₂ → Inv s₁ x₁ ∧ Inv s₂ x₂ ∧ x₁.gpr .r0 = cP s₁ ∧ x₁.gpr .r1 = O s₁ ∧
      x₁.gpr .r12 = ptr s₁ scrOff ∧ x₂.gpr .r0 = cP s₂ ∧ x₂.gpr .r1 = O s₂ ∧
      x₂.gpr .r12 = ptr s₂ scrOff ∧ Proof.Poly1305.countArm x₁ = Proof.Poly1305.countArm x₂) :
    RelCT isa F finalize fun _ _ => True := by
  obtain ⟨psp, -, -, -, -, a7, -, -, -, -⟩ := hpub
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
  have e2 : cP s₂ = cP s₁ := a7.symm
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
writable region), the tag, the destination, the source and its length are
public. -/
def τB : VG.Arm.Taint.T :=
  { regs := .ofList [.r4, .r6, .r7, .r10, .r11], flags := false, lens := lensOf false, bases := [(.r7, 1)] }

theorem wfB {s₀ s : State} (hp : APre false s₀) (h : Inv s₀ s) : VG.Arm.Taint.Wf τB s := by
  refine ⟨fun _ => by rw [h.wr]; exact wr_facts hp, fun p hp' => ?_, fun h' => (Nat.lt_irrefl 0 h').elim,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [τB, List.mem_singleton] at hp'
  subst hp'
  rw [h.regs.r7]; exact (region_ctx hp h.wr).symm

theorem agreeB {s₁ s₂ a b : State} (hp₁ : APre false s₁) (hp₂ : APre false s₂) (hpub : BPub s₁ s₂)
    (ha : Inv s₁ a) (hb : Inv s₂ b) : VG.Arm.Taint.Agree τB a b := by
  have hw := wr_eq hp₁ hp₂ hpub
  obtain ⟨psp, -, -, a4, a6, a7, -, -, a10, a11⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => by rw [ha.wr, hb.wr, hw], wfB hp₁ ha, wfB hp₂ hb,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => by rw [ha.sp, hb.sp, psp], fun k hk => (Nat.not_lt_zero k hk).elim⟩
  simp only [τB, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [ha.regs.r4, hb.regs.r4, tP, tP, a4]
  · rw [ha.regs.r6, hb.regs.r6, oP, oP, a6]
  · rw [ha.regs.r7, hb.regs.r7, cP, cP, a7]
  · rw [ha.regs.r10, hb.regs.r10, dP, dP, a10]
  · rw [ha.regs.r11, hb.regs.r11, a11]

/-! ## Seal -/

theorem sealBody_ct :
    RelCT isa (fun a b => APre true a ∧ APre true b ∧ BPub a b) sealBody fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp₁, hp₂, hpub⟩ e₁ e₂
  have hlen : (macData (A s₁) (Ct s₁)).length = (macData (A s₂) (Ct s₂)).length := by
    obtain ⟨-, -, -, -, -, -, -, p9, -, p11⟩ := hpub
    rw [length_macData, length_macData, length_encrypt, length_encrypt]
    simp only [VG.Proof.Poly1305.length_bytesAt, AL, L, p9, p11]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sealMain fun a b => True ∧ PreFs s₁ a ∧ PreFs s₂ b :=
    (RelCT.taint (A := taint) (τM true) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact agreeM hp₁ hp₂ hpub) (by native_taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨sealMain_ok hp₁, sealMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ PreFs s₁ a ∧ PreFs s₂ b) finalize
      fun a b => True ∧ PostFs s₁ a ∧ PostFs s₂ b :=
    (frame_ct hp₁ hp₂ hpub (O := tP) (outOk_tP hp₁) (outOk_tP hp₂) hpub.2.2.2.1.symm
      fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨finalize_seal_ok hp₁ h.2.1, finalize_seal_ok hp₂ h.2.2⟩
  have B : RelCT isa (fun a b => True ∧ PostFs s₁ a ∧ PostFs s₂ b) (.block sealEnd) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r7]) (fun a b h => VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.2.1.regs.r7, h.2.2.regs.r7, cP, cP, hpub.2.2.2.2.2.1]) (by native_taint_decide)
  exact ⟨((A.seq (F.seq B)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, trivial⟩

/-! ## Open -/

/-- Whether the message is authenticated, from the body's entry state. -/
def okB (s₀ : State) : Bool := (Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀)).isSome

theorem ok_iff (s₀ : State) :
    okB s₀ = true ↔ mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ := by
  unfold okB
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

/-- The result in two runs that agree on whether the tag is right. -/
theorem bit_eq {s₁ s₂ : State} (e : okB s₁ = okB s₂) :
    (if mac (otk s₁) (macData (A s₁) (D s₁)) = T0 s₁ then (1 : BitVec 32) else 0) =
      if mac (otk s₂) (macData (A s₂) (D s₂)) = T0 s₂ then 1 else 0 := by
  by_cases h₁ : okB s₁ = true
  · have h₂ : okB s₂ = true := e ▸ h₁
    simp only [(ok_iff s₁).mp h₁, (ok_iff s₂).mp h₂, ↓reduceIte]
  · have h₂ : ¬okB s₂ = true := e ▸ h₁
    simp only [show ¬mac (otk s₁) (macData (A s₁) (D s₁)) = T0 s₁ from fun h' => h₁ ((ok_iff s₁).mpr h'),
      show ¬mac (otk s₂) (macData (A s₂) (D s₂)) = T0 s₂ from fun h' => h₂ ((ok_iff s₂).mpr h'), ↓reduceIte]

/-- `open`'s body, for `open` and `open_to`: constant time from entry
states that agree on the registers the prologue set and on whether the tag is
right. -/
theorem openBody_ct :
    RelCT isa (fun a b => APre false a ∧ APre false b ∧ BPub a b ∧ okB a = okB b) openBody
      fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp₁, hp₂, hpub, hlk⟩ e₁ e₂
  have hlen : (macData (A s₁) (D s₁)).length = (macData (A s₂) (D s₂)).length := by
    obtain ⟨-, -, -, -, -, -, -, p9, -, p11⟩ := hpub
    rw [length_macData, length_macData]
    simp only [VG.Proof.Poly1305.length_bytesAt, AL, L, p9, p11]
  have A : RelCT isa (fun a b => a = s₁ ∧ b = s₂) openMain fun a b => True ∧ PreFo s₁ a ∧ PreFo s₂ b :=
    (RelCT.taint (A := taint) (τM false) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h; exact agreeM hp₁ hp₂ hpub) (by native_taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by obtain ⟨rfl, rfl⟩ := h; exact ⟨openMain_ok hp₁, openMain_ok hp₂⟩
  have F : RelCT isa (fun a b => True ∧ PreFo s₁ a ∧ PreFo s₂ b) finalize
      fun a b => True ∧ PostFo s₁ a ∧ PostFo s₂ b :=
    (frame_ct hp₁ hp₂ hpub (O := fun s => ptr s tagOff) (outOk_tag hp₁) (outOk_tag hp₂)
      (by simp only [ptr, cP, hpub.2.2.2.2.2.1])
      fun _ _ h => ⟨h.2.1.inv, h.2.2.inv, h.2.1.r0, h.2.1.r1, h.2.1.r12, h.2.2.r0,
      h.2.2.r1, h.2.2.r12, by rw [h.2.1.cnt, h.2.2.cnt, hlen]⟩).wp
      fun _ _ h => ⟨finalize_open_ok hp₁ h.2.1, finalize_open_ok hp₂ h.2.2⟩
  have B₁ : RelCT isa (fun a b => True ∧ PostFo s₁ a ∧ PostFo s₂ b)
      (.seq crypt (.block (Impl.ChaCha20Poly1305.Arm.compare ++ [.cmp .r0 (.imm 0)])))
      fun a b => True ∧ EB s₁ a ∧ EB s₂ b :=
    ((RelCT.taint (A := taint) τB (fun a b h => agreeB hp₁ hp₂ hpub h.2.1.inv h.2.2.inv)
      (by native_taint_decide)).wp (F₁ := PostC s₁) (F₂ := PostC s₂)
        fun a b h => ⟨cryptOpen_ok hp₁ h.2.1, cryptOpen_ok hp₂ h.2.2⟩).seq
    ((RelCT.taint (A := taint) τB (fun a b h => agreeB hp₁ hp₂ hpub h.2.1.inv h.2.2.inv)
      (by native_taint_decide)).wp fun a b h => ⟨cmp_ok hp₁ h.2.1, cmp_ok hp₂ h.2.2⟩)
  have r0 : ∀ {s₀ a : State}, EB s₀ a → isa.eval .eq a = some true → a.gpr .r0 = 0 := fun {_ a} h he => by
    have : a.z = true := Option.some.inj he
    rw [h.2.2.1] at this
    exact beq_iff_eq.mp this
  have he₂ : ∀ {a b : State}, (True ∧ EB s₁ a ∧ EB s₂ b) → isa.eval .eq a = some true →
      isa.eval .eq b = some true := fun {_ b} h he => by
    show some b.z = some true
    rw [h.2.2.2.2.1, h.2.2.2.1, ← bit_eq hlk, ← h.2.1.2.1, ← h.2.1.2.2.1]; exact he
  have Z : RelCT isa (fun a b => (True ∧ EB s₁ a ∧ EB s₂ b) ∧ isa.eval .eq a = some true) zeroData
      fun a b => Inv s₁ a ∧ Inv s₂ b :=
    ((RelCT.taint (A := taint) τB (fun a b h => agreeB hp₁ hp₂ hpub h.1.2.1.1 h.1.2.2.1)
      (by native_taint_decide)).wp (F₁ := Inv s₁) (F₂ := Inv s₂) fun a b h =>
        ⟨WP.mono (zeroData_ok hp₁ h.1.2.1.1 (r0 h.1.2.1 h.2)) fun _ h' => h'.1,
         WP.mono (zeroData_ok hp₂ h.1.2.2.1 (r0 h.1.2.2 (he₂ h.1 h.2))) fun _ h' => h'.1⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have S : RelCT isa (fun a b => (True ∧ EB s₁ a ∧ EB s₂ b) ∧ isa.eval .eq a = some false) (.block [])
      fun a b => Inv s₁ a ∧ Inv s₂ b := by
    intro _ _ _ _ _ _ h x₁ x₂
    cases x₁ with
    | block h₁ =>
      cases x₂ with
      | block h₂ =>
        simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
        rw [← h₁.1, ← h₂.1]
        exact ⟨h₁.2.symm.trans h₂.2, h.1.2.1.1, h.1.2.2.1⟩
  have B₂ : RelCT isa (fun a b => True ∧ EB s₁ a ∧ EB s₂ b) openTail fun _ _ => True :=
    (RelCT.ite (fun a b h => by
        show some (State.z a) = some (State.z b)
        rw [h.2.1.2.2.1, h.2.2.2.2.1, h.2.1.2.1, h.2.2.2.1, bit_eq hlk]) Z S).seq
      (RelCT.taint (A := taint) τB (fun a b h => agreeB hp₁ hp₂ hpub h.1 h.2) (by native_taint_decide))
  exact ⟨((A.seq (F.seq (B₁.seq B₂))) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, trivial⟩

/-! ## The prologues -/

/-- The prologue's taint: `key`, `nonce`, `aad`, `aad_len` and the `n` bytes
of stack arguments are public. -/
def τP (n : Nat) : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := n }

theorem agreeP {s₁ s₂ : State} {n : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * n ≤ 2 ^ 32)
    (h0 : s₁.gpr .r0 = s₂.gpr .r0) (h1 : s₁.gpr .r1 = s₂.gpr .r1) (h2 : s₁.gpr .r2 = s₂.gpr .r2)
    (h3 : s₁.gpr .r3 = s₂.gpr .r3) (ha : ∀ i < n, stackArg s₁ i = stackArg s₂ i)
    (hw₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨State.addr s₁.sp, 4 * n⟩ r)
    (hw₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨State.addr s₂.sp, 4 * n⟩ r) :
    VG.Arm.Taint.Agree (τP (4 * n)) s₁ s₂ := by
  have wf : ∀ s : State, s.sp.toNat + 4 * n ≤ 2 ^ 32 → (∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4 * n⟩ r) →
      VG.Arm.Taint.Wf (τP (4 * n)) s := fun s hf hw =>
    ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hf, hw⟩,
      fun _ h => (List.not_mem_nil h).elim⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf s₁ hf hw₁, wf s₂ (hsp ▸ hf) hw₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    argMem_of hsp hf ha⟩
  simp only [τP, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `seal`'s and `open`'s stack arguments are outside their writable regions. -/
theorem argWrIn {enc : Bool} {s : State} (h : preArm enc s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4 * 4⟩ r := by
  obtain ⟨-, hwr, -, -, -, -, -, c_arg, -, -, -, -, d_arg, t_arg, -⟩ := h
  have e' : State.addr s.sp = stackArgAddr s 0 := by simp [stackArgAddr]
  intro r hr
  rw [e']
  rw [hwr] at hr
  cases enc
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact d_arg.symm
    · exact c_arg.symm
  · simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr t_arg
    rcases hr with rfl | rfl | rfl
    · exact d_arg.symm
    · exact t_arg.symm
    · exact c_arg.symm

/-- `open_to`'s stack arguments are outside its writable regions. -/
theorem argWrTo {s : State} (h : preToArm s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4 * 6⟩ r := by
  obtain ⟨-, hwr, -, -, -, -, -, -, c_arg, -, -, -, -, -, d_arg, -⟩ := h
  have e' : State.addr s.sp = stackArgAddr s 0 := by simp [stackArgAddr]
  intro r hr
  rw [e']
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact d_arg.symm
  · exact c_arg.symm

/-- What two bodies' runs agree on, from what their functions' runs agree on. -/
theorem Entered.bpub {s₁ s₂ b₁ b₂ : State} {w t : Nat} (h₁ : Entered s₁ w t b₁) (h₂ : Entered s₂ w t b₂)
    (hsp : s₁.sp = s₂.sp) (h0 : s₁.gpr .r0 = s₂.gpr .r0) (h1 : s₁.gpr .r1 = s₂.gpr .r1)
    (h2 : s₁.gpr .r2 = s₂.gpr .r2) (h3 : s₁.gpr .r3 = s₂.gpr .r3) (a0 : stackArg s₁ 0 = stackArg s₂ 0)
    (a1 : stackArg s₁ 1 = stackArg s₂ 1) (aw : stackArg s₁ w = stackArg s₂ w)
    (at' : stackArg s₁ t = stackArg s₂ t) (h6 : b₁.gpr .r6 = b₂.gpr .r6) : BPub b₁ b₂ :=
  ⟨by rw [h₁.sp, h₂.sp, hsp], by rw [h₁.r0, h₂.r0, h0], by rw [h₁.r1, h₂.r1, h1], by rw [h₁.r4, h₂.r4, at'],
    h6, by rw [h₁.r7, h₂.r7, aw], by rw [h₁.r8, h₂.r8, h2], by rw [h₁.r9, h₂.r9, h3],
    by rw [h₁.r10, h₂.r10, a0], by rw [h₁.r11, h₂.r11, a1]⟩

/-- Whether the tag is right, from the function's arguments. -/
theorem Entered.ok_eq {s b : State} {w t : Nat} (he : Entered s w t b) (hp : APre false b) :
    okB b = (Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (State.addr (s.gpr .r0)) 32)
      (bytesAt s.mem (State.addr (s.gpr .r1)) 12) (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
      (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (bytesAt s.mem (State.addr (stackArg s t)) 16)).isSome := by
  obtain ⟨eK, eN, eA, eD, eT, -⟩ := he.inputs hp
  unfold okB
  rw [eK, eN, eA, eD, eT]

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub Impl.ChaCha20Poly1305.Arm.«seal» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  obtain ⟨psp, p0, p1, p2, p3, a0, a1, a2, a3⟩ := hpub
  have P : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (.block inPlace) fun a b =>
      True ∧ (Entered s₁ 3 2 a ∧ a.gpr .r6 = stackArg s₁ 0) ∧ (Entered s₂ 3 2 b ∧ b.gpr .r6 = stackArg s₂ 0) :=
    (RelCT.taint (A := taint) (τP (4 * 4)) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h
      exact agreeP psp (EntryOk.ofIn h₁).spfit p0 p1 p2 p3 (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> with_reducible assumption)
        (argWrIn h₁) (argWrIn h₂)) (by native_taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by
        obtain ⟨rfl, rfl⟩ := h; exact ⟨inPlace_ok (EntryOk.ofIn h₁), inPlace_ok (EntryOk.ofIn h₂)⟩
  refine ((P.seq (sealBody_ct.mono (fun a b h => ?_) fun _ _ h => h)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  obtain ⟨-, ⟨ha, a6⟩, ⟨hb, b6⟩⟩ := h
  exact ⟨APre.ofIn h₁ ha a6, APre.ofIn h₂ hb b6,
    ha.bpub hb psp p0 p1 p2 p3 a0 a1 a3 a2 (by rw [a6, b6, a0])⟩

theorem open_ct : ConstantTime isa openArm.pre openArm.pub Impl.ChaCha20Poly1305.Arm.«open» := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨psp, p0, p1, p2, p3, a0, a1, a2, a3⟩, hlk⟩ := hq
  have P : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (.block inPlace) fun a b =>
      True ∧ (Entered s₁ 3 2 a ∧ a.gpr .r6 = stackArg s₁ 0) ∧ (Entered s₂ 3 2 b ∧ b.gpr .r6 = stackArg s₂ 0) :=
    (RelCT.taint (A := taint) (τP (4 * 4)) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h
      exact agreeP psp (EntryOk.ofIn h₁).spfit p0 p1 p2 p3 (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> with_reducible assumption)
        (argWrIn h₁) (argWrIn h₂)) (by native_taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by
        obtain ⟨rfl, rfl⟩ := h; exact ⟨inPlace_ok (EntryOk.ofIn h₁), inPlace_ok (EntryOk.ofIn h₂)⟩
  refine ((P.seq (openBody_ct.mono (fun a b h => ?_) fun _ _ h => h)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  obtain ⟨-, ⟨ha, a6⟩, ⟨hb, b6⟩⟩ := h
  have hpa := APre.ofIn h₁ ha a6
  have hpb := APre.ofIn h₂ hb b6
  exact ⟨hpa, hpb, ha.bpub hb psp p0 p1 p2 p3 a0 a1 a3 a2 (by rw [a6, b6, a0]),
    by rw [ha.ok_eq hpa, hb.ok_eq hpb]; exact leak_bool hlk⟩

theorem openTo_ct : ConstantTime isa openToArm.pre openToArm.pub Impl.ChaCha20Poly1305.Arm.openTo := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨psp, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5⟩, hlk⟩ := hq
  have P : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (.block toEntry) fun a b =>
      True ∧ (Entered s₁ 5 4 a ∧ a.gpr .r6 = stackArg s₁ 2) ∧ (Entered s₂ 5 4 b ∧ b.gpr .r6 = stackArg s₂ 2) :=
    (RelCT.taint (A := taint) (τP (4 * 6)) (fun a b (h : a = s₁ ∧ b = s₂) => by
      obtain ⟨rfl, rfl⟩ := h
      exact agreeP psp (EntryOk.ofTo h₁).spfit p0 p1 p2 p3 (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
        (argWrTo h₁) (argWrTo h₂)) (by native_taint_decide)).wp
      fun a b (h : a = s₁ ∧ b = s₂) => by
        obtain ⟨rfl, rfl⟩ := h; exact ⟨toEntry_ok (EntryOk.ofTo h₁), toEntry_ok (EntryOk.ofTo h₂)⟩
  refine ((P.seq (openBody_ct.mono (fun a b h => ?_) fun _ _ h => h)) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  obtain ⟨-, ⟨ha, a6⟩, ⟨hb, b6⟩⟩ := h
  have hpa := APre.ofTo h₁ ha a6
  have hpb := APre.ofTo h₂ hb b6
  exact ⟨hpa, hpb, ha.bpub hb psp p0 p1 p2 p3 a0 a1 a5 a4 (by rw [a6, b6, a2]),
    by rw [ha.ok_eq hpa, hb.ok_eq hpb]; exact leak_bool hlk⟩

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
  seal_correct hs

theorem open_ok (s : State) (hs : openArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.Arm.«open» s t s' ∧ abiPreserved s s' ∧
      openArm.post s s' :=
  open_correct hs

theorem openTo_ok (s : State) (hs : openToArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.Arm.openTo s t s' ∧ abiPreserved s s' ∧
      openToArm.post s s' :=
  openTo_correct hs

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
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.«open» (openZeroScratchContract Arm.abi 79 8) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openArm,
          Proof.ChaCha20Poly1305.openLeakArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
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
          next _ e₂ => exact ⟨(e _ _).trans h.1, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openArm,
          Proof.ChaCha20Poly1305.openLeakArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openArm,
          Proof.ChaCha20Poly1305.openLeakArm, Proof.ChaCha20Poly1305.preArm,
          Proof.ChaCha20Poly1305.pubArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
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

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract Arm.abi 664).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 656 3 158 Impl.ChaCha20Poly1305.Arm.«open»)
      (Spec.ChaCha20Poly1305.openZeroContract Arm.abi 664) :=
  Arm.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 79) (post := Spec.ChaCha20Poly1305.openZeroPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.ChaCha20Poly1305.openLeak Arm.abi.ptrBits))
    (bytes := 656) (m := 3) (words := 158) open_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (pre_local _ _) (openZeroPost_local _) (openZeroPost_out _) openFrameSat_pre
    (hleak := Sig.LeakLocal.toL (openLeak_local _))

/-! ## Out of place -/

/-- A state satisfying `open_to`'s precondition (as `sealSat`, with no
source and no destination): the stack arguments at `0x5000`, `tag` at
`0x3000` the fifth. -/
def openToSat : State :=
  { sealSat with mem a := bif Nat.beq a.toNat 0x5011 then 0x30 else 0,
                 rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x5000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0, 632⟩] }

/-- The postconditions match on `decrypt`; the result is the low word of
`r1:r0`. -/
theorem openTo_verified :
    Verified Arm.target Impl.ChaCha20Poly1305.Arm.openTo (openToScratchContract Arm.abi 79 8) :=
  Verified.of_correct openTo_ok openTo_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
          Proof.ChaCha20Poly1305.openToArm, Proof.ChaCha20Poly1305.openToLeakArm,
          Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.preToArm,
          Proof.ChaCha20Poly1305.pubToArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        simp only [Proof.ChaCha20Poly1305.openToArm, Proof.ChaCha20Poly1305.openToRes, Arm.State.addr] at h
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
          next _ e₂ => exact ⟨(e _ _).trans h.1, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
          Proof.ChaCha20Poly1305.openToArm, Proof.ChaCha20Poly1305.openToLeakArm,
          Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.preToArm,
          Proof.ChaCha20Poly1305.pubToArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
          Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
          Proof.ChaCha20Poly1305.openToArm, Proof.ChaCha20Poly1305.openToLeakArm,
          Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.preToArm,
          Proof.ChaCha20Poly1305.pubToArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [Proof.ChaCha20Poly1305.Arm.openToSat, Proof.ChaCha20Poly1305.Arm.sealSat, Arm.stackArg,
            Arm.stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax]
          using Proof.ChaCha20Poly1305.Arm.openToSat }

/-- A state satisfying `open_to`'s precondition, without the working space. -/
def openToFrameSat : State :=
  { openToSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x5000, 20⟩],
                   wr := [⟨0, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract Arm.abi 672).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openToFrameSat, openToSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read,
      Spec.ChaCha20Poly1305.pMax]
    using openToFrameSat

theorem openTo_framed :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped 664 5 158 Impl.ChaCha20Poly1305.Arm.openTo)
      (Spec.ChaCha20Poly1305.openToContract Arm.abi 672) :=
  Arm.Verified.stackScratchWipedPre (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 79) (pre := Spec.ChaCha20Poly1305.openToPre Arm.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.ChaCha20Poly1305.openToLeak Arm.abi.ptrBits))
    (bytes := 664) (m := 5) (words := 158) openTo_verified (by decide) (by decide) (by decide)
    (by decide) (by decide) (openToPre_local _) (openToPost_local _) (openToPost_out _) openToFrameSat_pre
    (hleak := Sig.LeakLocal.toL (openToLeak_local _))

end VG.Proof.ChaCha20Poly1305.Arm
