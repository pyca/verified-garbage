module
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.PadRest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Wide
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Rest

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `open`

With the one-time key from the scalar block function (`openStitchedMain`,
`entry_zero`), or, for the lengths `route` picks, with the first 256 bytes'
keystream from `Short.lean`'s prologue, which decrypts them after they are absorbed
(`Wide.lean`), the stitched code continues (`Entry`): the chunks decrypt the data's whole
chunks and absorb them as they were; the rest is absorbed, then decrypted
(`openRest`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data after the chunks is as it was. -/
theorem rest_orig {s₀ s w u : State} {key msg : List Byte} {o T : Nat}
    (hc : Crypted false o s₀ s w key msg T u) :
    bytesAt u.mem (dp s₀ + BitVec.ofNat 64 (pre o false T)) (L s₀ - pre o false T) =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (pre o false T)) (L s₀ - pre o false T) := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have e : dp s₀ + BitVec.ofNat 64 (pre o false T) + BitVec.ofNat 64 i =
      dp s₀ + BitVec.ofNat 64 (o + 512 * T + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  have hle := hc.le
  have hi' : i < L s₀ - (o + 512 * T) := hi
  rw [e, hc.data _ (by omega), ite_eq_right (by omega)]

theorem openStitchedMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openStitchedMain v.callee) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold openStitchedMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  refine WP.seq (WP.mono (counterOne_ok hp i₃) fun s₃' ⟨m₃', k₃', v₃'⟩ => ?_)
  have D₃' : bytesAt s₃'.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃'.frame (by rdisj_all) hL', D₃]
  refine WP.seq ((cryptStitched_ok false rfl hp (entry_zero false i₃ st₃ R₃ m₃' k₃')).mono
    fun s₄ ⟨T, hc⟩ => ?_)
  have hle := hc.le
  have hpre : pre 0 false T = 512 * T := by simp [pre]
  -- The rest: stitched from 65 to 256 bytes (`TailO.rest`), otherwise absorbed and then
  -- decrypted (`openRest`).
  have hr512 := hc.lt
  refine WP.seq ((TailO.test_ok s₄ (r := L s₀ - 512 * T) (by omega)
    (by rw [hc.x23, hpre])).mono fun s₄' ⟨e₄, k₄', g₄', v₄'⟩ => ?_)
  have hc' := TailO.Crypted.keep hc k₄' g₄' v₄'
  have hm₄ : s₄'.mem = s₄.mem := by funext x; exact k₄'.frame x fun r hr => by simp at hr
  refine WP.seq (WP.mono (Q := fun (s₆ : State) =>
    (∀ r ∈ preservedV, (s₆.v r).extractLsb' 0 64 = (s₄.v r).extractLsb' 0 64) ∧ Inv0 s₀ s₆ ∧
    Frame [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, sub s₀ 768 512, dR s₀] s₄.mem s₆.mem ∧
    Repr s₆.mem (off (cx s₀) 448) (otk s₀) (([] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀))) ++
      bytesAt s₃'.mem (dp s₀) (512 * T)) ++
      (bytesAt s₃'.mem (dp s₀ + BitVec.ofNat 64 (512 * T)) (L s₀ - 512 * T) ++
        pad16 (bytesAt s₃'.mem (dp s₀ + BitVec.ofNat 64 (512 * T)) (L s₀ - 512 * T)))) ∧
    bytesAt s₆.mem (dp s₀) (L s₀) =
      Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s₃'.mem (dp s₀) (L s₀))) ?_ ?_)
  · refine WP.ite (decide (65 ≤ L s₀ - 512 * T ∧ L s₀ - 512 * T ≤ 256)) e₄ (fun h => ?_) (fun h => ?_)
    · have h' := of_decide_eq_true h
      refine (TailO.rest_ok v.callee.sve hp hc' (by decide) (by simp only [Nat.zero_add]; omega)
        (by simp only [Nat.zero_add]; omega)).mono fun s₆ ⟨v₆, i₆, f₆, r₆, pt₆⟩ => ?_
      simp only [Nat.zero_add] at f₆ r₆ pt₆ v₆
      refine ⟨fun r hr => (v₆ r hr).trans (v₄' r hr), i₆, ?_, r₆, pt₆⟩
      rw [← hm₄]
      exact f₆.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
        (srcAt hp (p := pre 0 false T) (by rw [hpre]; omega)) hc'.inv.x21 hc'.inv.rd hc'.inv.wr hc'.x22
        hc'.x23) (by lit_decide))
        fun s₅ ⟨⟨k₅, r₅⟩, v₅⟩ => ?_)
      have i₅ := mac_inv0 hc'.inv k₅
      have hd₅ : ∀ r ∈ macR s₀, (dR s₀).Disjoint r := by
        intro r hr; simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
      refine (openRest_ok v hp (s := s₃') (P := 512 * T) (by omega) (by omega) (fun _ => by omega)
        i₅.x21 (by rw [k₅.cs _ (pres .x22) (pres30 .x22), hc'.x22, hpre])
        (by rw [k₅.cs _ (pres .x23) (pres30 .x23), hc'.x23, hpre]) i₅.rd i₅.wr
        (fun _ => by rw [stateAt_frame k₅.frame (by rdisj_all), hc'.cnt,
          show 512 * T / 64 = 0 / 64 + 8 * T by omega])
        (fun k hk => by rw [data_frame k₅.frame hd₅ hk, hc'.data k hk, Nat.zero_add])).mono
        fun s₆ ⟨v₆, k₅₆, _, pt₆⟩ => ?_
      have i₆ : Inv0 s₀ s₆ := i₅.step k₅₆ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
          · exact ⟨dR s₀, by simp, fun _ h => h⟩
          · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
      have R₄ := hc'.mac
      simp only [Bool.false_eq_true, ↓reduceIte] at R₄
      have R₅ := r₅ _ _ R₄
      rw [rest_orig hc', hpre] at R₅
      refine ⟨fun r hr => (v₆ r hr).trans ((v₅ r hr).trans (v₄' r hr)), i₆, ?_,
        Repr.frame k₅₆.frame (by rdisj_all) R₅, pt₆⟩
      rw [← hm₄]
      refine (k₅.frame.sub fun r hr => ?_).trans (k₅₆.frame.sub fun r hr => ?_)
      · simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
        · exact ⟨sub s₀ 16 16, by simp, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
        · exact ⟨dR s₀, by simp, fun _ h => h⟩
        · exact ⟨sub s₀ 768 512, by simp, fun _ h => h⟩
  rintro s₆ ⟨v₆, i₆, f₆, R₆, pt₆⟩
  rw [D₃'] at pt₆
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₆) (by lit_decide)) fun s₇ ⟨⟨i₇, k₇, r₇⟩, v₇⟩ => ?_)
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₇ (out := 48) (by omega)) (by lit_decide))
    fun s₈ ⟨⟨k₈, tag₈⟩, v₈⟩ => ?_
  -- The tag computed.
  have R₅ := R₆
  rw [← hpre, List.append_assoc, split_pad (pre_mod (by decide) false T) (by rw [hpre]; omega), D₃'] at R₅
  have T₈ := tag₈ _ _ (r₇ _ _ R₅)
  have L₆ : bytesAt s₆.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₆ (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₃'.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₆, hA] at T₈
  refine ⟨i₇.step k₈ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₈ r hr).trans ((v₇ r hr).trans
      ((v₆ r hr).trans ((hc.vec r hr).trans ((v₃' r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₈]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₈.frame (by rdisj_all) hL', bytesAt_frame k₇.frame (by rdisj_all) hL', pt₆]

theorem openWideMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hL : 512 ≤ L s₀) :
    WP isa (openWideMain v.callee) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  have hL256 : 256 ≤ L s₀ := by omega
  unfold openWideMain
  refine WP.seq (WP.mono (WP.preservedV (Short.prologue_ok hp) (Short.prologue_keepsV v.callee.sve))
    fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (ShortRest.stash_ok hp h₁.inv h₁.st0) (by lit_decide))
    fun s₂ ⟨⟨i₂, k₂, st₂⟩, v₂⟩ => ?_)
  have hA : bytesAt s₂.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)]
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) i₂.x21 i₂.rd i₂.wr i₂.x24 (by rw [i₂.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₃ ⟨⟨k₃, r₃⟩, v₃⟩ => ?_)
  have i₃ := mac_inv i₂ k₃
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have R₃ : Repr s₃.mem (off (cx s₀) 448) (otk s₀) (A s₀ ++ pad16 (A s₀)) := by
    have := r₃ _ _ (Repr.frame k₂.frame (by rdisj_all) h₁.poly)
    rwa [List.nil_append, hA] at this
  refine WP.seq (WP.mono (WP.preservedV (absorbFirst_ok hp i₃ hL256) (by lit_decide))
    fun s₄ ⟨⟨i₄, k₄, r₄⟩, v₄⟩ => ?_)
  have K₄ : ∀ i < 256, s₄.mem (Short.kp' s₀ + BitVec.ofNat 64 i) = Short.ks5 s₀ (64 + i) :=
    fun i hi => by
      rw [Short.ks_frame k₄.frame (by rdisj_all) hi, Short.ks_frame k₃.frame (by rdisj_all) hi,
        Short.ks_frame k₂.frame (by rdisj_all) hi]
      exact Short.ks_post h₁.ks hi
  refine WP.seq (WP.mono (WP.preservedV (ShortRest.first_ok hp i₄ hL256) (by lit_decide))
    fun s₅ ⟨⟨i₅, k₅, x₅, f₅⟩, v₅⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₅) (by lit_decide))
    fun s₆ ⟨⟨i₆, k₆, len₆⟩, v₆⟩ => ?_)
  refine WP.seq (WP.mono (skipFirst_ok i₆ hL256) fun s₇ ⟨i₇, x22₇, x23₇, m₇, v₇⟩ => ?_)
  have E : Entry false 256 s₀ s₃ (otk s₀) (A s₀ ++ pad16 (A s₀)) s₇ := by
    refine ⟨i₇, by decide, hL256, x22₇, x23₇, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩
    · rw [m₇, stateAt_frame k₆.frame (by rdisj_all), stateAt_frame k₅.frame (by rdisj_all),
        stateAt_frame k₄.frame (by rdisj_all), stateAt_frame k₃.frame (by rdisj_all), st₂,
        VG.Proof.ChaCha20Poly1305.ctr_initState,
        show (1 : BitVec 32) + BitVec.ofNat 32 (256 / 64) = 5 by decide]
    · rw [m₇, data_frame k₆.frame (by rdisj_all) hk]
      by_cases h : k < 256
      · rw [x₅ k h, K₄ k h, Short.ks5_eq s₀ hk, data_frame k₄.frame (by rdisj_all) hk, ite_eq_left h]
      · rw [f₅ _ (ShortRest.rest_out hp (by omega) hk), data_frame k₄.frame (by rdisj_all) hk,
          ite_eq_right h]
    · simp only [Bool.false_eq_true, ite_false]
      rw [m₇]
      exact Repr.frame k₆.frame (by rdisj_all) (Repr.frame k₅.frame (by rdisj_all) (r₄ _ _ R₃))
    · exact (v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans (v₄ r hr)))
  refine WP.seq ((cryptStitched_ok false rfl hp E).mono fun s₈ ⟨T, hc⟩ => ?_)
  have hle := hc.le
  have hpre : pre 256 false T = 256 + 512 * T := rfl
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := pre 256 false T) (by rw [hpre]; omega)) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x22 hc.x23)
    (by lit_decide)) fun s₉ ⟨⟨k₉, r₉⟩, v₉⟩ => ?_)
  have i₉ := mac_inv0 hc.inv k₉
  have hd₉ : ∀ r ∈ macR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine WP.seq ((openRest_ok v hp (s := s₃) (P := 256 + 512 * T) hle hc.lt (fun _ => by omega) i₉.x21
    (by rw [k₉.cs _ (pres .x22) (pres30 .x22), hc.x22, hpre])
    (by rw [k₉.cs _ (pres .x23) (pres30 .x23), hc.x23, hpre]) i₉.rd i₉.wr
    (fun _ => by rw [stateAt_frame k₉.frame (by rdisj_all), hc.cnt,
      show (256 + 512 * T) / 64 = 256 / 64 + 8 * T by omega])
    (fun k hk => by rw [data_frame k₉.frame hd₉ hk, hc.data k hk])).mono
    fun s₁₀ ⟨v₁₀, k₉₁₀, _, pt₁₀⟩ => ?_)
  rw [D₃] at pt₁₀
  have i₁₀ : Inv0 s₀ s₁₀ := i₉.step k₉₁₀ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₀) (by lit_decide))
    fun s₁₁ ⟨⟨i₁₁, k₁₁, r₁₁⟩, v₁₁⟩ => ?_)
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₁₁ (out := 48) (by omega)) (by lit_decide))
    fun s₁₂ ⟨⟨k₁₂, tag₁₂⟩, v₁₂⟩ => ?_
  -- The tag computed.
  have R₈ := hc.mac
  simp only [Bool.false_eq_true, ↓reduceIte] at R₈
  have R₉ := r₉ _ _ R₈
  rw [rest_orig hc, List.append_assoc, split_pad (pre_mod (by decide) false T) (by omega), D₃] at R₉
  have T₁₂ := tag₁₂ _ _ (r₁₁ _ _ (Repr.frame k₉₁₀.frame (by rdisj_all) R₉))
  have L₁₀ : bytesAt s₁₀.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₉₁₀.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₉.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), m₇, len₆]
  rw [L₁₀] at T₁₂
  refine ⟨i₁₁.step k₁₂ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₁₂ r hr).trans ((v₁₁ r hr).trans
      ((v₁₀ r hr).trans ((v₉ r hr).trans ((hc.vec r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₁₂]
    simp only [macData, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₁₂.frame (by rdisj_all) hL', bytesAt_frame k₁₁.frame (by rdisj_all) hL', pt₁₀]

theorem openStitched_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openStitched v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' :=
  WP.seq (WP.mono (openStitchedMain_ok v hp) fun _ h => openTail_ok hp h)

end VG.Proof.ChaCha20Poly1305.AArch64
