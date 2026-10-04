import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `seal`

The chunks encrypt the data's whole chunks and absorb all but the last of
them; the rest is encrypted by `vg_chacha20_xor`, and absorbed with the last
chunk.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data from `p`. -/
theorem srcAt {s₀ : State} (hp : APre e s₀) {p : Nat} (hle : p ≤ L s₀) :
    Src s₀ (dp s₀ + BitVec.ofNat 64 p) (L s₀ - p) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  refine ⟨by omega, ?_, hp.c_d.sub_right (Offset.sub_base _ (by omega)),
    (srcD hp).cov_sub (a := p) (n := L s₀ - p) (by omega) rfl rfl⟩
  have := hp.wrap_d
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The data absorbed in two parts, at a multiple of 16 bytes, padded. -/
theorem split_pad {m : Mem} {p : Addr} {a n : Nat} (ha : a % 16 = 0) (hn : a ≤ n) :
    bytesAt m p a ++ (bytesAt m (p + BitVec.ofNat 64 a) (n - a) ++
      pad16 (bytesAt m (p + BitVec.ofNat 64 a) (n - a))) = bytesAt m p n ++ pad16 (bytesAt m p n) := by
  have hp : pad16 (bytesAt m (p + BitVec.ofNat 64 a) (n - a)) = pad16 (bytesAt m p n) := by
    simp only [pad16, VG.Proof.Poly1305.length_bytesAt]
    rw [show (n - a) % 16 = n % 16 by omega]
  rw [hp, ← List.append_assoc, ← VG.Proof.Poly1305.bytesAt_add, Nat.add_sub_cancel' hn]

/-- The Poly1305 state after the chunks, from that before, through `rs`. -/
theorem crypted_inv {enc : Bool} {s₀ : State} (hp : APre e s₀) {s u : State} {key msg : List Byte} {T : Nat}
    (hc : Crypted enc s₀ s key msg T u) {s' : State} (hk : Kept [sub s₀ 64 384, dR s₀] u s') :
    Inv0 s₀ s' :=
  hc.inv.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))

theorem sealStitchedMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealStitchedMain v.callee) s₀ (MainS s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold sealStitchedMain
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
  refine WP.seq ((cryptStitched_ok true hp i₃ st₃ R₃).mono fun s₄ ⟨T, hc⟩ => ?_)
  refine WP.seq (rest_call v hp hc.le hc.x0 hc.x1 hc.x2 hc.x3 hc.inv.wr hc.cnt hc.data
    |>.mono fun s₅ ⟨v₅, k₅, f₅, ct₅⟩ => ?_)
  rw [D₃] at ct₅
  have i₅ := crypted_inv hp hc k₅
  have hpre := pre_le true T
  have hle := hc.le
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := pre true T) (by omega)) i₅.x21 i₅.rd i₅.wr
    (by rw [k₅.cs _ (pres .x22) (pres30 .x22), hc.x22])
    (by rw [k₅.cs _ (pres .x23) (pres30 .x23), hc.x23])) (by lit_decide)) fun s₆ ⟨⟨k₆, r₆⟩, v₆⟩ => ?_)
  have i₆ := mac_inv0 i₅ k₆
  refine WP.mono (WP.preservedV (absorbLengths_ok0 hp i₆) (by lit_decide)) fun s₇ ⟨⟨i₇, k₇, r₇⟩, v₇⟩ => ?_
  -- The message absorbed.
  have R₄ := hc.mac
  simp only [↓reduceIte] at R₄
  have X₄ : bytesAt s₄.mem (dp s₀) (pre true T) = bytesAt s₅.mem (dp s₀) (pre true T) :=
    (prefix_rest hp f₅ hpre hle).symm
  rw [X₄] at R₄
  have R₆ := r₆ _ _ (Repr.frame k₅.frame (by rdisj_all) R₄)
  rw [List.append_assoc, split_pad (pre_mod true T) (by omega), ct₅] at R₆
  have R₇ := r₇ _ _ R₆
  have L₆ : bytesAt s₆.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₆, hA] at R₇
  refine ⟨i₇, fun r hr => (v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans ((hc.vec r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))), ?_, ?_⟩
  · refine (congrArg (Repr s₇.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₇
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', bytesAt_frame k₆.frame (by rdisj_all) hL', ct₅]

theorem sealStitched_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealStitched v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sealAArch64.post s₀ s' :=
  WP.seq (WP.mono (sealStitchedMain_ok v hp) fun _ h => sealTail_ok hp h)

end VG.Proof.ChaCha20Poly1305.AArch64
