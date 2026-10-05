import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal`. -/
section

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
  have i₅ := VG.Proof.ChaCha20Poly1305.AArch64.crypted_inv hp hc k₅
  have hpre := pre_le true T
  have hle := hc.le
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (VG.Proof.ChaCha20Poly1305.AArch64.srcAt hp (p := pre true T) (by omega)) i₅.x21 i₅.rd i₅.wr
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
  rw [List.append_assoc, VG.Proof.ChaCha20Poly1305.AArch64.split_pad (pre_mod true T) (by omega), ct₅] at R₆
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
  WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.AArch64.sealStitchedMain_ok v hp) fun _ h => sealTail_ok hp h)

end VG.Proof.ChaCha20Poly1305.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open`. -/
section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `open`

The chunks decrypt the data's whole chunks and absorb them as they were;
the rest is absorbed, then decrypted by `vg_chacha20_xor`.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data after the chunks is as it was. -/
theorem rest_orig {s₀ s u : State} {key msg : List Byte} {T : Nat}
    (hc : Crypted false s₀ s key msg T u) :
    bytesAt u.mem (dp s₀ + BitVec.ofNat 64 (pre false T)) (L s₀ - pre false T) =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (pre false T)) (L s₀ - pre false T) := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have e : dp s₀ + BitVec.ofNat 64 (pre false T) + BitVec.ofNat 64 i =
      dp s₀ + BitVec.ofNat 64 (512 * T + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl
  have hle := hc.le
  have hi' : i < L s₀ - 512 * T := hi
  rw [e, hc.data _ (by omega), ite_eq_right (by omega)]

theorem openStitchedMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openStitchedMain v.callee) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold openStitchedMain cryptRest
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
  refine WP.seq ((cryptStitched_ok false hp i₃ st₃ R₃).mono fun s₄ ⟨T, hc⟩ => ?_)
  have hle := hc.le
  have hpre : pre false T = 512 * T := rfl
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (VG.Proof.ChaCha20Poly1305.AArch64.srcAt hp (p := pre false T) (by omega)) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x22 hc.x23) (by lit_decide))
    fun s₅ ⟨⟨k₅, r₅⟩, v₅⟩ => ?_)
  have i₅ := mac_inv0 hc.inv k₅
  have hd₅ : ∀ r ∈ macR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine WP.seq (WP.seq ((restArgs_ok i₅.x21).mono fun w ⟨⟨a0, a1, a2, a3, kw⟩, vw⟩ => ?_))
  have mw := kw.mem_eq
  refine (rest_call v hp (s := s₃) hle a0
    (by rw [a1, k₅.cs _ (pres .x22) (pres30 .x22), hc.x22, hpre])
    (by rw [a2, k₅.cs _ (pres .x23) (pres30 .x23), hc.x23, hpre]) a3 (by rw [kw.wr, i₅.wr])
    (by rw [mw, stateAt_frame k₅.frame (by rdisj_all), hc.cnt])
    (fun k hk => by rw [mw, data_frame k₅.frame hd₅ hk, hc.data k hk])).mono
    fun s₆ ⟨v₆, k₆, _, pt₆⟩ => ?_
  rw [D₃] at pt₆
  have k₅₆ : Kept [sub s₀ 64 384, dR s₀] s₅ s₆ :=
    (kw.sub fun _ hr => absurd hr List.not_mem_nil).trans k₆
  have i₆ : Inv0 s₀ s₆ := i₅.step k₅₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₆) (by lit_decide)) fun s₇ ⟨⟨i₇, k₇, r₇⟩, v₇⟩ => ?_)
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₇ (out := 48) (by omega)) (by lit_decide))
    fun s₈ ⟨⟨k₈, tag₈⟩, v₈⟩ => ?_
  -- The tag computed.
  have R₄ := hc.mac
  simp only [Bool.false_eq_true, ↓reduceIte] at R₄
  have R₅ := r₅ _ _ R₄
  rw [VG.Proof.ChaCha20Poly1305.AArch64.rest_orig hc, List.append_assoc, VG.Proof.ChaCha20Poly1305.AArch64.split_pad (pre_mod false T) (by omega), D₃] at R₅
  have T₈ := tag₈ _ _ (r₇ _ _ (Repr.frame k₅₆.frame (by rdisj_all) R₅))
  have L₆ : bytesAt s₆.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₅₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₆, hA] at T₈
  refine ⟨i₇.step k₈ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₈ r hr).trans ((v₇ r hr).trans
      ((v₆ r hr).trans ((vw r hr).trans ((v₅ r hr).trans ((hc.vec r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₈]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₈.frame (by rdisj_all) hL', bytesAt_frame k₇.frame (by rdisj_all) hL', pt₆]

theorem openStitched_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openStitched v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.AArch64.openStitchedMain_ok v hp) fun _ h => openTail_ok hp h)

end VG.Proof.ChaCha20Poly1305.AArch64

end
