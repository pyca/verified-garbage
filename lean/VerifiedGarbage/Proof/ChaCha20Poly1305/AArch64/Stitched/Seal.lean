module

import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Wide
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.AddS
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `seal`

With the one-time key from the scalar block function (`sealStitchedMain`,
`entry_zero`), or, for the lengths `route` picks, with the first 256 bytes'
keystream from `Short.lean`'s prologue, which encrypts them before they are absorbed
(`Wide.lean`), the stitched code continues (`Entry`): the chunks encrypt the data's whole
chunks and absorb all but the last of them (and, if a rest remains, also the
last while the next 256 bytes' keystream is computed, of which up to the
rest's length is used: `Tail.rest`); whatever is left is encrypted by
`vg_chacha20_xor`, and absorbed with what was not.
-/

@[expose] public section

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
theorem sealed_inv {s₀ : State} (hp : APre e s₀) {s w u : State} {key msg : List Byte} {P A : Nat}
    (hc : Sealed s₀ s w key msg P A u) {s' : State} (hk : Kept [sub s₀ 64 384, dR s₀] u s') :
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
  refine WP.seq (WP.mono (counterOne_ok hp i₃) fun s₃' ⟨m₃', k₃', v₃'⟩ => ?_)
  have D₃' : bytesAt s₃'.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃'.frame (by rdisj_all) hL', D₃]
  refine WP.seq ((Tail.cryptStitchedSeal_ok v.callee.sve hp (entry_zero true i₃ st₃ R₃ m₃' k₃')).mono
    fun s₄ ⟨P, A, hc⟩ => ?_)
  refine WP.seq (rest_call v hp hc.le hc.p64 hc.x0 hc.x1 hc.x2 hc.x3 hc.inv.wr hc.cnt hc.data
    |>.mono fun s₅ ⟨v₅, k₅, f₅, ct₅⟩ => ?_)
  rw [D₃'] at ct₅
  have i₅ := sealed_inv hp hc k₅
  have hpre := hc.aP
  have hle := hc.le
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := A) (by omega)) i₅.x21 i₅.rd i₅.wr
    (by rw [k₅.cs _ (pres .x22) (pres30 .x22), hc.x22])
    (by rw [k₅.cs _ (pres .x23) (pres30 .x23), hc.x23])) (by lit_decide)) fun s₆ ⟨⟨k₆, r₆⟩, v₆⟩ => ?_)
  have i₆ := mac_inv0 i₅ k₆
  refine WP.mono (WP.preservedV (absorbLengths_ok0 hp i₆) (by lit_decide)) fun s₇ ⟨⟨i₇, k₇, r₇⟩, v₇⟩ => ?_
  -- The message absorbed.
  have R₄ := hc.mac
  have X₄ : bytesAt s₄.mem (dp s₀) A = bytesAt s₅.mem (dp s₀) A :=
    (prefix_rest hp f₅ hpre hle).symm
  rw [X₄] at R₄
  have R₆ := r₆ _ _ (Repr.frame k₅.frame (by rdisj_all) R₄)
  rw [List.append_assoc, split_pad hc.a16 (by omega), ct₅] at R₆
  have R₇ := r₇ _ _ R₆
  have L₆ : bytesAt s₆.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₃'.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₆, hA] at R₇
  refine ⟨i₇, fun r hr => (v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans ((hc.vec r hr).trans ((v₃' r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · refine (congrArg (Repr s₇.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₇
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', bytesAt_frame k₆.frame (by rdisj_all) hL', ct₅]

/-- The data's first 256 bytes are outside a part of the context. -/
theorem first_ctx {s₀ : State} (hp : APre e s₀) (hL : 256 ≤ L s₀) {k n : Nat} (h : k + n ≤ 1280) :
    (⟨dp s₀, 256⟩ : Region).Disjoint (sub s₀ k n) :=
  (data_ctx hp h).sub_left (Region.sub_prefix hL)

theorem sealWideMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hL : 512 ≤ L s₀) :
    WP isa (sealWideMain v.callee) s₀ (MainS s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  have hL256 : 256 ≤ L s₀ := by omega
  unfold sealWideMain
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
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₃) (by lit_decide))
    fun s₄ ⟨⟨i₄, k₄, len₄⟩, v₄⟩ => ?_)
  have K₄ : ∀ i < 256, s₄.mem (Short.kp' s₀ + BitVec.ofNat 64 i) = Short.ks5 s₀ (64 + i) :=
    fun i hi => by
      rw [Short.ks_frame k₄.frame (by rdisj_all) hi, Short.ks_frame k₃.frame (by rdisj_all) hi,
        Short.ks_frame k₂.frame (by rdisj_all) hi]
      exact Short.ks_post h₁.ks hi
  have D₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₄.frame (by rdisj_all) hL', bytesAt_frame k₃.frame (by rdisj_all) hL',
      bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  have R₄ : Repr s₄.mem (off (cx s₀) 448) (otk s₀) (A s₀ ++ pad16 (A s₀)) := by
    have := Repr.frame k₄.frame (by rdisj_all) (r₃ _ _ (Repr.frame k₂.frame (by rdisj_all) h₁.poly))
    rwa [List.nil_append, hA] at this
  refine WP.seq (WP.mono (WP.preservedV (ShortRest.first_ok hp i₄ hL256) (by lit_decide))
    fun s₅ ⟨⟨i₅, k₅, x₅, f₅⟩, v₅⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (absorbFirst_ok hp i₅ hL256) (by lit_decide))
    fun s₆ ⟨⟨i₆, k₆, r₆⟩, v₆⟩ => ?_)
  refine WP.seq (WP.mono (skipFirst_ok i₆ hL256) fun s₇ ⟨i₇, x22₇, x23₇, m₇, v₇⟩ => ?_)
  have f₆ : ∀ r ∈ macR s₀, (⟨dp s₀, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact first_ctx hp hL256 (by lit_omega)
  have E : Entry true 256 s₀ s₄ (otk s₀) (A s₀ ++ pad16 (A s₀)) s₇ := by
    refine ⟨i₇, by decide, hL256, x22₇, x23₇, ?_, fun k hk => ?_, ?_, fun r hr => ?_⟩
    · rw [m₇, stateAt_frame k₆.frame (by rdisj_all), stateAt_frame k₅.frame (by rdisj_all),
        stateAt_frame k₄.frame (by rdisj_all), stateAt_frame k₃.frame (by rdisj_all), st₂,
        VG.Proof.ChaCha20Poly1305.ctr_initState,
        show (1 : BitVec 32) + BitVec.ofNat 32 (256 / 64) = 5 by decide]
    · rw [m₇, data_frame k₆.frame (by rdisj_all) hk]
      by_cases h : k < 256
      · rw [x₅ k h, K₄ k h, Short.ks5_eq s₀ hk, ite_eq_left h]
      · rw [f₅ _ (ShortRest.rest_out hp (by omega) hk), ite_eq_right h]
    · simp only [ite_true]
      rw [m₇, bytesAt_frame k₆.frame f₆ (by omega)]
      exact r₆ _ _ (Repr.frame k₅.frame (by rdisj_all) R₄)
    · exact (v₇ r hr).trans ((v₆ r hr).trans (v₅ r hr))
  refine WP.seq ((Tail.cryptStitchedSeal_ok v.callee.sve hp E).mono fun s₈ ⟨P, A', hc⟩ => ?_)
  refine WP.seq (rest_call v hp hc.le hc.p64 hc.x0 hc.x1 hc.x2 hc.x3 hc.inv.wr hc.cnt hc.data
    |>.mono fun s₉ ⟨v₉, k₉, f₉, ct₉⟩ => ?_)
  rw [D₄] at ct₉
  have i₉ := sealed_inv hp hc k₉
  have hpre := hc.aP
  have hle := hc.le
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := A') (by omega)) i₉.x21 i₉.rd i₉.wr
    (by rw [k₉.cs _ (pres .x22) (pres30 .x22), hc.x22])
    (by rw [k₉.cs _ (pres .x23) (pres30 .x23), hc.x23])) (by lit_decide)) fun s₁₀ ⟨⟨k₁₀, r₁₀⟩, v₁₀⟩ => ?_)
  have i₁₀ := mac_inv0 i₉ k₁₀
  refine WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₀) (by lit_decide))
    fun s₁₁ ⟨⟨i₁₁, k₁₁, r₁₁⟩, v₁₁⟩ => ?_
  -- The message absorbed.
  have R₈ := hc.mac
  have X₈ : bytesAt s₈.mem (dp s₀) A' = bytesAt s₉.mem (dp s₀) A' :=
    (prefix_rest hp f₉ hpre hle).symm
  rw [X₈] at R₈
  have R₁₀ := r₁₀ _ _ (Repr.frame k₉.frame (by rdisj_all) R₈)
  rw [List.append_assoc, split_pad hc.a16 (by omega), ct₉] at R₁₀
  have R₁₁ := r₁₁ _ _ R₁₀
  have L₁₀ : bytesAt s₁₀.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₁₀.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₉.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), m₇,
      bytesAt_frame k₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega), len₄]
  have hA₄ : A s₀ = bytesAt s₄.mem (ad s₀) (AL s₀) := by
    rw [bytesAt_frame k₄.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame k₃.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt), hA]
  rw [L₁₀] at R₁₁
  refine ⟨i₁₁, fun r hr => (v₁₁ r hr).trans ((v₁₀ r hr).trans ((v₉ r hr).trans ((hc.vec r hr).trans
      ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · refine (congrArg (Repr s₁₁.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₁₁
    simp only [macData, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₁₁.frame (by rdisj_all) hL', bytesAt_frame k₁₀.frame (by rdisj_all) hL', ct₉]

theorem sealStitched_correct (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealStitched v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sealAArch64.post s₀ s' :=
  WP.seq (WP.mono (sealStitchedMain_ok v hp) fun _ h => sealTail_ok hp h)

end VG.Proof.ChaCha20Poly1305.AArch64
