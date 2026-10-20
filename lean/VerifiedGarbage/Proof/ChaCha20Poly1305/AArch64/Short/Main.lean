module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Prologue
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
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
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Offset
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
# ChaCha20-Poly1305 on AArch64, 64 to 256 bytes: `seal` and `open` up to the tag

The parts of `Short.sealMain` and `Short.openMain`, which leave what
`MainS` and `MainO` say, as the other forms of the code do.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Short

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Short
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream serialize block initState)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data's keystream from the five blocks: counters 1 to 4. -/
theorem ks5_eq (s₀ : State) {i n : Nat} (hi : i < n) :
    ks5 s₀ (64 + i) = (keystream (initState (K s₀) 1 (N s₀)) n).getD i 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ hi, ks5, show (64 + i) / 64 = i / 64 + 1 by omega,
    show (64 + i) % 64 = i % 64 by omega, ctr_initState, ctr_initState]
  congr 4
  rw [BitVec.ofNat_add, BitVec.add_comm]
  exact (BitVec.add_zero _).trans (BitVec.add_comm _ _)

/-- The data XORed with its keystream is the data encrypted from counter 1. -/
theorem ct_eq {s₀ : State} {m₃ m₄ : Mem} (hD : bytesAt m₃ (dp s₀) (L s₀) = D s₀)
    (hk : ∀ i < L s₀, m₃ (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i))
    (hx : ∀ i < L s₀, m₄ (dp s₀ + BitVec.ofNat 64 i) = m₃ (dp s₀ + BitVec.ofNat 64 i) ^^^
      m₃ (kp' s₀ + BitVec.ofNat 64 i)) :
    bytesAt m₄ (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  rw [encrypt_eq]
  apply List.ext_getElem
  · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
  · intro i h₁ h₂
    simp only [VG.Proof.Poly1305.length_bytesAt] at h₁
    have hD' := congrArg (·[i]?) hD
    simp only [bytesAt, List.getElem?_map, List.getElem?_range h₁, Option.map_some] at hD'
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith, hx i h₁, hk i h₁,
      ks5_eq s₀ (n := (D s₀).length) (by rw [VG.Proof.Poly1305.length_bytesAt]; exact h₁)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_keystream]; simpa using h₁), Option.getD_some]
    congr 1
    simpa using Option.some_inj.mp hD'

/-- The keystream at `ctx + 128` survives the parts that write the Poly1305
state, the padded block and the lengths block. -/
theorem ks_frame {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 128 256).Disjoint r) {i : Nat} (hi : i < 256) :
    m' (kp' s₀ + BitVec.ofNat 64 i) = m (kp' s₀ + BitVec.ofNat 64 i) :=
  hf.bytes (R := sub s₀ 128 256) hd (show 256 ≤ 2 ^ 64 by decide) hi

theorem ks_post {s₀ : State} {m : Mem} (h : ∀ k < 320, m (off (cx s₀) 64 + BitVec.ofNat 64 k) = ks5 s₀ k)
    {i : Nat} (hi : i < 256) : m (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := by
  rw [← h (64 + i) (by omega), kp', off_add, off_add, show 64 + (64 + i) = 128 + i by omega]

/-- The data's region is apart from the saved registers. -/
theorem dR_inv {s₀ : State} (hp : APre e s₀) :
    (∀ r ∈ [dR s₀], ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r') ∧
    (∀ r ∈ [dR s₀], (sub s₀ 576 56).Disjoint r) :=
  ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩,
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.sub_left (sub_ctx s₀ (by decide))⟩

/-- The prologue keeps the callee-saved vector registers. -/
theorem prologue_keepsV (sve : Bool) : (Short.prologue sve).allInstrs keepsV = true := by
  cases sve <;> lit_decide

theorem sealMain_ok {sve : Bool} {s₀ : State} (hp : APre true s₀) (hL256 : L s₀ ≤ 256) :
    WP isa (Short.sealMain sve) s₀ (MainS s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold Short.sealMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (prologue_keepsV sve)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.x21
    h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have K₃ : ∀ i < L s₀, s₃.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [ks_frame k₃.frame (by rdisj_all) (by omega), ks_frame k₂.frame (by rdisj_all) (by omega)]
    exact ks_post h₁.ks (by omega)
  refine WP.seq (WP.mono (WP.preservedV (xorKs_ok hp hL256 i₃.x21 i₃.x22 i₃.x23 i₃.rd i₃.wr) (by lit_decide))
    fun s₄ ⟨⟨k₄, x₄⟩, v₄⟩ => ?_)
  have i₄ : Inv s₀ s₄ := i₃.step k₄ (dR_inv hp).1 (dR_inv hp).2
  have ct₄ := ct_eq D₃ K₃ x₄
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

theorem openMain_ok {sve : Bool} {s₀ : State} (hp : APre false s₀) (hL256 : L s₀ ≤ 256) :
    WP isa (Short.openMain sve) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold Short.openMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (prologue_keepsV sve)) fun s₁ ⟨h₁, v₁⟩ => ?_)
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
  have D₅ : bytesAt s₅.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₅.frame (by rdisj_all) hL', bytesAt_frame k₄.frame (by rdisj_all) hL',
      bytesAt_frame k₃.frame (by rdisj_all) hL', D₂]
  have K₅ : ∀ i < L s₀, s₅.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [ks_frame k₅.frame (by rdisj_all) (by omega), ks_frame k₄.frame (by rdisj_all) (by omega),
      ks_frame k₃.frame (by rdisj_all) (by omega), ks_frame k₂.frame (by rdisj_all) (by omega)]
    exact ks_post h₁.ks (by omega)
  refine WP.seq (WP.mono (WP.preservedV (xorKs_ok hp hL256 i₅.x21 i₅.x22 i₅.x23 i₅.rd i₅.wr) (by lit_decide))
    fun s₆ ⟨⟨k₆, x₆⟩, v₆⟩ => ?_)
  have i₆ : Inv s₀ s₆ := i₅.step k₆ (dR_inv hp).1 (dR_inv hp).2
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
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', ct_eq D₅ K₅ x₆]

end VG.Proof.ChaCha20Poly1305.AArch64.Short
