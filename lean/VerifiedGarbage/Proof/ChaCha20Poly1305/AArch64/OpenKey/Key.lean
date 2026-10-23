module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.OpenKey.Copy
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.PadRest
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64, 513 to 704 bytes: the one-time key

`OpenKey.openMain`'s first parts: the prologue's first block (the state for
counter 0 at `ctx[64, 128)`), the state copied to `ctx[640, 704)`,
`ctx[768, 1280)` zeroed and the stream called on it from the copy, and
Poly1305 initialized with the first 32 bytes of the result: the prologue's
postcondition (`PostP`), with the keystream of counters 0 to 7 at
`ctx[768, 1280)` (`keyed_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenKey
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_movz)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ZeroedAt)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream serialize block initState)

variable {e : Bool}

/-- The keystream of counters 0 to 7. -/
abbrev ks8 (s₀ : State) (k : Nat) : Byte := (keystream (initState (K s₀) 0 (N s₀)) 512).getD k 0

/-- Its first 32 bytes are the one-time key. -/
theorem otk8_eq {s₀ : State} {m : Mem}
    (h : ∀ k < 512, m (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k) :
    bytesAt m (off (cx s₀) 768) 32 = otk s₀ := by
  apply List.ext_getElem
  · simp [bytesAt, Spec.ChaCha20Poly1305.polyKeyGen, Spec.ChaCha20.chacha20Block,
      VG.Proof.ChaCha20.length_serialize]
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, h i (by omega), ks8,
      VG.Proof.ChaCha20.keystream_getD _ (show i < 512 by omega), show i / 64 = 0 by omega,
      show i % 64 = i by omega, VG.Proof.ChaCha20.ctr_zero,
      Spec.ChaCha20Poly1305.polyKeyGen, Spec.ChaCha20.chacha20Block, List.getElem_take]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some]

/-- After the first block, the keystream of the data from counter 1. -/
theorem ks8_eq (s₀ : State) {i n : Nat} (hi : i < n) (h448 : i < 448) :
    ks8 s₀ (64 + i) = (keystream (initState (K s₀) 1 (N s₀)) n).getD i 0 := by
  rw [ks8, VG.Proof.ChaCha20.keystream_getD _ (show 64 + i < 512 by omega),
    VG.Proof.ChaCha20.keystream_getD _ hi, show (64 + i) / 64 = i / 64 + 1 by omega,
    show (64 + i) % 64 = i % 64 by omega, VG.Proof.ChaCha20Poly1305.ctr_initState,
    VG.Proof.ChaCha20Poly1305.ctr_initState]
  congr 4
  rw [BitVec.ofNat_add, BitVec.add_comm]
  exact (BitVec.add_zero _).trans (BitVec.add_comm _ _)

/-- The stream's arguments. -/
theorem args_ok {s₀ w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block args) w fun u =>
      u.gpr .x0 = off (cx s₀) 640 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 512 ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w u := by
  have core : WP isa (.block args) w fun u =>
      u.gpr .x0 = off (cx s₀) 640 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 512 ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ u.mem = w.mem ∧ u.rd = w.rd ∧ u.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ => wp_movz fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hx21],
          by rw [u₄.other _ (by decide), u₃.gpr]; exact setWidth_ofNat16 (by decide),
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  exact WP.mono (WP.kept core (by simp [args, clobbers, dstOf, preserved]))
    fun u ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- After the one-time key. -/
structure Keyed (s₀ s : State) : Prop where
  post : PostP s₀ s
  ks : ∀ k < 512, s.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k
  vec : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

/-- The parts up to Poly1305 initialized, then `rest`. -/
theorem keyed_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {rest : Prog isa}
    {Q : State → Prop} (hk : ∀ s, Keyed s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (save ++ moves ++ Impl.ChaCha20Poly1305.AArch64.initState ++
        ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr)))
      (.seq (.block (copy ++ Pad.zero ++ args))
      (.seq (.call v.callee.name v.callee.code)
      (.seq (.block keyArgs)
      (.seq (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init) rest))))) s₀ Q := by
  refine WP.seq (WP.mono (WP.preservedV (block1_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  -- The state copied.
  rw [List.append_assoc copy Pad.zero args]
  refine WP.seq (WP.block_append (WP.mono (WP.withSp (WP.preservedV
    (copy_ok hp h₁.inv.x21 h₁.inv.rd h₁.inv.wr) (by lit_decide))) fun s₂ ⟨⟨c₂, v₂⟩, sp₂⟩ => ?_))
  have k₂ : Kept [sub s₀ 640 64] s₁ s₂ :=
    Kept.of (fun r _ => c₂.gpr r (by rintro rfl; simp [preserved] at *)) sp₂ c₂.rd c₂.wr c₂.frame
  have i₂ := h₁.inv.step1 (k := 640) (n := 64) k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  -- `ctx[768, 1280)` zeroed.
  refine WP.block_append (WP.mono (Pad.zero_ok hp i₂.x21 i₂.wr) fun s₃ ⟨k₃, z₃, v₃⟩ => ?_)
  have i₃ := i₂.step1 (k := 768) (n := 512) k₃ (by lit_omega) (by lit_omega) (by lit_omega)
  refine WP.mono (WP.preservedV (args_ok i₃.x21) (by lit_decide)) fun s₄ ⟨⟨x0₄, x1₄, x2₄, x3₄, k₄⟩, v₄⟩ => ?_
  have i₄ := i₃.step0 k₄
  have hw : Covers [⟨off (cx s₀) 640, 64⟩, ⟨off (cx s₀) 768, 512⟩, ⟨off (cx s₀) 128, 320⟩] s₄.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [i₄.wr]; exact hp.ctx_wr, 640, rfl, by show 640 + 64 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [i₄.wr]; exact hp.ctx_wr, 768, rfl, by show 768 + 512 ≤ 1280; omega⟩
    · exact ⟨ctxR s₀, by rw [i₄.wr]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega⟩
  -- The stream on the zeros.
  have wc := hp.wrap_c
  refine WP.seq (xor_call v x0₄ x1₄ x2₄ x3₄ (by decide)
    (sub_disj s₀ (a := 640) (n := 64) (b := 768) (m := 512) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 640) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := 512) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by decide)]; lit_omega) (Covers.right hw) hw fun s₅ v₅ k₅ data₅ => ?_)
  have i₅ : Inv s₀ s₅ := i₄.step k₅
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  -- The state the stream started from.
  have st₄ : stateAt s₄.mem (off (cx s₀) 640) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₄.frame (fun r hr => absurd hr List.not_mem_nil),
      stateAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      stateAt_copy c₂, h₁.st]
  have ks₅ : ∀ k < 512, s₅.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    have x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₅ hk
    rw [x, st₄]
    have z : s₄.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = 0 := by
      rw [k₄.frame _ (fun r hr => absurd hr List.not_mem_nil),
        show off (cx s₀) 768 + BitVec.ofNat 64 k = cx s₀ + BitVec.ofNat 64 (768 + k) from off_off _ _ _]
      exact z₃.byte (k := k) (by omega) (by decide)
    rw [z]; simp
  -- Poly1305 initialized with the key.
  refine WP.seq (WP.mono (WP.preservedV (ptrs2_ok (a := 448) (b := 768) (by lit_omega) (by lit_omega) s₅)
    (by lit_decide)) fun s₆ ⟨⟨h0, h1, k₆⟩, v₆⟩ => ?_)
  have i₆ := i₅.step0 k₆
  rw [i₅.x21] at h0 h1
  refine WP.seq (WP.mono (WP.preservedV (Q := fun s' => Kept [sub s₀ 448 128] s₆ s' ∧
      Repr s'.mem (off (cx s₀) 448) (bytesAt s₆.mem (off (cx s₀) 768) 32) [])
    (init_call h0 h1 (sub_disj s₀ (a := 448) (n := 128) (b := 768) (m := 32) (by lit_omega)
      (by lit_omega) (by lit_omega))
    (covers2 hp i₆.wr (a := 448) (n := 128) (b := 768) (m := 32) (by lit_omega) (by lit_omega))
    (covers1 hp i₆.wr (a := 448) (n := 128) (by lit_omega)) fun s' k r => ⟨k, r⟩) (by lit_decide))
    fun s₇ ⟨⟨k₇, repr₇⟩, v₇⟩ => ?_)
  have m₆ := k₆.mem_eq
  have ks₇ : ∀ k < 512, s₇.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    rw [k₇.frame.bytes (R := sub s₀ 768 512) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (show 512 ≤ 2 ^ 64 by decide) hk,
      m₆, ks₅ k hk]
  -- The prologue's postcondition.
  have F : Frame [workR s₀] s₀.mem s₇.mem :=
    h₁.fine.trans ((frame_work1 (k := 640) (n := 64) k₂ (by lit_omega) (by lit_omega)).trans
      ((frame_work1 (k := 768) (n := 512) k₃ (by lit_omega) (by lit_omega)).trans
      ((by rw [k₄.mem_eq]; exact Frame.refl _ _ : Frame [workR s₀] s₃.mem s₄.mem).trans
      ((k₅.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩).trans
      (by rw [← m₆]; exact frame_work1 (k := 448) (n := 128) k₇ (by lit_omega) (by lit_omega))))))
  have st₇ : stateAt s₇.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₇.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), m₆,
      stateAt_frame k₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      stateAt_frame k₄.frame (fun r hr => absurd hr List.not_mem_nil),
      stateAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      stateAt_frame c₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), h₁.st]
  refine hk s₇ ⟨⟨i₆.step1 (k := 448) (n := 128) k₇ (by lit_omega) (by lit_omega) (by lit_omega), F, ?_, st₇⟩,
    ks₇, fun r hr => ?_⟩
  · have hk' : bytesAt s₆.mem (off (cx s₀) 768) 32 = otk s₀ := by
      rw [m₆]; exact otk8_eq ks₅
    rw [← hk']; exact repr₇
  · exact (v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey
