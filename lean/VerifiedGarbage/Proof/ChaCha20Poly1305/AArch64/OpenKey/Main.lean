module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Rest
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.PadRest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero

/-! ### `ChaCha20Poly1305.AArch64.OpenKey.Key`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.AArch64.OpenKey.Copy`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, 513 to 704 bytes: the state copied

`OpenKey.copy`: the ChaCha20 state at `ctx[64, 128)` copied to
`ctx[640, 704)` a word at a time, as `ShortRest.stash` copies it.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenKey
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_ldr32 wp_str32)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

/-- One word copied. -/
theorem copyW_ok {s₀ s : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (copyW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (640 + 4 * k)) (s.mem.readW (off (cx s₀) (64 + 4 * k)) 32) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain o : InRegions s.wr (off (cx s₀) (640 + 4 * k)) 4 := by
    rw [hwr]; exact hp.in_ctx (by omega_using [hk])
  obtain i : InRegions (s.rd ++ s.wr) (off (cx s₀) (64 + 4 * k)) 4 := by
    rw [hrd, hwr]; exact hp.in_ctx' (by omega_using [hk])
  unfold copyW
  refine wp_ldr32 (a := off (cx s₀) (64 + 4 * k)) ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hx21]) i fun s₁ u₁ => ?_
  refine wp_str32 (a := off (cx s₀) (640 + 4 * k)) ⟨by omega_using [], by omega_using [hk]⟩
    (by rw [u₁.other _ (by decide), hx21]) (by rw [u₁.wr]; exact o) fun s₂ g₂ =>
      WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · rw [g₂.mem, u₁.gpr, u₁.mem, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · rw [g₂.gpr, u₁.other r hr]
  · rw [g₂.rd, u₁.rd]
  · rw [g₂.wr, u₁.wr]

/-- The first `n` words of the copy. -/
def copyN (n : Nat) : List Instr := (List.range n).flatMap copyW

theorem copyN_succ (n : Nat) : copyN (n + 1) = copyN n ++ copyW n := by
  simp only [copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- After the first `n` words. -/
structure Copied (s₀ s : State) (n : Nat) (s' : State) : Prop where
  word : ∀ j < n, s'.mem.readW (off (cx s₀) (640 + 4 * j)) 32 = s.mem.readW (off (cx s₀) (64 + 4 * j)) 32
  frame : Frame [sub s₀ 640 64] s.mem s'.mem
  gpr : ∀ r, r ≠ .x9 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copyN_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : ∀ n ≤ 16, WP isa (.block (copyN n)) s (Copied s₀ s n)
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [copyN_succ]
    refine WP.block_append ((copyN_ok hp hx21 hrd hwr n (by omega_using [hn])).mono fun s₁ h₁ => ?_)
    refine (copyW_ok hp (k := n) (by omega_using [hn]) (by rw [h₁.gpr _ (by decide), hx21])
      (by rw [h₁.rd, hrd]) (by rw [h₁.wr, hwr])).mono fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    -- The source word `n` is outside the copy written so far.
    obtain src : s₁.mem.readW (off (cx s₀) (64 + 4 * n)) 32 = s.mem.readW (off (cx s₀) (64 + 4 * n)) 32 := by
      refine h₁.frame.readW (r := sub s₀ (64 + 4 * n) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_using [hn]) (by omega_using [hn]) (by omega_using [])
    refine ⟨fun j hj => ?_, ?_, fun r hr => by rw [g₂ r hr, h₁.gpr r hr], by rw [rd₂, h₁.rd],
      by rw [wr₂, h₁.wr]⟩
    · rw [m₂, src]
      by_cases hjn : j = n
      · subst hjn; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (by
            rw [show off (cx s₀) (640 + 4 * j) = off (cx s₀) (4 * (160 + j)) by congr 1; omega_using [],
              show off (cx s₀) (640 + 4 * n) = off (cx s₀) (4 * (160 + n)) by congr 1; omega_using []]
            exact Offset.sep _ (by omega_using [hjn]) (by omega_using [hn, hj]) (by omega_using [hn])) (by decide)]
        exact h₁.word j (by omega_using [hj, hjn])
    · rw [m₂]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ (by
        show (sub s₀ 640 64).Contains (off (cx s₀) (640 + 4 * n)) 4
        exact Offset.contains _ (e := 640) (k := 64) (by omega_using []) (by omega_using [hn]) (by omega_using []))

theorem copy_eq : copy = copyN 16 := rfl

/-- The state copied. -/
theorem stateAt_copy {s₀ s s' : State} (h : Copied s₀ s 16 s') :
    stateAt s'.mem (off (cx s₀) 640) = stateAt s.mem (off (cx s₀) 64) := by
  apply Vector.ext
  intro j hj
  obtain w := h.word j hj
  simp only [stateAt, Vector.getElem_ofFn]
  rw [show off (cx s₀) 640 + BitVec.ofNat 64 (4 * j) = off (cx s₀) (640 + 4 * j) from off_off _ _ _,
    show off (cx s₀) 64 + BitVec.ofNat 64 (4 * j) = off (cx s₀) (64 + 4 * j) from off_off _ _ _, w]

/-- `copy`, with the registers but `x9` kept. -/
theorem copy_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : WP isa (.block copy) s (Copied s₀ s 16) := by
  rw [copy_eq]; exact copyN_ok hp hx21 hrd hwr 16 (Nat.le_refl _)

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

end

end


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
    simp only [bytesAt, List.getElem_map, List.getElem_range, h i (by omega_using [h₁]), ks8,
      VG.Proof.ChaCha20.keystream_getD _ (show i < 512 by omega_using [h₁]), show i / 64 = 0 by omega_using [h₁],
      show i % 64 = i by omega_using [h₁], VG.Proof.ChaCha20.ctr_zero,
      Spec.ChaCha20Poly1305.polyKeyGen, Spec.ChaCha20.chacha20Block, List.getElem_take]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega_using [h₁]), Option.getD_some]

/-- After the first block, the keystream of the data from counter 1. -/
theorem ks8_eq (s₀ : State) {i n : Nat} (hi : i < n) (h448 : i < 448) :
    ks8 s₀ (64 + i) = (keystream (initState (K s₀) 1 (N s₀)) n).getD i 0 := by
  rw [ks8, VG.Proof.ChaCha20.keystream_getD _ (show 64 + i < 512 by omega_using [h448]),
    VG.Proof.ChaCha20.keystream_getD _ hi, show (64 + i) / 64 = i / 64 + 1 by omega_using [],
    show (64 + i) % 64 = i % 64 by omega_using [], VG.Proof.ChaCha20Poly1305.ctr_initState,
    VG.Proof.ChaCha20Poly1305.ctr_initState]
  congr 4
  rw [BitVec.ofNat_add, BitVec.add_comm]
  exact (BitVec.add_zero _).trans (BitVec.add_comm _ _)

/-- The stream's arguments. -/
theorem args_ok {s₀ w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block args) w fun u =>
      u.gpr .x0 = off (cx s₀) 640 ∧ u.gpr .x1 = off (cx s₀) 768 ∧ u.gpr .x2 = BitVec.ofNat 64 512 ∧
      u.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w u := by
  obtain core : WP isa (.block args) w fun u =>
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
  exact WP.mono (WP.kept core (by rfl))
    fun u ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- After the one-time key. -/
structure Keyed (e : Bool) (s₀ s : State) : Prop where
  post : PostP e s₀ s
  ks : ∀ k < 512, s.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k
  vec : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

/-- The parts up to Poly1305 initialized, then `rest`. -/
theorem keyed_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {rest : Prog isa}
    {Q : State → Prop} (hk : ∀ s, Keyed e s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (save ++ moves ++ Impl.ChaCha20Poly1305.AArch64.initState ++
        ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr)))
      (.seq (.block (copy ++ Pad.zero ++ args))
      (.seq v.callee.inPlace
      (.seq (.block keyArgs)
      (.seq (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init) rest))))) s₀ Q := by
  refine WP.seq (WP.mono (WP.preservedV (block1_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  -- The state copied.
  rw [List.append_assoc copy Pad.zero args]
  refine WP.seq (WP.block_append (WP.mono (WP.withSp (WP.preservedV
    (copy_ok hp h₁.inv.x21 h₁.inv.rd h₁.inv.wr) (by lit_decide))) fun s₂ ⟨⟨c₂, v₂⟩, sp₂⟩ => ?_))
  obtain k₂ : Kept [sub s₀ 640 64] s₁ s₂ :=
    Kept.of (fun r _ => c₂.gpr r (by rintro rfl; simp [preserved] at *)) sp₂ c₂.rd c₂.wr c₂.frame
  obtain i₂ := h₁.inv.step1 (k := 640) (n := 64) k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  -- `ctx[768, 1280)` zeroed.
  refine WP.block_append (WP.mono (Pad.zero_ok hp i₂.x21 i₂.wr) fun s₃ ⟨k₃, z₃, v₃⟩ => ?_)
  obtain i₃ := i₂.step1 (k := 768) (n := 512) k₃ (by lit_omega) (by lit_omega) (by lit_omega)
  refine WP.mono (WP.preservedV (args_ok i₃.x21) (by lit_decide)) fun s₄ ⟨⟨x0₄, x1₄, x2₄, x3₄, k₄⟩, v₄⟩ => ?_
  obtain i₄ := i₃.step0 k₄
  obtain hw : Covers [⟨off (cx s₀) 640, 64⟩, ⟨off (cx s₀) 768, 512⟩, ⟨off (cx s₀) 128, 320⟩] s₄.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [i₄.wr]; exact hp.ctx_wr, 640, rfl, by show 640 + 64 ≤ 1280; omega_using []⟩
    · exact ⟨ctxR s₀, by rw [i₄.wr]; exact hp.ctx_wr, 768, rfl, by show 768 + 512 ≤ 1280; omega_using []⟩
    · exact ⟨ctxR s₀, by rw [i₄.wr]; exact hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 1280; omega_using []⟩
  -- The stream on the zeros.
  have wc := hp.wrap_c
  refine WP.seq (xor_call v x0₄ x1₄ x2₄ x3₄ (by decide)
    (sub_disj s₀ (a := 640) (n := 64) (b := 768) (m := 512) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 640) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 768) (n := 512) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by decide)]; lit_omega) hw fun s₅ v₅ k₅ data₅ => ?_)
  obtain i₅ : Inv e s₀ s₅ := i₄.step k₅
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  -- The state the stream started from.
  obtain st₄ : stateAt s₄.mem (off (cx s₀) 640) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₄.frame (fun r hr => absurd hr List.not_mem_nil),
      stateAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      stateAt_copy c₂, h₁.st]
  obtain ks₅ : ∀ k < 512, s₅.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    obtain x := VG.Proof.ChaCha20.xor_getD (VG.Proof.ChaCha20.length_keystream _ _) data₅ hk
    rw [x, st₄]
    obtain z : s₄.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = 0 := by
      rw [k₄.frame _ (fun r hr => absurd hr List.not_mem_nil),
        show off (cx s₀) 768 + BitVec.ofNat 64 k = cx s₀ + BitVec.ofNat 64 (768 + k) from off_off _ _ _]
      exact z₃.byte (k := k) (by omega_using [hk]) (by decide)
    rw [z]; simp
  -- Poly1305 initialized with the key.
  refine WP.seq (WP.mono (WP.preservedV (ptrs2_ok (a := 448) (b := 768) (by lit_omega) (by lit_omega) s₅)
    (by lit_decide)) fun s₆ ⟨⟨h0, h1, k₆⟩, v₆⟩ => ?_)
  obtain i₆ := i₅.step0 k₆
  rw [i₅.x21] at h0 h1
  refine WP.seq (WP.mono (WP.preservedV (Q := fun s' => Kept [sub s₀ 448 128] s₆ s' ∧
      Repr s'.mem (off (cx s₀) 448) (bytesAt s₆.mem (off (cx s₀) 768) 32) [])
    (init_call h0 h1 (sub_disj s₀ (a := 448) (n := 128) (b := 768) (m := 32) (by lit_omega)
      (by lit_omega) (by lit_omega))
    (covers2 hp i₆.wr (a := 448) (n := 128) (b := 768) (m := 32) (by lit_omega) (by lit_omega))
    (covers1 hp i₆.wr (a := 448) (n := 128) (by lit_omega)) fun s' k r => ⟨k, r⟩) (by lit_decide))
    fun s₇ ⟨⟨k₇, repr₇⟩, v₇⟩ => ?_)
  have m₆ := k₆.mem_eq
  obtain ks₇ : ∀ k < 512, s₇.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    rw [k₇.frame.bytes (R := sub s₀ 768 512) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (show 512 ≤ 2 ^ 64 by decide) hk,
      m₆, ks₅ k hk]
  -- The prologue's postcondition.
  obtain F : Frame [workR s₀] s₀.mem s₇.mem :=
    h₁.fine.trans ((frame_work1 (k := 640) (n := 64) k₂ (by lit_omega) (by lit_omega)).trans
      ((frame_work1 (k := 768) (n := 512) k₃ (by lit_omega) (by lit_omega)).trans
      ((by rw [k₄.mem_eq]; exact Frame.refl _ _ : Frame [workR s₀] s₃.mem s₄.mem).trans
      ((k₅.frame.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩).trans
      (by rw [← m₆]; exact frame_work1 (k := 448) (n := 128) k₇ (by lit_omega) (by lit_omega))))))
  obtain st₇ : stateAt s₇.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) := by
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

end

end

/-!
# ChaCha20-Poly1305 on AArch64: `open` from 513 to 704 bytes

`OpenKey.openMain`: the one-time key and the keystream of the data's first
448 bytes from the stream (`keyed_ok`); the additional data and the lengths
block; the counter set to 8, and the four blocks after the first eight
computed into `ctx[128, 384)` while the data's whole blocks are absorbed
(`TailO.kernel_ok`, up to five after each double round); the data's last
partial block absorbed; the data XORed with the two keystreams; the
lengths absorbed, `ctx[768, 1280)` zeroed again, and the tag computed.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenKey
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_mov wp_movz wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (Rk)
open VG.Proof.ChaCha20Poly1305.AArch64.TailO (loadAtTo_ok outTo_ok moves_ok kernel_ok)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (kpAt kp')
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

theorem eight32 : ((((8 : BitVec 16).setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = 8 := rfl

theorem set12_initState8 (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 8 = Spec.ChaCha20.initState key 8 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

/-- The keystream of the blocks after the first eight continues the one from
counter 1. -/
theorem ks_hi (s₀ : State) {k : Nat} (hk : 448 + k < L s₀) :
    (serialize (block (ctr (Spec.ChaCha20.initState (K s₀) 8 (N s₀)) (k / 64)))).getD (k % 64) 0 =
      (KS1 s₀).getD (448 + k) 0 := by
  rw [KS1, VG.Proof.ChaCha20.keystream_getD _ hk, show (448 + k) / 64 = 7 + k / 64 by omega_arith,
    show (448 + k) % 64 = k % 64 by omega_arith, VG.Proof.ChaCha20Poly1305.ctr_initState,
    VG.Proof.ChaCha20Poly1305.ctr_initState]
  congr 4
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

/-- `pre`: the counter set to 8, and the kernel's arguments. -/
theorem pre_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv e s₀ s) :
    WP isa (.block OpenKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9] → s'.gpr r = s.gpr r) ∧ Kept [sub s₀ 64 64] s s' ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block OpenKey.pre) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (8 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.gpr .x2 = s.gpr .x23 ∧
      (∀ r, r ∉ [Reg.x0, .x2, .x3, .x9] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ =>
      WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
    · rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, eight32]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h2, h3, h9⟩ := hr
      rw [u₅.other _ h2, u₄.other _ h3, u₃.other _ h0, g₂.gpr, u₁.other _ h9]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.preservedV (WP.kept core (by rfl)) (by lit_decide))
    fun s' ⟨⟨⟨hm, h0, h3, h2, hg', hrd, hwr⟩, hg, hsp⟩, hv⟩ => ⟨hm, h0, h3, h2, hg', Kept.of hg hsp hrd hwr ?_, hv⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 513 ≤ L s₀) (hhi : L s₀ ≤ 704) : WP isa (OpenKey.openMain v.callee) s₀ (MainO s₀) := by
  -- Facts are stated with `obtain`, not `have`: `have` keeps its proof in the context (a `let` nothing
  -- unfolds), and every `(by …)` in a term first instantiates and shares the whole context
  -- (`Term.runTactic`): with sixty proofs in it, 19 ms for each of two hundred; with `obtain`, 4 ms.
  obtain hLt : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt hLt
  have wd := hp.wrap_d
  obtain oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  unfold OpenKey.openMain
  refine keyed_ok v hp fun s₁ ⟨h₁, ks₁, v₁⟩ => ?_
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  -- The additional data, and the lengths block.
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  obtain i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  obtain R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  obtain ks₃ : ∀ k < 512, s₃.mem (off (cx s₀) 768 + BitVec.ofNat 64 k) = ks8 s₀ k := fun k hk => by
    rw [k₃.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hk,
      k₂.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) hk, ks₁ k hk]
  -- The data, as it was, until it is XORed.
  obtain dat : ∀ {m : Mem}, (∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k)) →
      ∀ a n, a + n ≤ L s₀ → bytesAt m (dp s₀ + BitVec.ofNat 64 a) n = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 a) n := by
    intro m hm a n han
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    obtain hi := List.mem_range.mp hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm _ (by omega_arith)
  obtain d₃ : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
    rw [data_frame k₃.frame (by rdisj_all) hk, data_frame k₂.frame (by rdisj_all) hk,
      data_frame h₁.fine (by rdisj_all) hk]
  -- The counter set to 8, and the kernel's arguments.
  refine WP.seq (WP.block_append (WP.mono (pre_ok hp i₃) fun s₄ ⟨m₄, x0₄, x3₄, x2₄, g₄, k₄, v₄⟩ => ?_))
  obtain st₄ : stateAt s₄.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
    rw [m₄, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, st₃, set12_initState8]
  obtain R₄ := Repr.frame k₄.frame (by rdisj_all) R₃
  obtain x21₄ : s₄.gpr .x21 = cx s₀ := by rw [g₄ _ (by decide), i₃.x21]
  obtain rd₄ : s₄.rd = s₀.rd := by rw [k₄.rd, i₃.rd]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [k₄.wr, i₃.wr]
  obtain x23₄ : s₄.gpr .x23 = BitVec.ofNat 64 (L s₀) := by rw [g₄ _ (by decide), i₃.x23, hL]
  obtain d₄ : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk => by
    rw [data_frame k₄.frame (by rdisj_all) hk, d₃ k hk]
  -- The accumulator and the clamped key.
  refine (loadAtTo_ok hp hLt x21₄ rd₄ wr₄ x0₄ x23₄ R₄).mono
    fun s₅ ⟨a₅, x20₅, x8₅, x7₅, x6₅, m₅, x15₅, g₅, vv₅, sp₅, rd₅, wr₅⟩ => ?_
  obtain rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄]
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄]
  obtain x0₅ : s₅.gpr .x0 = off (cx s₀) 64 := by rw [g₅ _ (by decide), x0₄]
  obtain x3₅ : s₅.gpr .x3 = off (cx s₀) 128 := by rw [g₅ _ (by decide), x3₄]
  obtain x22₄ : s₄.gpr .x22 = dp s₀ := by rw [g₄ _ (by decide), i₃.x22]
  obtain hin : ∀ k : Fin 16, InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₅, oo, rd₅', wr₅']; exact hp.in_ctx' (by omega_arith)
  obtain hw : ∀ d, d + 16 ≤ 256 → InRegions s₅.wr (s₅.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₅, oo, wr₅']; exact hp.in_ctx (by omega_arith)
  obtain hst : (⟨s₅.gpr .x0, 64⟩ : Region).Disjoint ⟨s₅.gpr .x3, 256⟩ := by
    rw [x0₅, x3₅]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain hc16 : 16 * (L s₀ / 16) ≤ L s₀ := Nat.mul_div_le _ _
  obtain hrd : Readable (dp s₀) (16 * (L s₀ / 16)) s₅ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₅', wr₅']
      exact ⟨dR s₀, hp.d_in, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [rd₅', wr₅', x0₅, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₅', wr₅', x0₅, oo]; exact hp.in_ctx' (by lit_omega)
  -- The kernel: the keystream of counters 8 to 11, with the data's whole blocks absorbed.
  refine WP.seq ((WP.preservedV (kernel_ok v.callee.sve 5 (c := L s₀ / 16) (by omega_arith)
      (by rw [x20₅, x22₄]) x6₅ hin hw hst hrd a₅ (by omega_arith)) (by cases v.callee.sve <;> lit_decide)).mono
    fun s₆ ⟨⟨ks₆, f₆, hv₆, h2₆, x20₆, g₆, rd₆, wr₆, sp₆⟩, v₆⟩ => ?_)
  rw [x3₅, x0₅] at ks₆
  rw [x3₅] at f₆
  have g₆' (r : Reg) (h : r ≠ .x1 ∧ r ≠ .x4 ∧ r ≠ .x6 ∧ r ∉ Poly.regs) :
      s₆.gpr r = s₅.gpr r :=
    have ⟨h1, h4, h6, hp'⟩ := h
    g₆ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h6⟩) hp'
  obtain x0₆ : s₆.gpr .x0 = off (cx s₀) 64 := by
    rw [g₆' _ (by decide), x0₅]
  -- The accumulator stored.
  refine WP.seq ((outTo_ok hp x0₆ (by rw [rd₆, rd₅']) (by rw [wr₆, wr₅'])).mono
    fun s₇ ⟨acc₇, f₇, x21₇, x27₇, x28₇, x22₇, x23₇, x20₇, x24₇, x25₇, g₇, rd₇, wr₇, sp₇, vv₇⟩ => ?_)
  obtain x7₆ : s₆.gpr .x7 = dp s₀ := by rw [g₆' _ (by decide), x7₅, x22₄]
  obtain x2₆ : s₆.gpr .x2 = BitVec.ofNat 64 (L s₀) := by
    rw [g₆' _ (by decide), g₅ _ (by decide), x2₄, i₃.x23, hL]
  obtain x22₇' : s₇.gpr .x22 = dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16)) := by rw [x22₇, x20₆]
  obtain x23₇' : s₇.gpr .x23 = BitVec.ofNat 64 (L s₀ - 16 * (L s₀ / 16)) := by
    rw [x23₇, x7₆, x2₆, x20₆, VG.Offset.add_sub_add_left, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hc16]
  -- The data until the XOR.
  obtain d₇ : ∀ k < L s₀, s₇.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [data_frame (s₀ := s₀) f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk,
      data_frame (s₀ := s₀) f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk, m₅,
      data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28))
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk, d₄ k hk]
  obtain b₅ : bytesAt s₅.mem (dp s₀) (16 * (L s₀ / 16)) = bytesAt s₀.mem (dp s₀) (16 * (L s₀ / 16)) := by
    have := dat (m := s₅.mem) (fun k hk => by
      rw [m₅, data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28))
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk, d₄ k hk]) 0 (16 * (L s₀ / 16))
      (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- The Poly1305 state after `out`: the additional data and the data's whole blocks.
  let M := [] ++ (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))
  have hml : M.length % 16 = 0 := R₄.1
  let tgt := [sub s₀ 32 16, sub s₀ 64 408]
  have c408 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, by simp [tgt], sub_sub s₀ h₁ (by omega_arith) (by lit_omega)⟩
  obtain Fm : Frame tgt s₄.mem s₅.mem := by
    rw [m₅]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c408 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  obtain Fk : Frame tgt s₅.mem s₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 128 256 (by decide) (by decide)
  obtain Fo : Frame tgt s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 448 24 (by decide) (by decide)
  obtain F₇ : Frame tgt s₄.mem s₇.mem := Fm.trans (Fk.trans Fo)
  obtain R₇ : Repr s₇.mem (off (cx s₀) 448) (otk s₀) (M ++ bytesAt s₀.mem (dp s₀) (16 * (L s₀ / 16))) := by
    obtain k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    refine ⟨by rw [List.length_append, Poly1305.length_bytesAt]; omega_arith, ?_, ?_⟩
    · have e := R₄.2.1
      rw [k24] at e ⊢
      rw [bytesAt_frame F₇ (fun r hr => by
          simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega)]
      exact e
    · have hlt := Poly1305.accumulate_lt (Rk (otk s₀)) M
      rw [acc₇ h2₆, show hacc s₆ = Poly.hval s₆ from rfl, hv₆,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₅]
      exact (Poly1305.accumulate_append hml).symm
  -- The last partial block, absorbed with its padding.
  obtain rd₇' : s₇.rd = s₀.rd := by rw [rd₇, rd₆, rd₅']
  obtain wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆, wr₅']
  obtain hsrc := srcAt hp (p := 16 * (L s₀ / 16)) hc16
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ hsrc
    x21₇ rd₇' wr₇' x22₇' x23₇') (by lit_decide)) fun s₈ ⟨⟨k₈, r₈⟩, v₈⟩ => ?_)
  obtain R₈ := r₈ _ _ R₇
  -- The data, back in `x22` and `x23`.
  refine WP.seq (moves_ok.mono fun s₉ ⟨⟨x22₉, x23₉, g₉, m₉⟩, vv₉, sp₉, rd₉, wr₉⟩ => ?_)
  obtain x24₈ : s₈.gpr .x24 = dp s₀ := by rw [k₈.cs _ (pres .x24) (pres30 .x24), x24₇, x7₆]
  obtain x25₈ : s₈.gpr .x25 = BitVec.ofNat 64 (L s₀) := by rw [k₈.cs _ (pres .x25) (pres30 .x25), x25₇, x2₆]
  obtain x21₉ : s₉.gpr .x21 = cx s₀ := by
    rw [g₉ _ (by decide) (by decide), k₈.cs _ (pres .x21) (pres30 .x21), x21₇]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, k₈.rd, rd₇']
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, k₈.wr, wr₇']
  obtain d₉ : ∀ k < L s₀, s₉.mem (dp s₀ + BitVec.ofNat 64 k) = s₀.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₉, data_frame (s₀ := s₀) k₈.frame (fun r hr => by
      simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk, d₇ k hk]
  -- The data's first 448 bytes XORed with their keystream at `ctx + 832`.
  unfold xorFirst
  refine WP.seq (WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x14 = s₉.gpr .x23 ∧ u.gpr .x23 = BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .x14 → r ≠ .x23 → u.gpr r = s₉.gpr r) ∧ u.mem = s₉.mem)
    (wp_mov fun t₁ u₁ => wp_movz fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr]; exact setWidth_ofNat16 (by decide),
        fun r h14 h23 => by rw [u₂.other _ h23, u₁.other _ h14], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₁₀ ⟨⟨x14₁₀, x23₁₀, g₁₀, m₁₀⟩, vv₁₀, sp₁₀, rd₁₀, wr₁₀⟩ => ?_))
  obtain x21₁₀ : s₁₀.gpr .x21 = cx s₀ := by rw [g₁₀ _ (by decide) (by decide), x21₉]
  obtain x22₁₀ : s₁₀.gpr .x22 = dp s₀ + BitVec.ofNat 64 0 := by
    rw [g₁₀ _ (by decide) (by decide), x22₉, x24₈, BitVec.add_zero]
  obtain x28₁₀ : s₁₀.gpr .x28 = s₀.gpr .x28 := by
    rw [g₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide), k₈.cs _ (by decide) (by decide), x28₇,
      g₆' _ (by decide), x15₅, g₄ _ (by decide), i₃.un .x28 (by decide)]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsFromDst_ok hp hp.o true (k := 832) (o := 0) (n := 448)
    (by omega_arith) (by omega_arith) x21₁₀ x22₁₀ (cond_out (e := false) s₀ x28₁₀ 0) x23₁₀
    (by rw [rd₁₀, rd₉']) (by rw [wr₁₀, wr₉'])) (by lit_decide))
    fun s₁₁ ⟨⟨k₁₁, e₁₁, f₁₁, g₁₁⟩, v₁₁⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x23 = s₁₁.gpr .x14 ∧ (∀ r, r ≠ .x23 → u.gpr r = s₁₁.gpr r) ∧ u.mem = s₁₁.mem)
    (wp_mov fun t₁ u₁ => WP.block_nil ⟨u₁.gpr, fun r h23 => u₁.other _ h23, u₁.mem⟩)).mono
    fun s₁₂ ⟨⟨x23₁₂, g₁₂, m₁₂⟩, vv₁₂, sp₁₂, rd₁₂, wr₁₂⟩ => ?_
  -- The rest of the data, after 448 bytes.
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide) (Q := fun u =>
      u.gpr .x22 = s₁₂.gpr .x22 + BitVec.ofNat 64 448 ∧ u.gpr .x23 = s₁₂.gpr .x23 - BitVec.ofNat 64 448 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = s₁₂.gpr r) ∧ u.mem = s₁₂.mem)
    (wp_addImm (by decide) fun t₁ u₁ => wp_subImm (by decide) fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₁₃ ⟨⟨x22₁₃, x23₁₃, g₁₃, m₁₃⟩, vv₁₃, sp₁₃, rd₁₃, wr₁₃⟩ => ?_)
  have g₁₁' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₁₁.gpr r = s₁₀.gpr r :=
    have ⟨h9, h10, h11, h12, h13, h15⟩ := h
    g₁₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13, h15⟩)
  obtain x21₁₃ : s₁₃.gpr .x21 = cx s₀ := by
    rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide),
      g₁₁' _ (by decide), x21₁₀]
  obtain x22₁₃ : s₁₃.gpr .x22 = dp s₀ + BitVec.ofNat 64 448 := by
    rw [x22₁₃, g₁₂ _ (by decide), g₁₁' _ (by decide),
      g₁₀ _ (by decide) (by decide), x22₉, x24₈]
  obtain x23₁₃ : s₁₃.gpr .x23 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [x23₁₃, x23₁₂, g₁₁' _ (by decide), x14₁₀, x23₉, x25₈,
      VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat (by omega_arith)]
  obtain rd₁₃' : s₁₃.rd = s₀.rd := by rw [rd₁₃, rd₁₂, k₁₁.rd, rd₁₀, rd₉']
  obtain wr₁₃' : s₁₃.wr = s₀.wr := by rw [wr₁₃, wr₁₂, k₁₁.wr, wr₁₀, wr₉']
  -- The rest XORed with its keystream at `ctx + 128`.
  obtain x28₁₃ : s₁₃.gpr .x28 = s₀.gpr .x28 := by
    rw [g₁₃ _ (by decide) (by decide), g₁₂ _ (by decide), g₁₁' _ (by decide), x28₁₀]
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsDst_ok hp hp.o true (o := 448) (n := L s₀ - 448) (by omega_arith)
    (by omega_arith) x21₁₃ x22₁₃ (cond_out (e := false) s₀ x28₁₃ 448) x23₁₃ rd₁₃' wr₁₃') (by lit_decide))
    fun s₁₄ ⟨⟨k₁₄, e₁₄, f₁₄, g₁₄⟩, v₁₄⟩ => ?_)
  have g₁₄' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₁₄.gpr r = s₁₃.gpr r :=
    have ⟨h9, h10, h11, h12, h13, h15⟩ := h
    g₁₄ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13, h15⟩)
  -- Registers.
  have to₇ (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧
      r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x22 ∧ r ≠ .x23) : s₁₄.gpr r = s₇.gpr r := by
    obtain ⟨hr, h30, h9, h10, h11, h12, h13, h14, h15, h22, h23⟩ := h
    rw [g₁₄' r ⟨h9, h10, h11, h12, h13, h15⟩, g₁₃ r h22 h23, g₁₂ r h23, g₁₁' r ⟨h9, h10, h11, h12, h13, h15⟩, g₁₀ r h14 h23,
      g₉ r h22 h23, k₈.cs r hr h30]
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₆.mem.readW (off (cx s₀) d) 64 = s₅.mem.readW (off (cx s₀) d) 64 :=
    f₆.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by decide)
  obtain un₁₄ : ∀ r ∈ untouched, s₁₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain hu := i₃.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₇ _ (by decide), g₇ _ (by decide), g₆' _ (by decide),
        g₅ _ (by decide), g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide), x20₇, g₆' _ (by decide), x8₅,
        g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide), g₇ _ (by decide), g₆' _ (by decide),
        g₅ _ (by decide), g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide), x27₇, r32 32 (.inl rfl), m₅, memIn_800, g₄ _ (by decide), hu]
    · rw [to₇ _ (by decide), x28₇, g₆' _ (by decide), x15₅, g₄ _ (by decide), hu]
  -- The frames.
  let out := [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, oR false s₀]
  obtain Fa : Frame out s₃.mem s₄.mem := k₄.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
  obtain Fb : Frame out s₄.mem s₇.mem := F₇.sub fun r hr => by
    simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 32 16, by simp [out], fun _ h => h⟩
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
  obtain Fc : Frame out s₇.mem s₈.mem := k₈.frame.sub fun r hr => by
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
    · exact ⟨sub s₀ 16 16, by simp [out], fun _ h => h⟩
  obtain Fd : Frame out s₈.mem s₁₁.mem := by
    rw [← m₉, ← m₁₀]
    exact k₁₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨oR false s₀, by simp [out], fun _ h => h⟩
  obtain Fe : Frame out s₁₁.mem s₁₄.mem := by
    rw [← m₁₂, ← m₁₃]
    exact k₁₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨oR false s₀, by simp [out], fun _ h => h⟩
  obtain F : Frame out s₃.mem s₁₄.mem := Fa.trans (Fb.trans (Fc.trans (Fd.trans Fe)))
  obtain sp₁₄ : s₁₄.sp = s₀.sp := by
    rw [k₁₄.sp, sp₁₃, sp₁₂, k₁₁.sp, sp₁₀, sp₉, k₈.sp, sp₇, sp₆, sp₅, k₄.sp, i₃.sp]
  obtain i₁₄ : Inv0 false s₀ s₁₄ := ⟨by rw [g₁₄' _ (by decide), x21₁₃],
    un₁₄, sp₁₄, by rw [k₁₄.rd, rd₁₃'], by rw [k₁₄.wr, wr₁₃'],
    i₃.saved.frame F (fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.o.ctx.sub_left (sub_ctx s₀ (by lit_omega))),
    i₃.frame.trans (F.sub fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨oR false s₀, by simp, fun _ h => h⟩)⟩
  -- The lengths, `ctx[768, 1280)` zeroed again, and the tag.
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₄) (by lit_decide))
    fun s₁₅ ⟨⟨i₁₅, k₁₅, r₁₅⟩, v₁₅⟩ => ?_)
  refine WP.seq (WP.mono (Pad.zero_ok hp i₁₅.x21 i₁₅.wr) fun s₁₆ ⟨k₁₆, _, v₁₆⟩ => ?_)
  obtain i₁₆ : Inv0 false s₀ s₁₆ := i₁₅.step k₁₆
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₁₆ (out := 48) (by omega_arith)) (by lit_decide))
    fun s₁₇ ⟨⟨k₁₇, tag₁₇⟩, v₁₇⟩ => ?_
  -- The tag computed.
  obtain e₈ : bytesAt s₇.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ - 16 * (L s₀ / 16)) =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (L s₀ / 16))) (L s₀ - 16 * (L s₀ / 16)) :=
    dat d₇ _ _ (by omega_arith)
  rw [e₈, List.append_assoc, split_pad (m := s₀.mem) (p := dp s₀) (Nat.mul_mod_right 16 _) hc16] at R₈
  obtain hP : ∀ r ∈ [oR false s₀], (sub s₀ 448 128).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.o.ctx.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))
  obtain R₁₄ : Repr s₁₄.mem (off (cx s₀) 448) (otk s₀)
      (M ++ (bytesAt s₀.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s₀.mem (dp s₀) (L s₀)))) := by
    refine Repr.frame k₁₄.frame (fun r hr => (hP r hr).symm.symm) ?_
    rw [m₁₃, m₁₂]
    refine Repr.frame k₁₁.frame (fun r hr => (hP r hr).symm.symm) ?_
    rw [m₁₀, m₉]; exact R₈
  obtain R₁₆ := Repr.frame k₁₆.frame (by rdisj_all) (r₁₅ _ _ R₁₄)
  obtain T₁₇ := tag₁₇ _ _ R₁₆
  obtain L₁₄ : bytesAt s₁₄.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame F (by
        intro r hr; simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact hp.o.ctx.sub_left (sub_ctx s₀ (by lit_omega))) (by lit_omega), len₃]
  rw [L₁₄] at T₁₇
  simp only [M, hA] at T₁₇
  obtain vec : ∀ r ∈ preservedV, (s₁₇.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 := by
    intro r hr
    obtain a₁ : (s₁₄.v r).extractLsb' 0 64 = (s₁₃.v r).extractLsb' 0 64 := v₁₄ r hr
    obtain a₂ : (s₁₃.v r).extractLsb' 0 64 = (s₁₁.v r).extractLsb' 0 64 := by rw [vv₁₃, vv₁₂]
    obtain a₃ : (s₁₁.v r).extractLsb' 0 64 = (s₁₀.v r).extractLsb' 0 64 := v₁₁ r hr
    obtain a₄ : (s₁₀.v r).extractLsb' 0 64 = (s₈.v r).extractLsb' 0 64 := by rw [vv₁₀, vv₉]
    obtain a₅ : (s₇.v r).extractLsb' 0 64 = (s₆.v r).extractLsb' 0 64 := by rw [vv₇]
    obtain a₆ : (s₅.v r).extractLsb' 0 64 = (s₄.v r).extractLsb' 0 64 := by rw [vv₅]
    exact (v₁₇ r hr).trans ((v₁₆ r hr).trans ((v₁₅ r hr).trans (a₁.trans (a₂.trans (a₃.trans (a₄.trans
      ((v₈ r hr).trans (a₅.trans ((v₆ r hr).trans (a₆.trans ((v₄ r hr).trans ((v₃ r hr).trans
      ((v₂ r hr).trans (v₁ r hr))))))))))))))
  refine ⟨i₁₆.step k₁₇ (fun r hr => ?_) (fun r hr => ?_), vec, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₁₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  -- The data decrypted.
  · have fin : ∀ i < L s₀, s₁₇.mem (op false s₀ + BitVec.ofNat 64 i) =
        s₁₄.mem (op false s₀ + BitVec.ofNat 64 i) :=
      fun i hi => by
        rw [out_frame k₁₇.frame (by rdisj_all) hi, out_frame k₁₆.frame (by rdisj_all) hi,
          out_frame k₁₅.frame (by rdisj_all) hi]
    -- The keystream of the first 448 bytes, from the stream.
    obtain ksA : ∀ i < 448, s₁₀.mem (kpAt s₀ 832 + BitVec.ofNat 64 i) = (KS1 s₀).getD i 0 := by
      intro i hi
      obtain e : kpAt s₀ 832 + BitVec.ofNat 64 i = off (cx s₀) 768 + BitVec.ofNat 64 (64 + i) := by
        simp only [kpAt]; rw [oo, oo]; congr 1; omega_arith
      obtain h512 : 64 + i < 512 := by omega_arith
      rw [e, m₁₀, m₉,
        k₈.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        f₇.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        f₆.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512, m₅,
        (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28)).bytes (R := sub s₀ 768 512)
          (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        k₄.frame.bytes (R := sub s₀ 768 512) (by rdisj_all) (show 512 ≤ 2 ^ 64 by decide) h512,
        ks₃ _ h512, ks8_eq s₀ (n := L s₀) (by omega_arith) hi]
    -- The keystream of the rest, from the kernel.
    obtain st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 8 (N s₀) := by
      rw [m₅, stateAt_frame (memIn_frame (s₀ := s₀) s₄.mem (s₄.gpr .x27) (s₄.gpr .x28)) (by rdisj_all), st₄]
    obtain ksB : ∀ j < L s₀ - 448, s₁₃.mem (kp' s₀ + BitVec.ofNat 64 j) = (KS1 s₀).getD (448 + j) 0 := by
      intro j hj
      obtain hj' : j < 256 := by omega_arith
      rw [m₁₃, m₁₂, k₁₁.frame.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
        m₁₀, m₉, k₈.frame.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
        f₇.bytes (R := sub s₀ 128 256) (by rdisj_all) (show 256 ≤ 2 ^ 64 by decide) hj',
        ks₆ j hj', st₅, ks_hi s₀ (by omega_arith)]
    rw [bytesAt_frame k₁₇.frame (by rdisj_all) hL', bytesAt_frame k₁₆.frame (by rdisj_all) hL',
      bytesAt_frame k₁₅.frame (by rdisj_all) hL', encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      obtain hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      obtain hDl : (bytesAt s₀.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
      obtain e1 : (bytesAt s₁₄.mem (op false s₀) (L s₀))[i] = s₁₄.mem (op false s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      obtain e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [D, bytesAt]
      obtain e3 : ∀ h : i < (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (D s₀).length).length,
          (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (D s₀).length)[i] = (KS1 s₀).getD i 0 :=
        fun h => by rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, D, hDl]
      rw [List.getElem_zipWith, e1, e2, e3]
      by_cases h448 : i < 448
      · have x := e₁₁ i h448
        simp only [Nat.zero_add] at x
        rw [f₁₄ _ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact not_restQ (P := 448) h448 (by omega_arith)),
          m₁₃, m₁₂, x, ksA i h448, m₁₀, d₉ i hi]
      · have x := e₁₄ (i - 448) (by omega_arith)
        rw [show 448 + (i - 448) = i by omega_arith] at x
        obtain nf : ¬ (⟨op false s₀ + BitVec.ofNat 64 0, 448⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 i) 1 :=
          fun hc => hp.o.sep (a := 0) (n := 448) (c := i) (m := 1) (by omega_arith) (by omega_arith) _ hc
            (Region.contains_self _ _)
        rw [x, ksB (i - 448) (by omega_arith), show 448 + (i - 448) = i by omega_arith, m₁₃, m₁₂,
          f₁₁ _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact nf), m₁₀, d₉ i hi]

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey
