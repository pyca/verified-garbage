module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
import VerifiedGarbage.Proof.Framework.ContractPost
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
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
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
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
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Zeroize.Common
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
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

@[expose] public section

section

/-!
# ChaCha20-Poly1305 on AArch64: correctness

`seal` and `open`, from their parts: the code up to the tag (`sealMain`,
`openMain`, and their stitched forms), which leaves what `MainS` and `MainO`
say, and then the tag (`sealTail`, `openTail`), the same for every backend.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_movz wp_ldr)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the additional data, the data and the tag. (Matching
only reducibly, so that a lemma that does not apply fails fast.) -/
tactic_template "rdisj" : tactic => `(tactic| first
  | (with_reducible refine sub_disj _ ?_ ?_ ?_ <;> lit_omega)
  | (with_reducible refine (‹APre _ _›).c_d.sub_left (sub_ctx _ ?_) <;> lit_omega)
  | (with_reducible refine (‹APre _ _›).c_d.symm.sub_right (sub_ctx _ ?_) <;> lit_omega)
  | (with_reducible refine (‹APre _ _›).c_a.symm.sub_right (sub_ctx _ ?_) <;> lit_omega)
  | with_reducible exact (‹APre _ _›).a_d
  | (with_reducible refine (‹APre _ _›).c_t.sub_left (sub_ctx _ ?_) <;> lit_omega)
  | (with_reducible refine (‹APre _ _›).c_t.symm.sub_right (sub_ctx _ ?_) <;> lit_omega)
  | with_reducible exact (‹APre _ _›).d_t
  | with_reducible exact (‹APre _ _›).d_t.symm)

/-- A region is disjoint from each of a list of regions. -/
tactic_template "rdisj_all" : tactic => `(tactic| (
                   simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
                   repeat' apply And.intro
                   all_goals rdisj))

theorem hRDX (s₀ : State) : s₀.gpr .x3 = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .x3).isLt, hp.wrap_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.a_rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .x5).isLt, hp.wrap_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.d_wr], hc⟩⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The callee-saved registers on return: those saved in the context are
restored, and the others were never changed. -/
theorem preserved_split : ∀ r ∈ preserved, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30, .x6] →
    r ∈ untouched ∧ r ≠ .x30 := by decide

theorem abi_of0 {s₀ s s₁ s' : State} (h : Inv0 s₀ s)
    (hk : ∀ r ∈ preserved, r ≠ .x30 → s₁.gpr r = s.gpr r)
    (hr : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s₀.gpr r)
    (hg : ∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30, .x6] → s'.gpr r = s₁.gpr r)
    (hsp : s'.sp = s.sp) : GprAbi s₀ s' := by
  refine ⟨fun r hr' => ?_, by rw [hsp, h.sp]⟩
  by_cases hm : r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30]
  · exact hr r hm
  · have hm' : r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30, .x6] := by
      intro h'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h' hm
      rcases h' with h' | h' | h' | h' | h' | h' | rfl
      · exact hm (.inl h')
      · exact hm (.inr (.inl h'))
      · exact hm (.inr (.inr (.inl h')))
      · exact hm (.inr (.inr (.inr (.inl h'))))
      · exact hm (.inr (.inr (.inr (.inr (.inl h')))))
      · exact hm (.inr (.inr (.inr (.inr (.inr h')))))
      · exact absurd hr' (by decide)
    have hu := preserved_split r hr' hm'
    rw [hg r hm', hk r hr' hu.2, h.un r hu.1]

/-! ## The tag -/

/-- What holds after `seal`'s code but the tag (`sealTail`). -/
structure MainS (s₀ s : State) : Prop where
  inv : Inv0 s₀ s
  vec : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀)
    (macData (A s₀) (Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)))
  ct : bytesAt s.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

/-- What holds after `open`'s code but the comparison of the tags
(`openTail`). -/
structure MainO (s₀ s : State) : Prop where
  inv : Inv0 s₀ s
  vec : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64
  tag : bytesAt s.mem (off (cx s₀) 48) 16 = mac (otk s₀) (macData (A s₀) (D s₀))
  pt : bytesAt s.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

/-- The address of `tag`, loaded from the context into `r`. -/
theorem tagPtr_ok {r : Reg} {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀)
    (hsv : Saved s₀ s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hk : ([Instr.ldr .x r .x21 624].all fun i => preserved.all fun r' => !clobbers i r') = true) :
    WP isa (.block [.ldr .x r .x21 624]) s fun s' => s'.gpr r = tp s₀ ∧ Kept [] s s' := by
  have hs : s.mem.readW (off (cx s₀) 624) 64 = tp s₀ := hsv (.x6, 624) (by decide)
  have h : WP isa (.block [.ldr .x r .x21 624]) s fun s' =>
      s'.gpr r = tp s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_ldr (a := off (cx s₀) 624) (by decide) (by rw [hx21]) (by rw [hrd, hwr]; exact hp.in_ctx' (by lit_omega))
      fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, hs], u₁.rd, u₁.wr, u₁.mem⟩
  exact WP.mono (WP.kept h hk) fun s' ⟨⟨h0, hrd', hwr', hm⟩, hg, hsp⟩ =>
    ⟨h0, Kept.of hg hsp hrd' hwr' (by rw [hm]; exact Frame.refl _ _)⟩

/-- `x0 = x21 + 448`, `x1 = 0` and `x3 = x21 + 632`. -/
theorem ftptrs_ok (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x3 .x21 632]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = s.gpr .x2 ∧ Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x3 .x21 632]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = s.gpr .x2 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ =>
      wp_addImm (by decide) fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr]; rfl,
        by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by rfl))
    fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- The tag written to `tag` (its address in `x2`). -/
theorem finalizeTag_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : Inv0 s₀ s)
    (hx2 : s.gpr .x2 = tp s₀) :
    WP isa finalizeTag s fun s' => Kept [sub s₀ 448 128, tR s₀] s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (tp s₀) 16 = mac key msg := by
  unfold finalizeTag
  refine WP.seq (WP.mono (ftptrs_ok s) fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0
  rw [hx2] at h2
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  have hw : Covers [sub s₀ 448 128, tR s₀] s₁.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁]; exact hp.ctx_wr, 448, rfl, by show 448 + 128 ≤ 1280; omega⟩
    · exact ⟨tR s₀, by rw [wr₁]; exact hp.t_wr, 0, by simp, by simp⟩
  refine finalize_call h0 h1 h2 (hp.c_t.sub_left (sub_ctx s₀ (by lit_omega))) (Covers.right hw) hw
    fun s₂ k₂ tag₂ => ?_
  exact ⟨(k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂,
    fun key msg hr => tag₂ key msg (by rw [m₁]; exact hr)⟩

theorem sealTail_ok {s₀ s : State} (hp : APre true s₀) (h : MainS s₀ s) :
    WP isa sealTail s fun s' => abiPreserved s₀ s' ∧ sealAArch64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold sealTail
  refine WP.seq (WP.mono (WP.preservedV (tagPtr_ok (r := .x2) hp h.inv.x21 h.inv.saved h.inv.rd h.inv.wr
    (by decide)) (by lit_decide)) fun s₁ ⟨⟨x2₁, k₁⟩, v₁⟩ => ?_)
  have i₁ : Inv0 s₀ s₁ := h.inv.step k₁ (fun _ hr => absurd hr List.not_mem_nil)
    (fun _ hr => absurd hr List.not_mem_nil)
  refine WP.seq (WP.mono (WP.preservedV (finalizeTag_ok hp i₁ x2₁) (by lit_decide)) fun s₂ ⟨⟨k₂, tag₂⟩, v₂⟩ => ?_)
  refine WP.mono (WP.preservedV (restore_ok hp (by rw [k₂.cs _ (pres .x21) (pres30 .x21), i₁.x21])
    (i₁.saved.frame k₂.frame (by rdisj_all)) (by rw [k₂.rd, i₁.rd]) (by rw [k₂.wr, i₁.wr])) (by lit_decide))
    fun s₃ ⟨⟨⟨rs₃, g₃, m₃⟩, sp₃⟩, v₃⟩ => ?_
  have hg := abi_of0 i₁ k₂.cs rs₃ g₃ (by rw [sp₃, k₂.sp])
  refine ⟨⟨hg.1, hg.2, fun r hr => (v₃ r hr).trans ((v₂ r hr).trans ((v₁ r hr).trans (h.vec r hr)))⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₃.mem (dp s₀) (L s₀), bytesAt s₃.mem (tp s₀) 16)
  rw [m₃, tag₂ _ _ (by rw [k₁.mem_eq]; exact h.poly), bytesAt_frame k₂.frame (by rdisj_all) hL', k₁.mem_eq, h.ct]
  rfl

theorem eval_zero_w (s : State) (r : Reg) :
    isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  simp [eval, State.read]

theorem ofNat64_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- One step of `zeroData`'s loop: the byte at `data + j` zeroed, with `x11`
zero and `x9` at it. -/
theorem zeroStep_ok {s₀ : State} (hp : APre false s₀) {u : State} (hwr : u.wr = s₀.wr) {j : Nat}
    (hj : j < L s₀) (h11 : u.gpr .x11 = 0) (h9 : u.gpr .x9 = off (dp s₀) j)
    (hz : Proof.Zeroize.Prefix u.mem (dp s₀) j) :
    WP isa (.block [.strb .x11 .x9 0, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]) u fun u' =>
      u'.gpr .x9 = off (dp s₀) (j + 1) ∧ u'.gpr .x10 = u.gpr .x10 - 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      Frame [dR s₀] u.mem u'.mem ∧ Proof.Zeroize.Prefix u'.mem (dp s₀) (j + 1) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have hc : (dR s₀).Contains (off (dp s₀) j) 1 := Offset.contains_base _ (by omega) (by omega)
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_strb (by decide) (by rw [h9]; exact BitVec.add_zero _)
    ⟨dR s₀, by rw [hwr]; exact hp.d_wr, hc⟩ fun u₁ m₁ =>
    wp_addImm (by decide) fun u₂ v₂ => VG.Proof.ChaCha20.AArch64.Xor.wp_subImm (by decide) fun u₃ v₃ =>
    WP.block_nil ?_
  refine ⟨?_, ?_, fun r a b => ?_, by rw [v₃.rd, v₂.rd, m₁.rd], by rw [v₃.wr, v₂.wr, m₁.wr], ?_, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, h9, off, off, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr]; rfl
  · rw [v₃.other r b, v₂.other r a, m₁.gpr]
  · rw [v₃.mem, v₂.mem, m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc
  · rw [v₃.mem, v₂.mem, m₁.mem, h11, show BitVec.setWidth 8 (0 : BitVec 64) = 0 by decide]
    exact Proof.Zeroize.prefix_writeW hz (by omega)

/-- `zeroLoad`: `data`, `len` and zero, from after the context. -/
theorem zeroLoad_ok {s₀ : State} (hp : APre false s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hd : s.mem.readW (off (cx s₀) 1280) 64 = dp s₀)
    (hl : s.mem.readW (off (cx s₀) 1288) 64 = s₀.gpr .x5) :
    WP isa (.block zeroLoad) s fun u => u.gpr .x9 = dp s₀ ∧ u.gpr .x10 = s₀.gpr .x5 ∧ u.gpr .x11 = 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      u.mem = s.mem := by
  have hin : ∀ {u : State} (d : Nat), u.rd = s₀.rd → u.wr = s₀.wr → 1280 ≤ d → d + 8 ≤ 1296 →
      InRegions (u.rd ++ u.wr) (off (cx s₀) d) 8 := fun d hr hw h1 h2 =>
    ⟨slotR s₀, List.mem_append_right _ (by rw [hw, hp.wr]; simp),
      Offset.contains (cx s₀) h1 (by omega) (by decide)⟩
  unfold zeroLoad
  refine wp_ldr (a := off (cx s₀) 1280) (by decide) (by rw [hx21]) (hin 1280 hrd hwr (Nat.le_refl _) (by decide))
    fun u₁ v₁ => wp_ldr (a := off (cx s₀) 1288) (by decide) (by rw [v₁.other _ (by decide), hx21])
      (hin 1288 (by rw [v₁.rd, hrd]) (by rw [v₁.wr, hwr]) (by decide) (by decide)) fun u₂ v₂ =>
    wp_movz fun u₃ v₃ => WP.block_nil ⟨?_, ?_, ?_, fun r a b c => ?_, by rw [v₃.rd, v₂.rd, v₁.rd],
      by rw [v₃.wr, v₂.wr, v₁.wr], by rw [v₃.mem, v₂.mem, v₁.mem]⟩
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hd]
  · rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, hl]
  · rw [v₃.gpr]; rfl
  · rw [v₃.other r c, v₂.other r b, v₁.other r a]

/-- `zeroData`, with `data` and `len` saved after the context: zeros at
`data`, and only `x9`–`x11` and the data written. -/
theorem zeroData_ok {s₀ : State} (hp : APre false s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hd : s.mem.readW (off (cx s₀) 1280) 64 = dp s₀)
    (hl : s.mem.readW (off (cx s₀) 1288) 64 = s₀.gpr .x5) :
    WP isa zeroData s fun s' => bytesAt s'.mem (dp s₀) (L s₀) = List.replicate (L s₀) 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [dR s₀] s.mem s'.mem := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  unfold zeroData zeroLoop
  refine WP.seq (WP.mono (zeroLoad_ok hp hx21 hrd hwr hd hl)
    fun u₃ ⟨x9₃, x10₃, x11₃, o₃, rd₃, wr₃, m₃⟩ => ?_)
  by_cases hz : L s₀ = 0
  · have h0 : s₀.gpr .x5 = 0 := BitVec.eq_of_toNat_eq hz
    refine WP.ite true (by rw [show isa.eval (.zero .x .x10) u₃ = some (u₃.gpr .x10 == 0) from
      VG.Proof.ChaCha20.AArch64.Xor.eval_zero _ _, x10₃, h0]; rfl) (fun _ => WP.block_nil ⟨?_, o₃, rd₃, wr₃,
      by rw [m₃]; exact Frame.refl _ _⟩) (by simp)
    rw [hz]; rfl
  · have hne : s₀.gpr .x5 ≠ 0 := fun e => hz (by simp [L, e])
    refine WP.ite false (by rw [show isa.eval (.zero .x .x10) u₃ = some (u₃.gpr .x10 == 0) from
      VG.Proof.ChaCha20.AArch64.Xor.eval_zero _ _, x10₃, beq_false_of_ne hne]) (by simp) fun _ => ?_
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < L s₀ ∧ rem = L s₀ - j ∧ u.gpr .x11 = 0 ∧
      u.gpr .x9 = off (dp s₀) j ∧ u.gpr .x10 = BitVec.ofNat 64 (L s₀ - j) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      Frame [dR s₀] s.mem u.mem ∧ Proof.Zeroize.Prefix u.mem (dp s₀) j) ?_ (L s₀) u₃
      ⟨0, by omega, by omega, x11₃, by rw [x9₃]; exact (BitVec.add_zero _).symm,
        by rw [x10₃, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq], o₃, rd₃, wr₃,
        by rw [m₃]; exact Frame.refl _ _, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem u ⟨j, hj, hr, e11, e9, e10, ho, erd, ewr, hf, hpz⟩
    refine WP.mono (zeroStep_ok hp (by rw [ewr, hwr]) hj e11 e9 hpz)
      fun u' ⟨x9', x10', o', rd', wr', f', p'⟩ => ?_
    have hsub : BitVec.ofNat 64 (L s₀ - j) - 1 = BitVec.ofNat 64 (L s₀ - (j + 1)) := by
      rw [ofNat64_sub_one (by omega) (by omega), Nat.sub_sub]
    rw [e10, hsub] at x10'
    have o'' : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → u'.gpr r = s.gpr r := fun r a b c => by
      rw [o' r a b, ho r a b c]
    have f'' : Frame [dR s₀] s.mem u'.mem := hf.trans f'
    by_cases he : j + 1 = L s₀
    · left
      refine ⟨by rw [VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero_ofNat _ _ (by omega) x10', he, Nat.sub_self]; rfl,
        ?_, o'', by rw [rd', erd], by rw [wr', ewr], f''⟩
      rw [he] at p'
      exact Proof.Zeroize.prefix_spec p'
    · right
      refine ⟨by rw [VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero_ofNat _ _ (by omega) x10']; simp; omega,
        L s₀ - (j + 1), by omega, j + 1, by omega, rfl, by rw [o' _ (by decide) (by decide), e11], x9', x10',
        o'', by rw [rd', erd], by rw [wr', ewr], f'', p'⟩

/-- `data` and `len`, saved after the context, survive the code up to the tag. -/
theorem MainO.slot {s₀ s : State} (hp : APre false s₀) (h : MainO s₀ s) {d : Nat} (h1 : 1280 ≤ d)
    (h2 : d + 8 ≤ 1296) : s.mem.readW (off (cx s₀) d) 64 = s₀.mem.readW (off (cx s₀) d) 64 := by
  have hs := hp.slot rfl
  refine h.inv.frame.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint (cx s₀) (.inr (by omega)) (by have := hs.wrap_s; omega)
      (by have := hs.wrap_s; omega)
  · exact hs.s_d.sub_left (Offset.sub (cx s₀) h1 (by omega))

/-- The tag computed and the one received, after the code up to the tag. -/
theorem MainO.tags {s₀ s u : State} (hp : APre false s₀) (h : MainO s₀ s) (hm : u.mem = s.mem) :
    bytesAt u.mem (off (cx s₀) 48) 16 = mac (otk s₀) (macData (A s₀) (D s₀)) ∧
      bytesAt u.mem (tp s₀) 16 = T0 s₀ :=
  ⟨by rw [hm, h.tag], by rw [hm, bytesAt_frame h.inv.frame (by rdisj_all) (by lit_omega)]⟩

theorem ok_iff (s₀ : State) :
    okAArch64 s₀ = true ↔ mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ := by
  show (Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀)).isSome = true ↔ _
  constructor
  · intro h
    obtain ⟨pt, hpt⟩ := Option.isSome_iff_exists.mp h
    exact (decrypt_eq_some hpt).1
  · intro h
    cases hd : Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | none => exact absurd h (decrypt_eq_none hd)
    | some _ => rfl

/-- The branch to `zeroData`: `x21` and the stack pointer kept. -/
theorem zeroIte_ok {s₀ : State} (hp : APre false s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hd : s.mem.readW (off (cx s₀) 1280) 64 = dp s₀)
    (hl : s.mem.readW (off (cx s₀) 1288) 64 = s₀.gpr .x5) :
    WP isa (.ite (.zero .w .x0) zeroData (.block [])) s fun s' => s'.gpr .x21 = s.gpr .x21 ∧ s'.sp = s.sp := by
  cases hb : ((s.gpr .x0).setWidth 32 == 0)
  · exact WP.ite false (by rw [eval_zero_w, hb]) (by simp) fun _ => WP.block_nil ⟨rfl, rfl⟩
  · refine WP.ite true (by rw [eval_zero_w, hb]) (fun _ => ?_) (by simp)
    exact WP.mono (WP.withSp (zeroData_ok hp hx21 hrd hwr hd hl)) fun _ ⟨⟨_, o, _⟩, sp⟩ =>
      ⟨o _ (by decide) (by decide) (by decide), sp⟩

/-- The tags compared, the data zeroed if they differ, and the registers
restored, with `data` and `len` saved after the context on entry
(`saveData`). -/
theorem openTail_ok {s₀ s : State} (hp : APre false s₀) (h : MainO s₀ s)
    (hd : s₀.mem.readW (off (cx s₀) 1280) 64 = dp s₀)
    (hl : s₀.mem.readW (off (cx s₀) 1288) 64 = s₀.gpr .x5) :
    WP isa openTail s fun s' => abiPreserved s₀ s' ∧ openAArch64.post s₀ s' := by
  unfold openTail
  refine WP.seq (WP.mono (WP.preservedV (tagPtr_ok (r := .x12) hp h.inv.x21 h.inv.saved
    h.inv.rd h.inv.wr (by decide)) (by lit_decide)) fun s₁ ⟨⟨x12₁, k₁⟩, v₁⟩ => ?_)
  have m₁ := k₁.mem_eq
  have x21₁ : s₁.gpr .x21 = cx s₀ := by rw [k₁.cs _ (pres .x21) (pres30 .x21), h.inv.x21]
  refine WP.seq (WP.mono (WP.preservedV (compare_ok hp x21₁ x12₁ (by rw [k₁.rd, h.inv.rd])
    (by rw [k₁.wr, h.inv.wr])) (by lit_decide)) fun s₂ ⟨⟨rax₂, g₂, sp₂, m₂, rd₂, wr₂⟩, v₂⟩ => ?_)
  have T0₁ : bytesAt s₁.mem (tp s₀) 16 = T0 s₀ := by
    rw [m₁, bytesAt_frame h.inv.frame (by rdisj_all) (by lit_omega)]
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₁.mem (off (cx s₀) 48) 16 := by
    rw [m₁, h.tag]
  have x21₂ : s₂.gpr .x21 = cx s₀ := by rw [g₂ _ (pres .x21), x21₁]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, k₁.rd, h.inv.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, k₁.wr, h.inv.wr]
  have hk₂ : ∀ r ∈ preserved, r ≠ .x30 → s₂.gpr r = s.gpr r := fun r hr h30 => by
    rw [g₂ r hr, k₁.cs r hr h30]
  -- The end, from a state that keeps what `restore` and the ABI need.
  have fin : ∀ {u : State}, u.gpr .x21 = cx s₀ → Saved s₀ u.mem → u.rd = s₀.rd → u.wr = s₀.wr →
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = s.gpr r) → u.sp = s.sp →
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) →
      WP isa (.block restore) u fun s' => abiPreserved s₀ s' ∧ s'.gpr .x0 = u.gpr .x0 ∧ s'.mem = u.mem :=
    fun {u} x21 sv rd wr hk sp vv =>
    WP.mono (WP.preservedV (restore_ok hp x21 sv rd wr) (by lit_decide))
      fun s₃ ⟨⟨⟨rs₃, g₃, m₃⟩, sp₃⟩, v₃⟩ => by
      have hg := abi_of0 h.inv hk rs₃ g₃ (by rw [sp₃, sp])
      exact ⟨⟨hg.1, hg.2, fun r hr => (v₃ r hr).trans (vv r hr)⟩, g₃ .x0 (by decide), m₃⟩
  have vv₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 :=
    fun r hr => (v₂ r hr).trans ((v₁ r hr).trans (h.vec r hr))
  have sp₂' : s₂.sp = s.sp := by rw [sp₂, k₁.sp]
  have sv₂ : Saved s₀ s₂.mem := by rw [m₂, m₁]; exact h.inv.saved
  rw [m₁] at rax₂ hm T0₁
  by_cases hc : mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀
  · have he : bytesAt s.mem (off (cx s₀) 48) 16 = bytesAt s.mem (tp s₀) 16 := by rw [← hm, T0₁, hc]
    simp only [he, ↓reduceIte] at rax₂
    refine WP.seq (WP.ite false (by rw [eval_zero_w, rax₂]; rfl) (by simp) fun _ => WP.block_nil ?_)
    refine WP.mono (fin x21₂ sv₂ rd₂' wr₂' hk₂ sp₂' vv₂) fun s₃ ⟨ha, x0₃, m₃⟩ => ⟨ha, ?_⟩
    rw [openAArch64, Contract.post_mk]
    split
    next pt hpt =>
      obtain ⟨-, rfl⟩ := decrypt_eq_some hpt
      exact ⟨by rw [x0₃, rax₂], by rw [m₃, m₂, m₁, h.pt]⟩
    next hn => exact absurd hc (decrypt_eq_none hn)
  · have he : bytesAt s.mem (off (cx s₀) 48) 16 ≠ bytesAt s.mem (tp s₀) 16 := fun e => hc (by rw [hm, e, T0₁])
    simp only [he, ↓reduceIte] at rax₂
    refine WP.seq (WP.ite true (by rw [eval_zero_w, rax₂]; rfl) (fun _ => ?_) (by simp))
    refine WP.mono (WP.withSp (WP.preservedV (zeroData_ok hp x21₂ rd₂' wr₂'
      (by rw [m₂, m₁, h.slot hp (Nat.le_refl _) (by decide), hd]) (by rw [m₂, m₁, h.slot hp (by decide) (by decide), hl]))
      (by lit_decide))) fun s₃ ⟨⟨⟨z₃, o₃, rd₃, wr₃, f₃⟩, v₃⟩, sp₃⟩ => ?_
    refine WP.mono (fin (by rw [o₃ _ (by decide) (by decide) (by decide), x21₂])
      (sv₂.frame f₃ (by rdisj_all)) (by rw [rd₃, rd₂']) (by rw [wr₃, wr₂'])
      (fun r hr h30 => by
        rw [o₃ r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)
          (by rintro rfl; simp [preserved] at hr), hk₂ r hr h30])
      (by rw [sp₃, sp₂']) (fun r hr => (v₃ r hr).trans (vv₂ r hr))) fun s₄ ⟨ha, x0₄, m₄⟩ => ⟨ha, ?_⟩
    rw [openAArch64, Contract.post_mk]
    split
    next pt hpt => exact absurd (decrypt_eq_some hpt).1 hc
    next hn => exact ⟨by rw [x0₄, o₃ _ (by decide) (by decide) (by decide), rax₂], by rw [m₄, z₃]⟩

/-! ## The scalar backend -/

/-- What the step that encrypts or decrypts the data leaves (`cryptWith`,
`Pad.cryptPad`): the data encrypted from block counter 1. -/
def CryptPost (s₀ s s' : State) : Prop :=
  (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ Inv s₀ s' ∧
    Kept [sub s₀ 64 384, dR s₀, sub s₀ 768 512] s s' ∧
    bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))

/-- `crypt` meets `CryptPost` from any state between the parts with the
state for counter 0 at `ctx + 64`. -/
def CryptOk (s₀ : State) (crypt : Prog isa) : Prop :=
  ∀ s, Inv s₀ s → stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) →
    WP isa crypt s (CryptPost s₀ s)

theorem cryptWith_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) :
    CryptOk s₀ (cryptWith v.callee) := fun _ h hst =>
  (crypt_ok v hp h hst).mono fun _ ⟨v', i', k', c'⟩ => ⟨v', i', k'.sub fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp, fun _ h => h⟩, c'⟩

theorem sealMainWith_ok {crypt : Prog isa} {s₀ : State} (hp : APre true s₀) (hc : CryptOk s₀ crypt) :
    WP isa (sealMainWith crypt) s₀ (MainS s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold sealMainWith
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.x21
    h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono (hc s₃ i₃ st₃) fun s₄ ⟨v₄, i₄, k₄, ct₄⟩ => ?_)
  rw [D₃] at ct₄
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

theorem openMainWith_ok {crypt : Prog isa} {s₀ : State} (hp : APre false s₀) (hc : CryptOk s₀ crypt) :
    WP isa (openMainWith crypt) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold openMainWith
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
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
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₅.frame (by rdisj_all), stateAt_frame k₄.frame (by rdisj_all),
      stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  refine WP.seq (WP.mono (hc s₅ i₅ st₅) fun s₆ ⟨v₆, i₆, k₆, pt₆⟩ => ?_)
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
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', pt₆, bytesAt_frame k₅.frame (by rdisj_all) hL',
      bytesAt_frame k₄.frame (by rdisj_all) hL', bytesAt_frame k₃.frame (by rdisj_all) hL', D₂]

theorem sealMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealMain v.callee) s₀ (MainS s₀) :=
  sealMainWith_ok hp (cryptWith_ok v hp)

theorem openMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openMain v.callee) s₀ (MainO s₀) :=
  openMainWith_ok hp (cryptWith_ok v hp)

end VG.Proof.ChaCha20Poly1305.AArch64

end
