module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypt
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts

/-!
# ChaCha20-Poly1305 on AArch64: `open` from 449 to 511 bytes

`OpenPad.openMain`: after the prologue, the additional data and the lengths
block, `ctx[704, 1280)` is zeroed and the stream's arguments set (`args`), with
the keystream's buffer at `ctx + 256 + len` and the data's address in `x2`;
then `polyIn`, the chunk that computes the keystream of counters 1 to 8 into
the buffer while absorbing the data's first 448 bytes (`Stitch.bulkPad_ok`),
and `polyOut`; the data's address and its length are recovered from `x2`
and the buffer's address (`recover`); the rest of the data is absorbed with
its padding, then the lengths block; the data is XORed with the keystream
(`xorKsWithAt_ok`), the buffer zeroed again, and the tag computed.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenPad

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.OpenPad
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_subImm wp_sub wp_mov wp_lsr wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (ZeroedAt zeroAt_ok kpAt)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.ChaCha20Poly1305 (pad16 macData)

variable {e : Bool}

/-- `OpenPad.zero`: `ctx[704, 1280)` zeroed. -/
theorem zero_ok {s₀ s : State} (hp : APre e s₀) (hx21 : s.gpr .x21 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block zero) s fun s' => Kept [sub s₀ 704 576] s s' ∧
      ZeroedAt (cx s₀) 704 36 s.mem s'.mem ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have hv0 : ∀ r ∈ preservedV, r ≠ .v0 := by decide
  refine WP.mono (zeroAt_ok (b := 704) (J := 36) (by decide) (by decide) hx21 fun a ha => by
    rw [hwr]; exact hp.in_ctx (a := 704 + a) (by omega_arith)) fun s' ⟨g, rd, wr, sp, v, z⟩ =>
      ⟨Kept.of (fun r _ => by rw [g]) sp rd wr (z.frame (by decide)), z,
        fun r hr => by rw [v r (hv0 r hr)]⟩

/-- The stream's arguments, with the counter set to 1 and the buffer at
`ctx + 256 + len`. -/
theorem args_ok {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) :
    WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) (256 + L s₀) ∧ s'.gpr .x2 = dp s₀ ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ Kept [sub s₀ 64 64] s s' := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block args) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = off (cx s₀) (256 + L s₀) ∧ s'.gpr .x2 = dp s₀ ∧
      s'.gpr .x3 = off (cx s₀) 128 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_add fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
      wp_mov fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, one32]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
        u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.x21,
        h.x23, hL, off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x22]
    · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x21]
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core rfl)
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

/-- The data's address and length, and the rest after 448 bytes, from
`polyOut false`'s `x22` (the buffer) and `x23` (the data). -/
theorem recover_ok {s₀ s : State} (h449 : 449 ≤ L s₀) (h511 : L s₀ ≤ 511)
    (hx21 : s.gpr .x21 = cx s₀) (hx22 : s.gpr .x22 = off (cx s₀) (256 + L s₀))
    (hx23 : s.gpr .x23 = dp s₀) :
    WP isa (.block recover) s fun s' => s'.gpr .x22 = dp s₀ ∧
      s'.gpr .x23 = BitVec.ofNat 64 (L s₀) ∧ s'.gpr .x24 = dp s₀ + BitVec.ofNat 64 448 ∧
      s'.gpr .x25 = BitVec.ofNat 64 (L s₀ - 448) ∧
      (∀ r, r ∉ [Reg.x22, .x23, .x24, .x25] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_sub fun s₁ u₁ => wp_subImm (by decide) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have x25₂ : s₂.gpr .x25 = BitVec.ofNat 64 (L s₀ - 448) := by
    rw [u₂.gpr, u₁.gpr, hx22, hx21, off, Offset.add_sub_cancel_left, Offset.ofNat_sub_ofNat (by omega_arith),
      show 256 + L s₀ - 704 = L s₀ - 448 by omega_arith]
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hx23]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), x25₂, ← BitVec.ofNat_add,
      show L s₀ - 448 + 448 = L s₀ by omega_arith]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx23]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x25₂]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h22, h23, h24, h25⟩ := hr
    rw [u₅.other _ h23, u₄.other _ h24, u₃.other _ h22, u₂.other _ h25, u₁.other _ h25]

/-- `xorKs`'s setup: the data in `x9`, the keystream at `ctx + 256 + len` in
`x10`, and `len / 16` in `x11`. -/
theorem xsetup_ok {s₀ s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hx22 : s.gpr .x22 = dp s₀) (hx23 : s.gpr .x23 = BitVec.ofNat 64 (L s₀)) :
    WP isa (.block [mov .x9 .x22, .add .x .x10 .x21 .x23, .addImm .x .x10 .x10 256, .lsr .x .x11 .x23 4]) s
      fun s' => s'.gpr .x9 = dp s₀ + BitVec.ofNat 64 0 ∧ s'.gpr .x10 = kpAt s₀ (256 + L s₀) ∧
        s'.gpr .x11 = BitVec.ofNat 64 (L s₀ / 16) ∧
        Kept [] s s' ∧ ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r := by
  have hn : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have h : WP isa (.block [mov .x9 .x22, .add .x .x10 .x21 .x23, .addImm .x .x10 .x10 256,
      .lsr .x .x11 .x23 4]) s fun s' =>
      s'.gpr .x9 = dp s₀ + BitVec.ofNat 64 0 ∧ s'.gpr .x10 = kpAt s₀ (256 + L s₀) ∧
      s'.gpr .x11 = BitVec.ofNat 64 (L s₀ / 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r :=
    wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => wp_addImm (by decide) fun s₃ u₃ => wp_lsr (by decide)
      fun s₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx22,
          BitVec.add_zero],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide),
          hx21, hx23, kpAt, off, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx23,
          shr4_ofNat hn],
        by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem],
        fun r h9 h10 h11 => by rw [u₄.other _ h11, u₃.other _ h10, u₂.other _ h10, u₁.other _ h9]⟩
  exact WP.mono (WP.kept h rfl) fun s' ⟨⟨h9, h10, h11, hrd, hwr, hm, hg'⟩, hg, hsp⟩ =>
    ⟨h9, h10, h11, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hg'⟩

theorem bulkPad_otherV (sve : Bool) :
    (Stitch.bulkPad sve).allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by
  cases sve
  · show Stitch.bulkPadNeon.allInstrs _ = true; lit_decide
  · show Stitch.bulkPadSve.allInstrs _ = true; lit_decide

/-- `bulkPad`'s precondition, after `args` and `polyIn`. -/
theorem padPre_of {s₀ s : State} (hp : APre false s₀) (h449 : 449 ≤ L s₀) (h511 : L s₀ ≤ 511)
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = off (cx s₀) (256 + L s₀))
    (hx2 : s.gpr .x2 = dp s₀) (hx3 : s.gpr .x3 = off (cx s₀) 128) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) : Stitch.PadPre s := by
  have hsr : VG.Proof.ChaCha20.AArch64.Mixed8.sr s = sub s₀ 64 64 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.sr, hx0]
  have hbr : VG.Proof.ChaCha20.AArch64.Mixed8.br s = sub s₀ 128 320 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.br, hx3]
  have hdr : VG.Proof.ChaCha20.AArch64.Mixed8.dr s = sub s₀ (256 + L s₀) 512 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.dr, hx1]
  have hw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  refine ⟨fun k => ?_, fun k => ?_, ?_, fun d n h => ?_, fun d n h => ?_, ?_, ?_, ?_, ?_,
    fun d h => ?_, fun r hr => ?_⟩
  · rw [hw, hx0, Short.off_add]; exact hp.in_ctx' (by have := k.isLt; omega_arith)
  · rw [hw, hx0, Short.off_add]; exact hp.in_ctx' (by have := Nat.mod_lt k.val (show 4 > 0 by decide); omega_arith)
  · rw [hwr, hx0, Short.off_add]; exact hp.in_ctx (by decide)
  · rw [hwr, hx3, Short.off_add]; exact hp.in_ctx (by omega_arith)
  · rw [hwr, hx1, Short.off_add]; exact hp.in_ctx (by omega_arith)
  · rw [hsr, hbr]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [hsr, hdr]; exact sub_disj s₀ (by omega_arith) (by lit_omega) (by omega_arith)
  · rw [hdr, hbr]; exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)
  · rw [hx3, hx0]; exact (off_off _ 64 64).symm
  · rw [hx2, hw]
    exact ⟨dR s₀, by simp [hp.d_wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [hx2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have hs : (⟨dp s₀, 448⟩ : Region).Sub (dR s₀) := Region.sub_prefix (by omega_arith)
    rcases hr with rfl | rfl
    · rw [hsr]; exact (hp.c_d.symm.sub_left hs).sub_right (sub_ctx s₀ (by lit_omega))
    · rw [hbr]; exact (hp.c_d.symm.sub_left hs).sub_right (sub_ctx s₀ (by lit_omega))

/-- What `open` leaves after the chunk and `recover`, from `s` after the
lengths. -/
structure Crypted (s₀ s : State) (key msg : List Byte) (u : State) : Prop where
  inv : Inv0 s₀ u
  x22 : u.gpr .x22 = dp s₀
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀)
  x24 : u.gpr .x24 = dp s₀ + BitVec.ofNat 64 448
  x25 : u.gpr .x25 = BitVec.ofNat 64 (L s₀ - 448)
  frame : Frame [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576] s.mem u.mem
  ks : ∀ i < L s₀, u.mem (off (cx s₀) (256 + L s₀) + BitVec.ofNat 64 i) =
    (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0
  mac : Repr u.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) 448)
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem crypt_ok (sve : Bool) {s₀ : State} (hp : APre false s₀) (h449 : 449 ≤ L s₀) (h511 : L s₀ ≤ 511)
    {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg)
    {rest : Prog isa} {Q : State → Prop} (k : ∀ u, Crypted s₀ s key msg u → WP isa rest u Q) :
    WP isa (.seq (.block (zero ++ args ++ polyIn)) (.seq (Stitch.bulkPad sve)
      (.seq (.block (polyOut false ++ recover)) rest))) s Q := by
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt (s₀.gpr .x5).isLt
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (zero_ok hp h.x21 h.wr)
    fun s₄ ⟨k₄, z₄, v₄⟩ => ?_)))
  have i₄ : Inv s₀ s₄ := h.step1 k₄ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (WP.preservedV (args_ok hp i₄) (by lit_decide))
    fun s₅ ⟨⟨m₅, x0₅, x1₅, x2₅, x3₅, k₅⟩, v₅⟩ => ?_
  have i₅ : Inv s₀ s₅ := i₄.step1 k₅ (by omega_arith) (by omega_arith) (by omega_arith)
  refine (polyIn_ok hp i₅.x21 i₅.rd i₅.wr).mono
    fun s₆ ⟨⟨a21, a22, a23, m₆, g₆, rd₆, wr₆⟩, v₆, sp₆, _, _⟩ => ?_
  have x0₆ : s₆.gpr .x0 = off (cx s₀) 64 := by rw [g₆ _ (by decide), x0₅]
  have x1₆ : s₆.gpr .x1 = off (cx s₀) (256 + L s₀) := by rw [g₆ _ (by decide), x1₅]
  have x2₆ : s₆.gpr .x2 = dp s₀ := by rw [g₆ _ (by decide), x2₅]
  have x3₆ : s₆.gpr .x3 = off (cx s₀) 128 := by rw [g₆ _ (by decide), x3₅]
  have hr₅ : Repr s₅.mem (off (cx s₀) 448) key msg :=
    Repr.frame k₅.frame (by rdisj_all) (Repr.frame k₄.frame (by rdisj_all) hr)
  have ha := acc_in hr₅ x0₆ a21 a22 a23 m₆
  have pre : Stitch.PadPre s₆ := padPre_of hp h449 h511 x0₆ x1₆ x2₆ x3₆ (rd₆.trans i₅.rd)
    (wr₆.trans i₅.wr)
  -- The chunk.
  refine WP.seq ((WP.otherV (Stitch.bulkPad_ok (sve := sve) s₆ pre ha) (bulkPad_otherV sve)).mono
    fun s₇ ⟨hB, ov₇⟩ => ?_)
  -- `polyOut` and `recover`.
  refine WP.seq (WP.block_append ((polyOut_ok hp false (by rw [hB.x0, x0₆])
    (by rw [hB.rd, rd₆, i₅.rd]) (by rw [hB.wr, wr₆, i₅.wr])).mono
    fun s₈ ⟨⟨hv₈, m₈, x21₈, x27₈, x28₈, x22₈, x23₈, g₈, rd₈, wr₈⟩, vv₈, sp₈, _, _⟩ => ?_))
  refine (WP.preservedV (WP.withSp (recover_ok h449 h511 x21₈
    (by rw [x22₈]; show s₇.gpr .x1 = _; rw [hB.x1, x1₆])
    (by rw [x23₈]; show s₇.gpr .x2 = _; rw [hB.x2, x2₆]))) (by lit_decide)).mono
    fun s₉ ⟨⟨⟨x22₉, x23₉, x24₉, x25₉, g₉, m₉, rd₉, wr₉⟩, sp₉⟩, v₉⟩ => k s₉ ?_
  -- Memory.
  have hsr : VG.Proof.ChaCha20.AArch64.Mixed8.sr s₆ = sub s₀ 64 64 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.sr, x0₆]
  have hbr : VG.Proof.ChaCha20.AArch64.Mixed8.br s₆ = sub s₀ 128 320 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.br, x3₆]
  have hdr : VG.Proof.ChaCha20.AArch64.Mixed8.dr s₆ = sub s₀ (256 + L s₀) 512 := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.dr, x1₆]
  have f₅₆ : Frame (inR s₀) s₅.mem s₆.mem := by rw [m₆]; exact memIn_frame _ _ _
  have f₆₇ : Frame [sub s₀ 64 64, sub s₀ 128 320, sub s₀ (256 + L s₀) 512] s₆.mem s₇.mem := by
    have f := hB.frame; rw [hsr, hbr, hdr] at f; exact f
  have f₇₈ : Frame [sub s₀ 448 24] s₇.mem s₈.mem := by rw [m₈]; exact storeHm_frame _ _ _ _ _
  have hF : Frame [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576] s.mem s₉.mem := by
    have e (r : Region) (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) (hr : r = sub s₀ k n) :
        ∃ r' ∈ [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576], Region.Sub r r' :=
      ⟨sub s₀ 64 408, by simp, hr ▸ sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩
    rw [m₉]
    refine ((k₄.frame.sub ?_).trans (k₅.frame.sub ?_)).trans
      ((f₅₆.sub ?_).trans ((f₆₇.sub ?_).trans (f₇₈.sub ?_))) <;>
      intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · exact ⟨sub s₀ 704 576, by simp, hr ▸ fun _ h => h⟩
    · exact e r 64 64 (by decide) (by decide) hr
    · rcases hr with hr | hr
      · exact e r 288 16 (by decide) (by decide) hr
      · exact ⟨sub s₀ 32 16, by simp, hr ▸ fun _ h => h⟩
    · rcases hr with hr | hr | hr
      · exact e r 64 64 (by decide) (by decide) hr
      · exact e r 128 320 (by decide) (by decide) hr
      · subst hr; exact ⟨sub s₀ 704 576, by simp, sub_sub s₀ (by omega_arith) (by omega_arith) (by lit_omega)⟩
    · exact e r 448 24 (by decide) (by decide) hr
  have hFd : ∀ r ∈ [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact data_ctx hp (by lit_omega)
  -- The callee-saved registers.
  have r₇ (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₇.mem.readW (off (cx s₀) d) 64 = s₆.mem.readW (off (cx s₀) d) 64 := by
    refine f₆₇.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hd with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      exact sub_disj s₀ (by omega_arith) (by lit_omega) (by omega_arith)
  have un₉ : ∀ r ∈ untouched, s₉.gpr r = s₀.gpr r := by
    intro r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    have via (r : Reg) (hc : r ∈ preserved) (hn : r ∉ Stitch.accRegs)
        (h9 : r ∉ [Reg.x22, .x23, .x24, .x25])
        (h8 : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28])
        (h6 : r ∉ [Reg.x21, .x22, .x23, .x24, .x25]) (hu : r ∈ untouched) :
        s₉.gpr r = s₀.gpr r := by
      rw [g₉ r h9, g₈ r h8, hB.cs r hc hn, g₆ r h6, i₅.un r hu]
    have x2728 (r : Reg) (d : Nat) (hd : d = 32 ∨ d = 40) (hu : r ∈ untouched)
        (hx : s₈.gpr r = s₇.mem.readW (off (cx s₀) d) 64)
        (hm : (memIn s₅.mem (cx s₀) (s₅.gpr .x27) (s₅.gpr .x28)).readW (off (cx s₀) d) 64 = s₅.gpr r) :
        s₉.gpr r = s₀.gpr r := by
      rw [g₉ r (by rcases hd with rfl | rfl <;> simp only [untouched, List.mem_cons,
        List.not_mem_nil, or_false] at hu <;> rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide),
        hx, r₇ d hd, m₆, hm, i₅.un r hu]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact x2728 _ 32 (.inl rfl) (by decide) x27₈ (memIn_800 _ _ _ _)
    · exact x2728 _ 40 (.inr rfl) (by decide) x28₈ (memIn_808 _ _ _ _)
  -- The keystream.
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = initState (K s₀) 1 (N s₀) := by
    rw [m₅, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter,
      stateAt_frame k₄.frame (by rdisj_all), hst, set12_initState]
  have st₆ : VG.Proof.ChaCha20.AArch64.Mixed8.source s₆ = initState (K s₀) 1 (N s₀) := by
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.source, x0₆]
    rw [stateAt_frame f₅₆ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), st₅]
  have ks₉ : ∀ i < L s₀, s₉.mem (off (cx s₀) (256 + L s₀) + BitVec.ofNat 64 i) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := by
    intro i hi
    have hR : ∀ r ∈ [sub s₀ 448 24], (sub s₀ (256 + L s₀) 512).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)
    rw [m₉, f₇₈.bytes (R := sub s₀ (256 + L s₀) 512) hR (by show 512 ≤ 2 ^ 64; decide)
      (by show i < 512; omega_arith)]
    have d := hB.data i (by omega_arith)
    rw [x1₆, st₆] at d
    rw [d]
    -- The buffer was zero.
    have z : s₆.mem (off (cx s₀) (256 + L s₀) + BitVec.ofNat 64 i) = 0 := by
      rw [f₅₆.bytes (R := sub s₀ (256 + L s₀) 512) (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega))
          (by show 512 ≤ 2 ^ 64; decide) (by show i < 512; omega_arith),
        k₅.frame.bytes (R := sub s₀ (256 + L s₀) 512) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst hr
          exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by show 512 ≤ 2 ^ 64; decide)
          (by show i < 512; omega_arith),
        Short.off_add, show 256 + L s₀ + i = 704 + (L s₀ - 448 + i) by omega_arith]
      exact z₄.byte (k := L s₀ - 448 + i) (by omega_arith) (by decide)
    rw [z, VG.Proof.ChaCha20.keystream_getD _ hi]
    simp
  -- The accumulator.
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have ac₇ := hB.acc
  have hX := hv₈ ac₇.h2
  rw [show hacc s₇ = Poly.hval s₇ from rfl, ac₇.h, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)] at hX
  have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
  have hr1 := hr.2.1
  rw [k24] at hr1
  refine ⟨⟨by rw [g₉ _ (by decide), x21₈], un₉, by rw [sp₉, sp₈, hB.sp, sp₆, i₅.sp],
      by rw [rd₉, rd₈, hB.rd, rd₆, i₅.rd], by rw [wr₉, wr₈, hB.wr, wr₆, i₅.wr],
      h.saved.frame hF ?_, h.frame.trans (hF.sub ?_)⟩, x22₉, x23₉, x24₉, x25₉, hF, ks₉, ⟨?_, ?_, ?_⟩,
    fun r hr => ?_⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · rw [List.length_append, Poly1305.length_bytesAt]
    have := hr.1; omega_arith
  · rw [k24, bytesAt_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
      (by lit_omega)]
    exact hr1
  · rw [m₉, m₈, Poly1305.AArch64.storeHm_acc]
    show Poly1305.AArch64.Radix64.hval s₈ = _
    rw [hX, Poly1305.accumulate_append hr.1]
    refine congrArg (VG.Proof.Poly1305.absorbAll _ _) ?_
    rw [x2₆, prefix_frame f₅₆ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) (by omega_arith),
      prefix_frame k₅.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) (by omega_arith),
      prefix_frame k₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) (by omega_arith)]
  · have e7 : s₇.v r = s₆.v r := by
      by_cases h8 : r = .v8
      · subst h8; exact hB.v8
      by_cases h9 : r = .v9
      · subst h9; exact hB.v9
      exact ov₇ r hr h8 h9
    rw [v₉ r hr, vv₈, e7, v₆]
    exact (v₅ r hr).trans (v₄ r hr)

theorem openMain_ok (sve : Bool) {s₀ : State} (hp : APre false s₀) (h449 : 449 ≤ L s₀)
    (h511 : L s₀ ≤ 511) : WP isa (OpenPad.openMain sve) s₀ (MainO s₀) := by
  have hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold OpenPad.openMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  have i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  have R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  -- The keystream with the first 448 bytes absorbed.
  refine crypt_ok sve hp h449 h511 i₃ st₃ R₃ fun s₉ hc => ?_
  -- The rest of the data.
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcAt hp (p := 448) (by omega_arith)) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x24 hc.x25) (by lit_decide))
    fun s₁₀ ⟨⟨k₁₀, r₁₀⟩, v₁₀⟩ => ?_)
  have i₁₀ := mac_inv0 hc.inv k₁₀
  refine WP.seq (WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₀) (by lit_decide))
    fun s₁₁ ⟨⟨i₁₁, k₁₁, r₁₁⟩, v₁₁⟩ => ?_)
  have x22₁₁ : s₁₁.gpr .x22 = dp s₀ := by
    rw [k₁₁.cs _ (pres .x22) (pres30 .x22), k₁₀.cs _ (pres .x22) (pres30 .x22), hc.x22]
  have x23₁₁ : s₁₁.gpr .x23 = BitVec.ofNat 64 (L s₀) := by
    rw [k₁₁.cs _ (pres .x23) (pres30 .x23), k₁₀.cs _ (pres .x23) (pres30 .x23), hc.x23]
  -- The data decrypted.
  refine WP.seq (WP.mono (WP.preservedV (Short.xorKsWithAt_ok hp (k := 256 + L s₀) (o := 0) (n := L s₀)
    (by omega_arith) (by omega_arith) x23₁₁ i₁₁.rd i₁₁.wr (xsetup_ok i₁₁.x21 x22₁₁ x23₁₁)) (by lit_decide))
    fun s₁₂ ⟨⟨k₁₂, d₁₂, _, _⟩, v₁₂⟩ => ?_)
  have i₁₂ : Inv0 s₀ s₁₂ := i₁₁.step k₁₂
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  -- The keystream zeroed.
  refine WP.seq (WP.mono (zero_ok hp i₁₂.x21 i₁₂.wr) fun s₁₃ ⟨k₁₃, _, v₁₃⟩ => ?_)
  have i₁₃ : Inv0 s₀ s₁₃ := i₁₂.step k₁₃
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine WP.mono (WP.preservedV (finalizeTo_ok0 hp i₁₃ (out := 48) (by omega_arith)) (by lit_decide))
    fun s₁₄ ⟨⟨k₁₄, tag₁₄⟩, v₁₄⟩ => ?_
  -- The tag computed.
  have hR : ∀ r ∈ [sub s₀ 32 16, sub s₀ 64 408, sub s₀ 704 576],
      (⟨dp s₀ + BitVec.ofNat 64 448, L s₀ - 448⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hp.c_d.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (sub_ctx s₀ (by lit_omega))
  have R₁₀ := r₁₀ _ _ hc.mac
  rw [bytesAt_frame hc.frame hR (by omega_arith), List.append_assoc, split_pad (by decide) (by omega_arith),
    bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
    bytesAt_frame h₁.fine (by rdisj_all) hL'] at R₁₀
  have R₁₃ := Repr.frame k₁₃.frame (by rdisj_all) (Repr.frame k₁₂.frame (by rdisj_all) (r₁₁ _ _ R₁₀))
  have T₁₄ := tag₁₄ _ _ R₁₃
  have L₁₀ : bytesAt s₁₀.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₁₀.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₁₀, hA] at T₁₄
  refine ⟨i₁₃.step k₁₄ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₁₄ r hr).trans ((v₁₃ r hr).trans
      ((v₁₂ r hr).trans ((v₁₁ r hr).trans ((v₁₀ r hr).trans ((hc.vec r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))))))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₁₄]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  -- The data decrypted.
  · have hd₁₁ : ∀ i < L s₀, s₁₁.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
      fun i hi => by
        rw [data_frame k₁₁.frame (by rdisj_all) hi, data_frame k₁₀.frame (by rdisj_all) hi,
          data_frame hc.frame (by rdisj_all) hi, data_frame k₃.frame (by rdisj_all) hi,
          data_frame k₂.frame (by rdisj_all) hi, data_frame h₁.fine (by rdisj_all) hi]
    have hk₁₁ : ∀ i < L s₀, s₁₁.mem (kpAt s₀ (256 + L s₀) + BitVec.ofNat 64 i) =
        (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun i hi => by
      have hR' : ∀ r ∈ macR s₀, (sub s₀ (256 + L s₀) 512).Disjoint r := by
        intro r hr; simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)
      rw [k₁₁.frame.bytes (R := sub s₀ (256 + L s₀) 512) hR' (by show 512 ≤ 2 ^ 64; decide)
          (by show i < 512; omega_arith),
        k₁₀.frame.bytes (R := sub s₀ (256 + L s₀) 512) hR' (by show 512 ≤ 2 ^ 64; decide)
          (by show i < 512; omega_arith)]
      exact hc.ks i hi
    rw [bytesAt_frame k₁₄.frame (by rdisj_all) hL', bytesAt_frame k₁₃.frame (by rdisj_all) hL',
      encrypt_eq]
    apply List.ext_getElem
    · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
    · intro i h₁ h₂
      have hi : i < L s₀ := by simpa only [VG.Proof.Poly1305.length_bytesAt] using h₁
      have hDl : (bytesAt s₀.mem (dp s₀) (L s₀)).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
      have e1 : (bytesAt s₁₂.mem (dp s₀) (L s₀))[i] = s₁₂.mem (dp s₀ + BitVec.ofNat 64 i) := by
        simp [bytesAt]
      have e2 : ∀ h : i < (D s₀).length, (D s₀)[i] = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := fun h => by
        simp [D, bytesAt]
      have e3 : ∀ h : i < (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length).length,
          (keystream (initState (K s₀) 1 (N s₀)) (D s₀).length)[i] =
            (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD i 0 := fun h => by
        rw [VG.Proof.ChaCha20.getElem_eq_getD' _ h, D, hDl]
      rw [List.getElem_zipWith, e1, e2, e3]
      have d := d₁₂ i hi
      simp only [Nat.zero_add] at d
      rw [d, hd₁₁ i hi, hk₁₁ i hi]

/-- `open` from `Short.lo` to 511 bytes: `ShortRest.lean`'s code up to
`Pad.threshold`, `OpenPad.openMain` from 449 bytes, and `Pad.openMain` between
them. -/
theorem openRoute_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀)
    (hlo : 1 ≤ L s₀) (h511 : L s₀ ≤ 511) : WP isa (openRoute v.callee) s₀ (MainO s₀) := by
  unfold openRoute
  refine WP.seq (WP.mono (Pad.split_ok v.callee.sve s₀) fun s₁ ⟨ag, x9⟩ => ?_)
  have hp₁ := Short.APre.agree ag hp
  have hL₁ : L s₁ = L s₀ := by rw [L, L, ag.gpr .x5 (by decide) (by decide)]
  refine WP.ite (decide (L s₀ ≤ Pad.threshold v.callee.sve)) (Pad.split_eval h511 x9) (fun _ => ?_)
    (fun hgt => ?_)
  · exact WP.mono (ShortRest.openMain_ok v hp₁ (by omega_arith)) fun _ h => Short.MainO.agree ag h
  have hgt' := of_decide_eq_false hgt
  cases hs : v.callee.sve
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hs] at hgt'
    exact WP.mono (openMain_ok false hp₁ (by simp only [Pad.threshold, Bool.false_eq_true, ↓reduceIte] at hgt'; omega_arith) (by omega_arith))
      fun _ h => Short.MainO.agree ag h
  · simp only [↓reduceIte]
    refine WP.seq (WP.mono (Pad.split_ok false s₁) fun s₂ ⟨ag₂, x92⟩ => ?_)
    have hp₂ := Short.APre.agree ag₂ hp₁
    have hL₂ : L s₂ = L s₁ := by rw [L, L, ag₂.gpr .x5 (by decide) (by decide)]
    refine WP.ite (decide (L s₁ ≤ Pad.threshold false)) (Pad.split_eval (by omega_arith) x92) (fun _ => ?_)
      (fun hgt₂ => ?_)
    · exact WP.mono (Pad.openMain_ok v hp₂ (by omega_arith))
        fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)
    · have := of_decide_eq_false hgt₂
      simp only [Pad.threshold, Bool.false_eq_true, ↓reduceIte] at this
      exact WP.mono (openMain_ok true hp₂ (by omega_arith) (by omega_arith))
        fun _ h => Short.MainO.agree ag (Short.MainO.agree ag₂ h)

end VG.Proof.ChaCha20Poly1305.AArch64.OpenPad
