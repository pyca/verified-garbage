module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.TailO.Kernel
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Seal
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Round

/-!
# ChaCha20-Poly1305 on AArch64, the rest when decrypting

`TailO.rest`, from what `cryptStitched` leaves after `T` chunks with a rest
of `r = L - 512 T` bytes, `65 ≤ r ≤ 256` (`Crypted`): the rest's keystream
computed while its `r / 16` whole blocks are absorbed (`kernel_ok`), its last
partial block absorbed with its padding (`macPad_ok`), and the rest XORed
with the keystream (`xorKsAt_ok`): the Poly1305 state and the data as
`macPad` and `openRest` leave them.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.TailO

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_movz wp_lsr wp_sub wp_addImm wp_subImm)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc Readable)
open VG.Proof.ChaCha20Poly1305.AArch64.Tail (Rk wp_add)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

/-- `load`: our caller's `x20` in `x8`, the data from `x22` in `x20` and `x7`,
the whole blocks of its `n` bytes counted in `x6`, and the accumulator and
the clamped key as before the chunks. -/
theorem loadAt_ok {s₀ u : State} (hp : APre e s₀) {key M : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx21 : u.gpr .x21 = cx s₀) (hrd : u.rd = s₀.rd) (hwr : u.wr = s₀.wr)
    (hx0 : u.gpr .x0 = off (cx s₀) 64) (hx23 : u.gpr .x23 = BitVec.ofNat 64 n)
    (hm : Repr u.mem (off (cx s₀) 448) key M) :
    WP isa (.block TailO.load) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key) M) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x22 ∧
      s₂.gpr .x6 = BitVec.ofNat 64 (n / 16) ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x6, .x7, .x8, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  unfold TailO.load
  have hv : ∀ i ∈ [mov .x8 .x20, mov .x20 .x22, mov .x7 .x22, .lsr .x .x6 .x23 4], vdstOf i = none := by
    decide
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun s₁ =>
      s₁.gpr .x8 = u.gpr .x20 ∧ s₁.gpr .x20 = u.gpr .x22 ∧ s₁.gpr .x7 = u.gpr .x22 ∧
      s₁.gpr .x6 = BitVec.ofNat 64 (n / 16) ∧
      (∀ r, r ≠ .x8 → r ≠ .x20 → r ≠ .x7 → r ≠ .x6 → s₁.gpr r = u.gpr r) ∧ s₁.mem = u.mem)
    (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ =>
      WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx23,
          shr4_ofNat hn],
        fun r h8 h20 h7 h6 => by rw [u₄.other _ h6, u₃.other _ h7, u₂.other _ h20, u₁.other _ h8],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩)).mono
    fun s₁ ⟨⟨x8₁, x20₁, x7₁, x6₁, g₁, m₁⟩, v₁, sp₁, rd₁, wr₁⟩ => ?_)
  refine (polyIn_ok hp (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), hx21])
    (by rw [rd₁, hrd]) (by rw [wr₁, hwr])).mono
    fun s₂ ⟨⟨a21, a22, a23, m₂, g₂, _, _⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_
  have hr : Repr s₁.mem (off (cx s₀) 448) key M := by rw [m₁]; exact hm
  have x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by
    rw [g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide) (by decide), hx0]
  refine ⟨acc_in hr x0₂ a21 a22 a23 m₂, by rw [g₂ _ (by decide), x20₁], by rw [g₂ _ (by decide), x8₁],
    by rw [g₂ _ (by decide), x7₁], by rw [g₂ _ (by decide), x6₁],
    by rw [m₂, m₁, g₁ _ (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide)], fun r hr' => ?_, by rw [v₂, v₁],
    by rw [sp₂, sp₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  obtain ⟨h6, h7, h8, h20, h21, h22, h23, h24, h25⟩ := hr'
  rw [g₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
    ⟨h21, h22, h23, h24, h25⟩), g₁ r h8 h20 h7 h6]

/-- `load`, from what `cryptStitched` leaves. -/
theorem load_ok {s₀ s w₀ u : State} (hp : APre false s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted false o s₀ s w₀ key msg T u) :
    WP isa (.block TailO.load) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key)
        (msg ++ bytesAt s.mem (dp s₀) (o + 512 * T))) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x22 ∧
      s₂.gpr .x6 = BitVec.ofNat 64 ((L s₀ - (o + 512 * T)) / 16) ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x6, .x7, .x8, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have e := hc.mac
  simp only [Bool.false_eq_true, ite_false] at e
  exact loadAt_ok hp (by omega_arith) hc.inv.x21 hc.inv.rd hc.inv.wr hc.x0
    (by rw [hc.x23, show pre o false T = o + 512 * T from rfl]) e

/-- `out`: the accumulator stored, `x22` and `x23` set to what follows the
absorbed blocks, our caller's `x20` restored, and the rest kept in `x24`,
`x25`. -/
theorem out_ok {s₀ s : State} (hp : APre e s₀) (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block TailO.out) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 → Spec.Poly1305.leNum (bytesAt u.mem (off (cx s₀) 448) 24) =
        hacc s % Spec.Poly1305.P) ∧
      Frame [sub s₀ 448 24] s.mem u.mem ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      u.gpr .x22 = s.gpr .x20 ∧ u.gpr .x23 = s.gpr .x7 + s.gpr .x2 - s.gpr .x20 ∧
      u.gpr .x20 = s.gpr .x8 ∧ u.gpr .x24 = s.gpr .x7 ∧ u.gpr .x25 = s.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x20, .x21, .x22, .x23, .x24,
        .x25, .x27, .x28] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.v = s.v := by
  unfold TailO.out
  refine WP.block_append ((polyOut_ok hp false hx0 hrd hwr).mono
    fun s₁ ⟨⟨hv₁, m₁, x21₁, x27₁, x28₁, _, _, g₁, rd₁, wr₁⟩, v₁, sp₁, _, _⟩ => ?_)
  have hv : ∀ i ∈ [mov .x22 .x20, .add .x .x23 .x7 .x2, .sub .x .x23 .x23 .x20, mov .x20 .x8,
      mov .x24 .x7, mov .x25 .x2], vdstOf i = none := by decide
  have gs (r : Reg) (hr : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23,
      .x27, .x28]) : s₁.gpr r = s.gpr r := g₁ r hr
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun u =>
      u.gpr .x22 = s₁.gpr .x20 ∧ u.gpr .x23 = s₁.gpr .x7 + s₁.gpr .x2 - s₁.gpr .x20 ∧
      u.gpr .x20 = s₁.gpr .x8 ∧ u.gpr .x24 = s₁.gpr .x7 ∧ u.gpr .x25 = s₁.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x20, .x22, .x23, .x24, .x25] → u.gpr r = s₁.gpr r) ∧ u.mem = s₁.mem)
    (wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => wp_sub fun t₃ u₃ => wp_mov fun t₄ u₄ =>
      wp_mov fun t₅ u₅ => wp_mov fun t₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩)).mono
    fun u ⟨⟨x22u, x23u, x20u, x24u, x25u, gu, mu⟩, vu, spu, rdu, wru⟩ => ?_
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h20, h22, h23, h24, h25⟩ := hr
    rw [u₆.other _ h25, u₅.other _ h24, u₄.other _ h20, u₃.other _ h23, u₂.other _ h23, u₁.other _ h22]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have go (r : Reg) (hr : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23,
      .x27, .x28]) : s₁.gpr r = s.gpr r := gs r hr
  refine ⟨fun h23 => ?_, ?_, by rw [gu _ (by decide), x21₁], by rw [gu _ (by decide), x27₁],
    by rw [gu _ (by decide), x28₁], by rw [x22u, go _ (by decide)],
    by rw [x23u, go .x7 (by decide), go .x2 (by decide), go .x20 (by decide)],
    by rw [x20u, go _ (by decide)], by rw [x24u, go _ (by decide)], by rw [x25u, go _ (by decide)],
    fun r hr => ?_, by rw [rdu, rd₁], by rw [wru, wr₁], by rw [spu, sp₁], by rw [vu, v₁]⟩
  · rw [mu, m₁, Poly1305.AArch64.storeHm_acc]
    exact hv₁ h23
  · rw [mu, m₁]; exact storeHm_frame _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h20, h21, h22, h23, h24, h25, h27, h28⟩ := hr
    have a : r ∉ [Reg.x20, .x22, .x23, .x24, .x25] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h20, h22, h23, h24, h25⟩
    have b : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h21, h22, h23, h27, h28⟩
    rw [gu r a, go r b]

/-- `x22`, `x23` set to the rest again. -/
theorem moves_ok {s : State} :
    WP isa (.block [mov .x22 .x24, mov .x23 .x25]) s fun u =>
      (u.gpr .x22 = s.gpr .x24 ∧ u.gpr .x23 = s.gpr .x25 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = s.gpr r) ∧ u.mem = s.mem) ∧ u.v = s.v ∧ u.sp = s.sp ∧
      u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide)
    (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22], by rw [u₂.mem, u₁.mem]⟩)

/-- `TailO.rest`, after `T` chunks with a rest of 65 to 256 bytes. -/
theorem rest_ok (sve : Bool) {s₀ s w₀ u : State} (hp : APre false s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted false o s₀ s w₀ key msg T u) (ho : o % 64 = 0)
    (hr₁ : 65 ≤ L s₀ - (o + 512 * T)) (hr₂ : L s₀ - (o + 512 * T) ≤ 256) :
    WP isa (TailO.rest sve) u fun w =>
      (∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) ∧
      Inv0 s₀ w ∧ Frame [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, dR s₀] u.mem w.mem ∧
      Repr w.mem (off (cx s₀) 448) key ((msg ++ bytesAt s.mem (dp s₀) (o + 512 * T)) ++
        (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (o + 512 * T)) (L s₀ - (o + 512 * T)) ++
          Spec.ChaCha20Poly1305.pad16
            (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 (o + 512 * T)) (L s₀ - (o + 512 * T))))) ∧
      bytesAt w.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wd := hp.wrap_d
  have hle := hc.le
  have oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  -- `P`, the rest's offset, `r` its length, `c` its whole blocks.
  generalize hPdef : o + 512 * T = P at hr₁ hr₂ hle ⊢
  generalize hrdef : L s₀ - P = r at hr₁ hr₂ ⊢
  have hpre : pre o false T = P := by rw [← hPdef]; rfl
  have hc16 : 16 * (r / 16) ≤ r := Nat.mul_div_le _ _
  let W := dp s₀ + BitVec.ofNat 64 P
  refine (WP.withSp (WP.preservedV (c := TailO.rest sve) (Q := fun w =>
      (∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) → w.sp = u.sp →
      Inv0 s₀ w ∧ Frame [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, dR s₀] u.mem w.mem ∧
      Repr w.mem (off (cx s₀) 448) key ((msg ++ bytesAt s.mem (dp s₀) P) ++
        (bytesAt s.mem W r ++ Spec.ChaCha20Poly1305.pad16 (bytesAt s.mem W r))) ∧
      bytesAt w.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))) ?_
      (by cases sve <;> lit_decide))).mono
    fun w ⟨⟨hw, vw⟩, spw⟩ => ⟨vw, hw vw spw⟩
  unfold TailO.rest
  -- Load.
  refine WP.seq ((load_ok hp hc).mono
    fun s₂ ⟨a₂, x20₂, x8₂, x7₂, x6₂, m₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_)
  rw [hPdef] at a₂ x6₂
  rw [hrdef] at x6₂
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, hc.inv.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, hc.inv.wr]
  have x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by rw [g₂ _ (by decide), hc.x0]
  have x3₂ : s₂.gpr .x3 = off (cx s₀) 128 := by rw [g₂ _ (by decide), hc.x3]
  have x2₂ : s₂.gpr .x2 = BitVec.ofNat 64 r := by rw [g₂ _ (by decide), hc.x2, hPdef, hrdef]
  have x22u : u.gpr .x22 = W := by rw [hc.x22, hpre]
  have hin : ∀ k : Fin 16, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₂, oo, rd₂', wr₂']; exact hp.in_ctx' (by omega_arith)
  have hw : ∀ d, d + 16 ≤ 256 → InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₂, oo, wr₂']; exact hp.in_ctx (by omega_arith)
  have hst : (⟨s₂.gpr .x0, 64⟩ : Region).Disjoint ⟨s₂.gpr .x3, 256⟩ := by
    rw [x0₂, x3₂]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hrd : Readable W (16 * (r / 16)) s₂ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₂', wr₂', VG.Proof.ChaCha20.AArch64.Xor.add_ofNat]
      exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
  -- The kernel.
  refine WP.seq ((kernel_ok sve 2 (c := r / 16) (by omega_arith) (by rw [x20₂, x22u]) x6₂ hin hw hst hrd a₂
      (by omega_arith)).mono fun s₃ ⟨ks₃, f₃, hv₃, h2₃, x20₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  have g₃' (r : Reg) (h : r ≠ .x1 ∧ r ≠ .x4 ∧ r ≠ .x6 ∧ r ∉ Poly.regs) :
      s₃.gpr r = s₂.gpr r :=
    have ⟨h1, h4, h6, hp'⟩ := h
    g₃ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4, h6⟩) hp'
  have x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by
    rw [g₃' _ (by decide), x0₂]
  rw [x3₂] at ks₃ f₃
  -- The accumulator stored.
  refine WP.seq ((out_ok hp x0₃ (by rw [rd₃, rd₂']) (by rw [wr₃, wr₂'])).mono
    fun s₄ ⟨acc₄, f₄, x21₄, x27₄, x28₄, x22₄, x23₄, x20₄, x24₄, x25₄, g₄, rd₄, wr₄, sp₄, v₄⟩ => ?_)
  have x7₃ : s₃.gpr .x7 = W := by rw [g₃' _ (by decide), x7₂, x22u]
  have x2₃ : s₃.gpr .x2 = BitVec.ofNat 64 r := by
    rw [g₃' _ (by decide), x2₂]
  have x22₄' : s₄.gpr .x22 = dp s₀ + BitVec.ofNat 64 (P + 16 * (r / 16)) := by
    rw [x22₄, x20₃, BitVec.add_assoc, ← BitVec.ofNat_add]
  have x23₄' : s₄.gpr .x23 = BitVec.ofNat 64 (r - 16 * (r / 16)) := by
    rw [x23₄, x7₃, x2₃, x20₃, VG.Offset.add_sub_add_left, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hc16]
  -- The data: the rest is as it was until the XOR.
  have dctx : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    have e₁ := data_frame (s₀ := s₀) f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk
    have e₂ := data_frame (s₀ := s₀) f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk
    have e₃ := data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
    rw [e₁, e₂, m₂, e₃]
  have uorig : ∀ k < L s₀, P ≤ k → u.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk hPk
    rw [hc.data k hk, hPdef, ite_eq_right (by omega_arith)]
  have restEq : ∀ {m : Mem}, (∀ k < L s₀, P ≤ k → m (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k)) →
      ∀ a n, a + n ≤ r → bytesAt m (W + BitVec.ofNat 64 a) n = bytesAt s.mem (W + BitVec.ofNat 64 a) n := by
    intro m hm a n han
    simp only [bytesAt]
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    have e : W + BitVec.ofNat 64 a + BitVec.ofNat 64 i = dp s₀ + BitVec.ofNat 64 (P + a + i) := by
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.add_assoc]
    rw [e]; exact hm _ (by omega_arith) (by omega_arith)
  have b₂ : bytesAt s₂.mem W (16 * (r / 16)) = bytesAt s.mem W (16 * (r / 16)) := by
    have := restEq (m := s₂.mem) (fun k hk hPk => by
      rw [m₂, ← uorig k hk hPk]
      exact data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28))
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk) 0 (16 * (r / 16)) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- The Poly1305 state after `out`: the chunks and the rest's whole blocks.
  have hmac := hc.mac
  simp only [Bool.false_eq_true, ite_false, hpre] at hmac
  have hml : (msg ++ bytesAt s.mem (dp s₀) P).length % 16 = 0 := hmac.1
  let tgt := [sub s₀ 32 16, sub s₀ 64 408]
  have c408 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, by simp [tgt], sub_sub s₀ h₁ (by omega_arith) (by lit_omega)⟩
  have Fm : Frame tgt u.mem s₂.mem := by
    rw [m₂]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c408 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  have Fk : Frame tgt s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 128 256 (by decide) (by decide)
  have Fo : Frame tgt s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c408 448 24 (by decide) (by decide)
  have F₄ : Frame tgt u.mem s₄.mem := Fm.trans (Fk.trans Fo)
  have R₄ : Repr s₄.mem (off (cx s₀) 448) key
      ((msg ++ bytesAt s.mem (dp s₀) P) ++ bytesAt s.mem W (16 * (r / 16))) := by
    have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    refine ⟨by rw [List.length_append, Poly1305.length_bytesAt]; omega_arith, ?_, ?_⟩
    · have e := hmac.2.1
      rw [k24] at e ⊢
      rw [bytesAt_frame F₄ (fun r hr => by
          simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
          · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega)]
      exact e
    · have hlt := Poly1305.accumulate_lt (Rk key) (msg ++ bytesAt s.mem (dp s₀) P)
      rw [acc₄ h2₃, show hacc s₃ = Poly.hval s₃ from rfl, hv₃,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₂]
      exact (Poly1305.accumulate_append hml).symm
  -- The last partial block, absorbed with its padding.
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂']
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂']
  have hsrc := srcAt hp (p := P + 16 * (r / 16)) (by omega_arith)
  rw [show L s₀ - (P + 16 * (r / 16)) = r - 16 * (r / 16) by omega_arith] at hsrc
  refine WP.seq ((macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ hsrc x21₄ rd₄' wr₄' x22₄'
    x23₄').mono fun s₅ ⟨k₅, r₅⟩ => ?_)
  have R₅ := r₅ _ _ R₄
  -- The rest, back in `x22` and `x23`.
  refine WP.seq (moves_ok.mono fun s₆ ⟨⟨x22₆, x23₆, g₆, m₆⟩, v₆, sp₆, rd₆, wr₆⟩ => ?_)
  have x24₅ : s₅.gpr .x24 = W := by rw [k₅.cs _ (pres .x24) (pres30 .x24), x24₄, x7₃]
  have x25₅ : s₅.gpr .x25 = BitVec.ofNat 64 r := by rw [k₅.cs _ (pres .x25) (pres30 .x25), x25₄, x2₃]
  have x21₆ : s₆.gpr .x21 = cx s₀ := by
    rw [g₆ _ (by decide) (by decide), k₅.cs _ (pres .x21) (pres30 .x21), x21₄]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, k₅.rd, rd₄']
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, k₅.wr, wr₄']
  -- The rest XORed with its keystream.
  refine (Short.xorKsAt_ok hp (o := P) (n := r) hr₂ (by omega_arith) x21₆ (by rw [x22₆, x24₅])
    (by rw [x23₆, x25₅]) rd₆' wr₆').mono fun s₇ ⟨k₇, d₇, f₇, g₇⟩ => fun vw spw => ?_
  -- Registers.
  have g₇' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13) :
      s₇.gpr r = s₆.gpr r :=
    have ⟨h9, h10, h11, h12, h13⟩ := h
    g₇ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13⟩)
  have to₄ (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x22 ∧ r ≠ .x23) :
      s₇.gpr r = s₄.gpr r := by
    obtain ⟨hr, h30, h9, h10, h11, h12, h13, h22, h23⟩ := h
    rw [g₇' r ⟨h9, h10, h11, h12, h13⟩, g₆ r h22 h23, k₅.cs r hr h30]
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₃.mem.readW (off (cx s₀) d) 64 = s₂.mem.readW (off (cx s₀) d) 64 :=
    f₃.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by decide)
  have un₇ : ∀ r ∈ untouched, s₇.gpr r = s₀.gpr r := by
    intro r hr
    have hu := hc.inv.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₄ _ (by decide), g₄ _ (by decide), g₃' _ (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide), x20₄, g₃' _ (by decide), x8₂, hu]
    · rw [to₄ _ (by decide), g₄ _ (by decide), g₃' _ (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide), x27₄, r32 32 (.inl rfl), m₂, memIn_800, hu]
    · rw [to₄ _ (by decide), x28₄, r32 40 (.inr rfl), m₂, memIn_808, hu]
  -- The frames.
  let out := [sub s₀ 16 16, sub s₀ 32 16, sub s₀ 64 512, dR s₀]
  have Fa : Frame out u.mem s₄.mem := F₄.sub fun r hr => by
    simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 32 16, by simp [out], fun _ h => h⟩
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
  have Fb : Frame out s₄.mem s₅.mem := k₅.frame.sub fun r hr => by
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sub s₀ 64 512, by simp [out], sub_sub s₀ (by decide) (by decide) (by lit_omega)⟩
    · exact ⟨sub s₀ 16 16, by simp [out], fun _ h => h⟩
  have Fc : Frame out s₅.mem s₇.mem := by
    rw [← m₆]
    exact k₇.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [out], fun _ h => h⟩
  have F : Frame out u.mem s₇.mem := Fa.trans (Fb.trans Fc)
  have inv₇ : Inv0 s₀ s₇ := ⟨by rw [g₇' _ (by decide), x21₆],
    un₇, by rw [spw, hc.inv.sp], by rw [k₇.rd, rd₆'], by rw [k₇.wr, wr₆'],
    hc.inv.saved.frame F (fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))),
    hc.inv.frame.trans (F.sub fun r hr => by
      simp only [out, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)⟩
  -- The data, before the XOR, from `s₄` on.
  have d₅ : ∀ k < L s₀, s₆.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    rw [m₆, ← dctx k hk]
    exact data_frame (s₀ := s₀) k₅.frame (fun r hr => by
      simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
  refine ⟨inv₇, F, ?_, ?_⟩
  · -- The Poly1305 state.
    have e₄ : bytesAt s₄.mem (dp s₀ + BitVec.ofNat 64 (P + 16 * (r / 16))) (r - 16 * (r / 16)) =
        bytesAt s.mem (W + BitVec.ofNat 64 (16 * (r / 16))) (r - 16 * (r / 16)) := by
      rw [show dp s₀ + BitVec.ofNat 64 (P + 16 * (r / 16)) = W + BitVec.ofNat 64 (16 * (r / 16)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
      exact restEq (fun k hk hPk => by rw [dctx k hk, uorig k hk hPk]) _ _ (by omega_arith)
    rw [e₄, List.append_assoc, split_pad (m := s.mem) (p := W) (Nat.mul_mod_right 16 _) hc16] at R₅
    refine Repr.frame (k₇.frame) (fun r hr => ?_) (by rw [m₆]; exact R₅)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.c_d.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by lit_omega))
  · -- The data.
    show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
    rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      VG.Proof.Poly1305.length_bytesAt _ _ _]
    refine VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
    by_cases hk' : k < P
    · rw [f₇ _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Tail.not_in (.inl hk') (by omega_arith) (by omega_arith)),
        d₅ k hk, hc.data k hk, ite_eq_left (by rw [hPdef]; exact hk')]
    · have hi : k - P < r := by omega_arith
      have e := d₇ (k - P) hi
      rw [show P + (k - P) = k by omega_arith] at e
      rw [e, d₅ k hk, uorig k hk (by omega_arith)]
      congr 1
      have k₆ : s₆.mem (Short.kp' s₀ + BitVec.ofNat 64 (k - P)) =
          s₃.mem (off (cx s₀) 128 + BitVec.ofNat 64 (k - P)) := by
        rw [m₆]
        have e₅ := k₅.frame.bytes (R := ⟨off (cx s₀) 128, 256⟩) (fun r hr => by
          simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (show 256 ≤ 2 ^ 64 by decide) (show k - P < 256 by omega_arith)
        rw [show Short.kp' s₀ = off (cx s₀) 128 from rfl, e₅]
        exact f₄.bytes (R := ⟨off (cx s₀) 128, 256⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (show 256 ≤ 2 ^ 64 by decide) (show k - P < 256 by omega_arith)
      have st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt u.mem (off (cx s₀) 64) := by
        rw [m₂]
        exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame (memIn_frame (s₀ := s₀) _ _ _) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      have hP64 : 64 * (o / 64 + 8 * T) = P := by rw [← hPdef]; omega_arith
      rw [k₆, ks₃ _ (by omega_arith), x0₂, st₂, hc.cnt,
        ks_shift _ hk (q := o / 64 + 8 * T) (by omega_arith), hP64]


/-- `(r - k) >> 63` is 1 iff `r < k`, for both below `2^63`. -/
theorem sub_shr63 {r k : Nat} (hr : r < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 r - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if r < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith : r < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega_arith : k < 2 ^ 64)]
  split
  · rw [Nat.mod_eq_of_lt (by omega_arith : 2 ^ 64 - k + r < 2 ^ 64), show (BitVec.ofNat 64 1).toNat = 1 from rfl]
    exact Nat.div_eq_of_lt_le (by omega_arith) (by omega_arith)
  · rw [show 2 ^ 64 - k + r = (r - k) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith : r - k < 2 ^ 64), Nat.div_eq_of_lt (by omega_arith)]
    rfl

/-- `TailO.test`: `x9 = 0` iff the rest is 65 to 256 bytes. -/
theorem test_ok (w : State) {r : Nat} (hr : r < 2 ^ 63) (hx : w.gpr .x23 = BitVec.ofNat 64 r) :
    WP isa (.block TailO.test) w fun u =>
      isa.eval (.zero .x .x9) u = some (decide (65 ≤ r ∧ r ≤ 256)) ∧ Kept [] w u ∧
      (∀ q, q ≠ .x9 → q ≠ .x10 → q ≠ .x11 → u.gpr q = w.gpr q) ∧
      ∀ v ∈ preservedV, (u.v v).extractLsb' 0 64 = (w.v v).extractLsb' 0 64 := by
  have core : WP isa (.block TailO.test) w fun u =>
      u.gpr .x9 = BitVec.ofNat 64 (if 65 ≤ r ∧ r ≤ 256 then 0 else 1) ∧
      (∀ q, q ≠ .x9 → q ≠ .x10 → q ≠ .x11 → u.gpr q = w.gpr q) ∧ u.mem = w.mem ∧ u.rd = w.rd ∧
      u.wr = w.wr := by
    unfold TailO.test
    refine wp_subImm (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
      wp_subImm (by decide) fun s₃ u₃ => wp_lsr (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ =>
      wp_addImm (by decide) fun s₆ u₆ => ?_
    simp only [List.replicate]
    refine wp_movz fun t₁ v₁ => wp_movz fun t₂ v₂ => wp_movz fun t₃ v₃ => wp_movz fun t₄ v₄ =>
      wp_movz fun t₅ v₅ => wp_movz fun t₆ v₆ => wp_movz fun t₇ v₇ => wp_movz fun t₈ v₈ =>
      wp_movz fun t₉ v₉ => WP.block_nil ⟨?_, fun q h9 h10 h11 => ?_, ?_, ?_, ?_⟩
    · have b₁ : s₂.gpr .x9 = BitVec.ofNat 64 (if r < 257 then 1 else 0) := by
        rw [u₂.gpr, u₁.gpr, hx, sub_shr63 hr (by decide)]
      have b₂ : s₄.gpr .x10 = BitVec.ofNat 64 (if r < 65 then 1 else 0) := by
        rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hx, sub_shr63 hr (by decide)]
      rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide),
        v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
        v₁.other _ (by decide), u₆.gpr, u₅.gpr, b₂, u₄.other _ (by decide), u₃.other _ (by decide), b₁]
      by_cases h₁ : r < 65
      · simp only [h₁, show r < 257 by omega_arith, ite_true, show ¬ (65 ≤ r ∧ r ≤ 256) by omega_arith, ite_false]; rfl
      · by_cases h₂ : r < 257
        · simp only [h₁, h₂, ite_true, ite_false, show 65 ≤ r ∧ r ≤ 256 by omega_arith]; rfl
        · simp only [h₁, h₂, ite_false, show ¬ (65 ≤ r ∧ r ≤ 256) by omega_arith]; rfl
    · rw [v₉.other _ h11, v₈.other _ h11, v₇.other _ h11, v₆.other _ h11, v₅.other _ h11, v₄.other _ h11,
        v₃.other _ h11, v₂.other _ h11, v₁.other _ h11, u₆.other _ h9, u₅.other _ h9, u₄.other _ h10,
        u₃.other _ h10, u₂.other _ h9, u₁.other _ h9]
    · rw [v₉.mem, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₆.mem, u₅.mem, u₄.mem,
        u₃.mem, u₂.mem, u₁.mem]
    · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, u₆.rd, u₅.rd, u₄.rd,
        u₃.rd, u₂.rd, u₁.rd]
    · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, u₆.wr, u₅.wr, u₄.wr,
        u₃.wr, u₂.wr, u₁.wr]
  refine WP.mono (WP.preservedV (WP.kept core (by rfl))
    (by rfl)) fun u ⟨⟨⟨h9, hg, hm, hrd, hwr⟩, hk, hsp⟩, hv⟩ =>
      ⟨?_, Kept.of hk hsp hrd hwr (by rw [hm]; exact Frame.refl _ _), hg, hv⟩
  rw [show isa.eval (.zero .x .x9) u = some (u.gpr .x9 == 0) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_zero u .x9, h9]
  by_cases h : 65 ≤ r ∧ r ≤ 256
  · simp only [h, and_self, ite_true, decide_true]; rfl
  · simp only [h, ite_false, decide_false]; rfl

/-- `Crypted` holds after code that writes only `x9`–`x11` (`TailO.test`). -/
theorem Crypted.keep {enc : Bool} {o : Nat} {s₀ s w u u' : State} {key msg : List Byte} {T : Nat}
    (hc : Crypted enc o s₀ s w key msg T u) (hk : Kept [] u u')
    (hg : ∀ q, q ≠ .x9 → q ≠ .x10 → q ≠ .x11 → u'.gpr q = u.gpr q)
    (hv : ∀ v ∈ preservedV, (u'.v v).extractLsb' 0 64 = (u.v v).extractLsb' 0 64) :
    Crypted enc o s₀ s w key msg T u' := by
  have hm : u'.mem = u.mem := by
    funext x; exact hk.frame x fun r hr => by simp at hr
  refine ⟨hc.inv.step hk (fun r hr => by simp at hr) (fun r hr => by simp at hr), hc.le, hc.lt,
    by rw [hg _ (by decide) (by decide) (by decide), hc.x0],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x1],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x2],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x3],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x22],
    by rw [hg _ (by decide) (by decide) (by decide), hc.x23],
    by rw [hm]; exact hc.cnt, fun k hk' => by rw [hm]; exact hc.data k hk',
    by rw [hm]; exact hc.frame, by rw [hm]; exact hc.mac, fun r hr => (hv r hr).trans (hc.vec r hr)⟩

end VG.Proof.ChaCha20Poly1305.AArch64.TailO
