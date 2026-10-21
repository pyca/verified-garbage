module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Kernel
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting

`Tail.rest`, from what `cryptStitched` leaves after `T ≥ 1` chunks with a rest
of `L - 512 T > 0` bytes (`Crypted`): the last chunk absorbed while the
keystream of the next four blocks is computed (`kernel_ok`), and the first
`m = min(L - 512 T, 256)` bytes of the rest encrypted with it: the data's first
`512 T + m` bytes encrypted and its first `512 T` absorbed (`Sealed`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Tail

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_movz wp_lsr wp_sub wp_addImm wp_ldr32
  wp_addImm32 wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

/-- The clamped key's value. -/
abbrev Rk (key : List Byte) : Nat := Spec.Poly1305.clamp (Spec.Poly1305.leNum (key.take 16))

/-- `load`: our caller's `x20` in `x8`, the rest in `x7`, the last chunk in
`x20`, and the accumulator and the clamped key as before the chunks. -/
theorem load_ok {s₀ s u : State} (hp : APre true s₀) {key msg : List Byte} {T : Nat}
    (hc : Crypted true s₀ s key msg T u) (hx21 : u.gpr .x21 = cx s₀) :
    WP isa (.block Tail.load) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key)
        (msg ++ bytesAt u.mem (dp s₀) (512 * (T - 1)))) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x1 ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x7, .x8, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  unfold Tail.load
  have hv : ∀ i ∈ [mov .x8 .x20, mov .x20 .x22, mov .x7 .x1], vdstOf i = none := by decide
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun s₁ =>
      s₁.gpr .x8 = u.gpr .x20 ∧ s₁.gpr .x20 = u.gpr .x22 ∧ s₁.gpr .x7 = u.gpr .x1 ∧
      (∀ r, r ≠ .x8 → r ≠ .x20 → r ≠ .x7 → s₁.gpr r = u.gpr r) ∧ s₁.mem = u.mem)
    (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
        by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        fun r h8 h20 h7 => by rw [u₃.other _ h7, u₂.other _ h20, u₁.other _ h8],
        by rw [u₃.mem, u₂.mem, u₁.mem]⟩)).mono
    fun s₁ ⟨⟨x8₁, x20₁, x7₁, g₁, m₁⟩, v₁, sp₁, rd₁, wr₁⟩ => ?_)
  refine (polyIn_ok hp (by rw [g₁ _ (by decide) (by decide) (by decide), hx21])
    (by rw [rd₁, hc.inv.rd]) (by rw [wr₁, hc.inv.wr])).mono
    fun s₂ ⟨⟨a21, a22, a23, m₂, g₂, _, _⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_
  have hr : Repr s₁.mem (off (cx s₀) 448) key (msg ++ bytesAt u.mem (dp s₀) (512 * (T - 1))) := by
    have e := hc.mac
    simp only [ite_true, pre] at e
    rw [m₁]; exact e
  have x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by
    rw [g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide), hc.x0]
  refine ⟨acc_in hr x0₂ a21 a22 a23 m₂, by rw [g₂ _ (by decide), x20₁], by rw [g₂ _ (by decide), x8₁],
    by rw [g₂ _ (by decide), x7₁], by rw [m₂, m₁, g₁ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide)], fun r hr' => ?_, by rw [v₂, v₁], by rw [sp₂, sp₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  obtain ⟨h7, h8, h20, h21, h22, h23, h24, h25⟩ := hr'
  rw [g₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
    ⟨h21, h22, h23, h24, h25⟩), g₁ r h8 h20 h7]

/-- `out`: the accumulator stored, `x22` set to the rest, our caller's `x20`
restored, and the counter advanced past the four blocks. -/
theorem out_ok {s₀ s : State} (hp : APre e s₀) (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block Tail.out) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 → Spec.Poly1305.leNum (bytesAt u.mem (off (cx s₀) 448) 24) =
        hacc s % Spec.Poly1305.P) ∧
      Frame [sub s₀ 448 24, sub s₀ 112 4] s.mem u.mem ∧
      stateAt u.mem (off (cx s₀) 64) = ctr (stateAt s.mem (off (cx s₀) 64)) 4 ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      u.gpr .x22 = s.gpr .x7 ∧ u.gpr .x20 = s.gpr .x8 ∧ u.gpr .x23 = s.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x20, .x21, .x22, .x23, .x27,
        .x28] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.v = s.v := by
  unfold Tail.out
  rw [List.append_assoc]
  refine WP.block_append ((polyOut_ok hp false hx0 hrd hwr).mono
    fun s₁ ⟨⟨hv₁, m₁, x21₁, x27₁, x28₁, x22₁, x23₁, g₁, rd₁, wr₁⟩, v₁, sp₁, _, _⟩ => ?_)
  have hv : ∀ i ∈ [mov .x22 .x7, mov .x20 .x8], vdstOf i = none := by decide
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun s₂ =>
      s₂.gpr .x22 = s₁.gpr .x7 ∧ s₂.gpr .x20 = s₁.gpr .x8 ∧
      (∀ r, r ≠ .x22 → r ≠ .x20 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem)
    (wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h20 => by rw [u₂.other _ h20, u₁.other _ h22], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₂ ⟨⟨x22₂, x20₂, g₂, m₂⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_)
  have x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hx0]
  have p48 : s₂.gpr .x0 + BitVec.ofNat 64 48 = off (cx s₀) 112 := by rw [x0₂]; exact off_off _ 64 48
  have hi : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [p48, rd₂, wr₂, rd₁, wr₁, hrd, hwr]; exact hp.in_ctx' (by lit_omega)
  have ho : InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [p48, wr₂, wr₁, hwr]; exact hp.in_ctx (by lit_omega)
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.counter_ok s₂ (by decide) false hi ho).mono
    fun s₃ ⟨m₃, g₃, rd₃, wr₃, v₃, sp₃⟩ => ?_
  simp only [Bool.false_eq_true, ite_false] at m₃
  have fs : Frame [sub s₀ 448 24] s.mem s₂.mem := by rw [m₂, m₁]; exact storeHm_frame _ _ _ _ _
  have fc : Frame [sub s₀ 112 4] s₂.mem s₃.mem := by
    rw [m₃, p48]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (contains_sub s₀ (by decide) (by decide)
      (by lit_omega))
  have hg (r : Reg) (h4 : r ≠ .x4) (h20 : r ≠ .x20) (h22 : r ≠ .x22) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r h4, g₂ r h22 h20]
  refine ⟨fun h23 => ?_, ?_, ?_, by rw [hg _ (by decide) (by decide) (by decide), x21₁],
    by rw [hg _ (by decide) (by decide) (by decide), x27₁],
    by rw [hg _ (by decide) (by decide) (by decide), x28₁],
    by rw [g₃ _ (by decide), x22₂, g₁ _ (by decide)], by rw [g₃ _ (by decide), x20₂, g₁ _ (by decide)],
    by rw [hg _ (by decide) (by decide) (by decide), x23₁]; rfl, fun r hr => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁], by rw [v₃, v₂, v₁]⟩
  · rw [bytesAt_frame fc (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega),
      m₂, m₁, Poly1305.AArch64.storeHm_acc]
    exact hv₁ h23
  · intro x hx
    rw [fc x fun r hr => hx r (by simp only [List.mem_singleton] at hr; simp [hr]),
      fs x fun r hr => hx r (by simp only [List.mem_singleton] at hr; simp [hr])]
  · rw [m₃, x0₂, VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame fs (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h20, h21, h22, h23, h27, h28⟩ := hr
    rw [hg r h4 h20 h22, g₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
      ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h21, h22, h23, h27, h28⟩)]

theorem shr8_ofNat {r : Nat} (h : r < 2 ^ 64) : BitVec.ofNat 64 r >>> 8 = BitVec.ofNat 64 (r / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.ChaCha20.AArch64.toNat_ofNat_lt h,
    VG.Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- `take`: `x23 = min(x2, 256)`. -/
theorem take_ok {s : State} {r : Nat} (hr : r < 2 ^ 64) (hx2 : s.gpr .x2 = BitVec.ofNat 64 r) :
    WP isa Tail.take s fun u =>
      u.gpr .x23 = BitVec.ofNat 64 (min r 256) ∧
      (∀ q, q ≠ .x9 → q ≠ .x23 → u.gpr q = s.gpr q) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  unfold Tail.take
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have x9₁ : s₁.gpr .x9 = BitVec.ofNat 64 (r / 256) := by rw [u₁.gpr, hx2, shr8_ofNat hr]
  refine WP.ite (decide (r / 256 = 0)) (by
      rw [show isa.eval (.zero .x .x9) s₁ = some (s₁.gpr .x9 == 0) from
        VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₁ .x9, x9₁,
        VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)]) (fun h => ?_) (fun h => ?_)
  · have h' : r < 256 := by have := of_decide_eq_true h; omega
    refine wp_mov fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.other _ (by decide), hx2,
      Nat.min_eq_left (by omega)], fun q h9 h23 => by rw [u₂.other _ h23, u₁.other _ h9],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  · have h' : 256 ≤ r := by have := of_decide_eq_false h; omega
    refine wp_movz fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, Nat.min_eq_right h']; rfl,
      fun q h9 h23 => by rw [u₂.other _ h23, u₁.other _ h9],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩

theorem wp_add {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n + s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

/-- `args`: the stream's arguments after the `m` bytes XORed, and `x23` the
rest's length again. -/
theorem args_ok {s₀ s : State} {D : Addr} {m r : Nat} (hm : m ≤ r)
    (hx21 : s.gpr .x21 = cx s₀) (hx22 : s.gpr .x22 = D) (hx23 : s.gpr .x23 = BitVec.ofNat 64 m)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 r) :
    WP isa (.block Tail.args) s fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = D + BitVec.ofNat 64 m ∧
      u.gpr .x2 = BitVec.ofNat 64 (r - m) ∧ u.gpr .x3 = off (cx s₀) 128 ∧
      u.gpr .x23 = BitVec.ofNat 64 r ∧
      (∀ q, q ∉ [Reg.x0, .x1, .x2, .x3, .x23] → u.gpr q = s.gpr q) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  unfold Tail.args
  refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_add fun s₃ u₃ => wp_addImm (by decide)
    fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have x2₂ : s₂.gpr .x2 = BitVec.ofNat 64 (r - m) := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hx2, hx23,
      VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hm]
  refine ⟨by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hx21],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hx22, hx23],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x2₂],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hx21],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, x2₂,
      u₂.other _ (by decide), u₁.other _ (by decide), hx23, ← BitVec.ofNat_add,
      Nat.sub_add_cancel hm], fun q hq => ?_,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  obtain ⟨h0, h1, h2, h3, h23⟩ := hq
  rw [u₅.other _ h3, u₄.other _ h0, u₃.other _ h23, u₂.other _ h2, u₁.other _ h1]

/-- A byte of the data outside `[a, a + n)` is outside that region. -/
theorem not_in {D : Addr} {a n k : Nat} (h : k < a ∨ a + n ≤ k) (hk : k < 2 ^ 64) (han : a + n ≤ 2 ^ 64) :
    ¬ (⟨D + BitVec.ofNat 64 a, n⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  intro hc
  have := (Offset.lt_iff (D + BitVec.ofNat 64 k) D han).mp (by omega)
  rw [Mem.sub_ofNat_toNat D hk] at this
  omega

/-- `Tail.rest`, after `T ≥ 1` chunks with a rest. -/
theorem rest_ok (sve : Bool) {s₀ s u : State} (hp : APre true s₀) {key msg : List Byte} {T : Nat}
    (hc : Crypted true s₀ s key msg T u) (hT : 1 ≤ T) (hr : 512 * T < L s₀) :
    WP isa (Tail.rest sve) u fun w => ∃ P, Sealed s₀ s key msg P (512 * T) w := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wd := hp.wrap_d
  have pre_eq : pre true T = 512 * (T - 1) := rfl
  have oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  refine (WP.withSp (WP.preservedV (c := Tail.rest sve) (Q := fun w => ∃ P,
      (∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) → w.sp = u.sp →
        Sealed s₀ s key msg P (512 * T) w) ?_ (by cases sve <;> lit_decide))).mono
    fun w ⟨⟨⟨P, hw⟩, vw⟩, spw⟩ => ⟨P, hw vw spw⟩
  unfold Tail.rest
  refine WP.seq ((load_ok hp hc hc.inv.x21).mono
    fun s₂ ⟨a₂, x20₂, x8₂, x7₂, m₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_)
  -- The kernel, on the last chunk.
  let W := dp s₀ + BitVec.ofNat 64 (512 * (T - 1))
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, hc.inv.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, hc.inv.wr]
  have x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by rw [g₂ _ (by decide), hc.x0]
  have x3₂ : s₂.gpr .x3 = off (cx s₀) 128 := by rw [g₂ _ (by decide), hc.x3]
  have hin : ∀ k : Fin 16, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₂, oo, rd₂', wr₂']; exact hp.in_ctx' (by omega)
  have hw : ∀ d, d + 16 ≤ 256 → InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₂, oo, wr₂']; exact hp.in_ctx (by omega)
  have hst : (⟨s₂.gpr .x0, 64⟩ : Region).Disjoint ⟨s₂.gpr .x3, 256⟩ := by
    rw [x0₂, x3₂]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hrd : Readable W s₂ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₂', wr₂', VG.Proof.ChaCha20.AArch64.Xor.add_ofNat]
      exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega) (by omega)⟩
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
  have x20₂' : s₂.gpr .x20 = W := by rw [x20₂, hc.x22, pre_eq]
  refine WP.seq ((kernel_ok sve x20₂' hin hw hst hrd a₂).mono
    fun s₃ ⟨ks₃, f₃, hv₃, h2₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  have g₃' (r : Reg) (h1 : r ≠ .x1) (h4 : r ≠ .x4) (hp' : r ∉ Poly.regs) : s₃.gpr r = s₂.gpr r :=
    g₃ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4⟩) hp'
  have x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by rw [g₃' _ (by decide) (by decide) (by decide), x0₂]
  rw [x3₂] at ks₃ f₃
  -- The accumulator stored.
  refine WP.seq ((out_ok hp x0₃ (by rw [rd₃, rd₂']) (by rw [wr₃, wr₂'])).mono
    fun s₄ ⟨acc₄, f₄, st₄, x21₄, x27₄, x28₄, x22₄, x20₄, x23₄, g₄, rd₄, wr₄, sp₄, v₄⟩ => ?_)
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T) := by
    rw [g₄ _ (by decide), g₃' _ (by decide) (by decide) (by decide), g₂ _ (by decide), hc.x2]
  -- `m` bytes of the rest.
  refine WP.seq ((take_ok (r := L s₀ - 512 * T) (by omega) x2₄).mono
    fun s₅ ⟨x23₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  have x21₅ : s₅.gpr .x21 = cx s₀ := by rw [g₅ _ (by decide) (by decide), x21₄]
  have x22₅ : s₅.gpr .x22 = dp s₀ + BitVec.ofNat 64 (512 * T) := by
    rw [g₅ _ (by decide) (by decide), x22₄, g₃' _ (by decide) (by decide) (by decide), x7₂, hc.x1]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄, rd₃, rd₂']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, wr₃, wr₂']
  refine WP.seq ((Short.xorKsAt_ok hp (o := 512 * T) (n := min (L s₀ - 512 * T) 256) (by omega)
    (by omega) x21₅ x22₅ x23₅ rd₅' wr₅').mono fun s₆ ⟨k₆, d₆, f₆, g₆⟩ => ?_)
  -- The stream's arguments.
  have g₆' (r : Reg) (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12)
      (h13 : r ≠ .x13) : s₆.gpr r = s₅.gpr r :=
    g₆ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13⟩)
  refine (args_ok (s₀ := s₀) (D := dp s₀ + BitVec.ofNat 64 (512 * T))
    (m := min (L s₀ - 512 * T) 256) (r := L s₀ - 512 * T) (Nat.min_le_left _ _)
    (by rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), x21₅])
    (by rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), x22₅])
    (by rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), x23₅])
    (by rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₅ _ (by decide) (by decide), x2₄])).mono
    fun s₇ ⟨x0₇, x1₇, x2₇, x3₇, x23₇, g₇, m₇, rd₇, wr₇⟩ =>
      ⟨512 * T + min (L s₀ - 512 * T) 256, fun vw spw => ?_⟩
  -- The frames.
  have hM : 512 * T + min (L s₀ - 512 * T) 256 ≤ L s₀ := by omega
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (512 * T), min (L s₀ - 512 * T) 256⟩ (dR s₀) :=
    Offset.sub_base _ hM
  let tgt := [sub s₀ 64 408, sub s₀ 32 16, dR s₀]
  have c64 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, List.mem_cons_self, sub_sub s₀ h₁ (by omega) (by lit_omega)⟩
  have F₁ : Frame tgt u.mem s₂.mem := by
    rw [m₂]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c64 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  have F₂ : Frame tgt s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c64 128 256 (by decide) (by decide)
  have F₃ : Frame tgt s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c64 448 24 (by decide) (by decide)
    · exact c64 112 4 (by decide) (by decide)
  have F₄ : Frame tgt s₅.mem s₇.mem := by
    rw [m₇]
    exact f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [tgt], dsub⟩
  have F : Frame tgt u.mem s₇.mem := F₁.trans (F₂.trans (F₃.trans (by rw [m₅] at F₄; exact F₄)))
  -- The context frames keep the data.
  have dctx : ∀ k < L s₀, s₅.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    have e₁ := data_frame (s₀ := s₀) f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
    have e₂ := data_frame (s₀ := s₀) f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk
    have e₃ := data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
    rw [m₅, e₁, e₂, m₂, e₃]
  have dout : ∀ k < L s₀, (k < 512 * T ∨ 512 * T + min (L s₀ - 512 * T) 256 ≤ k) →
      s₇.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk hout
    rw [m₇, f₆ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact not_in hout (by omega) (by omega),
      dctx k hk]
  -- Registers.
  have g₇' (r : Reg) (h0 : r ≠ .x0) (h1 : r ≠ .x1) (h2 : r ≠ .x2) (h3 : r ≠ .x3) (h23 : r ≠ .x23) :
      s₇.gpr r = s₆.gpr r :=
    g₇ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h0, h1, h2, h3, h23⟩)
  have to₄ (r : Reg) (h0 : r ≠ .x0) (h1 : r ≠ .x1) (h2 : r ≠ .x2) (h3 : r ≠ .x3) (h23 : r ≠ .x23)
      (h9 : r ≠ .x9) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12) (h13 : r ≠ .x13) :
      s₇.gpr r = s₄.gpr r := by
    rw [g₇' r h0 h1 h2 h3 h23, g₆' r h9 h10 h11 h12 h13, g₅ r h9 h23]
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₃.mem.readW (off (cx s₀) d) 64 = s₂.mem.readW (off (cx s₀) d) 64 :=
    f₃.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega) (by omega) (by lit_omega)) (by decide)
  have un₇ : ∀ r ∈ untouched, s₇.gpr r = s₀.gpr r := by
    intro r hr
    have hu := hc.inv.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), g₄ _ (by decide), g₃' _ (by decide) (by decide) (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), x20₄, g₃' _ (by decide) (by decide) (by decide), x8₂, hu]
    · rw [to₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), g₄ _ (by decide), g₃' _ (by decide) (by decide) (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), x27₄, r32 32 (.inl rfl), m₂, memIn_800, hu]
    · rw [to₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), x28₄, r32 40 (.inr rfl), m₂, memIn_808, hu]
  have x21₇ : s₇.gpr .x21 = cx s₀ := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), x21₅]
  have x22₇ : s₇.gpr .x22 = dp s₀ + BitVec.ofNat 64 (512 * T) := by
    rw [g₇' _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), x22₅]
  have rd₇' : s₇.rd = s₀.rd := by rw [rd₇, k₆.rd, rd₅']
  have wr₇' : s₇.wr = s₀.wr := by rw [wr₇, k₆.wr, wr₅']
  -- The counter.
  have st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt u.mem (off (cx s₀) 64) := by
    rw [m₂]
    exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame (memIn_frame (s₀ := s₀) _ _ _) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = stateAt s₂.mem (off (cx s₀) 64) :=
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have st₇ : stateAt s₇.mem (off (cx s₀) 64) = stateAt s₄.mem (off (cx s₀) 64) := by
    rw [m₇, ← m₅]
    exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right dsub
  -- The data before the rest is kept.
  have pfx : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' → (∀ r ∈ rs, (dR s₀).Disjoint r) →
      bytesAt m' (dp s₀) (512 * T) = bytesAt m (dp s₀) (512 * T) :=
    fun hf hd => prefix_frame hf hd (by omega)
  have b₅ : bytesAt s₅.mem (dp s₀) (512 * T) = bytesAt s₂.mem (dp s₀) (512 * T) := by
    rw [m₅, pfx f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)),
      pfx f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega))]
  have b₇ : bytesAt s₇.mem (dp s₀) (512 * T) = bytesAt s₂.mem (dp s₀) (512 * T) := by
    rw [m₇, ← b₅]
    exact bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)) (by omega)
  have b₂ : ∀ n ≤ 512 * T, bytesAt s₂.mem (dp s₀) n = bytesAt u.mem (dp s₀) n := fun n hn => by
    rw [m₂]
    exact prefix_frame (memIn_frame (s₀ := s₀) _ _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) (by omega)
  have hsplit : bytesAt s₂.mem (dp s₀) (512 * T) =
      bytesAt s₂.mem (dp s₀) (512 * (T - 1)) ++ bytesAt s₂.mem W 512 := by
    rw [← Poly1305.bytesAt_add, show 512 * (T - 1) + 512 = 512 * T by omega]
  have hmac := hc.mac
  simp only [ite_true, pre] at hmac
  have hml : msg.length % 16 = 0 := by
    have := hmac.1
    rw [List.length_append, Poly1305.length_bytesAt] at this
    omega
  refine ⟨⟨x21₇, un₇, by rw [spw, hc.inv.sp], rd₇', wr₇', hc.inv.saved.frame F (fun r hr => ?_),
      hc.inv.frame.trans (F.sub fun r hr => ?_)⟩, hM, by have := hc.lt; omega, by omega, by omega,
    fun h => by omega,
    x0₇, by rw [x1₇, VG.Proof.ChaCha20.AArch64.Xor.add_ofNat],
    by rw [x2₇, show L s₀ - 512 * T - min (L s₀ - 512 * T) 256 =
      L s₀ - (512 * T + min (L s₀ - 512 * T) 256) by omega], x3₇, x22₇, x23₇, fun hlt => ?_,
    fun k hk => ?_, hc.frame.trans F, ⟨?_, ?_, ?_⟩, fun r hr => (vw r hr).trans (hc.vec r hr)⟩
  · simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  · simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  · -- The counter, past the four blocks.
    have h256 : min (L s₀ - 512 * T) 256 = 256 := by omega
    rw [st₇, st₄, st₃, st₂, hc.cnt, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add, h256,
      show (512 * T + 256) / 64 = 8 * T + 4 by omega]
  · -- The data.
    by_cases h₁ : k < 512 * T
    · rw [dout k hk (.inl h₁), hc.data k hk, ite_eq_left h₁, ite_eq_left (by omega)]
    by_cases h₂ : k < 512 * T + min (L s₀ - 512 * T) 256
    · have hi : k - 512 * T < min (L s₀ - 512 * T) 256 := by omega
      have e := d₆ (k - 512 * T) hi
      rw [show 512 * T + (k - 512 * T) = k by omega] at e
      rw [m₇, e, dctx k hk, hc.data k hk, ite_eq_right h₁, ite_eq_left h₂]
      congr 1
      have k₅ : s₅.mem (Short.kp' s₀ + BitVec.ofNat 64 (k - 512 * T)) =
          s₃.mem (off (cx s₀) 128 + BitVec.ofNat 64 (k - 512 * T)) := by
        rw [m₅]
        exact f₄.bytes (R := ⟨off (cx s₀) 128, 256⟩) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (show 256 ≤ 2 ^ 64 by decide) (show k - 512 * T < 256 by omega)
      rw [k₅, ks₃ _ (by omega), x0₂, st₂, hc.cnt, KS1,
        ks_shift _ hk (q := 8 * T) (by omega), show 64 * (8 * T) = 512 * T by omega]
    · rw [dout k hk (.inr (by omega)), hc.data k hk, ite_eq_right h₁, ite_eq_right h₂]
  · -- The message's length.
    show (msg ++ bytesAt s₇.mem (dp s₀) (512 * T)).length % 16 = 0
    rw [List.length_append, Poly1305.length_bytesAt]; omega
  · -- The key.
    have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    have e := hmac.2.1
    rw [k24] at e ⊢
    rw [bytesAt_frame F (fun r hr => by
        simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))))
      (by lit_omega)]
    exact e
  · -- The accumulator.
    have l₇ : Spec.Poly1305.leNum (bytesAt s₇.mem (off (cx s₀) 448) 24) =
        Spec.Poly1305.leNum (bytesAt s₄.mem (off (cx s₀) 448) 24) := by
      rw [m₇, ← m₅, bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right dsub) (by lit_omega)]
    have hlt := Poly1305.accumulate_lt (Rk key) (msg ++ bytesAt u.mem (dp s₀) (512 * (T - 1)))
    rw [l₇, acc₄ h2₃, show hacc s₃ = Poly.hval s₃ from rfl, hv₃,
      Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₇, hsplit, ← List.append_assoc,
      b₂ _ (by omega)]
    exact (Poly1305.accumulate_append (r := Rk key) (a := msg ++ bytesAt u.mem (dp s₀) (512 * (T - 1)))
      (by rw [List.length_append, Poly1305.length_bytesAt]; omega)).symm

theorem wp_seq3 {a b c x : Prog isa} {s : State} {Q' Q : State → Prop}
    (h : WP isa (.seq a (.seq b c)) s Q') (hx : ∀ t, Q' t → WP isa x t Q) :
    WP isa (.seq a (.seq b (.seq c x))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine h.mono fun t ht => ?_
  rw [WP.seq_iff] at ht ⊢
  exact ht.mono fun t' ht' => WP.seq (ht'.mono hx)

/-- `cryptStitched` when encrypting. -/
theorem cryptStitchedSeal_ok (sve : Bool) {s₀ : State} (hp : APre true s₀) {s : State}
    (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptStitched sve true) s fun u => ∃ P A, Sealed s₀ s key msg P A u := by
  unfold cryptStitched afterBulk
  simp only [ite_true]
  refine WP.seq ((setup_ok hp h).mono fun s₂ ⟨m₂, x0₂, x1₂, x2₂, x3₂, x5₂, _, _, k₂, v₂⟩ => ?_)
  apply WP.ite (decide (L s₀ < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short x5₂)
  · intro hs
    exact WP.block_nil ⟨_, _, (short_crypted true hp h hst hr m₂ x0₂ x1₂ x2₂ x3₂ k₂ v₂
      (of_decide_eq_true hs)).sealed⟩
  · intro hs
    refine wp_seq3 (long_crypted (sve := sve) true hp h hst hr m₂ x0₂ x1₂ x2₂ x3₂ k₂ v₂
      (by have := of_decide_eq_false hs; omega)) fun u ⟨T, hT, hc⟩ => ?_
    have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
    refine WP.ite (decide (L s₀ - 512 * T = 0)) (by
        rw [show isa.eval (.zero .x .x2) u = some (u.gpr .x2 == 0) from
          VG.Proof.ChaCha20.AArch64.Xor.eval_zero u .x2, hc.x2,
          VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega)]) (fun _ => ?_) (fun hz => ?_)
    · exact WP.block_nil ⟨_, _, hc.sealed⟩
    · have h₁ := of_decide_eq_false hz
      have hle := hc.le
      exact (rest_ok sve hp hc hT (by omega)).mono fun w ⟨P, hw⟩ => ⟨P, _, hw⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Tail
