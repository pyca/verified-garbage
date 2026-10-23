module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Fused
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ChaCha20-Poly1305 on AArch64: the MAC's input absorbed in one pass

`Fused.macAll` leaves the Poly1305 state as `macPad` twice and
`absorbLengths` do (`macAll_ok`): the accumulator stays in registers
(`HInv`) from `setup` to `storeH`, through each segment (`seg_ok`) and its
padded last block (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Fused

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Fused
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_addImm wp_mov wp_lsr eval_zero eval_nonzero_ofNat
  ofNat_beq_zero add_ofNat sub_ofNat)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Proof.Poly1305.AArch64.Radix64 (HInv HInv.of_regs setup_hinv absorb_hinv loop_hinv
  epilogue_hinv)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-- Code without calls keeps every register that none of its instructions writes. -/
theorem WP.keepRegs {c : Prog isa} {s : State} {Q : State → Prop} (L : List Reg) (h : WP isa c s Q)
    (hc : ((instrs c).all fun i => L.all fun r => !clobbers i r) = true) (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ (∀ r ∈ L, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), Exec.rdwr he⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- The registers that hold the key and the accumulator. -/
abbrev accRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x17]

theorem hinv_keep {R A : Nat} {X : List Byte} {s s' : State} (h : HInv R A X s)
    (hk : ∀ r ∈ accRegs, s'.gpr r = s.gpr r) : HInv R A X s' :=
  h.of_regs hk

/-! ## The padded last block -/

theorem tail_eq : tail =
    .seq (.block [.movz .x .x11 0 0, .str .x .x11 .x21 16, .str .x .x11 .x21 24, .addImm .x .x9 .x21 16])
    (.seq (.loop (.block copyBody) (.nonzero .x .x10))
      (.block (.addImm .x .x1 .x21 16 :: Impl.Poly1305.AArch64.Radix64.absorb true))) := rfl

theorem copyLoop_keeps : ((instrs (.loop (.block copyBody) (.nonzero .x .x10) : Prog isa)).all fun i =>
    (Reg.x21 :: accRegs).all fun r => !clobbers i r) = true := by decide +kernel

/-- The `t` (1 to 15) bytes at `x1 = Q`, padded with zeros, absorbed. -/
theorem tail_ok {s₀ : State} (hp : APre e s₀) {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16)
    (hx1 : s.gpr .x1 = Q) (hx10 : s.gpr .x10 = BitVec.ofNat 64 t) (hx21 : s.gpr .x21 = cx s₀)
    (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ 16 16))
    {R A : Nat} {X : List Byte} (hI : HInv R A X s) :
    WP isa tail s fun s' => HInv R A (X ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) s' ∧
      Frame [sub s₀ 16 16] s.mem s'.mem := by
  rw [tail_eq]
  refine WP.seq (WP.mono (WP.withSp (padZ_ok hp hx21 hwr)) fun s₂ ⟨⟨x9₂, g₂, rd₂, wr₂, f₂, z₂⟩, sp₂⟩ => ?_)
  have hd' : ∀ j < t, ∀ r ∈ [sub s₀ 16 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  have acc₂ : ∀ r ∈ accRegs, s₂.gpr r = s.gpr r := fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => CpInv s₀ s₂ Q t t s₃ ∧ (∀ r ∈ Reg.x21 :: accRegs, s₃.gpr r = s₂.gpr r))
    (WP.mono (WP.keepRegs (Reg.x21 :: accRegs) ?_ copyLoop_keeps (by decide)) fun s₃ ⟨h₃, k₃, _⟩ => ⟨h₃, k₃⟩)
    fun s₃ ⟨h₃, k₃⟩ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval (.nonzero .x .x10) s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval (.nonzero .x .x10) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI)
        fun s' h' => ?_
      have hz := eval_nonzero_ofNat s' .x10 (by lit_omega) h'.x10
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz]; simp; omega, t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), hx1]; simp,
      by rw [x9₂], by rw [g₂ _ (by decide) (by decide), hx10]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have x21₃ : s₃.gpr .x21 = cx s₀ := by
    rw [k₃ .x21 (by simp), g₂ _ (by decide) (by decide), hx21]
  refine wp_addImm (by decide) fun s₄ u₄ => ?_
  have x1₄ : s₄.gpr .x1 = off (cx s₀) 16 := by rw [u₄.gpr, x21₃]
  have hI₄ : HInv R A X s₄ := hinv_keep hI fun r hr => by
    rw [u₄.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₃ r (List.mem_cons_of_mem _ hr), acc₂ r hr]
  have hb : ∀ d, d + 8 ≤ 16 → InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [x1₄, u₄.rd, u₄.wr, h₃.rd, h₃.wr, rd₂, wr₂, hwr,
      show off (cx s₀) 16 + BitVec.ofNat 64 d = off (cx s₀) (16 + d) from off_off _ _ _]
    obtain ⟨r, hr, hc⟩ := hp.in_ctx (a := 16 + d) (w := 8) (by lit_omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (absorb_hinv s₄ hI₄ (hb 0 (by decide)) (hb 8 (by decide))) fun s₅ ⟨h₅, k₅⟩ => ?_
  have m₅ : s₅.mem = s₃.mem := by rw [k₅.2.1, u₄.mem]
  refine ⟨?_, by rw [m₅]; exact f₂.trans h₃.frame⟩
  have hbytes : bytesAt s₄.mem (s₄.gpr .x1) 16 = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
    rw [x1₄, u₄.mem, padded_bytes ht h₃.buf]
    refine congrArg (· ++ _) ?_
    simp only [bytesAt]
    apply List.map_congr_left
    intro j hj
    exact src₂ j (List.mem_range.mp hj)
  rw [← hbytes]
  exact h₅

/-! ## One padded segment -/

theorem segA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [mov .x1 p, .lsr .x .x2 n 4]) s fun s' =>
      s'.gpr .x1 = s.gpr p ∧ s'.gpr .x2 = s.gpr n >>> 4 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_mov fun _ u₁ => wp_lsr (by decide) fun _ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ hr.n_ne.2.1],
      fun r h₁ h₂ => by rw [u₂.other _ h₂, u₁.other _ h₁], by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr]⟩

theorem segC_ok (n : Reg) (s : State) :
    WP isa (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60]) s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 ((s.gpr n).toNat % 16) ∧ (∀ r, r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  wp_lsl (by decide) fun _ u₁ => wp_lsr (by decide) fun _ u₂ => WP.block_nil
    ⟨by rw [u₂.gpr, u₁.gpr, shl_shr60], fun r h => by rw [u₂.other _ h, u₁.other _ h],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩

theorem loop_keeps : ((instrs loop).all fun i =>
    [Reg.x7, .x8, .x17, .x21, .x22, .x23, .x24, .x25].all fun r => !clobbers i r) = true := by
  decide +kernel

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem seg_ok {s₀ : State} (hp : APre e s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hx21 : s.gpr .x21 = cx s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len)
    {R A : Nat} {X : List Byte} (hI : HInv R A X s) :
    WP isa (seg p n) s fun s' =>
      HInv R A (X ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) s' ∧
      Frame [sub s₀ 16 16] s.mem s'.mem := by
  have hpn := hr.p_ne
  have hnn := hr.n_ne
  have hlt := hs.lt
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hin : ∀ d w, d + w ≤ len → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 d) w := fun d w hd => by
    rw [hrd, hwr]
    exact hs.cov _ _ ⟨_, List.mem_singleton_self _, contains_off_sub hd (Region.contains_self _ _)⟩
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  unfold seg
  refine WP.seq (WP.mono (segA_ok hr s) fun s₁ ⟨x1₁, x2₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have acc₁ : ∀ r ∈ accRegs, s₁.gpr r = s.gpr r := fun r hr' => g₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'; rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'; rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [hP] at x1₁
  rw [hn, shr4_ofNat hlt] at x2₁
  -- After the whole blocks.
  let Q₂ : State → Prop := fun s₂ =>
    HInv R A (X ++ bytesAt s.mem P (16 * (len / 16))) s₂ ∧
    s₂.gpr .x1 = P + BitVec.ofNat 64 (16 * (len / 16)) ∧ s₂.gpr .x21 = cx s₀ ∧ s₂.gpr n = s.gpr n ∧
    s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr
  refine WP.seq (WP.mono (Q := Q₂) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (len / 16 = 0)) (by
      have e : isa.eval (.zero .x .x2) s₁ = some (s₁.gpr .x2 == 0) := eval_zero s₁ .x2
      rw [e, x2₁, ofNat_beq_zero (by lit_omega)]) (fun h => ?_) (fun h => ?_)
    · have h0 : len / 16 = 0 := by simpa using h
      refine WP.block_nil ⟨?_, by rw [x1₁, h0]; simp, by rw [g₁ _ (by decide) (by decide), hx21],
        g₁ n hnn.2.1 hnn.2.2.1, m₁, rd₁, wr₁⟩
      rw [h0, show bytesAt s.mem P (16 * 0) = [] by simp [bytesAt], List.append_nil]
      exact hinv_keep hI acc₁
    · have h0 : len / 16 ≠ 0 := by simpa using h
      refine WP.mono (WP.keepRegs [Reg.x7, .x8, .x17, .x21, .x22, .x23, .x24, .x25]
        (loop_hinv s₁ (hinv_keep hI acc₁) x1₁ x2₁ (Nat.pos_of_ne_zero h0) (by lit_omega)
          (fun d hd => by rw [rd₁, wr₁]; exact hin d 8 (by omega))) loop_keeps (by decide))
        fun s₂ ⟨⟨hI₂, x1₂, k₂⟩, kr₂, rd₂, wr₂, _⟩ => ?_
      have n₂ : s₂.gpr n = s.gpr n := by
        rw [kr₂ n (by rcases hr.2 with rfl | rfl <;> decide), g₁ n hnn.2.1 hnn.2.2.1]
      refine ⟨by rw [m₁] at hI₂; exact hI₂, x1₂, by rw [kr₂ .x21 (by decide), g₁ _ (by decide) (by decide), hx21],
        n₂, by rw [k₂.2.1, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  obtain ⟨hI₂, x1₂, x21₂, n₂, m₂, rd₂, wr₂⟩ := h₂
  refine WP.seq (WP.mono (segC_ok n s₂) fun s₃ ⟨x10₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  rw [n₂, hn, toNat_ofNat_lt hlt] at x10₃
  have acc₃ : ∀ r ∈ accRegs, s₃.gpr r = s₂.gpr r := fun r hr' => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'; rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hI₃ := hinv_keep hI₂ acc₃
  refine WP.ite (decide (len % 16 = 0)) (by
      have e : isa.eval (.zero .x .x10) s₃ = some (s₃.gpr .x10 == 0) := eval_zero s₃ .x10
      rw [e, x10₃, ofNat_beq_zero (by lit_omega)]) (fun h => ?_) (fun h => ?_)
  · have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨?_, by rw [m₃, m₂]; exact Frame.refl _ _⟩
    rw [show pad16 (bytesAt s.mem P len) = [] by simp [VG.Spec.ChaCha20Poly1305.pad16, hlen, h0],
      List.append_nil, ← show 16 * (len / 16) = len by omega]
    exact hI₃
  · have h0 : len % 16 ≠ 0 := by simpa using h
    have hsrc : ∀ j < len % 16, InRegions (s₃.rd ++ s₃.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [add_ofNat, rd₃, wr₃, rd₂, wr₂]
      exact hin _ 1 (by omega)
    have hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ 16 16) := fun j hj => by
      rw [add_ofNat]
      exact (Src.disj_sub (hcP.sub_left (sub_ctx s₀ (by lit_omega))) (a := 16 * (len / 16) + j) (n := 1)
        (by lit_omega)).symm
    refine WP.mono (tail_ok hp (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by lit_omega) (by lit_omega) (by rw [g₃ _ (by decide), x1₂]) x10₃
      (by rw [g₃ _ (by decide), x21₂]) (by rw [wr₃, wr₂, hwr]) hsrc hdj hI₃) fun s₄ ⟨hI₄, f₄⟩ => ?_
    refine ⟨?_, by rw [m₃, m₂] at f₄; exact f₄⟩
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by
      simp [VG.Spec.ChaCha20Poly1305.pad16, hlen, h0], x_eq, m₃, m₂] at *
    simpa only [List.append_assoc] using hI₄

/-! ## The whole input -/

theorem segA_keeps : ((instrs (seg .x24 .x25)).all fun i =>
    (Reg.x0 :: preserved).all fun r => !clobbers i r) = true := by decide +kernel

theorem segD_keeps : ((instrs (seg .x22 .x23)).all fun i =>
    (Reg.x0 :: preserved).all fun r => !clobbers i r) = true := by decide +kernel

/-- The clamped key and the accumulator of the state at `ctx + 448` survive a
frame apart from it. -/
theorem st_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 448 128).Disjoint r) :
    Proof.Poly1305.AArch64.Rk m' (off (cx s₀) 448) = Proof.Poly1305.AArch64.Rk m (off (cx s₀) 448) ∧
    Spec.Poly1305.leNum (bytesAt m' (off (cx s₀) 448) 24) =
      Spec.Poly1305.leNum (bytesAt m (off (cx s₀) 448) 24) := by
  have e : Proof.Poly1305.AArch64.off (off (cx s₀) 448) 24 = off (cx s₀) 472 := off_off _ _ _
  constructor
  · rw [← Proof.Poly1305.AArch64.clamp_key, ← Proof.Poly1305.AArch64.clamp_key, e,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left
        (sub_sub s₀ (a := 448) (m := 128) (k := 472) (n := 32) (by lit_omega) (by lit_omega) (by lit_omega)))
        (by lit_omega)]
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left
        (sub_sub s₀ (a := 448) (m := 128) (k := 448) (n := 24) (by lit_omega) (by lit_omega) (by lit_omega)))
        (by lit_omega)]

theorem macAll_eq : macAll =
    .seq (.block (([.addImm .x .x0 .x21 448] : List Instr) ++ Impl.Poly1305.AArch64.Radix64.setup))
    (.seq (seg .x24 .x25)
    (.seq (seg .x22 .x23)
      (.block ((.addImm .x .x1 .x21 0 :: Impl.Poly1305.AArch64.Radix64.absorb true) ++
        (Impl.Poly1305.AArch64.Radix64.reduce ++ Impl.Poly1305.AArch64.Radix64.storeH))))) := by
  simp only [macAll, List.append_assoc, List.singleton_append]

/-- The registers each part writes are not callee-saved. -/
theorem pres_ne : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧
    r ∉ [Reg.x4, .x5, .x6, .x7, .x8, .x16, .x17] := by decide

/-- `x0` and `setup`. -/
theorem first_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block (([.addImm .x .x0 .x21 448] : List Instr) ++ Impl.Poly1305.AArch64.Radix64.setup)) s
      fun s₂ => HInv (Proof.Poly1305.AArch64.Rk s.mem (off (cx s₀) 448))
          (Spec.Poly1305.leNum (bytesAt s.mem (off (cx s₀) 448) 24)) [] s₂ ∧
        s₂.gpr .x0 = off (cx s₀) 448 ∧ (∀ r, r ≠ .x0 → r ∉ [Reg.x4, .x5, .x6, .x7, .x8, .x16, .x17] →
          s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  have wrS : Covers [sub s₀ 448 128] s₀.wr := covers1 hp rfl (by lit_omega)
  refine WP.block_append (wp_addImm (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have x0₁ : s₁.gpr .x0 = off (cx s₀) 448 := by rw [u₁.gpr, h.x21]
  have wr₁ : s₁.wr = s₀.wr := by rw [u₁.wr, h.wr]
  refine WP.narrow (rd := []) (wr := [sub s₀ 448 128])
    (setup_hinv (s₁.withRegions [] [sub s₀ 448 128]) (by
      simp only [State.withRegions_gpr, State.withRegions_wr, x0₁]; exact List.mem_singleton_self _))
    (Covers.right (by rw [wr₁]; exact wrS)) (by rw [wr₁]; exact wrS) fun s₂ rd₂ wr₂ _ _ ⟨hI₂, k₂⟩ => ?_
  have g₂ : ∀ r, r ∉ [Reg.x4, .x5, .x6, .x7, .x8, .x16, .x17] → s₂.gpr r = s₁.gpr r := fun r hr => by
    simpa only [State.withRegions_gpr] using k₂.1 r hr
  have m₂ : s₂.mem = s₁.mem := by simpa only [State.withRegions_mem] using k₂.2.1
  simp only [State.withRegions_gpr, State.withRegions_mem, x0₁, u₁.mem] at hI₂
  refine ⟨hinv_keep hI₂ fun r _ => by simp only [State.withRegions_gpr], by rw [g₂ _ (by decide), x0₁],
    fun r h₀ hr => by rw [g₂ r hr, u₁.other r h₀], by rw [m₂, u₁.mem], by rw [rd₂, u₁.rd],
    by rw [wr₂, u₁.wr]⟩

/-- The lengths block, `reduce` and `storeH`. -/
theorem last_ok {s₀ : State} (hp : APre e s₀) {s : State} {R A : Nat} {X : List Byte}
    (hI : HInv R A X s) (hx0 : s.gpr .x0 = off (cx s₀) 448) (hx21 : s.gpr .x21 = cx s₀)
    (hwr : s.wr = s₀.wr)
    (hR : Proof.Poly1305.AArch64.Rk s.mem (off (cx s₀) 448) = R)
    (hA : Spec.Poly1305.leNum (bytesAt s.mem (off (cx s₀) 448) 24) = A) :
    WP isa (.block ((.addImm .x .x1 .x21 0 :: Impl.Poly1305.AArch64.Radix64.absorb true) ++
        (Impl.Poly1305.AArch64.Radix64.reduce ++ Impl.Poly1305.AArch64.Radix64.storeH))) s fun s' =>
      (∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (X ++ bytesAt s.mem (off (cx s₀) 0) 16))) ∧
      Frame [sub s₀ 448 128] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wrS : Covers [sub s₀ 448 128] s₀.wr := covers1 hp rfl (by lit_omega)
  refine WP.block_append (wp_addImm (by decide) fun s₅ u₅ => ?_)
  have x1₅ : s₅.gpr .x1 = off (cx s₀) 0 := by rw [u₅.gpr, hx21]
  have hb : ∀ d, d + 8 ≤ 16 → InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [x1₅, u₅.rd, u₅.wr, hwr, show off (cx s₀) 0 + BitVec.ofNat 64 d = off (cx s₀) (0 + d) from off_off _ _ _]
    obtain ⟨r, hr, hc⟩ := hp.in_ctx (a := 0 + d) (w := 8) (by lit_omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (absorb_hinv s₅ (hinv_keep hI fun r hr => u₅.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (hb 0 (by decide)) (hb 8 (by decide)))
    fun s₆ ⟨hI₆, k₆⟩ => ?_
  have x0₆ : s₆.gpr .x0 = off (cx s₀) 448 := by rw [k₆.gpr', u₅.other _ (by decide), hx0]
  have m₆ : s₆.mem = s.mem := by rw [k₆.2.1, u₅.mem]
  have wr₆ : s₆.wr = s₀.wr := by rw [k₆.2.2.2, u₅.wr, hwr]
  rw [x1₅, u₅.mem] at hI₆
  refine WP.narrow (rd := []) (wr := [sub s₀ 448 128])
    (epilogue_hinv (s₆.withRegions [] [sub s₀ 448 128]) (hinv_keep hI₆ fun r _ => by
        simp only [State.withRegions_gpr])
      (by simp only [State.withRegions_gpr, State.withRegions_wr, x0₆]; exact List.mem_singleton_self _)
      (by simp only [State.withRegions_gpr, State.withRegions_mem, x0₆, m₆]; exact hR)
      (by simp only [State.withRegions_gpr, State.withRegions_mem, x0₆, m₆]; exact hA))
    (Covers.right (by rw [wr₆]; exact wrS)) (by rw [wr₆]; exact wrS)
    fun s₇ rd₇ wr₇ _ f₇ ⟨rep₇, _, _, _, _⟩ => ?_
  simp only [State.withRegions_gpr, State.withRegions_mem, x0₆, m₆] at rep₇
  refine ⟨fun key msg hr => by simpa only [List.append_assoc] using rep₇ key msg hr,
    by rw [← m₆]; exact f₇, by rw [rd₇, k₆.2.2.1, u₅.rd], by rw [wr₇, k₆.2.2.2, u₅.wr]⟩

/-- The additional data and the data, each padded, and the lengths block at
`ctx`, absorbed into the state at `ctx + 448`. -/
theorem macAll_ok {s₀ : State} (hp : APre e s₀) (srcA : Src s₀ (ad s₀) (AL s₀))
    (srcD : Src s₀ (dp s₀) (L s₀)) {s : State} (h : Inv s₀ s) :
    WP isa macAll s fun s' => Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++
          ((bytesAt s.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s.mem (ad s₀) (AL s₀))) ++
          ((bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++
            bytesAt s.mem (off (cx s₀) 0) 16))) := by
  rw [macAll_eq]
  refine WP.seq (WP.mono (WP.kept (first_ok hp h) rfl)
    fun s₂ ⟨⟨hI₂, x0₂, g₂, m₂, rd₂, wr₂⟩, cs₂, sp₂⟩ => ?_)
  have x21₂ : s₂.gpr .x21 = cx s₀ := by rw [g₂ _ (by decide) (by decide), h.x21]
  -- The additional data.
  refine WP.seq (WP.mono (WP.keepRegs (Reg.x0 :: preserved)
    (seg_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩ srcA x21₂ (by rw [rd₂, h.rd])
      (by rw [wr₂, h.wr]) (by rw [g₂ _ (by decide) (by decide), h.x24])
      (by rw [g₂ _ (by decide) (by decide), h.x25]; simp [AL]) hI₂) segA_keeps (by decide))
    fun s₃ ⟨⟨hI₃, f₃⟩, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  -- The data.
  refine WP.seq (WP.mono (WP.keepRegs (Reg.x0 :: preserved)
    (seg_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩ srcD
      (by rw [g₃ _ (by decide), x21₂]) (by rw [rd₃, rd₂, h.rd]) (by rw [wr₃, wr₂, h.wr])
      (by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), h.x22])
      (by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), h.x23, hL s₀]) hI₃)
      segD_keeps (by decide))
    fun s₄ ⟨⟨hI₄, f₄⟩, g₄, rd₄, wr₄, sp₄⟩ => ?_)
  have d16 : ∀ r ∈ [sub s₀ 16 16], (sub s₀ 448 128).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have f₂₄ : Frame [sub s₀ 16 16] s.mem s₄.mem := by rw [← m₂]; exact f₃.trans f₄
  obtain ⟨eR, eA⟩ := st_frame f₂₄ d16
  refine WP.mono (WP.kept (last_ok hp hI₄ (by rw [g₄ _ (by decide), g₃ _ (by decide), x0₂])
      (by rw [g₄ _ (by decide), g₃ _ (by decide), x21₂])
      (by rw [wr₄, wr₃, wr₂, h.wr]) eR eA) rfl)
    fun s₇ ⟨⟨rep₇, f₇, rd₇, wr₇⟩, cs₇, sp₇⟩ => ⟨⟨fun r hr _ => ?_, ?_, ?_, ?_, ?_⟩, fun key msg hr => ?_⟩
  · obtain ⟨h0, -, h4⟩ := pres_ne r hr
    rw [cs₇ r hr, g₄ r (List.mem_cons_of_mem _ hr), g₃ r (List.mem_cons_of_mem _ hr), g₂ r h0 h4]
  · rw [sp₇, sp₄, sp₃, sp₂]
  · rw [rd₇, rd₄, rd₃, rd₂]
  · rw [wr₇, wr₄, wr₃, wr₂]
  · exact (f₂₄.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [macR]).trans
      (f₇.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [macR])
  · have hr₄ : Repr s₄.mem (off (cx s₀) 448) key msg := Repr.frame f₂₄ d16 hr
    have := rep₇ key msg hr₄
    have eD : bytesAt s₃.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := by
      rw [bytesAt_frame f₃ (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact (srcD.ctx.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt srcD.lt), m₂]
    have eL : bytesAt s₄.mem (off (cx s₀) 0) 16 = bytesAt s.mem (off (cx s₀) 0) 16 :=
      bytesAt_frame f₂₄ (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact sub_disj s₀ (a := 0) (n := 16) (b := 16) (m := 16) (by lit_omega) (by lit_omega) (by lit_omega))
        (by lit_omega)
    rw [m₂, eD, eL] at this
    simpa only [List.nil_append, List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.AArch64.Fused
