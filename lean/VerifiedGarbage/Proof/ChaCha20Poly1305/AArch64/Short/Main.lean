module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Prologue
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.XorKs
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Fused
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Inline
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
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.AddS
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

/-! ### `ChaCha20Poly1305.AArch64.Fused`, which only this module used -/

section

/-! ### `Poly1305.AArch64.Radix64.Inline`, which only this module used -/

section

/-!
# Poly1305 radix 64 on AArch64, in a caller's code

`vg_poly1305_blocks`'s parts, run in a caller's own code: one `setup`, then
blocks absorbed from any number of places (`absorb true`, and the loop of
`blocks`), then one `reduce` and `storeH`. `HInv` is the accumulator in
registers between them: from `A`, the accumulator `setup` loaded, it has
absorbed the whole blocks `X`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Radix64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)

/-- The clamped key `R` in `x7`, `x8` and `x17`, and the accumulator in
`x4`–`x6`: from `A` (if it is less than `p`), the whole blocks `X` absorbed. -/
def HInv (R A : Nat) (X : List Byte) (s : State) : Prop :=
  Keys R s ∧ X.length % 16 = 0 ∧
    (A < P → hval s % P = Poly1305.absorbAll R A X % P ∧ Bounds s)

theorem HInv.of_regs {R A : Nat} {X : List Byte} {s s' : State} (h : HInv R A X s)
    (hr : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8, .x17], s'.gpr r = s.gpr r) : HInv R A X s' := by
  obtain ⟨hk, hx, ha⟩ := h
  refine ⟨hk.of_regs fun r hr' => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
    rcases hr' with rfl | rfl | rfl <;> simp only [reduceCtorEq, or_true, true_or]), hx, fun hA => ?_⟩
  obtain ⟨e, b⟩ := bounds_eq (s := s) (s' := s') fun r hr' => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
    rcases hr' with rfl | rfl | rfl <;> simp only [reduceCtorEq, or_true, true_or])
  obtain ⟨hv, hb⟩ := ha hA
  exact ⟨by rw [e]; exact hv, b hb⟩

/-- `setup` from the state at `x0`: the accumulator in it, with nothing yet absorbed. -/
theorem setup_hinv (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block setup) s fun s' =>
      HInv (Rk s.mem (s.gpr .x0)) (leNum (bytesAt s.mem (s.gpr .x0) 24)) [] s' ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x16, .x17] s s' :=
  (setup_ok s hw).mono fun _ ⟨hk, ha, k⟩ =>
    ⟨⟨hk, rfl, fun hA => by
      obtain ⟨e, b⟩ := ha hA
      exact ⟨by rw [e, Poly1305.absorbAll_nil], b⟩⟩, k⟩

/-- The value of a block of 16 bytes with the `0x01` byte appended. -/
theorem block16_value (m : Mem) (p : Addr) :
    w64 m p 0 + 2 ^ 64 * w64 m p 8 + 2 ^ 128 * true.toNat = leNum (bytesAt m p 16 ++ [0x01]) := by
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

/-- One block absorbed from `x1`. -/
theorem absorb_hinv (s : State) {R A : Nat} {X : List Byte} (h : HInv R A X s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (absorb true)) s fun s' =>
      HInv R A (X ++ bytesAt s.mem (s.gpr .x1) 16) s' ∧ Keeps absorbRegs s s' := by
  obtain ⟨hk, hx, ha⟩ := h
  refine (absorb_key_ok s true hk h0 h8).mono fun s' ⟨hab, k⟩ =>
    ⟨⟨hk.of_regs fun r hr => k.1 r ?_, ?_, fun hA => ?_⟩, k⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hx]
  · obtain ⟨hv, hb⟩ := ha hA
    obtain ⟨hv', hb'⟩ := hab hb
    refine ⟨?_, hb'⟩
    obtain hb1 : 0 < (bytesAt s.mem (s.gpr .x1) 16).length := by rw [Poly1305.length_bytesAt]; decide
    obtain hb2 : (bytesAt s.mem (s.gpr .x1) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
    rw [hv', show word s.mem (s.gpr .x1) 0 = w64 s.mem (s.gpr .x1) 0 from rfl,
      show word s.mem (s.gpr .x1) 8 = w64 s.mem (s.gpr .x1) 8 from rfl, block16_value, mod_step hv,
      Poly1305.absorbAll_append hx, Poly1305.absorbAll_block hb1 hb2]

theorem keeps_refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The loop of `blocks`: the `n` blocks at `x1 = p` (`x2 = n`, nonzero),
with `x1` left past them. -/
theorem loop_hinv {R A : Nat} {X : List Byte} (s₀ : State) (h : HInv R A X s₀) {p : Addr} {n : Nat}
    (hx1 : s₀.gpr .x1 = p) (hx2 : s₀.gpr .x2 = BitVec.ofNat 64 n) (hn0 : 0 < n) (hn : 16 * n < 2 ^ 64)
    (hin : ∀ d, d + 8 ≤ 16 * n → InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 d) 8) :
    WP isa (.loop (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) (.nonzero .x .x2)) s₀
      fun s' => HInv R A (X ++ bytesAt s₀.mem p (16 * n)) s' ∧
        s'.gpr .x1 = p + BitVec.ofNat 64 (16 * n) ∧ Keeps (.x1 :: .x2 :: absorbRegs) s₀ s' := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = n - i ∧ i < n ∧
    HInv R A (X ++ bytesAt s₀.mem p (16 * i)) s ∧ s.gpr .x1 = p + BitVec.ofNat 64 (16 * i) ∧
    s.gpr .x2 = BitVec.ofNat 64 (n - i) ∧ Keeps (.x1 :: .x2 :: absorbRegs) s₀ s
  obtain hstep : ∀ m s, Inv m s → WP isa (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) s
      (fun s' => (eval (.nonzero .x .x2) s' = some false ∧
        (HInv R A (X ++ bytesAt s₀.mem p (16 * n)) s' ∧ s'.gpr .x1 = p + BitVec.ofNat 64 (16 * n) ∧
          Keeps (.x1 :: .x2 :: absorbRegs) s₀ s')) ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hI, hx1', hx2', ks⟩
    obtain hrd : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8 := by
      intro d hd
      rw [hx1', Offset.add_add_eq _ (c := 16 * i + d) rfl, ks.2.2.1, ks.2.2.2]
      exact hin _ (by omega_using [hd, hi])
    refine WP.block_append (WP.mono (absorb_hinv s hI (hrd 0 (by decide)) (hrd 8 (by decide)))
      fun s₁ ⟨h₁, k₁⟩ => ?_)
    refine WP.mono (VG.Proof.Poly1305.AArch64.advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
    have k₂ : Keeps [.x1, .x2] s₁ s₂ := k₂
    obtain hI₂ : HInv R A (X ++ bytesAt s₀.mem p (16 * (i + 1))) s₂ := by
      obtain e : X ++ bytesAt s₀.mem p (16 * i) ++ bytesAt s.mem (s.gpr .x1) 16 =
          X ++ bytesAt s₀.mem p (16 * (i + 1)) := by
        rw [ks.2.1, hx1', List.append_assoc, show 16 * (i + 1) = 16 * i + 16 by omega_using [],
          Poly1305.bytesAt_add]
      rw [← e]
      exact h₁.of_regs fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    obtain ks₂ : Keeps (.x1 :: .x2 :: absorbRegs) s₀ s₂ :=
      ((ks.trans k₁).trans k₂).mono (by decide)
    obtain hx1₂ : s₂.gpr .x1 = p + BitVec.ofNat 64 (16 * (i + 1)) := by
      rw [a₁, k₁.gpr' (r := .x1), hx1', Offset.add_add, Nat.mul_succ]
    obtain hx2₂ : s₂.gpr .x2 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [a₂, k₁.gpr' (r := .x2), hx2', Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
    obtain hev : eval (.nonzero .x .x2) s₂ = some (BitVec.ofNat 64 (n - (i + 1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₂]
    by_cases hlast : i + 1 = n
    · left
      refine ⟨by rw [hev, hlast]; simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, bne_self_eq_false],
        hlast ▸ hI₂, hlast ▸ hx1₂, ks₂⟩
    · right
      obtain hne : n - (i + 1) ≠ 0 := by omega_using [hi, hlast]
      obtain h0 : BitVec.ofNat 64 (n - (i + 1)) ≠ 0 := by
        intro h
        obtain h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hn, h'])] at h'
        exact hne h'
      exact ⟨by rw [hev]; simpa using h0, n - (i + 1), by omega_using [hi, hne],
        i + 1, rfl, by omega_using [hi, hne], hI₂, hx1₂, hx2₂, ks₂⟩
  exact WP.loop (M := isa) Inv hstep n s₀ ⟨0, by omega_using [], hn0,
    by rw [show bytesAt s₀.mem p (16 * 0) = [] by simp [bytesAt], List.append_nil]; exact h,
    by rw [hx1]; simp only [Nat.mul_zero, BitVec.add_zero],
    by rw [hx2, Nat.sub_zero], keeps_refl _ _⟩

/-- `reduce` and `storeH`: the state at `x0`, from which `setup` loaded `R`
and `A`, then represents `msg ++ X` if it represented `msg`. -/
theorem epilogue_hinv (s : State) {R A : Nat} {X : List Byte}
    (h : HInv R A X s) (hw : sR (s.gpr .x0) ∈ s.wr)
    (hRk : Rk s.mem (s.gpr .x0) = R) (hA : leNum (bytesAt s.mem (s.gpr .x0) 24) = A) :
    WP isa (.block (reduce ++ storeH)) s fun s' =>
      (∀ key msg, Repr s.mem (s.gpr .x0) key msg → Repr s'.mem (s.gpr .x0) key (msg ++ X)) ∧
      Frame [hR (s.gpr .x0), wR (s.gpr .x0)] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14] → s'.gpr r = s.gpr r := by
  obtain ⟨_, hx, ha⟩ := h
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.gpr'
  refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.storeH_ok s₁ (by rw [k₁.2.2.2, x0₁]; exact hw))
    fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
  rw [x0₁, k₁.2.1] at m₂
  obtain hf : Frame [hR (s.gpr .x0), wR (s.gpr .x0)] s.mem s₂.mem := by
    rw [m₂]; exact storeHm_frame (Frame.refl _ _) _ _ _
  refine ⟨fun key msg hrep => ?_, hf, by rw [rd₂, k₁.2.2.1], by rw [wr₂, k₁.2.2.2],
    fun r hr' => by rw [g₂]; exact k₁.1 r hr'⟩
  obtain hA' : A < P := by
    have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
    rw [← hrep.2.2, hA] at this
    exact this
  obtain ⟨hv₀, hb⟩ := ha hA'
  obtain hN := hr hb
  have hk : bytesAt s.mem (s.gpr .x0 + 24) 32 = key := hrep.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append]; omega_using [hrep.1, hx]
  · rw [← off_24, key_frame hf, off_24]; exact hk
  · rw [m₂, storeHm_acc, ← hk, ← off_24, clamp_key, hRk, Poly1305.accumulate_append hrep.1]
    obtain hacc : accumulate R msg = A := by
      rw [← hA, hrep.2.2, ← hk, ← off_24, clamp_key, hRk]
    rw [hacc]
    change hval s₁ = _
    rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA' _)]

end VG.Proof.Poly1305.AArch64.Radix64

end

end


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
  obtain hd' : ∀ j < t, ∀ r ∈ [sub s₀ 16 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  obtain src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  obtain acc₂ : ∀ r ∈ accRegs, s₂.gpr r = s.gpr r := fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => CpInv s₀ s₂ Q t t s₃ ∧ (∀ r ∈ Reg.x21 :: accRegs, s₃.gpr r = s₂.gpr r))
    (WP.mono (WP.keepRegs (Reg.x21 :: accRegs) ?_ copyLoop_keeps (by decide)) fun s₃ ⟨h₃, k₃, _⟩ => ⟨h₃, k₃⟩)
    fun s₃ ⟨h₃, k₃⟩ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    obtain hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval (.nonzero .x .x10) s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval (.nonzero .x .x10) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI)
        fun s' h' => ?_
      obtain hz := eval_nonzero_ofNat s' .x10 (by lit_omega) h'.x10
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz]; simp; omega_using [hi, hl], t - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, hl], h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), hx1]; simp,
      by rw [x9₂], by rw [g₂ _ (by decide) (by decide), hx10]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  obtain x21₃ : s₃.gpr .x21 = cx s₀ := by
    rw [k₃ .x21 (by simp), g₂ _ (by decide) (by decide), hx21]
  refine wp_addImm (by decide) fun s₄ u₄ => ?_
  obtain x1₄ : s₄.gpr .x1 = off (cx s₀) 16 := by rw [u₄.gpr, x21₃]
  obtain hI₄ : HInv R A X s₄ := hinv_keep hI fun r hr => by
    rw [u₄.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₃ r (List.mem_cons_of_mem _ hr), acc₂ r hr]
  obtain hb : ∀ d, d + 8 ≤ 16 → InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [x1₄, u₄.rd, u₄.wr, h₃.rd, h₃.wr, rd₂, wr₂, hwr,
      show off (cx s₀) 16 + BitVec.ofNat 64 d = off (cx s₀) (16 + d) from off_off _ _ _]
    obtain ⟨r, hr, hc⟩ := hp.in_ctx (a := 16 + d) (w := 8) (by lit_omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (absorb_hinv s₄ hI₄ (hb 0 (by decide)) (hb 8 (by decide))) fun s₅ ⟨h₅, k₅⟩ => ?_
  obtain m₅ : s₅.mem = s₃.mem := by rw [k₅.2.1, u₄.mem]
  refine ⟨?_, by rw [m₅]; exact f₂.trans h₃.frame⟩
  obtain hbytes : bytesAt s₄.mem (s₄.gpr .x1) 16 = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
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
  obtain hin : ∀ d w, d + w ≤ len → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 d) w := fun d w hd => by
    rw [hrd, hwr]
    exact hs.cov _ _ ⟨_, List.mem_singleton_self _, contains_off_sub hd (Region.contains_self _ _)⟩
  obtain hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  obtain hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  obtain x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  unfold seg
  refine WP.seq (WP.mono (segA_ok hr s) fun s₁ ⟨x1₁, x2₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain acc₁ : ∀ r ∈ accRegs, s₁.gpr r = s.gpr r := fun r hr' => g₁ r (by
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
      obtain e : isa.eval (.zero .x .x2) s₁ = some (s₁.gpr .x2 == 0) := eval_zero s₁ .x2
      rw [e, x2₁, ofNat_beq_zero (by lit_omega)]) (fun h => ?_) (fun h => ?_)
    · have h0 : len / 16 = 0 := by simpa using h
      refine WP.block_nil ⟨?_, by rw [x1₁, h0]; simp, by rw [g₁ _ (by decide) (by decide), hx21],
        g₁ n hnn.2.1 hnn.2.2.1, m₁, rd₁, wr₁⟩
      rw [h0, show bytesAt s.mem P (16 * 0) = [] by simp [bytesAt], List.append_nil]
      exact hinv_keep hI acc₁
    · have h0 : len / 16 ≠ 0 := by simpa using h
      refine WP.mono (WP.keepRegs [Reg.x7, .x8, .x17, .x21, .x22, .x23, .x24, .x25]
        (loop_hinv s₁ (hinv_keep hI acc₁) x1₁ x2₁ (Nat.pos_of_ne_zero h0) (by lit_omega)
          (fun d hd => by rw [rd₁, wr₁]; exact hin d 8 (by omega_using [hd]))) loop_keeps (by decide))
        fun s₂ ⟨⟨hI₂, x1₂, k₂⟩, kr₂, rd₂, wr₂, _⟩ => ?_
      obtain n₂ : s₂.gpr n = s.gpr n := by
        rw [kr₂ n (by rcases hr.2 with rfl | rfl <;> decide), g₁ n hnn.2.1 hnn.2.2.1]
      refine ⟨by rw [m₁] at hI₂; exact hI₂, x1₂, by rw [kr₂ .x21 (by decide), g₁ _ (by decide) (by decide), hx21],
        n₂, by rw [k₂.2.1, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  obtain ⟨hI₂, x1₂, x21₂, n₂, m₂, rd₂, wr₂⟩ := h₂
  refine WP.seq (WP.mono (segC_ok n s₂) fun s₃ ⟨x10₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  rw [n₂, hn, toNat_ofNat_lt hlt] at x10₃
  obtain acc₃ : ∀ r ∈ accRegs, s₃.gpr r = s₂.gpr r := fun r hr' => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'; rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain hI₃ := hinv_keep hI₂ acc₃
  refine WP.ite (decide (len % 16 = 0)) (by
      obtain e : isa.eval (.zero .x .x10) s₃ = some (s₃.gpr .x10 == 0) := eval_zero s₃ .x10
      rw [e, x10₃, ofNat_beq_zero (by lit_omega)]) (fun h => ?_) (fun h => ?_)
  · have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨?_, by rw [m₃, m₂]; exact Frame.refl _ _⟩
    rw [show pad16 (bytesAt s.mem P len) = [] by simp [VG.Spec.ChaCha20Poly1305.pad16, hlen, h0],
      List.append_nil, ← show 16 * (len / 16) = len by omega_using [h0]]
    exact hI₃
  · have h0 : len % 16 ≠ 0 := by simpa using h
    obtain hsrc : ∀ j < len % 16, InRegions (s₃.rd ++ s₃.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [add_ofNat, rd₃, wr₃, rd₂, wr₂]
      exact hin _ 1 (by omega_using [hj])
    obtain hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
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
  obtain e : Proof.Poly1305.AArch64.off (off (cx s₀) 448) 24 = off (cx s₀) 472 := off_off _ _ _
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
theorem first_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv e s₀ s) :
    WP isa (.block (([.addImm .x .x0 .x21 448] : List Instr) ++ Impl.Poly1305.AArch64.Radix64.setup)) s
      fun s₂ => HInv (Proof.Poly1305.AArch64.Rk s.mem (off (cx s₀) 448))
          (Spec.Poly1305.leNum (bytesAt s.mem (off (cx s₀) 448) 24)) [] s₂ ∧
        s₂.gpr .x0 = off (cx s₀) 448 ∧ (∀ r, r ≠ .x0 → r ∉ [Reg.x4, .x5, .x6, .x7, .x8, .x16, .x17] →
          s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
  obtain wrS : Covers [sub s₀ 448 128] s₀.wr := covers1 hp rfl (by lit_omega)
  refine WP.block_append (wp_addImm (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain x0₁ : s₁.gpr .x0 = off (cx s₀) 448 := by rw [u₁.gpr, h.x21]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [u₁.wr, h.wr]
  refine WP.narrow (rd := []) (wr := [sub s₀ 448 128])
    (setup_hinv (s₁.withRegions [] [sub s₀ 448 128]) (by
      simp only [State.withRegions_gpr, State.withRegions_wr, x0₁]; exact List.mem_singleton_self _))
    (Covers.right (by rw [wr₁]; exact wrS)) (by rw [wr₁]; exact wrS) fun s₂ rd₂ wr₂ _ _ ⟨hI₂, k₂⟩ => ?_
  obtain g₂ : ∀ r, r ∉ [Reg.x4, .x5, .x6, .x7, .x8, .x16, .x17] → s₂.gpr r = s₁.gpr r := fun r hr => by
    simpa only [State.withRegions_gpr] using k₂.1 r hr
  obtain m₂ : s₂.mem = s₁.mem := by simpa only [State.withRegions_mem] using k₂.2.1
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
  obtain wrS : Covers [sub s₀ 448 128] s₀.wr := covers1 hp rfl (by lit_omega)
  refine WP.block_append (wp_addImm (by decide) fun s₅ u₅ => ?_)
  obtain x1₅ : s₅.gpr .x1 = off (cx s₀) 0 := by rw [u₅.gpr, hx21]
  obtain hb : ∀ d, d + 8 ≤ 16 → InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [x1₅, u₅.rd, u₅.wr, hwr, show off (cx s₀) 0 + BitVec.ofNat 64 d = off (cx s₀) (0 + d) from off_off _ _ _]
    obtain ⟨r, hr, hc⟩ := hp.in_ctx (a := 0 + d) (w := 8) (by lit_omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (absorb_hinv s₅ (hinv_keep hI fun r hr => u₅.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (hb 0 (by decide)) (hb 8 (by decide)))
    fun s₆ ⟨hI₆, k₆⟩ => ?_
  obtain x0₆ : s₆.gpr .x0 = off (cx s₀) 448 := by rw [k₆.gpr', u₅.other _ (by decide), hx0]
  obtain m₆ : s₆.mem = s.mem := by rw [k₆.2.1, u₅.mem]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [k₆.2.2.2, u₅.wr, hwr]
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
    (srcD : Src s₀ (dp s₀) (L s₀)) {s : State} (h : Inv e s₀ s) :
    WP isa macAll s fun s' => Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++
          ((bytesAt s.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s.mem (ad s₀) (AL s₀))) ++
          ((bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++
            bytesAt s.mem (off (cx s₀) 0) 16))) := by
  rw [macAll_eq]
  refine WP.seq (WP.mono (WP.kept (first_ok hp h) rfl)
    fun s₂ ⟨⟨hI₂, x0₂, g₂, m₂, rd₂, wr₂⟩, cs₂, sp₂⟩ => ?_)
  obtain x21₂ : s₂.gpr .x21 = cx s₀ := by rw [g₂ _ (by decide) (by decide), h.x21]
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
  obtain d16 : ∀ r ∈ [sub s₀ 16 16], (sub s₀ 448 128).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain f₂₄ : Frame [sub s₀ 16 16] s.mem s₄.mem := by rw [← m₂]; exact f₃.trans f₄
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
    obtain eD : bytesAt s₃.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := by
      rw [bytesAt_frame f₃ (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact (srcD.ctx.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt srcD.lt), m₂]
    obtain eL : bytesAt s₄.mem (off (cx s₀) 0) 16 = bytesAt s.mem (off (cx s₀) 0) 16 :=
      bytesAt_frame f₂₄ (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact sub_disj s₀ (a := 0) (n := 16) (b := 16) (m := 16) (by lit_omega) (by lit_omega) (by lit_omega))
        (by lit_omega)
    rw [m₂, eD, eL] at this
    simpa only [List.nil_append, List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.AArch64.Fused

end

end


/-!
# ChaCha20-Poly1305 on AArch64, 64 to 256 bytes: `seal` and `open` up to the tag

The parts of `Short.sealAfter` and `Short.openAfter`, which leave what
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
  rw [VG.Proof.ChaCha20.keystream_getD _ hi, ks5, show (64 + i) / 64 = i / 64 + 1 by omega_using [],
    show (64 + i) % 64 = i % 64 by omega_using [], ctr_initState, ctr_initState]
  congr 4
  rw [BitVec.ofNat_add, BitVec.add_comm]
  exact (BitVec.add_zero _).trans (BitVec.add_comm _ _)

/-- The data XORed with its keystream is the data encrypted from counter 1. -/
theorem ct_eq {s₀ : State} {Q : Addr} {m₃ m₄ : Mem} (hD : bytesAt m₃ (dp s₀) (L s₀) = D s₀)
    (hk : ∀ i < L s₀, m₃ (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i))
    (hx : ∀ i < L s₀, m₄ (Q + BitVec.ofNat 64 i) = m₃ (dp s₀ + BitVec.ofNat 64 i) ^^^
      m₃ (kp' s₀ + BitVec.ofNat 64 i)) :
    bytesAt m₄ Q (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  rw [encrypt_eq]
  apply List.ext_getElem
  · simp [VG.Proof.Poly1305.length_bytesAt, VG.Proof.ChaCha20.length_keystream]
  · intro i h₁ h₂
    simp only [VG.Proof.Poly1305.length_bytesAt] at h₁
    obtain hD' := congrArg (·[i]?) hD
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
  rw [← h (64 + i) (by omega_using [hi]), kp', off_add, off_add, show 64 + (64 + i) = 128 + i by omega_using []]

/-- The prologue keeps the callee-saved vector registers. -/
theorem prologue_keepsV (sve : Bool) : (Short.prologue sve).allInstrs keepsV = true := by
  cases sve <;> lit_decide

/-- After the prologue. -/
theorem sealAfter_ok {s₀ s₁ : State} (hp : APre true s₀) (hL256 : L s₀ ≤ 256) (h₁ : PostP true s₀ s₁)
    (v₁ : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    WP isa Short.sealAfter s₁ (MainS s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  obtain hAL := (Nat.le_of_lt (s₀.gpr .x3).isLt)
  unfold Short.sealAfter
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.inv.frame (by rdisj_all) hAL
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp h₁.inv) (by lit_decide)) fun s₂ ⟨⟨i₂, k₂, len₂⟩, v₂⟩ => ?_)
  obtain D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  obtain K₂ : ∀ i < L s₀, s₂.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [ks_frame k₂.frame (by rdisj_all) (by omega_using [hL256, hi])]
    exact ks_post h₁.ks (by omega_using [hL256, hi])
  refine WP.seq (WP.mono (WP.preservedV (xorKsOut_ok hp hL256 i₂.x21 i₂.x22 (i₂.un .x28 (by decide)) i₂.x23
    i₂.rd i₂.wr) (by lit_decide)) fun s₃ ⟨⟨k₃, x₃⟩, v₃⟩ => ?_)
  obtain i₃ : Inv true s₀ s₃ := i₂.step k₃ (oR_inv hp).1 (oR_inv hp).2
  obtain ct₃ := ct_eq D₂ K₂ x₃
  rw [op_true] at ct₃
  refine WP.mono (WP.preservedV (Fused.macAll_ok hp (srcA hp) (srcD hp) i₃) (by lit_decide))
    fun s₄ ⟨⟨k₄, r₄⟩, v₄⟩ => ?_
  obtain i₄ := mac_inv i₃ k₄
  obtain R₄ := r₄ (otk s₀) [] (Repr.frame k₃.frame (by rdisj_all) (Repr.frame k₂.frame (by rdisj_all) h₁.poly))
  obtain A₃ : bytesAt s₃.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hAL, bytesAt_frame k₂.frame (by rdisj_all) hAL, hA]
  obtain L₃ : bytesAt s₃.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) (by lit_omega), len₂]
  rw [A₃, ct₃, L₃] at R₄
  refine ⟨i₄.inv0, fun r hr => (v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))), ?_, ?_⟩
  · refine (congrArg (Repr s₄.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₄
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₄.frame (by rdisj_all) hL', ct₃]

/-- After the prologue. -/
theorem openAfter_ok {s₀ s₁ : State} (hp : APre false s₀) (hL256 : L s₀ ≤ 256) (h₁ : PostP false s₀ s₁)
    (v₁ : ∀ r ∈ preservedV, (s₁.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    WP isa Short.openAfter s₁ (MainO s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  obtain hAL := (Nat.le_of_lt (s₀.gpr .x3).isLt)
  unfold Short.openAfter
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ := bytesAt_frame h₁.inv.frame (by rdisj_all) hAL
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp h₁.inv) (by lit_decide)) fun s₂ ⟨⟨i₂, k₂, len₂⟩, v₂⟩ => ?_)
  obtain D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  obtain A₂ : bytesAt s₂.mem (ad s₀) (AL s₀) = A s₀ := by rw [bytesAt_frame k₂.frame (by rdisj_all) hAL, hA]
  refine WP.seq (WP.mono (WP.preservedV (Fused.macAll_ok hp (srcA hp) (srcD hp) i₂) (by lit_decide))
    fun s₃ ⟨⟨k₃, r₃⟩, v₃⟩ => ?_)
  obtain i₃ := mac_inv i₂ k₃
  obtain R₃ := r₃ (otk s₀) [] (Repr.frame k₂.frame (by rdisj_all) h₁.poly)
  rw [A₂, D₂, len₂] at R₃
  obtain D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame k₃.frame (by rdisj_all) hL', D₂]
  obtain K₃ : ∀ i < L s₀, s₃.mem (kp' s₀ + BitVec.ofNat 64 i) = ks5 s₀ (64 + i) := fun i hi => by
    rw [ks_frame k₃.frame (by rdisj_all) (by omega_using [hL256, hi]), ks_frame k₂.frame (by rdisj_all) (by omega_using [hL256, hi])]
    exact ks_post h₁.ks (by omega_using [hL256, hi])
  refine WP.seq (WP.mono (WP.preservedV (xorKsOut_ok hp hL256 i₃.x21 i₃.x22 (i₃.un .x28 (by decide)) i₃.x23
    i₃.rd i₃.wr) (by lit_decide)) fun s₄ ⟨⟨k₄, x₄⟩, v₄⟩ => ?_)
  obtain i₄ : Inv false s₀ s₄ := i₃.step k₄ (oR_inv hp).1 (oR_inv hp).2
  refine WP.mono (WP.preservedV (finalizeTo_ok hp i₄ (out := 48) (by omega_using [])) (by lit_decide))
    fun s₅ ⟨⟨k₅, tag₅⟩, v₅⟩ => ?_
  obtain T₅ := tag₅ _ _ (Repr.frame k₄.frame (by rdisj_all) R₃)
  refine ⟨i₄.inv0.step k₅ (fun r hr => ?_) (fun r hr => ?_), fun r hr => (v₅ r hr).trans ((v₄ r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr)))), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [T₅]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  · rw [bytesAt_frame k₅.frame (by rdisj_all) hL', ct_eq D₃ K₃ x₄]

end VG.Proof.ChaCha20Poly1305.AArch64.Short
