module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModExp
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSqr
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Four-bit windows on PPC64LE: the working space

`ModExp.powWin` works in a working space of 24 arrays (`slot w j`, `j <
24`). `WCtx` is what its Montgomery multiplications need (`WCtx.mont`),
with `N` the modulus in array 0; everything it writes is in arrays 1 to 23
(`win`). `sel_ok`: a masked copy by `selectAcc`; `copy_ok`, `toEntry_ok`:
the copies of `powWin`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

/-- Array `j`'s number. -/
abbrev A (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (slot w j) (2 * w)

/-- The mask of `b`: all ones if `b`, else 0. -/
abbrev mask (b : Bool) : BitVec 64 := BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)

theorem slot_lt {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- Arrays 1 to 23: everything `powWin` may write. -/
def win (w : Nat) : List (Nat × Nat) := [(slot w 1, 23 * (8 * (w + 2)))]

/-- What the Montgomery multiplications need, with `N` the modulus in array
0. -/
structure WCtx (s : State) (B : Addr) (Z w N : Nat) : Prop where
  scr : Scr s B Z
  w2 : 2 ≤ w
  w31 : w < 2 ^ 31
  hZ : slot w 24 ≤ Z
  r10 : s.gpr .r10 = off B (slot w 0)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (s.gpr .r12).toNat < 2 ^ 32
  inv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  n : A s.mem B w 0 = N

/-- The registers `WCtx` reads. -/
def ctxRegs : List Reg := [.r10, .r11, .r12, .r29]

theorem WCtx.sl {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {j : Nat} (hj : j < 24) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_lt hj) h.hZ

theorem WCtx.nw {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) : B.toNat + slot w 24 ≤ 2 ^ 64 := by
  have := h.scr.nowrap; have := h.hZ; omega

/-- An array apart from an array that changed. -/
theorem arr_out {B : Addr} {w o j : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * (w + 2)) m m')
    (hj : j < 24) (hne : j ≠ o) (hn : B.toNat + slot w 24 ≤ 2 ^ 64) : A m' B w j = A m B w j := by
  have := slot_sep (w := w) hne
  have := slot_lt (w := w) hj
  exact (Outs.of_outside h (List.mem_singleton_self _)).val32
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; omega) (by omega)

/-- An array apart from those of a Montgomery multiplication into `o`. -/
theorem arr_mont {B : Addr} {w o j : Nat} {m m' : Mem}
    (h : Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] m m')
    (hj : j < 24) (h2 : j ≠ 2) (h3 : j ≠ 3) (ho : j ≠ o) (hn : B.toNat + slot w 24 ≤ 2 ^ 64) :
    A m' B w j = A m B w j := by
  have := slot_lt (w := w) hj
  refine h.val32 (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := slot_sep (w := w) h2; omega
  · have := slot_sep (w := w) h3; omega
  · have := slot_sep (w := w) ho; omega

theorem slot_win {w o : Nat} (h1 : 1 ≤ o) (h24 : o < 24) :
    slot w 1 ≤ slot w o ∧ slot w o + 8 * (w + 2) ≤ slot w 1 + 23 * (8 * (w + 2)) := by
  have := slot_lt (w := w) h24
  have e24 : slot w 24 = slot w 1 + 23 * (8 * (w + 2)) := by unfold slot; omega
  refine ⟨?_, by omega⟩
  unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) h1; omega

theorem win_of_out {B : Addr} {w o : Nat} {m m' : Mem} (h : Outside B (slot w o) (8 * (w + 2)) m m')
    (h1 : 1 ≤ o) (h24 : o < 24) : Outs B (win w) m m' := fun x hx => h x (by
  have hx' := hx _ (List.mem_singleton_self _)
  have := slot_win (w := w) h1 h24
  simp only [Mont.ofs, ofs] at hx' ⊢
  omega)

theorem win_of_mont {B : Addr} {w o : Nat} {m m' : Mem}
    (h : Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] m m')
    (h1 : 1 ≤ o) (h24 : o < 24) : Outs B (win w) m m' := fun x hx => h x (by
  have hx' := hx _ (List.mem_singleton_self _)
  simp only [Mont.ofs] at hx'
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := slot_win (w := w) (o := 2) (by decide) (by decide); simp only [Mont.ofs] at *; omega
  · have := slot_win (w := w) (o := 3) (by decide) (by decide); simp only [Mont.ofs] at *; omega
  · have := slot_win (w := w) h1 h24; simp only [Mont.ofs] at *; omega)

/-- The context after code that writes only arrays 1–23 and none of
`ctxRegs`. -/
theorem WCtx.of {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) (o : Outs B (win w) s.mem t.mem) : WCtx t B Z w N := by
  have hn := h.nw
  have s0 := slot_lt (w := w) (show 0 < 24 by decide)
  have e1 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega
  have g := fun r hr => k.gpr r (hrs r hr)
  have a0 : ∀ r ∈ win w, slot w 0 + 4 * (2 * w) ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0 := fun r hr => by
    rw [win, List.mem_singleton] at hr; subst hr; simp only; omega
  refine ⟨h.scr.congr k.wr, h.w2, h.w31, h.hZ, (g .r10 (by decide)).trans h.r10,
    (g .r29 (by decide)).trans h.r29, (g .r11 (by decide)).trans h.r11,
    by rw [g .r12 (by decide)]; exact h.r12, ?_, ?_⟩
  · have := h.w2
    have := o.val32 (d := slot w 0) (k := 1) (fun r hr => by have := a0 r hr; omega) (by omega)
    rw [g .r12 (by decide), show w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0) by simpa [val32] using this]
    exact h.inv
  · rw [← h.n]
    exact o.val32 a0 (by omega)

theorem WCtx.regs {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) (hm : t.mem = s.mem) : WCtx t B Z w N :=
  h.of k hrs (by rw [hm]; exact Outs.refl _ _ _)

/-- A Montgomery multiplication in the context. -/
theorem WCtx.mont {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {o a b : Nat} (ho : o < 24) (ha : a < 24)
    (hb : b < 24) (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hB : A s.mem B w b < N) :
    WP isa (montOp o a b) s fun t =>
      (WCtx t B Z w N ∧ A t.mem B w o < N ∧
        A t.mem B w o * 2 ^ (64 * w) % N = A s.mem B w a * A s.mem B w b % N ∧
        (∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ o → A t.mem B w j = A s.mem B w j) ∧
        Outs B (win w) s.mem t.mem) ∧ Keep Pub.montRegs s t := by
  refine WP.mono (Pub.montOpN_ok h.scr (n := 24) (by decide) ho ha hb ho2 ho3 ha2 hb2 h.w2 h.w31 h.hZ h.r10 h.r29
    h.r11 h.r12 h.inv (by rw [show val32 s.mem B (slot w 0) (2 * w) = N from h.n]; exact hB))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  have op := win_of_mont out (by omega) ho
  rw [show val32 s.mem B (slot w 0) (2 * w) = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) op, hlt, he, fun j hj h2 h3 hjo => arr_mont out hj h2 h3 hjo h.nw, op⟩, k⟩

/-- `WCtx.mont` for `sqrOp o a` (`a` other than array 3). -/
theorem WCtx.sqr {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {o a : Nat} (ho : o < 24) (ha : a < 24)
    (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (ha3 : a ≠ 3) (hA : A s.mem B w a < N) :
    WP isa (PublicChecked.sqrOp o a) s fun t =>
      (WCtx t B Z w N ∧ A t.mem B w o < N ∧
        A t.mem B w o * 2 ^ (64 * w) % N = A s.mem B w a * A s.mem B w a % N ∧
        (∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ o → A t.mem B w j = A s.mem B w j) ∧
        Outs B (win w) s.mem t.mem) ∧ Keep Pub.montRegs s t := by
  refine WP.mono (Pub.sqrOpN_ok h.scr (n := 24) (by decide) ho ha ho2 ho3 ha2 ha3 h.w2 h.w31 h.hZ h.r10 h.r29
    h.r11 h.r12 h.inv (by rw [show val32 s.mem B (slot w 0) (2 * w) = N from h.n]; exact hA))
    fun t ⟨⟨hlt, he, out⟩, k⟩ => ?_
  have op := win_of_mont out (by omega) ho
  rw [show val32 s.mem B (slot w 0) (2 * w) = N from h.n] at hlt he
  exact ⟨⟨h.of k (by decide) op, hlt, he, fun j hj h2 h3 hjo => arr_mont out hj h2 h3 hjo h.nw, op⟩, k⟩

/-! ## Copies and selections -/

/-- `selectAcc` with the bases already in `r5`, `r8` and `r9`. -/
theorem selectAt_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {b : Bool} {o a t : Nat}
    (ho : o < 24) (ha : a < 24) (ht : t < 24) (hoa : o ≠ a) (hot : o ≠ t)
    (h5 : s.gpr .r5 = off B (slot w o)) (h8 : s.gpr .r8 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w t))
    (h20 : s.gpr .r20 = mask b) :
    WP isa selectAcc s fun s' =>
      (A s'.mem B w o = (if b then A s.mem B w a else A s.mem B w t) ∧
        Outside B (slot w o) (8 * (w + 2)) s.mem s'.mem) ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s' := by
  have sep := fun {j k : Nat} (hjk : j ≠ k) => slot_sep (w := w) hjk
  have hO := h.sl ho
  have hA := h.sl ha
  have hT := h.sl ht
  refine WP.mono (selectAcc_ok h.scr (dA := slot w a) (dT := slot w t) (dO := slot w o) (n := 2 * w) (b := b)
      h8 h9 h5 h.r11 h20 (by have := h.w2; omega) (by have := h.w31; omega)
      (by omega) (by omega) (by omega)
      (by have := sep hoa; omega) (by have := sep hot; omega)) fun s' ⟨hv, hout, k⟩ =>
    ⟨⟨hv, hout.mono (Nat.le_refl _) (by omega)⟩, k⟩

theorem ones_ok (s : State) :
    WP isa (.block ones) s fun t => (t.gpr .r20 = mask true ∧ t.mem = s.mem) ∧ Keep [.r20] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ones
  prun
  rfl

/-- The registers `copy` and `toEntry` write. -/
def copyRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- `copy o a`: array `o` := array `a`. -/
theorem copy_ok {s : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {o a : Nat} (ho : o < 24) (ha : a < 24)
    (hoa : o ≠ a) :
    WP isa (copy o a) s fun t =>
      (A t.mem B w o = A s.mem B w a ∧ Outside B (slot w o) (8 * (w + 2)) s.mem t.mem) ∧ Keep copyRegs s t := by
  unfold copy
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok s) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h.r10)
    ((k1.gpr _ (by decide)).trans h.r29) a) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h.r10)
    ((k12.gpr _ (by decide)).trans h.r29) a) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h.r10)
    ((k13.gpr _ (by decide)).trans h.r29) o) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (selectAt_ok (h.regs k14 (by decide) hm) (b := true) ho ha ha hoa hoa a5
    (by rw [k4.gpr .r8 (by decide), k3.gpr .r8 (by decide), a8]) (by rw [k4.gpr .r9 (by decide), a9])
    (by rw [k4.gpr .r20 (by decide), k3.gpr .r20 (by decide), k2.gpr .r20 (by decide), h20]))
    fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k14.trans k).mono (by simp [copyRegs])⟩

theorem entry_addr (B : Addr) (w j : Nat) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 8) * BitVec.ofNat 64 (8 * (w + 2)) + off B (slot w 0) =
      off B (slot w (8 + j)) := by
  simp only [off, slot, Impl.Bignum.hdrBytes, Nat.zero_mul, Nat.add_zero]
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul, Nat.add_comm 8 j, BitVec.ofNat_add 256]
  ac_rfl

/-- `entry`: the base of table entry `j` (in `r19`) into `r8`. -/
theorem entry_ok {s : State} {B : Addr} {Z w N j : Nat} (h : WCtx s B Z w N)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 j) :
    WP isa (.block entry) s fun t => (t.gpr .r8 = off B (slot w (8 + j)) ∧ t.mem = s.mem) ∧ Keep [.r8] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold entry
  prun [h19, h.r29, h.r10, entry_addr]

/-- `toEntry`: table entry `j` (in `r19`) := array 6. -/
theorem toEntry_ok {s : State} {B : Addr} {Z w N j : Nat} (h : WCtx s B Z w N)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 j) (hj : j < 16) :
    WP isa toEntry s fun t =>
      (A t.mem B w (8 + j) = A s.mem B w 6 ∧ Outside B (slot w (8 + j)) (8 * (w + 2)) s.mem t.mem) ∧
        Keep copyRegs s t := by
  unfold toEntry
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok s) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_
  have c1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) c1 (by rw [k1.gpr .r19 (by decide), h19])) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have c2 := c1.regs k2 (by decide) m2
  rw [WP.block_append_iff]
  have hblk : WP isa (.block [.addi .r5 .r8 0]) t₂ fun t =>
      (t.gpr .r5 = off B (slot w (8 + j)) ∧ t.mem = t₂.mem) ∧ Keep [.r5] t₂ t := by
    refine WP.keep _ ?_ (by decide)
    prun [a8, BitVec.add_zero]
  refine WP.mono hblk fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have c3 := c2.regs k3 (by decide) m3
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) c3.r10 c3.r29 6) fun t₄ ⟨⟨b8, m4⟩, k4⟩ => ?_
  have c4 := c3.regs k4 (by decide) m4
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) c4.r10 c4.r29 6) fun t₅ ⟨⟨b9, m5⟩, k5⟩ => ?_
  have c5 := c4.regs k5 (by decide) m5
  have k15 := (((k1.trans k2).trans k3).trans k4).trans k5
  have hm : t₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  refine WP.mono (selectAt_ok c5 (b := true) (o := 8 + j) (a := 6) (t := 6) (by omega) (by decide) (by decide)
    (by omega) (by omega) (by rw [k5.gpr .r5 (by decide), k4.gpr .r5 (by decide), a5])
    (by rw [k5.gpr .r8 (by decide), b8]) b9
    (by rw [k5.gpr .r20 (by decide), k4.gpr .r20 (by decide), k3.gpr .r20 (by decide),
      k2.gpr .r20 (by decide), h20])) fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k15.trans k).mono (by simp [copyRegs])⟩

end VG.Proof.Bignum.PPC64LE.Win
