import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Short Weierstrass curves on x86 (32-bit): numbers to and from big-endian bytes

`loadBE n o src` reads the `8 n` bytes at `src`, big-endian, into `[o]`
(`loadBE_ok`), and `storeBE n dst d a` writes `[a]` masked with `ecx`, so the
number or zeros, big-endian, to the `8 n` bytes at `dst + d` (`storeBE_ok`):
a 32-bit word at a time, each byte-reversed (`bswap`, which is
`byteRev32`), from the last.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem bswap_eq (w : BitVec 32) : bswap w = byteRev32 w := rfl

/-- `[r + d]`, for `r` whose `k` bytes up do not wrap. -/
theorem ea_ptr (s : State) {r : Reg} {d : Nat} (h : (s.gpr r).toNat + d < 2 ^ 32) :
    s.ea (at_ r d) = (s.gpr r).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq h

/-- A 32-bit word of a range whose bytes are kept. -/
theorem readW32_keep {m m' : Mem} {p : Addr} {d : Nat}
    (h : ∀ i < 4, m' (p + BitVec.ofNat 64 (d + i)) = m (p + BitVec.ofNat 64 (d + i))) :
    m'.readW (p + BitVec.ofNat 64 d) 32 = m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun i hi => by rw [Offset.add_add, h i hi]

/-! ## Loads -/

/-- One word of `loadBE`. -/
def ldStep (n o : Nat) (src : Reg) (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ src (4 * (2 * n - 1 - j)))), .bswap .eax, .store (sc (o + 4 * j)) .eax]

theorem loadBE_eq (n o : Nat) (src : Reg) : loadBE n o src = (List.range (2 * n)).flatMap (ldStep n o src) :=
  rfl

theorem ldSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .eax) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + 8 * n ≤ 2 ^ 32)
    (hr : ∀ d, d + 4 ≤ 8 * n → InRegions (s.rd ++ s.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr src).setWidth 64, 8 * n⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (ldStep n o src))) s fun s' =>
      (∀ j < k, w32 s'.mem base (o + 4 * j) =
        (byteRev32 (s.mem.readW ((s.gpr src).setWidth 64 + BitVec.ofNat 64 (4 * (2 * n - 1 - j))) 32)).toNat) ∧
      Keeps [.eax] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ldSteps_ok hs hsrc ho hp hr hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.1 _ (by simpa using hsrc)
    have ha₁ : s₁.ea (at_ src (4 * (2 * n - 1 - k))) =
        (s.gpr src).setWidth 64 + BitVec.ofNat 64 (4 * (2 * n - 1 - k)) := by
      rw [ea_ptr s₁ (by rw [hp₁]; omega), hp₁]
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 4 := by
      rw [k₁.2.1, k₁.2.2]; exact hr _ (by omega)
    have hw : s₁.mem.readW ((s.gpr src).setWidth 64 + BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 32 =
        s.mem.readW ((s.gpr src).setWidth 64 + BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 32 :=
      readW32_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [ldStep]
    refine wp_movS (show readSrc s₁ (.mem (at_ src (4 * (2 * n - 1 - k)))) = some _ by
      show s₁.load32 _ = _; rw [ha₁, State.load32, ite_eq_left_iff.mpr fun h => absurd hr₁ h]) fun s₂ u₂ _ => ?_
    refine wp_bswap fun s₃ u₃ => ?_
    have k₃ : Keeps [.eax] s₁ s₃ := u₂.keeps.trans u₃.keeps
    have hs₃ := hs₁.of_keeps k₃ (by decide)
    refine wp_storeS (hs₃.ea (d := o + 4 * k) (by omega)) (hs₃.write (d := o + 4 * k) (n := 4) (by omega))
      fun s₄ m₄ => WP.block_nil ?_
    have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (k₃.trans (m₄.keeps _)),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, hw, bswap_eq]

/-- `[o] = ` the `8 n` bytes at `src`, big-endian. -/
theorem loadBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o : Nat} {src : Reg}
    (hsrc : src ≠ .eax) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + 8 * n ≤ 2 ^ 32)
    (hr : ∀ d, d + 4 ≤ 8 * n → InRegions (s.rd ++ s.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr src).setWidth 64, 8 * n⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBE n o src)) s fun s' =>
      wordsVal s'.mem base o n =
        Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((s.gpr src).setWidth 64) (8 * n)) ∧
      Keeps [.eax] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBE_eq]
  refine WP.mono (ldSteps_ok hs hsrc ho hp hr hd (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega]; exact O⟩
  rw [wordsVal_eq_val32, show 8 * n = 4 * (2 * n) by omega]
  exact val32_eq_ofBytes _ _ _ _ o (2 * n) e

/-! ## Stores -/

/-- One word of `storeBE`. -/
def stStep (n : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (a + 4 * j))), .alu .and .eax (.reg .ecx), .bswap .eax,
    .store (at_ dst (d + 4 * (2 * n - 1 - j))) .eax]

theorem storeBE_eq (n : Nat) (dst : Reg) (d a : Nat) :
    storeBE n dst d a = (List.range (2 * n)).flatMap (stStep n dst d a) := rfl

theorem stSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .eax) {c : Bool} (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0))
    (ha : a + 8 * n ≤ size) (hq : (s.gpr dst).toNat + d + 8 * n ≤ 2 ^ 32)
    (hw : ∀ e, e + 4 ≤ 8 * n →
      InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨(s.gpr dst).setWidth 64 + BitVec.ofNat 64 d, 8 * n⟩) :
    ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (stStep n dst d a))) s fun s' =>
      (∀ j < k, s'.mem.readW ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d +
          BitVec.ofNat 64 (4 * (2 * n - 1 - j))) 32 =
        byteRev32 (s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0))) ∧
      Keeps [.eax] s s' ∧
      Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) (4 * (2 * n - k)) (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (stSteps_ok hs hdst hc ha hq hw hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.1 _ (by simpa using hdst)
    have hc₁ : s₁.gpr .ecx = (if c then BitVec.allOnes 32 else 0) := by rw [k₁.1 _ (by decide), hc]
    have hqa : (s.gpr dst).setWidth 64 + BitVec.ofNat 64 (d + 4 * (2 * n - 1 - k)) =
        (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * (2 * n - 1 - k)) :=
      (Offset.add_add _ _ _).symm
    have hword : s₁.mem.readW (off base (a + 4 * k)) 32 = s.mem.readW (off base (a + 4 * k)) 32 := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 4 * k)) 32 = s.mem.readW (base + BitVec.ofNat 64 (a + 4 * k)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [stStep]
    refine wp_movS (readSrc_sc hs₁ (d := a + 4 * k) (by omega)) fun s₂ u₂ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
    refine wp_bswap fun s₄ u₄ => ?_
    have k₄ : Keeps [.eax] s₁ s₄ := (u₂.keeps.trans u₃.keeps).trans u₄.keeps
    have hq₄ : s₄.gpr dst = s.gpr dst := by rw [k₄.1 _ (by simpa using hdst), hq₁]
    have ha₄ : s₄.ea (at_ dst (d + 4 * (2 * n - 1 - k))) =
        (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 (4 * (2 * n - 1 - k)) := by
      rw [ea_ptr s₄ (by rw [hq₄]; omega), hq₄, hqa]
    have hw₄ : InRegions s₄.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d +
        BitVec.ofNat 64 (4 * (2 * n - 1 - k))) 4 := by
      rw [k₄.2.2, k₁.2.2]; exact hw _ (by omega)
    refine wp_storeS ha₄ hw₄ fun s₅ m₅ => WP.block_nil ?_
    have v₄ : s₄.gpr .eax = byteRev32 (s.mem.readW (off base (a + 4 * k)) 32 &&&
        (if c then BitVec.allOnes 32 else 0)) := by
      rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), hc₁, hword, bswap_eq]
      simp only [ite_true]
    have mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have O₂ : Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) (4 * (2 * n - 1 - k)) 4 s₁.mem s₅.mem := by
      rw [m₅.mem, mem₄]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (k₄.trans (m₅.keeps _)),
      (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [m₅.mem, mem₄, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₅.mem, Mem.readW_writeW_self32, v₄]

/-- The `8 n` bytes at `dst + d` are `[a]` big-endian if the mask `ecx` is all
ones (`c`), zeros if it is zero. -/
theorem storeBE_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d a : Nat} {dst : Reg}
    (hdst : dst ≠ .eax) (c : Bool) (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0))
    (ha : a + 8 * n ≤ size) (hq : (s.gpr dst).toNat + d + 8 * n ≤ 2 ^ 32)
    (hw : ∀ e, e + 4 ≤ 8 * n →
      InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 e) 4)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨(s.gpr dst).setWidth 64 + BitVec.ofNat 64 d, 8 * n⟩) :
    WP isa (.block (storeBE n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) (8 * n) =
        (if c then Spec.Weierstrass.toBytes (8 * n) (wordsVal s.mem base a n)
          else List.replicate (8 * n) 0) ∧
      Keeps [.eax] s s' ∧ Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) 0 (8 * n) s.mem s'.mem := by
  rw [storeBE_eq]
  refine WP.mono (stSteps_ok hs hdst hc ha hq hw hd (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, ?_⟩
  · rw [wordsVal_eq_val32, show 8 * n = 4 * (2 * n) by omega]
    exact bytesAt_eq_toBytes32 _ _ _ _ c e
  · rw [Nat.sub_self, Nat.mul_zero, show 4 * (2 * n) = 8 * n by omega] at O
    exact O

end VG.Proof.Weierstrass.X86
