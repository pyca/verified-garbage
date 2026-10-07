import VerifiedGarbage.Proof.Bignum.X86_64.Csub

/-!
# Multiword arithmetic on x86-64: Montgomery multiplication

The working space at `B` (`rdi`) holds the header and, after it, eight
arrays of `w + 2` words (`slot w j`). The header (`Hdr`) gives `w`,
`-m⁻¹ mod 2⁶⁴` and the arrays' bases. `montMul mo acc tmp o a b` leaves
`[o] < m` with `[o] R ≡ [a] [b] (mod m)` for `R = 2^(64 w)` and `m = [mo]`
(`montMul_ok`), changing only the arrays `acc`, `tmp` and `o`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- A header slot's address, as `xrun` leaves it. -/
theorem hdrOff (B : Addr) (i : Nat) : B + BitVec.ofInt 64 (8 * (i : Int)) = off B (8 * i) := by
  rw [show (8 * (i : Int)) = ((8 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-- `bases o a b mo acc tmp`: the bases from the header, and `w` and `-m⁻¹`. -/
theorem bases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b mo acc tmp : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) :
    WP isa (.block (bases o a b mo acc tmp)) s fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧ t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w mo) ∧ t.gpr .r8 = off B (slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w tmp) ∧ t.mem = s.mem ∧
      Keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] (c := .block (bases o a b mo acc tmp))
    (Q := fun t => t.gpr .rbx = off B (slot w o) ∧ t.gpr .r11 = off B (slot w a) ∧
      t.gpr .r9 = off B (slot w b) ∧ t.gpr .r10 = off B (slot w mo) ∧ t.gpr .r8 = off B (slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = off B (slot w tmp) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, k⟩
  unfold bases
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr o) (by unfold sArr; omega), hl (sArr a) (by unfold sArr; omega),
    hl (sArr b) (by unfold sArr; omega), hl (sArr mo) (by unfold sArr; omega),
    hl (sArr acc) (by unfold sArr; omega), hl (sArr tmp) (by unfold sArr; omega), hl sW (by decide),
    hl sMinv (by decide), hH.harr o ho, hH.harr a ha, hH.harr b hb, hH.harr mo hmo, hH.harr acc hacc,
    hH.harr tmp htmp, hH.hw, hH.hminv]

/-- The registers `montMul` may change: all but `rdi` and `rsp`. -/
def mmRegs : List Reg :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- What follows `bases` in `montMul`: from the bases, `w` and `-m⁻¹` in
registers (`bases_ok`), `[o] = [a] [b] R⁻¹ mod m` for `m = [mo]`, if `[b] < m`
and `-m⁻¹` is right. -/
theorem mmTail_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d4 : acc ≠ a) (d5 : acc ≠ b)
    (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hbx : s.gpr .rbx = off B (slot w o)) (h11 : s.gpr .r11 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w b))
    (h10 : s.gpr .r10 = off B (slot w mo)) (h8 : s.gpr .r8 = off B (slot w acc))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h15 : s.gpr .r15 = minv) (hsi₁ : s.gpr .rsi = off B (slot w tmp))
    (hinv : ((word s.mem B (slot w mo)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w mo) w) :
    WP isa (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc))) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w mo) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w mo) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hN0 : 0 < wv s.mem B (slot w mo) w := by omega
  have hs₁ := hs
  have k₁ : Keep [] s s := Keep.refl _ _
  -- The accumulator := 0.
  refine WP.seq (WP.mono (zeroAccLoop_ok hs₁ h8 h12 (by omega) hw' (sl acc hacc))
    fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  have fr₂ : ∀ {j}, j < 8 → j ≠ acc → wv s₂.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun hj hne => ho₂.wv (by have := sp hne; omega) (by have := sl _ hj; omega)
  have fw₂ : word s₂.mem B (slot w mo) = word s.mem B (slot w mo) :=
    ho₂.word (by have := sp (Ne.symm d1); have := sl _ hmo; omega) (by have := sl _ hmo; omega)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h9)
    ((k₂.gpr (by decide)).trans h10) ((k₂.gpr (by decide)).trans h11) ((k₂.gpr (by decide)).trans h12)
    hw hw' (sl acc hacc) (by have := sl b hb; omega) (by have := sl mo hmo; omega)
    (by have := sl a ha; omega) (by have := sp (Ne.symm d5); omega) (by have := sp (Ne.symm d1); omega)
    (by have := sp (Ne.symm d4); omega)
    (by rw [fw₂, (k₂.gpr (by decide) : s₂.gpr .r15 = s.gpr .r15), h15]; exact hinv) hz₂
    (by rw [fr₂ hb (Ne.symm d5), fr₂ hmo (Ne.symm d1)]; exact hB)) fun s₃ hR => ?_)
  have hTlt := hR.lt
  have hTc := hR.cong
  rw [fr₂ hmo (Ne.symm d1)] at hTlt hTc
  rw [fr₂ ha (Ne.symm d4), fr₂ hb (Ne.symm d5)] at hTc
  have k123 := k12.trans hR.keep
  have hs₃ := hR.scr
  have fr₃ : ∀ {j}, j < 8 → j ≠ acc → wv s₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun hj hne =>
    (hR.out.wv (by have := sp hne; omega) (by have := sl _ hj; omega)).trans (fr₂ hj hne)
  have k14 := k₂.trans hR.keep
  have hsi : s₃.gpr .rsi = off B (slot w tmp) := (k14.gpr (by decide)).trans hsi₁
  -- `T - m`.
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k14.gpr (by decide)).trans h8) ((k14.gpr (by decide)).trans h10)
    hsi ((k14.gpr (by decide)).trans h12) (by omega) hw' (by have := sl acc hacc; omega)
    (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega) (by have := sp d2; omega)
    (by have := sp d6; omega)) fun s₅ ⟨c, lt, hbp, hlt, hD, ho₅, k₅⟩ => ?_)
  have k5 := k123.trans k₅
  have k15 := k14.trans k₅
  -- The selection.
  have hs₅ := hs₃.congr k₅.2.2
  refine WP.mono (selectAcc_ok hs₅ ((k15.gpr (by decide)).trans h8) ((k₅.gpr (by decide)).trans hsi)
    ((k15.gpr (by decide)).trans hbx) ((k15.gpr (by decide)).trans h12) hbp (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv, hot, k₆⟩ => ?_
  -- The words of `T` in `s₅`, as after the rounds.
  have hacc₅ : wv s₅.mem B (slot w acc) w = wv s₃.mem B (slot w acc) w :=
    ho₅.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  have hD' : wv s₅.mem B (slot w tmp) w + wv s.mem B (slot w mo) w = wv s₃.mem B (slot w acc) w +
      2 ^ (64 * w) * c.toNat := by
    rw [← fr₃ hmo (Ne.symm d1)]; exact hD
  have hres : wv t.mem B (slot w o) w = wv s₃.mem B (slot w acc) (w + 2) % wv s.mem B (slot w mo) w := by
    rw [hv, hacc₅, hlt, wv_top2]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w acc) w)
      (Tw := (word s₃.mem B (slot w acc + 8 * w)).toNat)
      (Tw1 := (word s₃.mem B (slot w acc + 8 * w + 8)).toNat) (D := wv s₅.mem B (slot w tmp) w)
      (m := wv s.mem B (slot w mo) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w mo) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD'
    rw [← this]
    by_cases h : (word s₃.mem B (slot w acc + 8 * w)).toNat < c.toNat <;> simp [h]
  refine ⟨?_, ?_, ?_, (k5.trans k₆).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hN0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, hTc]
  · have a3 : Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) (ho₂.trans hR.out) (Nat.le_refl _) (Nat.le_refl _)
    have a5 : Arrays B w [acc, tmp, o] s₃.mem s₅.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₅ (Nat.le_refl _) (by omega)
    have a6 : Arrays B w [acc, tmp, o] s₅.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a5).trans a6

/-- Montgomery multiplication: `[o] = [a] [b] R⁻¹ mod m` for `m = [mo]`, if
`[b] < m` and `-m⁻¹` is right. -/
theorem montMul_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d4 : acc ≠ a) (d5 : acc ≠ b)
    (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hinv : ((word s.mem B (slot w mo)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w mo) w) :
    WP isa (montMul mo acc tmp o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w mo) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w mo) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold montMul
  refine WP.seq (WP.mono (bases_ok hs hdi hH hZ ho ha hb hmo hacc htmp)
    fun s₁ ⟨hbx, h11, h9, h10, h8, h12, h15, hsi₁, hm₁, k₁⟩ => ?_)
  rw [← hm₁] at hinv hB ⊢
  exact WP.mono (mmTail_ok (hs.congr k₁.2.2) hZ hw hw' hmo hacc htmp ho ha hb d1 d2 d3 d4 d5 d6 d7 hbx h11 h9 h10
    h8 h12 h15 hsi₁ hinv hB) fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩

end VG.Proof.Bignum.X86_64
