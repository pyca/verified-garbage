import VerifiedGarbage.Proof.RsaKeyGen.X86_64.ModE
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes

/-!
# A candidate on x86-64: `gcd(c − 1, e)` for an odd `e > 1`

`gcdE` keeps `e` in `kG`, puts `c − 1` in `aX` (a copy of `c` with its low
bit cleared), reduces it modulo `e` (`modWords_ok`), runs the binary gcd
(`gcdLoop_ok`) and leaves `gcd(c − 1, e)` in `kG` (`gcdE_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem sx_m2 : BitVec.signExtend 64 (BitVec.ofInt 32 (-2)) = BitVec.allOnes 64 - 1 := by decide

/-- Clearing the low bit of an odd word. -/
theorem and_m2_toNat {x : BitVec 64} (h : x.toNat % 2 = 1) : (x &&& (BitVec.allOnes 64 - 1)).toNat = x.toNat - 1 := by
  have hx : x = (x - 1) + 1 := by rw [BitVec.sub_add_cancel]
  have h1 : (x - 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 1 ≤ x.toNat; omega_arith)]; rfl
  have : x &&& (BitVec.allOnes 64 - 1) = x - 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [h1, BitVec.toNat_and]
    have ha : (BitVec.allOnes 64 - 1).toNat = 2 ^ 64 - 2 := by decide
    rw [ha]
    have hxl := x.isLt
    -- `x = 2 q + 1`; the mask keeps every bit but the lowest.
    obtain ⟨q, hq⟩ : ∃ q, x.toNat = 2 * q + 1 := ⟨x.toNat / 2, by omega_arith⟩
    rw [hq, show 2 * q + 1 - 1 = 2 * q by omega_arith]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    rcases i with _ | i
    · simp [Nat.testBit_zero]
    · rw [show (2 : Nat) ^ 64 - 2 = 2 * (2 ^ 63 - 1) by omega_arith, Nat.testBit_succ, Nat.testBit_succ,
        Nat.testBit_succ, show (2 * q + 1) / 2 = q by omega_arith, show 2 * (2 ^ 63 - 1) / 2 = 2 ^ 63 - 1 by omega_arith,
        show 2 * q / 2 = q by omega_arith]
      rw [show (2 : Nat) ^ 63 - 1 = 2 ^ 63 - 1 from rfl, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < 63
      · simp [hi]
      · simp only [hi, decide_false, Bool.and_false]
        symm
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show q < 2 ^ 63 by omega_arith)
          (Nat.pow_le_pow_right (by decide) (by omega_arith)))
  rw [this, h1]

/-- A number by its low word. -/
theorem wv_low (m : Mem) (B : Addr) (d n : Nat) :
    wv m B d (n + 1) = (word m B d).toNat + 2 ^ 64 * wv m B (d + 8) n := by
  rw [Nat.add_comm n 1, wv_add, Nat.mul_one]; simp [wv]

/-- The header, after changes past it. -/
theorem _root_.VG.Proof.Bignum.Hdr.outside {m m' : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (h : Hdr m B w minv) {o n : Nat}
    (ho : Outside B o n m m') (hlo : hdrBytes ≤ o) : Hdr m' B w minv :=
  ⟨by rw [ho.word (Or.inl (by unfold sW hdrBytes at *; omega_arith)) (by unfold sW hdrBytes at *; omega_arith)]; exact h.hw,
    by rw [ho.word (Or.inl (by unfold sMinv hdrBytes at *; omega_arith)) (by unfold sMinv hdrBytes at *; omega_arith)]; exact h.hminv,
    fun j hj => by
      rw [ho.word (Or.inl (by unfold sArr hdrBytes at *; omega_arith)) (by unfold sArr hdrBytes at *; omega_arith)]
      exact h.harr j hj⟩

/-- A header slot of the functions' own, stored. -/
theorem storeSlot_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32) {r : Reg} :
    WP isa (.block [.store (hdr i) r]) s fun t =>
      t.mem = s.mem.writeW (off B (8 * i)) (s.gpr r) ∧ Good t B Z w minv ∧
      Outside B (8 * i) 8 s.mem t.mem ∧ Keep [] s t := by
  have hn := hg.scr.nowrap
  have hst : InRegions s.wr (off B (8 * i)) 8 := hg.scr.st (by have := hdr_lt_slot w 8 hi'; omega_arith)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * i)) (s.gpr r))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hst]) rfl) fun t ⟨hm, k⟩ => ⟨hm, ⟨hg.scr.congr k.2.2,
      (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr.store hi hi' _⟩,
      by rw [hm]; exact writeW_outside _ _ _ (by have := hdr_lt_slot w 8 hi'; omega_arith), k⟩

/-- `aX := c` in `modLoop`. -/
theorem modCopy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))), .mov .rbx (.mem (hdr (sArr aX)))])
      copyWords) s fun t =>
      (∀ i < w, word t.mem B (slot w aX + 8 * i) = word s.mem B (slot w aN + 8 * i)) ∧
      Outside B (slot w aX) (8 * w) s.mem t.mem ∧ t.gpr .rbx = off B (slot w aX) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.r12, .rsi, .rbx, .rax, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sp := slot_sep (w := w) (show aX ≠ aN by decide)
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w aN) ∧ t.gpr .rbx = off B (slot w aX) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aN) (by decide), hl (sArr aX) (by decide), hl sW (by decide),
      hg.hdr.harr aN (by decide), hg.hdr.harr aX (by decide), hg.hdr.hw]) rfl) fun s₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega_arith) (fun i hi => hs₁.ld (by omega_arith))
    (fun i hi => hs₁.st (by omega_arith)) (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith))
    fun t ⟨_, hw₃, ho₃, k₃⟩ => ⟨fun i hi => by rw [hw₃ i hi, hm₁], by rw [hm₁] at ho₃; exact ho₃,
      (k₃.gpr (by decide)).trans hbx, (k₃.gpr (by decide)).trans h12, (k₁.trans k₃).mono (by decide)⟩

/-- `modLoop`'s set-up: the low bit of `aX` cleared, `e` back from `kG`, and
`r := 0`. -/
theorem modClear_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hbx : s.gpr .rbx = off B (slot w aX)) :
    WP isa (.block [.mov .r8 (.reg .rbx), .mov .rax (.mem (at0 .rbx)),
      .alu .and .rax (.imm (BitVec.ofInt 32 (-2))), .store (at0 .rbx) .rax, .mov .rbx (.mem (hdr kG)),
      .mov32 .rsi (.imm 0), .mov32 .r14 (.imm 0)]) s
      fun t => t.mem = s.mem.writeW (off B (slot w aX)) (word s.mem B (slot w aX) &&& (BitVec.allOnes 64 - 1)) ∧
        t.gpr .rbx = word s.mem B (8 * kG) ∧ t.gpr .r8 = off B (slot w aX) ∧ t.gpr .rsi = 0 ∧
        t.gpr .r14 = BitVec.ofNat 64 0 ∧ Keep [.rax, .rbx, .r8, .rsi, .r14] s t := by
  have hn := hg.scr.nowrap
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have hGX : 8 * kG + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  have hAX : 8 * sArr aX + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  generalize hv : word s.mem B (slot w aX) &&& (BitVec.allOnes 64 - 1) = v
  have hGs : (s.mem.writeW (off B (slot w aX)) v).readW (off B (8 * kG)) 64 = word s.mem B (8 * kG) :=
    (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)
  refine WP.mono (WP.keep [.rax, .rbx, .r8, .rsi, .r14] (Q := fun t =>
      t.mem = s.mem.writeW (off B (slot w aX)) v ∧ t.gpr .rbx = word s.mem B (8 * kG) ∧
      t.gpr .r8 = off B (slot w aX) ∧ t.gpr .rsi = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0) ?_ rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5⟩, k⟩ => ⟨h1, h2, h3, h4, h5, k⟩
  xrun [State.ea, at0, hdr, hg.rdi, hdrOff, hbx, hg.scr.ld (show slot w aX + 8 ≤ Z by omega_arith),
    hg.scr.st (show slot w aX + 8 ≤ Z by omega_arith), sx_m2, hl kG (by decide), hl (sArr aX) (by decide),
    BitVec.ofInt_ofNat, BitVec.add_zero, hv, hGs]

/-- The gcd's steps from `r = rsi < e`, `e` in `kG`: `gcd(r, e)` into `kG`. -/
theorem gcdTail_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (he : (word s.mem B (8 * kG)).toNat % 2 = 1) :
    WP isa (seqs [.block [.mov .rbx (.mem (hdr kG)), .mov32 .r13 (.imm 128)],
      .loop (.block (Impl.RsaKeyGen.X86_64.Candidate.bgcdStep ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) .ne,
      .block [.store (hdr kG) .rbx]]) s fun t =>
      word t.mem B (8 * kG) = BitVec.ofNat 64 (Nat.gcd (s.gpr .rsi).toNat (word s.mem B (8 * kG)).toNat) ∧
      Good t B Z w minv ∧ Outside B (8 * kG) 8 s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r13] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kG)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbx, .r13] (Q := fun t => t.gpr .rbx = word s.mem B (8 * kG) ∧
      t.gpr .r13 = BitVec.ofNat 64 128 ∧ t.mem = s.mem) (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl, sx_ofNat]) rfl)
    fun s₁ ⟨⟨hbx, h13, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (gcdLoop_ok h13 (by rw [hbx]; exact he)) fun s₂ ⟨hg₂, hm₂, k₂⟩ => ?_)
  have hg₂' : Good s₂ B Z w minv := ⟨hg.scr.congr (k₂.2.2.trans k₁.2.2), (k₂.gpr (by decide)).trans
    ((k₁.gpr (by decide)).trans hg.rdi), by rw [hm₂, hm₁]; exact hg.hdr⟩
  refine WP.mono (storeSlot_ok hg₂' hZ (i := kG) (by decide) (by decide) (r := .rbx)) fun t ⟨hm, hgt, ho, k⟩ => ?_
  refine ⟨?_, hgt, by rw [hm₂, hm₁] at ho; exact ho, ((k₁.trans k₂).trans k).mono (by decide)⟩
  rw [hm, word_writeW_self]
  apply BitVec.eq_of_toNat_eq
  rw [hg₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.gcd_le_right _ (by omega_arith))
    (word s.mem B (8 * kG)).isLt), show s₁.gpr .rsi = s.gpr .rsi from k₁.gpr (by decide), hbx]

/-- `gcdE`: `kG := gcd(c − 1, e)` for `c` (in `aN`) odd and `e` (in `rbx`)
odd and above 1. -/
theorem gcdE_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hc : wv s.mem B (slot w aN) w % 2 = 1)
    (he : (s.gpr .rbx).toNat % 2 = 1) (he1 : 1 < (s.gpr .rbx).toNat) :
    WP isa (seqs gcdE) s fun t =>
      word t.mem B (8 * kG) = BitVec.ofNat 64 (Nat.gcd (wv s.mem B (slot w aN) w - 1) (s.gpr .rbx).toNat) ∧
      Good t B Z w minv ∧ Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r8, .r12, .r13, .r14] s t := by
  have hn := hg.scr.nowrap
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sp := slot_sep (w := w) (show aX ≠ aN by decide)
  have hG : 8 * kG + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hGX : 8 * kG + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  unfold gcdE modLoop
  rw [show ∀ (a b c d e f g h : Prog isa), [a] ++ [b, c, d, e] ++ [f, g, h] = [a] ++ ([b, c] ++ ([d, e] ++ [f, g, h]))
    from fun _ _ _ _ _ _ _ _ => rfl]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (storeSlot_ok hg hZ (i := kG) (by decide) (by decide) (r := .rbx)) fun s₁ ⟨hm₁, hg₁, ho₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (modCopy_ok hg₁ hZ hw hw') fun s₂ ⟨hw₂, ho₂, hbx₂, h12₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
    Hdr.outside hg₁.hdr ho₂ (by unfold slot; omega_arith)⟩
  have hG₂ : word s₂.mem B (8 * kG) = s.gpr .rbx := by
    rw [ho₂.word (Or.inl hGX) (by omega_arith), hm₁, word_writeW_self]
  have hc₂ : wv s₂.mem B (slot w aX) w = wv s.mem B (slot w aN) w := by
    rw [wv_congr2 (m := s₁.mem) (p := B) (d := slot w aN) hw₂]
    exact ho₁.wv (Or.inr hG) (by omega_arith)
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (modClear_ok hg₂ hZ hw hbx₂) fun s₃ ⟨hm₃, hbx₃, h8₃, hsi₃, h14₃, k₃⟩ => ?_)
  -- `aX` holds `c − 1`.
  have hcm1 : wv s₃.mem B (slot w aX) w = wv s.mem B (slot w aN) w - 1 := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega_arith⟩
    have hodd : (VG.Proof.Bignum.word s₂.mem B (slot (w' + 1) aX)).toNat % 2 = 1 := by
      have := hc; rw [← hc₂, wv_low] at this; omega_arith
    rw [hm₃, wv_low, word_writeW_self, and_m2_toNat hodd,
      (writeW_outside s₂.mem B _ (by omega_arith)).wv (Or.inr (Nat.le_refl _)) (by omega_arith), ← hc₂, wv_low]
    have : 1 ≤ (VG.Proof.Bignum.word s₂.mem B (slot (w' + 1) aX)).toNat := by omega_arith
    omega_arith
  have hs₃ := hg₂.scr.congr k₃.2.2
  refine WP.mono (modWords_ok hs₃ h8₃ ((k₃.gpr (by decide)).trans h12₂) h14₃ hw hw' (by omega_arith) hsi₃
      (by rw [hbx₃, hG₂]; exact he1)) fun s₄ ⟨hv₄, hm₄, k₄⟩ => ?_
  have hg₄ : Good s₄ B Z w minv := ⟨hs₃.congr k₄.2.2, (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hg₂.rdi),
    by rw [hm₄, hm₃]; exact Hdr.outside hg₂.hdr (writeW_outside _ _ _ (by omega_arith)) (by unfold slot; omega_arith)⟩
  have hG₄ : VG.Proof.Bignum.word s₄.mem B (8 * kG) = s.gpr .rbx := by
    rw [hm₄, hm₃, (writeW_outside s₂.mem B _ (by omega_arith)).word (by omega_arith) (by omega_arith), hG₂]
  refine WP.mono (gcdTail_ok hg₄ hZ (by rw [hG₄]; exact he)) fun t ⟨hgt, hgd, hot, kt⟩ => ⟨?_, hgd, ?_, ?_⟩
  · rw [hgt, hG₄, hv₄, hcm1, hbx₃, hG₂, ← Nat.gcd_rec, Nat.gcd_comm]
  · have f1 : Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s.mem s₁.mem := Frm.of_outside ho₁ (by simp)
    have f2 : Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s₁.mem s₂.mem :=
      Frm.of_outside (ho₂.mono (o' := slot w aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
    have f3 : Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s₂.mem s₄.mem := by
      rw [hm₄, hm₃]; exact Frm.of_outside ((writeW_outside _ _ _ (by omega_arith)).mono (o' := slot w aX) (n' := 8 * (w + 2))
        (Nat.le_refl _) (by omega_arith)) (by simp)
    exact ((f1.trans f2).trans f3).trans (Frm.of_outside hot (by simp))
  · exact ((((k₁.trans k₂).trans k₃).trans k₄).trans kt).mono (by decide)

/-- `loadE`: `e` (`e_len ≤ 8` octets at `kE`, most significant first) into
`rbx`. -/
theorem loadE_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) {eP : Addr} {eB : List Byte} (hE : word s.mem B (8 * kE) = eP)
    (hEl : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length) (hl1 : 1 ≤ eB.length) (hl8 : eB.length ≤ 8)
    (hsrc : Src s B Z eP eB) :
    WP isa (seqs loadE) s fun t => (t.gpr .rbx).toNat = Spec.Rsa.os2ip eB ∧ t.mem = s.mem ∧
      Keep [.rsi, .rcx, .rbx, .rax] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  unfold loadE
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = eP ∧
      t.gpr .rcx = BitVec.ofNat 64 eB.length ∧ t.gpr .rbx = 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl kE (by decide), hl kElen (by decide), hE, hEl]) rfl)
    fun s₁ ⟨⟨hsi, hcx, hbx, hm₁⟩, k₁⟩ => ?_)
  refine wp_countdown (cnt := .rcx) (N := eB.length) (by omega_arith) (by omega_arith)
    (fun i t => (t.gpr .rbx).toNat = pre eB i ∧ t.gpr .rsi = eP + BitVec.ofNat 64 i ∧ t.mem = s.mem ∧
      Keep [.rsi, .rcx, .rbx, .rax] s t) ?_ (fun t ⟨h1, _, h3, k⟩ => ⟨by rw [h1, pre_len], h3, k⟩)
    ⟨by rw [hbx]; rfl, by rw [hsi]; exact (BitVec.add_zero eP).symm, hm₁, k₁.mono (by decide)⟩ hcx
  intro i hi t ⟨hb, hsi', hm, k⟩ _
  have hpre : pre eB i < 2 ^ 56 := by
    have := pre_lt eB (i := i) (by omega_arith)
    calc pre eB i < 256 ^ i := this
      _ ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 2 ^ 56 := by decide
  have hrd : InRegions (t.rd ++ t.wr) (eP + BitVec.ofNat 64 i) 1 := by
    rw [k.2.1, k.2.2]; exact hsrc.rd i hi
  have hbyte : t.mem (eP + BitVec.ofNat 64 i) = eB[i] := by rw [hm]; exact hsrc.val i hi
  refine WP.mono (WP.keep [.rsi, .rcx, .rbx, .rax] (Q := fun t' =>
      (t'.gpr .rbx).toNat = pre eB (i + 1) ∧ t'.gpr .rsi = eP + BitVec.ofNat 64 (i + 1) ∧ t'.mem = t.mem ∧
      t'.gpr .rcx = t.gpr .rcx - 1 ∧ t'.zf = some (t.gpr .rcx - 1 == 0)) ?_ rfl)
    fun t' ⟨⟨h1, h2, h3, h4, h5⟩, k'⟩ => ⟨⟨h1, h2, h3.trans hm, (k.trans k').mono (by decide)⟩, h4, h5⟩
  xrun [State.ea, at0, hsi', BitVec.ofInt_ofNat, BitVec.add_zero, hrd, hbyte, BitVec.add_assoc, ofNat_add_one]
  rw [BitVec.toNat_add, ror56_toNat _ (by rw [hb]; exact hpre), hb, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (b := 2 ^ 64) (by have := eB[i].isLt; omega_arith), pre_succ eB hi]
  have := eB[i].isLt
  rw [Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem gcd_even_ne_one {a e : Nat} (ha : a % 2 = 0) (he : e % 2 = 0) : Nat.gcd a e ≠ 1 := by
  intro h
  have h2a : 2 ∣ Nat.gcd a e := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero he)
  rw [h] at h2a
  exact absurd (Nat.le_of_dvd (by decide) h2a) (by decide)

/-- `gcdCheck`: ZF set iff `gcd(c − 1, e) = 1`, for `c` (in `aN`) odd and at
least 3, and `e` at `kE`. -/
theorem gcdCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hc : wv s.mem B (slot w aN) w % 2 = 1)
    (hc3 : 3 ≤ wv s.mem B (slot w aN) w) {eP : Addr} {eB : List Byte} (hE : word s.mem B (8 * kE) = eP)
    (hEl : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length) (hl1 : 1 ≤ eB.length) (hl8 : eB.length ≤ 8)
    (hsrc : Src s B Z eP eB) :
    WP isa (seqs gcdCheck) s fun t =>
      t.zf = some (decide (Nat.gcd (wv s.mem B (slot w aN) w - 1) (Spec.Rsa.os2ip eB) = 1)) ∧
      Good t B Z w minv ∧ Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r8, .r12, .r13, .r14] s t := by
  have hn := hg.scr.nowrap
  have hGl : InRegions (s.rd ++ s.wr) (off B (8 * kG)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_arith)
  have hG : 8 * kG + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  unfold gcdCheck
  refine wp_seqs_append (by simp [loadE]) (by simp) (WP.mono (loadE_ok hg hZ hE hEl hl1 hl8 hsrc)
    fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w minv := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  generalize hEv : Spec.Rsa.os2ip eB = E at hbx₁ ⊢
  generalize hcv : wv s.mem B (slot w aN) w = c at hc hc3 ⊢
  simp only [seqs]
  -- `kG := e`, ZF from its low bit.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kG)) (s₁.gpr .rbx) ∧
      t.zf = some (decide (E % 2 = 0)) ∧ t.gpr .rbx = s₁.gpr .rbx) (by
    have hst : InRegions s₁.wr (off B (8 * kG)) 8 := by rw [k₁.2.2]; exact hg.scr.st (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_arith)
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hst, sx1]
    rw [← hbx₁]
    refine Bool.eq_iff_iff.mpr ?_
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, and1_toNat]; rfl) rfl) fun s₂ ⟨⟨hm₂, hz₂, hbx₂⟩, k₂⟩ => ?_)
  have hg₂ : Good s₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
    by rw [hm₂]; exact hg₁.hdr.store (by decide) (by decide) _⟩
  have ho₂ : Outside B (8 * kG) 8 s.mem s₂.mem := by rw [hm₂, hm₁]; exact writeW_outside _ _ _ (by omega_arith)
  have hG₂ : word s₂.mem B (8 * kG) = s₁.gpr .rbx := by rw [hm₂]; exact word_writeW_self _ _ _ _
  have hc₂ : wv s₂.mem B (slot w aN) w = c := by rw [← hcv]; exact ho₂.wv (Or.inr hG) (by omega_arith)
  -- The branches, then ZF from `kG`.
  have fin : ∀ t : State, Good t B Z w minv → (∃ g, g < 2 ^ 64 ∧ (g = 1 ↔ Nat.gcd (c - 1) E = 1) ∧
        word t.mem B (8 * kG) = BitVec.ofNat 64 g) →
      Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s.mem t.mem →
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r8, .r12, .r13, .r14] s t →
      WP isa (.block [.mov .rax (.mem (hdr kG)), .alu .cmp .rax (.imm 1)]) t fun t' =>
        t'.zf = some (decide (Nat.gcd (c - 1) E = 1)) ∧ Good t' B Z w minv ∧
        Frm B [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] s.mem t'.mem ∧
        Keep [.rax, .rcx, .rdx, .rbp, .rsi, .rbx, .r8, .r12, .r13, .r14] s t' := by
    intro t hgt ⟨g, hg64, hiff, hv⟩ hf kt
    have hl : InRegions (t.rd ++ t.wr) (off B (8 * kG)) 8 := hgt.scr.ld (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_arith)
    refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (Nat.gcd (c - 1) E = 1)) ∧ t'.mem = t.mem) ?_ rfl)
      fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hz, ⟨hgt.scr.congr k.2.2, (k.gpr (by decide)).trans hgt.rdi, by rw [hm]; exact hgt.hdr⟩,
        by rw [hm]; exact hf, (kt.trans k).mono (by decide)⟩
    xrun [State.ea, hdr, hgt.rdi, hdrOff, hl, sx1, hv]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_beq hg64 (by decide)]
    exact decide_eq_decide.mpr hiff
  have hcm : (c - 1) % 2 = 0 := by omega_arith
  have hEl64 : E < 2 ^ 64 := by rw [← hbx₁]; exact (s₁.gpr .rbx).isLt
  have hE64 : s₁.gpr .rbx = BitVec.ofNat 64 E := by rw [← hbx₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.ite (decide (E % 2 = 0)) (by simp [eval, hz₂]) (fun he => ?_) (fun he => ?_))
  · -- An even `e`: `kG` keeps it.
    simp only [decide_eq_true_eq] at he
    refine WP.block_nil (fin s₂ hg₂ ⟨E, hEl64, ⟨fun h => by omega_arith, fun h => absurd h (gcd_even_ne_one hcm he)⟩,
      by rw [hG₂, ← hbx₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩ (Frm.of_outside ho₂ (by simp)) ((k₁.trans k₂).mono (by decide)))
  · simp only [decide_eq_false_iff_not] at he
    refine WP.seq (WP.mono (WP.keep [.rbx] (Q := fun t => t.zf = some (decide (E = 1)) ∧ t.mem = s₂.mem ∧
        t.gpr .rbx = s₂.gpr .rbx) (by
      xrun [sx1, hbx₂, hE64]
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_beq hEl64 (by decide)]) rfl)
      fun s₃ ⟨⟨hz₃, hm₃, hbx₃'⟩, k₃⟩ => ?_)
    have hg₃ : Good s₃ B Z w minv := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, by rw [hm₃]; exact hg₂.hdr⟩
    refine WP.ite (decide (E = 1)) (by simp [eval, hz₃]) (fun h1 => ?_) (fun h1 => ?_)
    · simp only [decide_eq_true_eq] at h1
      refine WP.block_nil (fin s₃ hg₃ ⟨1, by decide, ⟨fun _ => by rw [h1, Nat.gcd_one_right], fun _ => rfl⟩,
        by rw [hm₃, hG₂, hE64, h1]⟩
        (by rw [hm₃]; exact Frm.of_outside ho₂ (by simp)) (((k₁.trans k₂).trans k₃).mono (by decide)))
    · simp only [decide_eq_false_iff_not] at h1
      have hbx₃ : s₃.gpr .rbx = s₁.gpr .rbx := hbx₃'.trans hbx₂
      have hc₃ : wv s₃.mem B (slot w aN) w = c := by rw [hm₃, hc₂]
      refine WP.mono (gcdE_ok hg₃ hZ hw hw' (by rw [hc₃]; exact hc) (by rw [hbx₃, hbx₁]; omega_arith)
        (by rw [hbx₃, hbx₁]; omega_arith)) fun s₄ ⟨hG₄, hg₄, hf₄, k₄⟩ => fin s₄ hg₄ ⟨_, ?_, Iff.rfl, ?_⟩ ?_ ?_
      · exact Nat.lt_of_le_of_lt (Nat.gcd_le_right _ (by omega_arith)) hEl64
      · rw [hG₄, hc₃, hbx₃, hbx₁]
      · rw [hm₃] at hf₄
        intro x hx
        rw [hf₄ x hx, Frm.of_outside ho₂ (by simp) x hx]
      · exact ((((k₁.trans k₂).trans k₃).trans k₄)).mono (by decide)

end VG.Proof.RsaKeyGen.X86_64