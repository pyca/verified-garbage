import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-!
# RSA with the CRT on x86-64: the exponentiation in a prime's workspace

`expBit`, in a prime's workspace (`X`, `w_X` words, `R = 2^(64 w_X)`):
`Y := Y² R⁻¹`, `T := Y [aXc] R⁻¹`, and `Y := T` if the bit is set, by a
masked selection (`crtExpBit_ok`); `expLoop` does it for every bit of the
exponent, read from the modulus' header (`crtExpLoop_ok`): `Y ≡ x^d R`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- `selectAcc` in place: `[o] := lt ? [a] : [o]`. -/
theorem selectAcc_self_ok {s : State} {B : Addr} {Z w eA eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hsi : s.gpr .rsi = off B eo) (hbx : s.gpr .rbx = off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) :
    WP isa selectAcc s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eo w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have hn := hs.nowrap
  unfold selectAcc
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SelInv s B Z eA eo eo lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by
      cases lt <;> rfl⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (SelInv s B Z eA eo eo lt) h0 ?_)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro j _ hj t hI
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = off B eo := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tbp : t.gpr .rbp = mask lt := (hI.keep.gpr (by decide)).trans hbp
  have hx : word t.mem B (eA + 8 * j) = word s.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eo + 8 * j) = word s.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if lt then word s.mem B (eA + 8 * j) else word s.mem B (eo + 8 * j))) (by
      xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, addr0 tbx hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy, select_mask]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    cases lt <;> simp [wv]

/-! ## What the exponentiation changes -/

/-- What a bit of the exponentiation changes in the prime's workspace:
arrays and header slots. -/
def crtBitRanges (wx : Nat) : List (Nat × Nat) :=
  [(slot wx aAcc, 8 * (wx + 2)), (slot wx aTmp, 8 * (wx + 2)), (slot wx aY, 8 * (wx + 2)),
    (slot wx Crt.aT, 8 * (wx + 2)), (8 * Crt.sV, 8), (8 * Crt.sBit, 8)]

/-- What the exponentiation changes: also the exponent's pointer and length
and the byte index. -/
def crtExpRanges (wx : Nat) : List (Nat × Nat) :=
  (8 * Crt.sExp, 8) :: (8 * Crt.sExpLen, 8) :: (8 * Crt.sI, 8) :: crtBitRanges wx

theorem crtBitRanges_sub (wx : Nat) : ∀ r ∈ crtBitRanges wx, r ∈ crtExpRanges wx :=
  fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem crtExpRanges_ok (wx : Nat) : ∀ r ∈ crtExpRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 := by
  have := hdr_lt_slot wx 0 (show 31 < 32 by decide)
  have := slot_le (w := wx) (show aAcc < 8 by decide)
  have := slot_le (w := wx) (show aTmp < 8 by decide)
  have := slot_le (w := wx) (show aY < 8 by decide)
  have := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have h1 : slot wx 0 ≤ slot wx aAcc := by unfold slot; omega
  have h2 : slot wx 0 ≤ slot wx aTmp := by unfold slot; omega
  have h3 : slot wx 0 ≤ slot wx aY := by unfold slot; omega
  have h4 : slot wx 0 ≤ slot wx Crt.aT := by unfold slot; omega
  simp only [crtExpRanges, crtBitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sV, Crt.sBit, sFn] at * <;> omega

theorem crtBitRanges_ok (wx : Nat) : ∀ r ∈ crtBitRanges wx, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 :=
  fun r hr => crtExpRanges_ok wx r (crtBitRanges_sub wx r hr)

/-- The arrays the exponentiation does not change. -/
theorem crtExpRanges_arr (wx : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ Crt.aT) : ∀ r ∈ crtExpRanges wx, slot wx j + 8 * (wx + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot wx j := by
  have := hdr_lt_slot wx j (show 31 < 32 by decide)
  have s1 := slot_sep (w := wx) h1
  have s2 := slot_sep (w := wx) h2
  have s3 := slot_sep (w := wx) h3
  have s4 := slot_sep (w := wx) h4
  have := hj
  simp only [crtExpRanges, crtBitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [Crt.sExp, Crt.sExpLen, Crt.sI, Crt.sV, Crt.sBit, sFn] at * <;> omega

/-- A header slot that a bit of the exponentiation does not change. -/
theorem crtBitRanges_hdr (wx : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ Crt.sV) (h2 : k ≠ Crt.sBit) :
    ∀ r ∈ crtBitRanges wx, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have := hdr_lt_slot wx aAcc hk
  have := hdr_lt_slot wx aTmp hk
  have := hdr_lt_slot wx aY hk
  have := hdr_lt_slot wx Crt.aT hk
  simp only [crtBitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sV, Crt.sBit, sFn] at * <;> omega

/-! ## The prime's workspace -/

/-- What the exponentiation keeps in the workspace at `P` (`w_X` words):
the workspace, the prime `X` (and its low word, for `-X⁻¹`), and
`Xc ≡ x R`. -/
structure CExpCtx (t : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc : Nat) : Prop where
  good : Good t P (slot wx 8) wx minv
  n : wv t.mem P (slot wx aN) wx = X
  inv : ((word t.mem P (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem P (slot wx Crt.aXc) wx = Xc

/-- What changes only within the exponentiation's ranges keeps the context. -/
theorem CExpCtx.of_frm {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hf : Frm P (crtExpRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : CExpCtx t' P wx minv X Xc := by
  have hn := hc.good.scr.nowrap
  have rN := crtExpRanges_arr wx (j := aN) (by decide) (by decide) (by decide) (by decide) (by decide)
  have rX := crtExpRanges_arr wx (j := Crt.aXc) (by decide) (by decide) (by decide) (by decide) (by decide)
  have lN := slot_le (w := wx) (show aN < 8 by decide)
  have lX := slot_le (w := wx) (show Crt.aXc < 8 by decide)
  have hh : ∀ i < 17, word t'.mem P (8 * i) = word t.mem P (8 * i) := fun i hi =>
    hf.word_eq (fun r hr => Or.inl (by have := crtExpRanges_ok wx r hr; omega))
      (by have := hdr_lt_slot wx 8 (show i < 32 by omega); omega)
  exact ⟨⟨hc.good.scr.congr hwr, hdi.trans hc.good.rdi,
    ⟨(hh _ (by decide)).trans hc.good.hdr.hw, (hh _ (by decide)).trans hc.good.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (hc.good.hdr.harr j hj)⟩⟩,
    by rw [hf.wv_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact hc.n,
    by rw [hf.word_eq (fun r hr => by have := rN r hr; omega) (by omega)]; exact hc.inv,
    by rw [hf.wv_eq (fun r hr => by have := rX r hr; omega) (by omega)]; exact hc.x⟩

theorem CExpCtx.of_bit {t t' : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hf : Frm P (crtBitRanges wx) t.mem t'.mem) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = t.gpr .rdi) : CExpCtx t' P wx minv X Xc :=
  hc.of_frm (hf.mono (crtBitRanges_sub wx)) hwr hdi

/-! ## A bit -/

/-- The mask of the top bit of the byte in `sV`, as `shr 7; and 1; neg` leaves it. -/
theorem crtBitMask (V : Nat) (hV : V < 2 ^ 64) :
    BitVec.setWidth 64 (0 : BitVec 32) - (BitVec.ofNat 64 V >>> 7 &&& 1) = mask (decide (V / 128 % 2 = 1)) := by
  have h : (BitVec.ofNat 64 V >>> 7 &&& 1).toNat = V / 128 % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
      Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have e : (BitVec.ofNat 64 V >>> 7 &&& 1) = (BitVec.ofBool (decide (V / 128 % 2 = 1))).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [h]
    by_cases h1 : V / 128 % 2 = 1
    · rw [h1]; simp
    · rw [show V / 128 % 2 = 0 by omega]; simp
  rw [e]; rfl

/-- The block between the products: the bit's mask into `rbp`, `sV` doubled,
and the bases of the selection. -/
theorem crtBitMid_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc V : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62) :
    WP isa (.block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
      .store (hdr Crt.sV) .rax,
      .shift .shr .rdx 7, .alu .and .rdx (.imm 1), .mov32 .rbp (.imm 0), .alu .sub .rbp (.reg .rdx),
      .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr Crt.aT))), .mov .rsi (.mem (hdr (sArr aY))),
      .mov .rbx (.mem (hdr (sArr aY)))]) t fun t' =>
      t'.gpr .rbp = mask (decide (V / 128 % 2 = 1)) ∧ t'.gpr .r12 = BitVec.ofNat 64 wx ∧
      t'.gpr .r8 = off P (slot wx Crt.aT) ∧ t'.gpr .rsi = off P (slot wx aY) ∧
      t'.gpr .rbx = off P (slot wx aY) ∧
      t'.mem = t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V + V)) ∧
      Keep [.rdx, .rax, .rbp, .r12, .r8, .rsi, .rbx] t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have hs : ∀ i < 32, InRegions t.wr (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega)
  have hW : ∀ v : BitVec 64, (t.mem.writeW (off P (8 * Crt.sV)) v).readW (off P (8 * sW)) 64 =
      BitVec.ofNat 64 wx := fun v =>
    (hdrStore_hdr t.mem P v (by decide) (by decide) (by decide)).trans hc.good.hdr.hw
  have hA : ∀ j < 8, ∀ v : BitVec 64, (t.mem.writeW (off P (8 * Crt.sV)) v).readW (off P (8 * sArr j)) 64 =
      off P (slot wx j) := fun j hj v =>
    (hdrStore_hdr t.mem P v (by decide) (by unfold sArr; omega) (by unfold sArr Crt.sV sFn; omega)).trans
      (hc.good.hdr.harr j hj)
  refine WP.mono (WP.keep [.rdx, .rax, .rbp, .r12, .r8, .rsi, .rbx] (Q := fun t' =>
      t'.gpr .rbp = mask (decide (V / 128 % 2 = 1)) ∧ t'.gpr .r12 = BitVec.ofNat 64 wx ∧
      t'.gpr .r8 = off P (slot wx Crt.aT) ∧ t'.gpr .rsi = off P (slot wx aY) ∧
      t'.gpr .rbx = off P (slot wx aY) ∧
      t'.mem = t.mem.writeW (off P (8 * Crt.sV)) (BitVec.ofNat 64 (V + V))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl Crt.sV (by decide), hs Crt.sV (by decide), hV,
      hl sW (by decide), hl (sArr Crt.aT) (by decide), hl (sArr aY) (by decide), hW, hA Crt.aT (by decide),
      hA aY (by decide), crtBitMask V (by omega), ← BitVec.ofNat_add]) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩

/-- The bit count decremented, `ZF` when it reaches 0. -/
theorem crtBitEnd_ok {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc b : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b)
    (hb' : b < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]) t
      fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b - 1)) ∧
        t'.zf = some (decide (b - 1 = 0)) ∧ Keep [.rax] t t' := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have hs : ∀ i < 32, InRegions t.wr (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off P (8 * Crt.sBit))
      (BitVec.ofNat 64 (b - 1)) ∧ t'.zf = some (decide (b - 1 = 0))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl Crt.sBit (by decide), hs Crt.sBit (by decide), hb,
      ofNat64_pred hb1 (by omega), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩

/-- A Montgomery squaring of `Y ≡ y^F x^E R`: `y^(2F) x^(2E) R`. -/
theorem mont_sq2 {Y Y' y x F E R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = y ^ F * x ^ E * R % m)
    (h : Y' * R % m = Y * Y % m) : Y' % m = y ^ (2 * F) * x ^ (2 * E) * R % m := by
  rw [VG.Proof.Bignum.mont_sq (x := y ^ F * x ^ E) (E := 1) hR (by rw [Nat.pow_one]; exact hY) h, Nat.mul_one,
    Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm F 2, Nat.mul_comm E 2]

/-- A Montgomery multiplication of `Y ≡ y^F x^E R` by `X ≡ x R`: `y^F x^(E+1) R`. -/
theorem mont_mulx2 {Y Y' Xc y x F E R m : Nat} (hR : Nat.Coprime R m) (hY : Y % m = y ^ F * x ^ E * R % m)
    (hX : Xc % m = x * R % m) (h : Y' * R % m = Y * Xc % m) : Y' % m = y ^ F * x ^ (E + 1) * R % m := by
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, Nat.mul_mod, hY, hX, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  ring

/-- One bit: `Y ≡ y^F x^E R` becomes `x^(2E + bit) R`, for the bit at the top of
the byte `V / 128 mod 2`; `V` doubles and the bit count `b` drops. -/
theorem crtExpBit_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc y F x E Y V b : Nat}
    (hc : CExpCtx t P wx minv X Xc) (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X) (hXc : Xc % X = x * 2 ^ (64 * wx) % X)
    (hY : wv t.mem P (slot wx aY) wx = Y) (hYN : Y < X) (hYc : Y % X = y ^ F * x ^ E * 2 ^ (64 * wx) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62)
    (hb : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa (seqs (Crt.expBit M.mm)) t fun t' => CExpCtx t' P wx minv X Xc ∧
      (∃ Y', wv t'.mem P (slot wx aY) wx = Y' ∧ Y' < X ∧
        Y' % X = y ^ (2 * F) * x ^ (2 * E + V / 128 % 2) * 2 ^ (64 * wx) % X) ∧
      word t'.mem P (8 * Crt.sV) = BitVec.ofNat 64 (V + V) ∧
      word t'.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm P (crtBitRanges wx) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hT0 := slot_le (w := wx) (show Crt.aT < 8 by decide)
  have hYT := slot_sep (w := wx) (show aY ≠ Crt.aT by decide)
  simp only [Crt.expBit, seqs]
  -- `Y := Y²`.
  refine WP.seq (WP.mono (M.mm_ok (o := aY) (a := aY) (b := aY) hc.good (Nat.le_refl _) hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hY, hc.n]; exact hYN)) fun t₁ ⟨_, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁
  rw [hc.n, hY] at hm₁
  have f₁ : Frm P (crtBitRanges wx) t.mem t₁.mem := Frm.of_arrays ha₁ (by simp [crtBitRanges])
  have hc₁ := hc.of_bit f₁ k₁.2.2 (k₁.gpr (by decide))
  have hY₁ : wv t₁.mem P (slot wx aY) wx % X = y ^ (2 * F) * x ^ (2 * E) * 2 ^ (64 * wx) % X :=
    mont_sq2 hR hYc hm₁
  -- `T := Y Xc`.
  refine WP.seq (WP.mono (M.mm_ok (o := Crt.aT) (a := aY) (b := Crt.aXc) hc₁.good (Nat.le_refl _) hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hc₁.x, hc₁.n]; exact hXN)) fun t₂ ⟨_, hlt₂, hm₂, ha₂, k₂⟩ => ?_)
  rw [hc₁.n] at hlt₂
  rw [hc₁.n, hc₁.x] at hm₂
  have f₂ : Frm P (crtBitRanges wx) t₁.mem t₂.mem := Frm.of_arrays ha₂ (by simp [crtBitRanges])
  have hc₂ := hc₁.of_bit f₂ k₂.2.2 (k₂.gpr (by decide))
  have hT₂ : wv t₂.mem P (slot wx Crt.aT) wx % X = y ^ (2 * F) * x ^ (2 * E + 1) * 2 ^ (64 * wx) % X :=
    mont_mulx2 hR hY₁ hXc hm₂
  have hY₂ : wv t₂.mem P (slot wx aY) wx = wv t₁.mem P (slot wx aY) wx :=
    ha₂.wv_of_not_mem (by decide) (by decide) hn
  have hV₂ : word t₂.mem P (8 * Crt.sV) = BitVec.ofNat 64 V := by
    rw [ha₂.hslot (by decide), ha₁.hslot (by decide)]; exact hV
  have hb₂ : word t₂.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b := by
    rw [ha₂.hslot (by decide), ha₁.hslot (by decide)]; exact hb
  -- The mask, `sV` doubled, the bases.
  refine WP.seq (WP.mono (crtBitMid_ok hc₂ hV₂ hV') fun t₃ ⟨hbp₃, h12₃, h8₃, hsi₃, hbx₃, hm₃, k₃⟩ => ?_)
  have o₃ := writeW_outside t₂.mem P (d := 8 * Crt.sV) (BitVec.ofNat 64 (V + V)) (by decide)
  rw [← hm₃] at o₃
  have f₃ : Frm P (crtBitRanges wx) t₂.mem t₃.mem := Frm.of_outside o₃ (by simp [crtBitRanges])
  have hc₃ := hc₂.of_bit f₃ k₃.2.2 (k₃.gpr (by decide))
  have hYv₃ : wv t₃.mem P (slot wx aY) wx = wv t₂.mem P (slot wx aY) wx :=
    o₃.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega) (by omega)
  have hTv₃ : wv t₃.mem P (slot wx Crt.aT) wx = wv t₂.mem P (slot wx Crt.aT) wx :=
    o₃.wv (by have := hdr_lt_slot wx Crt.aT (show Crt.sV < 32 by decide); omega) (by omega)
  -- `Y := bit ? T : Y`.
  refine WP.seq (WP.mono (selectAcc_self_ok hc₃.good.scr h8₃ hsi₃ hbx₃ h12₃ hbp₃ (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun t₄ ⟨hsel₄, o₄, k₄⟩ => ?_)
  have f₄ : Frm P (crtBitRanges wx) t₃.mem t₄.mem :=
    Frm.of_outside (o₄.mono (o' := slot wx aY) (n' := 8 * (wx + 2)) (Nat.le_refl _) (by omega))
      (by simp [crtBitRanges])
  have hc₄ := hc₃.of_bit f₄ k₄.2.2 (k₄.gpr (by decide))
  have hb₄ : word t₄.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b := by
    rw [o₄.word (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega) (by decide), hm₃,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hb₂
  -- The bit count.
  refine WP.mono (crtBitEnd_ok hc₄ hb₄ hb1 hb') fun t' ⟨hm', hz', k'⟩ => ?_
  have o₅ := writeW_outside t₄.mem P (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b - 1)) (by decide)
  rw [← hm'] at o₅
  have f₅ : Frm P (crtBitRanges wx) t₄.mem t'.mem := Frm.of_outside o₅ (by simp [crtBitRanges])
  have hY' : wv t'.mem P (slot wx aY) wx = wv t₄.mem P (slot wx aY) wx :=
    o₅.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega) (by omega)
  refine ⟨hc₄.of_bit f₅ k'.2.2 (k'.gpr (by decide)), ⟨_, hY', ?_, ?_⟩, ?_, ?_, hz',
    (((f₁.trans f₂).trans f₃).trans f₄).trans f₅,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · rw [hsel₄, hTv₃, hYv₃, hY₂]
    split
    · exact hlt₂
    · exact hlt₁
  · rw [hsel₄, hTv₃, hYv₃, hY₂]
    by_cases h1 : V / 128 % 2 = 1
    · simp only [h1, decide_true, ↓reduceIte]; exact hT₂
    · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show V / 128 % 2 = 0 by omega, Nat.add_zero]; exact hY₁
  · rw [o₅.word (by decide) (by decide), o₄.word (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega)
      (by decide), hm₃, word_writeW_self]
  · rw [hm', word_writeW_self]

/-! ## The bits of a byte -/

/-- After `j` bits of the byte `v` from `t₀`, where `Y ≡ y^F x^E R`. -/
structure CBitInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc y F x E v : Nat) (j : Nat)
    (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  y : ∃ Y, wv t.mem P (slot wx aY) wx = Y ∧ Y < X ∧
    Y % X = y ^ (F * 2 ^ j) * x ^ (E * 2 ^ j + v / 2 ^ (8 - j)) * 2 ^ (64 * wx) % X
  v : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 (v * 2 ^ j)
  b : word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (8 - j)
  frm : Frm P (crtBitRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Bit `j` of the byte `v`. -/
theorem crtBitStep_ok (M : Mont) {t s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc y F x E v : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X)
    (hXc : Xc % X = x * 2 ^ (64 * wx) % X) (hv : v < 256) {j : Nat} (hj : j < 8)
    (hI : CBitInv t P wx minv X Xc y F x E v j s) :
    WP isa (seqs (Crt.expBit M.mm)) s fun s' => s'.zf = some (decide (j + 1 = 8)) ∧
      CBitInv t P wx minv X Xc y F x E v (j + 1) s' := by
  obtain ⟨Y, hY, hYN, hYc⟩ := hI.y
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (crtExpBit_ok M hI.ctx hw hw' hR hXN hXc hY hYN hYc hI.v
    (by have := Nat.mul_le_mul_left v hp; omega) hI.b (by omega) (by omega))
    fun s' ⟨hc', ⟨Y', hY', hYN', hYc'⟩, hV', hb', hz', hfr', k'⟩ => ⟨?_, ⟨hc', ⟨Y', hY', hYN', ?_⟩, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by simp [mmRegs])⟩⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [hYc', show 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) by
        rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc],
      show 2 * (F * 2 ^ j) = F * 2 ^ (j + 1) by rw [Nat.pow_succ, Nat.mul_comm 2 (F * 2 ^ j), Nat.mul_assoc]]
  · rw [hV', ← Nat.two_mul, Nat.pow_succ]; congr 1; rw [Nat.mul_comm, Nat.mul_assoc]
  · rw [hb']; congr 1

/-- The eight bits of the byte `v`: `Y ≡ y^F x^E R` becomes `y^(256 F) x^(256 E + v) R`. -/
theorem crtBits_ok (M : Mont) {t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc y F x E v : Nat}
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X)
    (hXc : Xc % X = x * 2 ^ (64 * wx) % X) (hv : v < 256) (h0 : CBitInv t P wx minv X Xc y F x E v 0 t) :
    WP isa (.loop (seqs (Crt.expBit M.mm)) .ne) t (CBitInv t P wx minv X Xc y F x E v 8) :=
  wp_upto (a := 0) (N := 8) (by decide) (CBitInv t P wx minv X Xc y F x E v)
    (fun _ _ hj _ hI => crtBitStep_ok M hw hw' hR hXN hXc hv hj hI) (fun _ h => h) h0

/-! ## The bytes of the exponent -/

/-- After `i` bytes of the exponent (`L` bytes `eb` at `ep`) from `t₀`. -/
structure CByteInv (t₀ : State) (P : Addr) (wx : Nat) (minv : BitVec 64) (X Xc y x : Nat) (ep : Addr)
    (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : CExpCtx t P wx minv X Xc
  y : ∃ Y, wv t.mem P (slot wx aY) wx = Y ∧ Y < X ∧ Y % X = y ^ (256 ^ i) * x ^ pre eb i * 2 ^ (64 * wx) % X
  idx : word t.mem P (8 * Crt.sI) = BitVec.ofNat 64 i
  e : word t.mem P (8 * Crt.sExp) = ep
  len : word t.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L
  frm : Frm P (crtExpRanges wx) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- The loads of the byte's address. -/
theorem crtByteHead1_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc y x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hI : CByteInv t₀ P wx minv X Xc y x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ CByteInv t₀ P wx minv X Xc y x ep L eb i t₁ := by
  have hc := hI.ctx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl Crt.sExp (by decide), hl Crt.sI (by decide), hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  have hf : Frm P (crtExpRanges wx) t.mem t₁.mem := by rw [hm]; exact Frm.refl _ _ _
  exact ⟨hc.of_frm hf k.2.2 (k.gpr (by decide)), hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e, hm ▸ hI.len,
    hI.frm.trans hf, (hI.keep.trans k).mono (by decide)⟩

/-- The byte into `sV`, and the bit count 8: the start of the bits. -/
theorem crtByteHead2_ok {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc y x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, slot wx 8 ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc y x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
      .mov32 .rax (.imm 8), .store (hdr Crt.sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (off P (8 * Crt.sV)) ((eb[i]'(by omega)).setWidth 64)).writeW
        (off P (8 * Crt.sBit)) (BitVec.setWidth 64 (8 : BitVec 32)) ∧ Keep [.rax] t t₁ ∧
      CBitInv t₁ P wx minv X Xc y (256 ^ i) x (pre eb i) (eb[i]'(by omega)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.good.scr.nowrap
  have hs : ∀ i < 32, InRegions t.wr (off P (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega)
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := (crtExpRanges_ok wx r hr).2; have := hout i hi; omega)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off P (8 * Crt.sV))
      ((eb[i]'(by omega)).setWidth 64)).writeW (off P (8 * Crt.sBit)) (BitVec.setWidth 64 (8 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hax, hcx, byteRead, hrdi, hbi, hs Crt.sV (by decide),
      hs Crt.sBit (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have o1 := writeW_outside t.mem P (d := 8 * Crt.sV) ((eb[i]'(by omega)).setWidth 64) (by decide)
  have o2 := writeW_outside (t.mem.writeW (off P (8 * Crt.sV)) ((eb[i]'(by omega)).setWidth 64)) P
    (d := 8 * Crt.sBit) (BitVec.setWidth 64 (8 : BitVec 32)) (by decide)
  rw [← hm₁] at o2
  have f₁ : Frm P (crtBitRanges wx) t.mem t₁.mem :=
    (Frm.of_outside o1 (by simp [crtBitRanges])).trans (Frm.of_outside o2 (by simp [crtBitRanges]))
  have hc₁ := hc.of_bit f₁ k₁.2.2 (k₁.gpr (by decide))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  obtain ⟨Y, hY, hYN, hYc⟩ := hI.y
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  refine ⟨hc₁, ⟨Y, ?_, hYN, ?_⟩, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [o2.wv (by have := hdr_lt_slot wx aY (show Crt.sBit < 32 by decide); omega) (by omega),
      o1.wv (by have := hdr_lt_slot wx aY (show Crt.sV < 32 by decide); omega) (by omega)]; exact hY
  · rw [hYc, Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 2 ^ 8 from hv),
      Nat.add_zero]
  · rw [o2.word (by decide) (by decide), word_writeW_self, setWidth_byte]
  · rw [hm₁, word_writeW_self]; rfl

theorem crtByteHead_eq : ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
      .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 8),
      .store (hdr Crt.sBit) .rax] : List Instr) =
    ([.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI))] : List Instr) ++
    ([.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 8),
      .store (hdr Crt.sBit) .rax] : List Instr) := rfl

/-- One byte of the exponent: its eight bits, then the next byte. -/
theorem crtByte_ok (M : Mont) {t₀ t : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {X Xc y x : Nat}
    {ep : Addr} {L : Nat} {eb : List Byte} {i : Nat} (hw : 2 ≤ wx) (hw' : wx < 2 ^ 30)
    (hR : Nat.Coprime (2 ^ (64 * wx)) X) (hXN : Xc < X) (hXc : Xc % X = x * 2 ^ (64 * wx) % X)
    (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, slot wx 8 ≤ ofs P (ep + BitVec.ofNat 64 i))
    (hI : CByteInv t₀ P wx minv X Xc y x ep L eb i t) :
    WP isa (seqs [.block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
        .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax, .mov32 .rax (.imm 8),
        .store (hdr Crt.sBit) .rax],
      .loop (seqs (Crt.expBit M.mm)) .ne,
      .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
        .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ CByteInv t₀ P wx minv X Xc y x ep L eb (i + 1) t' := by
  have hn := hI.ctx.good.scr.nowrap
  simp only [seqs]
  rw [crtByteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (crtByteHead1_ok hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (crtByteHead2_ok hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine WP.seq (WP.mono (crtBits_ok M hw hw' hR hXN hXc hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off P (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot wx 8 hi; omega)
  have hs₂ : ∀ i < 32, InRegions t₂.wr (off P (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.st (by have := hdr_lt_slot wx 8 hi; omega)
  have hh₂ : ∀ k < 32, k ≠ Crt.sV → k ≠ Crt.sBit → word t₂.mem P (8 * k) = word tₐ.mem P (8 * k) :=
    fun k hk h1 h2 => by
      rw [h₂.frm.word_eq (crtBitRanges_hdr wx hk h1 h2) (by omega), hm₁,
        hdrStore_hdr (i := Crt.sBit) _ _ _ (by decide) hk (Ne.symm h2),
        hdrStore_hdr (i := Crt.sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ Crt.sI (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ Crt.sExp (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ Crt.sExpLen (by decide) (by decide) (by decide)).trans hIₐ.len
  have hlen₂' : (t₂.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i + 1))).readW (off P (8 * Crt.sExpLen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off P (8 * Crt.sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hl₂ Crt.sI (by decide), hs₂ Crt.sI (by decide), hidx₂,
      ofNat_add_one, hl₂ Crt.sExpLen (by decide), hlen₂', ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega)
      (show L < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  have o' := writeW_outside t₂.mem P (d := 8 * Crt.sI) (BitVec.ofNat 64 (i + 1)) (by decide)
  rw [← hm'] at o'
  have f' : Frm P (crtExpRanges wx) t₂.mem t'.mem := Frm.of_outside o' (by simp [crtExpRanges])
  obtain ⟨Y₂, hY₂, hYN₂, hYc₂⟩ := h₂.y
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  refine ⟨hc₂.of_frm f' k'.2.2 (k'.gpr (by decide)), ⟨Y₂, ?_, hYN₂, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o'.wv (by have := hdr_lt_slot wx aY (show Crt.sI < 32 by decide); omega) (by omega)]; exact hY₂
  · rw [hYc₂, pre_succ eb (by omega), Nat.pow_zero, Nat.div_one, Nat.mul_comm (pre eb i), Nat.pow_succ 256 i]
    rfl
  · rw [hm', word_writeW_self]
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm P (crtExpRanges wx) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (writeW_outside tₐ.mem P _ (d := 8 * Crt.sV) (by decide))
        (by simp [crtExpRanges, crtBitRanges])).trans
        (Frm.of_outside (writeW_outside _ P _ (d := 8 * Crt.sBit) (by decide))
          (by simp [crtExpRanges, crtBitRanges]))
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (crtBitRanges_sub wx))).trans f'
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-! ## The exponentiation -/

/-- `expLoop`'s start: the exponent's pointer and length from the modulus'
header slots `sp` and `sl`, and byte index 0. -/
theorem crtExpInit_ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {L : Nat}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
      .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
      .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]) s fun t =>
      t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW (off (off B o) (8 * Crt.sExpLen))
        (BitVec.ofNat 64 L)).writeW (off (off B o) (8 * Crt.sI)) (BitVec.setWidth 64 (0 : BitVec 32)) ∧
      Keep [.rax, .rdx] s t := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.ld (by have := hdr_lt_slot wx 8 hi'; omega)
  have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi' =>
    hc.scr.ld (by have := hdr_lt_slot w 8 hi'; omega)
  have hst : ∀ i < 32, InRegions s.wr (off (off B o) (8 * i)) 8 := fun i hi' =>
    hc.good.scr.st (by have := hdr_lt_slot wx 8 hi'; omega)
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have hW : (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).readW (off B (8 * sl)) 64 = BitVec.ofNat 64 L :=
    ((Frm.of_outside (rs := [(8 * Crt.sExp, 8)]) o1 (by simp)).word_below (L := slot wx 8)
      (fun r hr => by rw [List.mem_singleton.mp hr]; unfold Crt.sExp sFn slot hdrBytes; omega) (by omega)
      (by unfold slot hdrBytes at hi; omega) (by have := hdr_lt_slot w 8 hsl; omega)).trans hel
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
      (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 L)).writeW (off (off B o) (8 * Crt.sI))
      (BitVec.setWidth 64 (0 : BitVec 32)))
    (by xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hl Crt.sLink (by decide), hc.link, hln sp hsp, hep,
      hst Crt.sExp (by decide), hln sl hsl, hW, hst Crt.sExpLen (by decide), hst Crt.sI (by decide)]) rfl)
    fun t ⟨hm, k⟩ => ⟨hm, k⟩

/-- The exponentiation in a prime's workspace: `Y ≡ y R` becomes
`Y ≡ y^(2^(8 L)) x^d R` modulo `X`, for the exponent `d` whose `L` bytes `eb` (most significant
first) are at `ep`, outside the working space, the pointer and length in
the modulus' header slots `sp` and `sl`. -/
theorem crtExpLoop_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x y : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % X = y * 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop M.mm sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      wv t.mem (off B o) (slot wx aY) wx % X =
        y ^ (2 ^ (8 * eb.length)) * x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hPn := hc.good.scr.nowrap
  have hBn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h256 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have hR : Nat.Coprime (2 ^ (64 * wx)) X := VG.Proof.Bignum.coprime_pow2 hodd _
  have hout : ∀ i < eb.length, slot wx 8 ≤ ofs (off B o) (ep + BitVec.ofNat 64 i) := fun i hi' => by
    have := he.out i hi'
    rcases ofs_rebase B (ep + BitVec.ofNat 64 i) (o := o) (by omega) with ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · omega
  have hc₀ : CExpCtx s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) :=
    ⟨hc.good, hn, hinv, rfl⟩
  refine WP.seq (WP.mono (crtExpInit_ok hc hsp hsl hep hel) fun t₁ ⟨hm₁, k₁⟩ => ?_)
  have o1 := writeW_outside s.mem (off B o) (d := 8 * Crt.sExp) ep (by decide)
  have o2 := writeW_outside (s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep) (off B o) (d := 8 * Crt.sExpLen)
    (BitVec.ofNat 64 eb.length) (by decide)
  have o3 := writeW_outside ((s.mem.writeW (off (off B o) (8 * Crt.sExp)) ep).writeW
    (off (off B o) (8 * Crt.sExpLen)) (BitVec.ofNat 64 eb.length)) (off B o) (d := 8 * Crt.sI)
    (BitVec.setWidth 64 (0 : BitVec 32)) (by decide)
  rw [← hm₁] at o3
  have f₁ : Frm (off B o) (crtExpRanges wx) s.mem t₁.mem :=
    ((Frm.of_outside o1 (by simp [crtExpRanges])).trans (Frm.of_outside o2 (by simp [crtExpRanges]))).trans
      (Frm.of_outside o3 (by simp [crtExpRanges]))
  have hY0 := slot_le (w := wx) (show aY < 8 by decide)
  have hY1 := hdr_lt_slot wx aY (show 31 < 32 by decide)
  have h₁ : CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) y x ep eb.length eb 0 t₁ := by
    refine ⟨hc₀.of_frm f₁ k₁.2.2 (k₁.gpr (by decide)), ⟨_, ?_, hyl, ?_⟩, ?_, ?_, ?_, f₁, k₁.mono (by decide)⟩
    · rw [o3.wv (by unfold Crt.sI sFn at *; omega) (by omega), o2.wv (by unfold Crt.sExpLen sFn at *; omega)
        (by omega), o1.wv (by unfold Crt.sExp sFn at *; omega) (by omega)]
    · rw [hyc, pre_zero, Nat.pow_zero, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
    · rw [hm₁, word_writeW_self]; rfl
    · rw [hm₁, hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr (i := Crt.sExpLen) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
    · rw [hm₁, hdrStore_hdr (i := Crt.sI) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  refine wp_upto (a := 0) (N := eb.length) (by omega)
    (CByteInv s (off B o) wx minv X (wv s.mem (off B o) (slot wx Crt.aXc) wx) y x ep eb.length eb)
    (fun i _ hi' t hI => crtByte_ok M hw2 (by omega) hR hxl hxc rfl (by omega) hi' he.rd he.val hout hI)
    (fun t hI => ?_) h₁
  obtain ⟨Y', h1, h2, h3⟩ := hI.y
  exact ⟨hc.of_frm hI.frm (crtExpRanges_ok wx) hI.keep.2.2 (hI.keep.gpr (by decide)), by rw [h1]; exact h2,
    by rw [h1, h3, pre_len, show 2 ^ (8 * eb.length) = 256 ^ eb.length by rw [Nat.pow_mul]],
    hI.frm, hI.keep⟩

/-- `crtExpLoop_ok` from `Y ≡ R`: `Y ≡ x^d R`. -/
theorem crtExpLoop_one_ok (M : Mont) {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (Crt.expLoop M.mm sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X ∧
      Frm (off B o) (crtExpRanges wx) s.mem t.mem ∧ Keep mmRegs s t :=
  WP.mono (crtExpLoop_ok M (y := 1) hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl (by rw [hyc, Nat.one_mul]) hsp hsl
    hep hel hL1 hL2 he) fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, by rw [h3, Nat.one_pow, Nat.one_mul], h4, h5⟩

end VG.Proof.Bignum.X86_64
