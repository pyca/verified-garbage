module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoops
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtEst
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.QDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: a digit of the square root

The step's window (`winPtrs_ok`), the estimate (`estX_ok`), `R - q̂ D`
(`mulSubX_ok`), the corrections' addend (`toE_ok`), a correction (`fixX_ok`),
`D`'s update (`updX_ok`), and the step (`stepX_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `winPtrs` at count `c` (`1 ≤ c ≤ h - 1`, `W = 2 h + 4`): the window
`X' + 16 (c - 1)` in `rbx` and `r8`, `D + 8 (c - 1)` in `r10`, its length
`h - (c - 1) + 2` in `r12`. -/
theorem winPtrs_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) {c : Nat}
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) :
    WP isa (.block winPtrs) s fun t =>
      t.gpr .rbx = off B (slot W sqZ + 16 * (c - 1)) ∧ t.gpr .r8 = off B (slot W sqZ + 16 * (c - 1)) ∧
      t.gpr .r10 = off B (slot W sqD + 8 * (c - 1)) ∧ t.gpr .r12 = BitVec.ofNat 64 (h - (c - 1) + 2) ∧
      t.gpr .r9 = BitVec.ofNat 64 (8 * (W + 2)) ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbx, .r10, .rcx, .r8] s t := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  unfold winPtrs
  rw [show ws ++ base sqZ .rbx ++ base sqD .r10 ++ hOf ++ ([.mov .rcx (.mem (hdr sCt)), .alu .sub .rcx (.imm 1),
      .alu .sub .r12 (.reg .rcx), .alu .add .r12 (.imm 2), .shift .shl .rcx 3, .alu .add .r10 (.reg .rcx),
      .alu .add .rbx (.reg .rcx), .alu .add .rbx (.reg .rcx), .mov .r8 (.reg .rbx)] : List Instr) =
    ws ++ ((base sqZ .rbx ++ base sqD .r10) ++ (hOf ++ ([.mov .rcx (.mem (hdr sCt)), .alu .sub .rcx (.imm 1),
      .alu .sub .r12 (.reg .rcx), .alu .add .r12 (.imm 2), .shift .shl .rcx 3, .alu .add .r10 (.reg .rcx),
      .alu .add .rbx (.reg .rcx), .alu .add .rbx (.reg .rcx), .mov .r8 (.reg .rbx)] : List Instr))) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok sqZ sqD (r₁ := .rbx) (r₂ := .r10) (w := W) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun s₂ ⟨hbx, h10, m₂, k₂⟩ => ?_
  have hs₂ := hw.scr.congr (k₁.trans k₂).2.2
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hw.rdi
  refine WP.mono (WP.keep [.r12, .rbx, .r10, .rcx, .r8] (Q := fun t =>
      t.gpr .rbx = off B (slot W sqZ + 16 * (c - 1)) ∧ t.gpr .r8 = off B (slot W sqZ + 16 * (c - 1)) ∧
      t.gpr .r10 = off B (slot W sqD + 8 * (c - 1)) ∧ t.gpr .r12 = BitVec.ofNat 64 (h - (c - 1) + 2) ∧
      t.mem = s₂.mem) (by
    simp only [hOf, List.cons_append, List.nil_append]
    have hc' : word s₂.mem B (8 * sCt) = BitVec.ofNat 64 c := by rw [m₂, m₁, hc]
    xrun [(k₂.gpr (by decide) : s₂.gpr .r12 = _), h12, hOf_ofNat (W := W) (by omega_arith) (by omega_arith),
      show W / 2 - 2 = h by omega_arith, State.ea, hdr, hdi₂, hdrOff,
      hs₂.ld (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), hc', hbx, h10,
      sx_ofNat (show 1 < 2 ^ 31 by decide), sx_ofNat (show 2 < 2 ^ 31 by decide)]
    rw [sub_one_ofNat hc1 (by omega_arith), ofNat_shl3 (by omega_arith),
      ofNat_sub64 (by omega_arith) (by omega_arith), show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
      ← BitVec.ofNat_add]
    refine ⟨?_, ?_, by rw [off_addN], rfl⟩ <;>
    · unfold off
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 2; omega_arith) rfl) fun t ⟨⟨a1, a2, a3, a4, m₃⟩, k₃⟩ => ?_
  exact ⟨a1, a2, a3, a4, (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9), by rw [m₃, m₂, m₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-! ## The estimate -/

/-- An address `b + 8 i + d` at a word `k` of the base. -/
theorem addrI {b i p : Addr} {e j k : Nat} {d : Int} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j)
    (hk : (8 * j : Int) + d = 8 * k) : b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 d = off p (e + 8 * k) := by
  subst hb hi
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 d = BitVec.ofNat 64 (8 * k) := by
    rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add,
      show ((8 * j : Nat) : Int) + d = ((8 * k : Nat) : Int) by push_cast; omega, BitVec.ofInt_natCast]
  rw [ofNat_mul8, off, BitVec.add_assoc, BitVec.add_assoc, h8, ← BitVec.ofNat_add]

/-- The halving's word: `(a 2^64 + b) / 2` modulo `2^64`. -/
def hv (a b : BitVec 64) : BitVec 64 := (a <<< 63) ||| (b >>> (64 - 63))

theorem hv_toNat (a b : BitVec 64) : (hv a b).toNat = a.toNat % 2 * 2 ^ 63 + b.toNat / 2 := by
  have h1 : (a <<< 63).toNat % 2 ^ 63 = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 63 ∣ 2 ^ 64)]
    exact Nat.mul_mod_left _ _
  have h2 : (b >>> (64 - 63)).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := b.isLt; omega
  unfold hv
  rw [or_disj _ _ h1 h2, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 64 = 2 * 2 ^ 63 by decide, Nat.mul_mod_mul_right]

/-- `half x t a o`: word `o` at `t` := words `L + a + 1` and `L + a` of `x`, halved. -/
theorem half_ok {t : State} {B : Addr} {Z ex et L k o : Nat} {x tr : Reg} {a oi : Int} (hs : Scr t B Z)
    (hx : t.gpr x = off B ex) (htr : t.gpr tr = off B et) (h12 : t.gpr .r12 = BitVec.ofNat 64 L)
    (hk : (L : Int) + a = k) (ho : oi = o) (hxr : x ≠ .rax) (htra : tr ≠ .rax) (htrd : tr ≠ .rdx)
    (hX : ex + 8 * (k + 2) ≤ Z) (hT : et + 8 * (o + 1) ≤ Z) :
    WP isa (.block (half x tr a oi)) t fun t' =>
      t'.mem = t.mem.writeW (off B (et + 8 * o)) (hv (word t.mem B (ex + 8 * (k + 1))) (word t.mem B (ex + 8 * k))) ∧
      Keep [.rax, .rdx] t t' := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t' => t'.mem = t.mem.writeW (off B (et + 8 * o))
    (hv (word t.mem B (ex + 8 * (k + 1))) (word t.mem B (ex + 8 * k)))) ?_ rfl) fun t' ⟨h, k'⟩ => ⟨h, k'⟩
  have a1 := addrI (d := 8 * (a + 1)) (k := k + 1) hx h12 (by omega)
  have a0 := addrI (d := 8 * a) (k := k) hx h12 (by omega)
  have hat := show t.gpr tr + BitVec.ofInt 64 (8 * oi) = off B (et + 8 * o) by
    rw [htr, ho, show (8 * (o : Int)) = ((8 * o : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast, off_addN]
  have shv : (1 ≤ 63 ∧ 63 ≤ 63) = True := eq_true ⟨by decide, by decide⟩
  unfold half
  xrun [State.ea, ix, a1, a0, hat, execShld, shv, hs.ld (d := ex + 8 * (k + 1)) (by omega), hs.ld (d := ex + 8 * k) (by omega),
    hs.st (d := et + 8 * o) (by omega), hxr, htra, htrd]
  rfl

theorem word_wW {m : Mem} {B : Addr} {d d' : Nat} (v : BitVec 64) (hsep : d' + 8 ≤ d ∨ d + 8 ≤ d')
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : word (m.writeW (off B d) v) B d' = word m B d' :=
  (writeW_outside m B v hd).word (by omega) hd'

/-- The estimate: the halved remainder's top three words into the scratch `[5]`,
the root's top two into words 1 and 2 of `[1]` (whose word 0 is the reciprocal
of the top one), and `q̂ = min(⌊U / D⌋, 2^64 - 1)` into `sU`. -/
theorem estX_ok {s : State} {B : Addr} {Z W h c L eZ eD : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h)
    (heZ : eZ = slot W sqZ + 16 * (c - 1)) (heD : eD = slot W sqD + 8 * (c - 1)) (hL : L = h - (c - 1) + 2)
    {u0 u1 u2 d0 d1 : BitVec 64}
    (eu0 : u0 = hv (word s.mem B (eZ + 8 * (L - 4 + 1))) (word s.mem B (eZ + 8 * (L - 4))))
    (eu1 : u1 = hv (word s.mem B (eZ + 8 * (L - 3 + 1))) (word s.mem B (eZ + 8 * (L - 3))))
    (eu2 : u2 = hv (word s.mem B (eZ + 8 * (L - 2 + 1))) (word s.mem B (eZ + 8 * (L - 2))))
    (ed0 : d0 = hv (word s.mem B (eD + 8 * (L - 4 + 1))) (word s.mem B (eD + 8 * (L - 4))))
    (ed1 : d1 = hv (word s.mem B (eD + 8 * (L - 3 + 1))) (word s.mem B (eD + 8 * (L - 3))))
    (hd : 2 ^ 63 ≤ d1.toNat) (hv0 : (word s.mem B (slot W sqS)).toNat = (2 ^ 128 - 1) / d1.toNat - 2 ^ 64)
    (hu : u2.toNat ≤ d1.toNat)
    (hUD : u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat < (2 ^ 64 + 1) * (d1.toNat * 2 ^ 64 + d0.toNat)) :
    WP isa (.block estX) s fun t =>
      t.mem = (((((s.mem.writeW (off B (slot W sqU)) u0).writeW (off B (slot W sqU + 8 * 1)) u1).writeW
        (off B (slot W sqU + 8 * 2)) u2).writeW (off B (slot W sqS + 8 * 1)) d0).writeW
          (off B (slot W sqS + 8 * 2)) d1).writeW (off B (8 * sU))
          (BitVec.ofNat 64 (min ((u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) /
            (d1.toNat * 2 ^ 64 + d0.toNat)) (2 ^ 64 - 1))) ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have sU' : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have sS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  subst heZ heD hL
  unfold estX
  rw [show ws ++ base sqU .rsi ++ base sqS .r11 ++ winPtrs ++ half .rbx .rsi (-4) 0 ++ half .rbx .rsi (-3) 1 ++
      half .rbx .rsi (-2) 2 ++ half .r10 .r11 (-4) 1 ++ half .r10 .r11 (-3) 2 ++
      ([.mov .rbx (.reg .rsi), .mov .r10 (.reg .r11), .mov .rbp (.reg .r11), .mov32 .r12 (.imm 3)] : List Instr) ++
      R2Words.quot ++ R2Words.refine3 ++ ([.store (hdr sU) .rcx] : List Instr) =
    ws ++ ((base sqU .rsi ++ base sqS .r11) ++ (winPtrs ++ (half .rbx .rsi (-4) 0 ++ (half .rbx .rsi (-3) 1 ++
      (half .rbx .rsi (-2) 2 ++ (half .r10 .r11 (-4) 1 ++ (half .r10 .r11 (-3) 2 ++
      (([.mov .rbx (.reg .rsi), .mov .r10 (.reg .r11), .mov .rbp (.reg .r11), .mov32 .r12 (.imm 3)] : List Instr) ++
      (R2Words.quot ++ (R2Words.refine3 ++ ([.store (hdr sU) .rcx] : List Instr))))))))))) by
    simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok sqU sqS (r₁ := .rsi) (r₂ := .r11) (w := W) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun s₂ ⟨hsi, h11, m₂, k₂⟩ => ?_
  have hw₂ : Ws s₂ B Z W := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₂, m₁]) (fun _ f => f.elim)
    (k₁.trans k₂) (by simp)
  rw [WP.block_append_iff]
  refine WP.mono (winPtrs_ok hw₂ hwh (by rw [m₂, m₁, hc]) hc1 hch) fun s₃ ⟨hbx, h8, h10, h12', h9', m₃, k₃⟩ => ?_
  have hs₃ := hw.scr.congr ((k₁.trans k₂).trans k₃).2.2
  have s3si : s₃.gpr .rsi = off B (slot W sqU) := (k₃.gpr (by decide)).trans hsi
  have s311 : s₃.gpr .r11 = off B (slot W sqS) := (k₃.gpr (by decide)).trans h11
  have ms : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  -- The halvings.
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (k := h - (c - 1) + 2 - 4) (o := 0) hs₃ hbx s3si h12' (by omega_arith) rfl (by decide)
    (by decide) (by decide) (by omega_arith) (by omega_arith)) fun s₄ ⟨m₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (k := h - (c - 1) + 2 - 3) (o := 1) (hs₃.congr k₄.2.2) ((k₄.gpr (by decide)).trans hbx)
    ((k₄.gpr (by decide)).trans s3si) ((k₄.gpr (by decide)).trans h12') (by omega_arith) rfl (by decide)
    (by decide) (by decide) (by omega_arith) (by omega_arith)) fun s₅ ⟨m₅, k₅⟩ => ?_
  have k45 := k₄.trans k₅
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (k := h - (c - 1) + 2 - 2) (o := 2) (hs₃.congr k45.2.2) ((k45.gpr (by decide)).trans hbx)
    ((k45.gpr (by decide)).trans s3si) ((k45.gpr (by decide)).trans h12') (by omega_arith) rfl (by decide)
    (by decide) (by decide) (by omega_arith) (by omega_arith)) fun s₆ ⟨m₆, k₆⟩ => ?_
  have k46 := k45.trans k₆
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (k := h - (c - 1) + 2 - 4) (o := 1) (hs₃.congr k46.2.2) ((k46.gpr (by decide)).trans h10)
    ((k46.gpr (by decide)).trans s311) ((k46.gpr (by decide)).trans h12') (by omega_arith) rfl (by decide)
    (by decide) (by decide) (by omega_arith) (by omega_arith)) fun s₇ ⟨m₇, k₇⟩ => ?_
  have k47 := k46.trans k₇
  rw [WP.block_append_iff]
  refine WP.mono (half_ok (k := h - (c - 1) + 2 - 3) (o := 2) (hs₃.congr k47.2.2) ((k47.gpr (by decide)).trans h10)
    ((k47.gpr (by decide)).trans s311) ((k47.gpr (by decide)).trans h12') (by omega_arith) rfl (by decide)
    (by decide) (by decide) (by omega_arith) (by omega_arith)) fun s₈ ⟨m₈, k₈⟩ => ?_
  have k48 := k47.trans k₈
  -- The words written, from those on entry.
  have mem8 : s₈.mem = ((((s.mem.writeW (off B (slot W sqU)) u0).writeW (off B (slot W sqU + 8 * 1)) u1).writeW
      (off B (slot W sqU + 8 * 2)) u2).writeW (off B (slot W sqS + 8 * 1)) d0).writeW (off B (slot W sqS + 8 * 2)) d1 := by
    rw [m₈, m₇, m₆, m₅, m₄, ms, eu0, eu1, eu2, ed0, ed1, Nat.mul_zero, Nat.add_zero]
    simp (disch := omega_arith) only [word_wW]
  -- The scratch's words.
  have wU0 : word s₈.mem B (slot W sqU + 8 * (3 - 3)) = u0 := by
    rw [mem8]; simp (disch := omega_arith) only [word_wW]; exact word_writeW_self _ _ _ _
  have wU1 : word s₈.mem B (slot W sqU + 8 * (3 - 2)) = u1 := by
    rw [mem8]; simp (disch := omega_arith) only [word_wW]; exact word_writeW_self _ _ _ _
  have wU2 : word s₈.mem B (slot W sqU + 8 * (3 - 1)) = u2 := by
    rw [mem8]; simp (disch := omega_arith) only [word_wW]; exact word_writeW_self _ _ _ _
  have wS1 : word s₈.mem B (slot W sqS + 8 * (3 - 2)) = d0 := by
    rw [mem8]; simp (disch := omega_arith) only [word_wW]; exact word_writeW_self _ _ _ _
  have wS2 : word s₈.mem B (slot W sqS + 8 * (3 - 1)) = d1 := by
    rw [mem8]; exact word_writeW_self _ _ _ _
  have wS0 : word s₈.mem B (slot W sqS) = word s.mem B (slot W sqS) := by
    rw [mem8]; simp (disch := omega_arith) only [word_wW]
  -- The registers for the estimate.
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx, .r10, .rbp, .r12] (Q := fun t => t.gpr .rbx = off B (slot W sqU) ∧
      t.gpr .r10 = off B (slot W sqS) ∧ t.gpr .rbp = off B (slot W sqS) ∧ t.gpr .r12 = BitVec.ofNat 64 3 ∧
      t.mem = s₈.mem) (by
    xrun [(k48.gpr (by decide) : s₈.gpr .rsi = _), (k48.gpr (by decide) : s₈.gpr .r11 = _), s3si, s311]) rfl) fun s₉ ⟨⟨r9bx, r910, r9bp, r912, m₉⟩, k₉⟩ => ?_
  have hs₉ := hs₃.congr (k48.trans k₉).2.2
  rw [← m₉] at wU0 wU1 wU2 wS1 wS2 wS0
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.R2w.quot_ok (w := 3) hs₉ r9bx r910 r912 r9bp (by decide) (by omega_arith)
    (by omega_arith) (by omega_arith) (by rw [wU2, wS2]; exact hu) (by rw [wS2]; exact hd)
    (by rw [wS0, wS2]; exact hv0)) fun s₁₀ ⟨q10, m₁₀, k₁₀⟩ => ?_
  rw [wU2, wU1, wS2] at q10
  have est := est21 (u2 := u2.toNat) (u1 := u1.toNat) (u0 := u0.toNat) (d0 := d0.toNat) u0.isLt d0.isLt hd
  have q10' : (s₁₀.gpr .rcx).toNat = min ((u2.toNat * 2 ^ 64 + u1.toNat) / d1.toNat) (2 ^ 64 - 1) := by
    rw [q10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))]
  have hs₁₀ := hs₉.congr k₁₀.2.2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.R2w.refine3_ok (w := 3) hs₁₀ ((k₁₀.gpr (by decide)).trans r9bx)
    ((k₁₀.gpr (by decide)).trans r910) ((k₁₀.gpr (by decide)).trans r912) (by decide) (by omega_arith)
    (by omega_arith) (by rw [m₁₀, wU2, wU1, wU0]) (by rw [m₁₀, wS2, wS1]) (by omega_arith) hUD
    (by rw [q10']; exact est.1) (by rw [q10']; exact est.2)) fun s₁₁ ⟨q11, m₁₁, k₁₁⟩ => ?_
  have hs₁₁ := hs₁₀.congr k₁₁.2.2
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₁₁.mem.writeW (off B (8 * sU)) (s₁₁.gpr .rcx)) (by
    xrun [State.ea, hdr, hdrOff, ((((k48.trans k₉).trans k₁₀).trans k₁₁).gpr (by decide) : s₁₁.gpr .rdi = _),
      (k₃.gpr (by decide) : s₃.gpr .rdi = _), (k₂.gpr (by decide) : s₂.gpr .rdi = _),
      (k₁.gpr (by decide) : s₁.gpr .rdi = _), hw.rdi,
      hs₁₁.st (d := 8 * sU) (by simp only [sU, sFn]; omega_arith)]) rfl) fun t ⟨mt, kt⟩ => ?_
  refine ⟨?_, (((((((k₁.trans k₂).trans k₃).trans k48).trans k₉).trans k₁₀).trans k₁₁).trans kt).mono (by decide)⟩
  rw [mt, m₁₁, m₁₀, m₉, mem8, of_toNat q11]

/-! ## `R - q̂ D` -/

/-- `mulSubX`: `D`'s word `m := q̂` (`sU`), then `T := R - q̂ D` over the window of
`L` words, modulo `2^(64 L)`. -/
theorem mulSubX_ok {s : State} {B : Addr} {Z W h c : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) {q : Nat}
    (hq : word s.mem B (8 * sU) = BitVec.ofNat 64 q) (hq64 : q < 2 ^ 64) :
    WP isa mulSubX s fun t => ∃ k,
      wv t.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) +
        q * wv (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) (BitVec.ofNat 64 q)) B (slot W sqD + 8 * (c - 1))
          (h - (c - 1) + 2) =
        wv s.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) + 2 ^ (64 * (h - (c - 1) + 2)) * k ∧
      Outside B (slot W sqZ + 16 * (c - 1)) (8 * (h - (c - 1) + 2))
        (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) (BitVec.ofNat 64 q)) t.mem ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  unfold mulSubX
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (winPtrs_ok hw hwh hc hc1 hch)
    fun s₁ ⟨hbx, h8, h10, h12, h9, m₁, k₁⟩ => WP.mono (WP.keep [.rcx, .r9, .rbp] (Q := fun t =>
      t.gpr .rcx = BitVec.ofNat 64 q ∧ t.gpr .r9 = 0 ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) (BitVec.ofNat 64 q)) (by
      xrun [State.ea, hdr, hdrOff, at0, (k₁.gpr (by decide) : s₁.gpr .rdi = _), hw.rdi, h10, m₁, hq,
        (hw.scr.congr k₁.2.2).ld (d := 8 * sU) (by simp only [sU, sFn]; omega_arith),
        (hw.scr.congr k₁.2.2).st (d := slot W sqD + 8 * (c - 1)) (by omega_arith), sx0, add_ofInt0]) rfl) fun s₂ ⟨⟨a, b, c', d⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have hs₂ := hw.scr.congr k12.2.2
  refine WP.mono (msub_ok hs₂ ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h10)
    ((k₂.gpr (by decide)).trans h12) b c' (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (Or.inr (by omega_arith))) fun t ⟨k, hv, ho, kt⟩ => ?_
  have hwin : wv (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) (BitVec.ofNat 64 q)) B (slot W sqZ + 16 * (c - 1))
      (h - (c - 1) + 2) = wv s.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) :=
    (writeW_outside s.mem B (BitVec.ofNat 64 q) (d := slot W sqD + 8 * (c - 1)) (by omega_arith)).wv
      (by omega_arith) (by omega_arith)
  rw [a, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64, d, hwin] at hv
  rw [d] at ho
  exact ⟨k, hv, ho, (k12.trans kt).mono (by decide)⟩

/-! ## `D`'s low two words -/

theorem ofBool_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl

theorem sx0' : BitVec.signExtend 64 (0 : BitVec 32) = 0#64 := rfl

/-- `(b, 2 a) - 1` modulo `2^128`, as `add`, `adc 0`, `sub 1`, `sbb 0` compute it. -/
theorem dec2 (a b : BitVec 64) :
    (b + 0#64 + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + a.toNat))).setWidth 64 - 0#64 -
        (BitVec.ofBool (decide ((a + a).toNat < (1 : BitVec 64).toNat))).setWidth 64).toNat * 2 ^ 64 +
      (a + a - 1).toNat =
      (b.toNat * 2 ^ 64 + 2 * a.toNat + 2 ^ 128 - 1) % 2 ^ 128 := by
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.add_zero, BitVec.sub_zero, BitVec.toNat_sub, BitVec.toNat_add, ofBool_toNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  cases h1 : decide (2 ^ 64 ≤ x + x) <;> cases h2 : decide ((x + x) % 2 ^ 64 < 1) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false] at h1 h2 ⊢ <;> omega

/-- `toE`'s arithmetic: `(rdx, rax) := (hi, 2 lo) - 1` modulo `2^128`. -/
theorem toE_ok {s : State} {B : Addr} {Z W h c : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) :
    WP isa (.block toE) s fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo).writeW (off B (slot W sqD + 8 * (c - 1) + 8)) hi ∧
      hi.toNat * 2 ^ 64 + lo.toNat = ((word s.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat * 2 ^ 64 +
        2 * (word s.mem B (slot W sqD + 8 * (c - 1))).toNat + 2 ^ 128 - 1) % 2 ^ 128 ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  unfold toE
  rw [WP.block_append_iff]
  refine WP.mono (winPtrs_ok hw hwh hc hc1 hch) fun s₁ ⟨_, _, h10, _, _, m₁, k₁⟩ => ?_
  have hs₁ := hw.scr.congr k₁.2.2
  generalize hlo : word s.mem B (slot W sqD + 8 * (c - 1)) = lo0
  generalize hhi : word s.mem B (slot W sqD + 8 * (c - 1) + 8) = hi0
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo).writeW (off B (slot W sqD + 8 * (c - 1) + 8)) hi ∧
      hi.toNat * 2 ^ 64 + lo.toNat = (hi0.toNat * 2 ^ 64 + 2 * lo0.toNat + 2 ^ 128 - 1) % 2 ^ 128) ?_ rfl)
    fun t ⟨⟨lo, hi, hm, hv⟩, k⟩ => ⟨lo, hi, hm, hv, (k₁.trans k).mono (by decide)⟩
  have e8 : off B (slot W sqD + 8 * (c - 1)) + BitVec.ofInt 64 8 = off B (slot W sqD + 8 * (c - 1) + 8) := by
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, off_addN]
  xrun [State.ea, at0, add_ofInt0, e8, h10, m₁, hlo, hhi, hs₁.ld (d := slot W sqD + 8 * (c - 1)) (by omega_arith),
    hs₁.ld (d := slot W sqD + 8 * (c - 1) + 8) (by omega_arith), hs₁.st (d := slot W sqD + 8 * (c - 1)) (by omega_arith),
    hs₁.st (d := slot W sqD + 8 * (c - 1) + 8) (by omega_arith)]
  refine ⟨_, _, rfl, ?_⟩
  rw [sx0']
  exact dec2 lo0 hi0

/-- `(b, a) - 2 c` modulo `2^128`, as `sub`, `sbb 0` compute it. -/
theorem sub2 (a b : BitVec 64) (c : Bool) :
    (b - 0#64 - (BitVec.ofBool (decide (a.toNat < (mask c &&& BitVec.ofNat 64 2).toNat))).setWidth 64).toNat * 2 ^ 64 +
      (a - (mask c &&& BitVec.ofNat 64 2)).toNat =
      (b.toNat * 2 ^ 64 + a.toNat + 2 ^ 128 - 2 * c.toNat) % 2 ^ 128 := by
  have ha := a.isLt; have hb := b.isLt
  have hm : (mask c &&& BitVec.ofNat 64 2).toNat = 2 * c.toNat := by cases c <;> rfl
  simp only [BitVec.sub_zero, BitVec.toNat_sub, ofBool_toNat, hm]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.not_lt_zero, decide_false, Nat.sub_zero]
    omega
  · simp only [Bool.toNat_true, Nat.mul_one]
    by_cases h2 : x < 2
    · simp only [h2, decide_true, Bool.toNat_true]; omega
    · simp only [h2, decide_false, Bool.toNat_false]; omega

/-- `(b, a) + 1` modulo `2^128`, as `add 1`, `adc 0` compute it. -/
theorem inc2 (a b : BitVec 64) :
    (b + 0#64 + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + (1 : BitVec 64).toNat))).setWidth 64).toNat * 2 ^ 64 +
      (a + 1).toNat = (b.toNat * 2 ^ 64 + a.toNat + 1) % 2 ^ 128 := by
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.add_zero, BitVec.toNat_add, ofBool_toNat, show (1 : BitVec 64).toNat = 1 from rfl]
  generalize a.toNat = x at *
  generalize b.toNat = y at *
  cases h1 : decide (2 ^ 64 ≤ x + 1) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false] at h1 ⊢ <;> omega

/-- `updX`: `D`'s low two words plus one, modulo `2^128`. -/
theorem updX_ok {s : State} {B : Addr} {Z W h c : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) :
    WP isa (.block updX) s fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo).writeW (off B (slot W sqD + 8 * (c - 1) + 8)) hi ∧
      hi.toNat * 2 ^ 64 + lo.toNat = ((word s.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat * 2 ^ 64 +
        (word s.mem B (slot W sqD + 8 * (c - 1))).toNat + 1) % 2 ^ 128 ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  unfold updX
  rw [WP.block_append_iff]
  refine WP.mono (winPtrs_ok hw hwh hc hc1 hch) fun s₁ ⟨_, _, h10, _, _, m₁, k₁⟩ => ?_
  have hs₁ := hw.scr.congr k₁.2.2
  generalize hlo : word s.mem B (slot W sqD + 8 * (c - 1)) = lo0
  generalize hhi : word s.mem B (slot W sqD + 8 * (c - 1) + 8) = hi0
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo).writeW (off B (slot W sqD + 8 * (c - 1) + 8)) hi ∧
      hi.toNat * 2 ^ 64 + lo.toNat = (hi0.toNat * 2 ^ 64 + lo0.toNat + 1) % 2 ^ 128) ?_ rfl)
    fun t ⟨⟨lo, hi, hm, hv⟩, k⟩ => ⟨lo, hi, hm, hv, (k₁.trans k).mono (by decide)⟩
  have e8 : off B (slot W sqD + 8 * (c - 1)) + BitVec.ofInt 64 8 = off B (slot W sqD + 8 * (c - 1) + 8) := by
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, off_addN]
  xrun [State.ea, at0, add_ofInt0, e8, h10, m₁, hlo, hhi, hs₁.ld (d := slot W sqD + 8 * (c - 1)) (by omega_arith),
    hs₁.ld (d := slot W sqD + 8 * (c - 1) + 8) (by omega_arith), hs₁.st (d := slot W sqD + 8 * (c - 1)) (by omega_arith),
    hs₁.st (d := slot W sqD + 8 * (c - 1) + 8) (by omega_arith)]
  refine ⟨_, _, rfl, ?_⟩
  exact inc2 lo0 hi0

/-! ## A correction -/

/-- `fixX`: if the window's top word has its top bit set (`T < 0`), `T := T + D`
over the window (modulo `2^(64 L)`), then `D`'s low two words less two. -/
theorem fixX_ok {s : State} {B : Addr} {Z W h c : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4)
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (hc1 : 1 ≤ c) (hch : c + 1 ≤ h) :
    WP isa fixX s fun t => ∃ (m : Mem) (c' : Bool) (lo hi : BitVec 64),
      wv m B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) + 2 ^ (64 * (h - (c - 1) + 2)) * c'.toNat =
        (if 2 ^ 63 ≤ (word s.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))).toNat then
          wv s.mem B (slot W sqD + 8 * (c - 1)) (h - (c - 1) + 2) else 0) +
          wv s.mem B (slot W sqZ + 16 * (c - 1)) (h - (c - 1) + 2) ∧
      Outside B (slot W sqZ + 16 * (c - 1)) (8 * (h - (c - 1) + 2)) s.mem m ∧
      t.mem = (m.writeW (off B (slot W sqD + 8 * (c - 1))) lo).writeW (off B (slot W sqD + 8 * (c - 1) + 8)) hi ∧
      hi.toNat * 2 ^ 64 + lo.toNat = ((word s.mem B (slot W sqD + 8 * (c - 1) + 8)).toNat * 2 ^ 64 +
        (word s.mem B (slot W sqD + 8 * (c - 1))).toNat + 2 ^ 128 -
        2 * (decide (2 ^ 63 ≤ (word s.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))).toNat)).toNat) %
          2 ^ 128 ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hw2 := hw.w2
  have hZ := hw.hZ
  rw [slotE] at hZ
  have sZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have sD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  generalize hneg : decide (2 ^ 63 ≤ (word s.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))).toNat) = neg
  unfold fixX
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.mono (winPtrs_ok hw hwh hc hc1 hch)
    fun s₁ ⟨hbx, h8, h10, h12, h9, m₁, k₁⟩ => WP.mono (WP.keep [.rax, .r15, .rbp] (Q := fun t =>
      t.gpr .r15 = mask neg ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
      have ea : s₁.gpr .rbx + s₁.gpr .r12 * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) =
          off B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1)) :=
        addrm8 hbx h12 (by omega_arith)
      xrun [State.ea, ix, ea, m₁, (hw.scr.congr k₁.2.2).ld (d := slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))
        (by omega_arith)]
      rw [← hneg]
      unfold mask
      congr 3
      apply decide_eq_decide.mpr
      show _ ↔ 2 ^ 63 ≤ (word s.mem B (slot W sqZ + 16 * (c - 1) + 8 * (h - (c - 1) + 2 - 1))).toNat
      unfold Bignum.word
      omega) rfl) fun s₂ ⟨⟨a15, abp, m₂⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  have hs₂ := hw.scr.congr k12.2.2
  refine WP.mono (addM_ok (c := neg) (N := h - (c - 1) + 2) hs₂ ((k₂.gpr (by decide)).trans hbx)
    ((k₂.gpr (by decide)).trans h10) ((k₂.gpr (by decide)).trans h8) a15 ((k₂.gpr (by decide)).trans h12) abp
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))
    (Or.inr (Nat.le_refl _))) fun s₃ ⟨c', _, hv, ho, k₃⟩ => ?_
  rw [m₂] at hv ho
  rw [← hneg] at hv
  simp only [decide_eq_true_eq] at hv
  have hs₃ := hs₂.congr k₃.2.2
  have r10 : s₃.gpr .r10 = off B (slot W sqD + 8 * (c - 1)) := (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h10)
  have r15 : s₃.gpr .r15 = mask neg := (k₃.gpr (by decide)).trans a15
  have wlo : word s₃.mem B (slot W sqD + 8 * (c - 1)) = word s.mem B (slot W sqD + 8 * (c - 1)) :=
    ho.word (by omega_arith) (by omega_arith)
  have whi : word s₃.mem B (slot W sqD + 8 * (c - 1) + 8) = word s.mem B (slot W sqD + 8 * (c - 1) + 8) :=
    ho.word (by omega_arith) (by omega_arith)
  generalize hlo : word s.mem B (slot W sqD + 8 * (c - 1)) = lo0 at wlo
  generalize hhi : word s.mem B (slot W sqD + 8 * (c - 1) + 8) = hi0 at whi
  have e8 : off B (slot W sqD + 8 * (c - 1)) + BitVec.ofInt 64 8 = off B (slot W sqD + 8 * (c - 1) + 8) := by
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, off_addN]
  refine WP.mono (WP.keep [.r11, .rax, .rdx] (Q := fun t => ∃ lo hi : BitVec 64,
      t.mem = (s₃.mem.writeW (off B (slot W sqD + 8 * (c - 1))) lo).writeW (off B (slot W sqD + 8 * (c - 1) + 8)) hi ∧
      hi.toNat * 2 ^ 64 + lo.toNat = (hi0.toNat * 2 ^ 64 + lo0.toNat + 2 ^ 128 - 2 * neg.toNat) % 2 ^ 128) (by
    xrun [State.ea, at0, add_ofInt0, e8, r10, r15, wlo, whi, hs₃.ld (d := slot W sqD + 8 * (c - 1)) (by omega_arith),
      hs₃.ld (d := slot W sqD + 8 * (c - 1) + 8) (by omega_arith), hs₃.st (d := slot W sqD + 8 * (c - 1)) (by omega_arith),
      hs₃.st (d := slot W sqD + 8 * (c - 1) + 8) (by omega_arith)]
    refine ⟨_, _, rfl, ?_⟩
    rw [sx0']
    exact sub2 lo0 hi0 neg) rfl) fun t ⟨⟨lo, hi, hm, hval⟩, kt⟩ => ?_
  exact ⟨s₃.mem, c', lo, hi, hv, ho, hm, hval, ((k12.trans k₃).trans kt).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.Rd
