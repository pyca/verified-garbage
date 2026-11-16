module

public import VerifiedGarbage.Proof.Gcm.AArch64.Holes
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.Poly
meta import VerifiedGarbage.Proof.Gcm.AArch64.Holes
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Gcm.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Gcm.Powers
meta import VerifiedGarbage.Proof.Gcm.Poly

-- separate module: only the registration of `vg_aes_gcm_store_powers` imports it, and the
-- many modules that import `Proof.Gcm.AArch64.Ghash` need not rebuild it.

/-!
# The powers of the hash subkey from a key context, without PMULL (AArch64)

`keyPowers_verified` proves `Impl.Gcm.AArch64.keyPowers`
(`vg_aes_gcm_store_powers_scratch`) against `Spec.Gcm.storePowersContract`
with its working space as a last argument: it saves `x19`–`x28`, computes
the key `x⁻¹ · H` of the multiplication of `vg_ghash` and its masks from
`H` at byte 240 of the key context (`setup_ok`), loads `H` into `Z` and
stores `preparedPower(H)` (`first_ok`); then, for `k` from 2 to 8, it
multiplies `Z` by `H` (`mulCode_ok`, `Holes.mulK_eq`) and stores
`preparedPower(Hᵏ)` (`body_ok`, by `enc_eq`), and restores the registers.
`keyPowers_framed` is `vg_aes_gcm_store_powers`, which runs it with the
working space in a frame of its own.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Gcm.AArch64.KeyPowers

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Gcm.AArch64 VG.Proof.Gcm VG.Proof.Gcm.AArch64
open VG.Spec.Gcm (Block blockAt hpow preparedPower)

/-! ## The encoding -/

/-- The high doubleword of `0xc2 ‖ 0¹¹⁸ ‖ 1`. -/
def cHigh : BitVec 64 := 0xc200000000000000

/-- `storeEnc`'s two doublewords, the high then the low, from `Z = zh ++ zl`. -/
theorem enc_eq (zh zl : BitVec 64) :
    ((zh <<< 1 ||| zl >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - zh >>> 63))) ++
      ((zl <<< 1) ^^^ (((0 : BitVec 64) - zh >>> 63) >>> 63)) = preparedPower (zh ++ zl) := by
  rw [neg_msb, preparedPower, ← shl1]
  obtain hm : (zh ++ zl).getMsbD 0 = zh.msb := by
    rw [← BitVec.msb, BitVec.msb_append]; simp
  rw [hm]
  cases zh.msb
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [show BitVec.allOnes 64 >>> 63 = 1 from by decide, ← BitVec.xor_append]
    exact congrArg _ (by decide)

/-! ## Memory -/

/-- A little-endian 128-bit word is its high doubleword at `a + 8` and its
low one at `a`. -/
theorem readW128 (m : Mem) (a : Addr) :
    m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  apply BitVec.eq_of_toNat_eq
  obtain h := Proof.Mont.read_toNat_add m 8 8 a
  obtain e1 : (m.readW a 128).toNat = (m.read a (8 + 8)).toNat := by
    simp only [Mem.readW, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (m.read a (8 + 8)).isLt
  obtain e2 : ∀ b, (m.readW b 64).toNat = (m.read b 8).toNat := fun b => by
    simp only [Mem.readW, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (m.read b 8).isLt
  rw [e1, BitVec.toNat_append, e2, e2, h, ← Nat.shiftLeft_add_eq_or_of_lt (m.read a 8).isLt,
    Nat.shiftLeft_eq]
  omega_using []

/-! ## The contract -/

/-- `vg_aes_gcm_store_powers_scratch(ctx = x0, pw = x1, scratch = x2)` on
AArch64: the 256-byte key context readable, the 128-byte powers' buffer and
the 80 bytes of working space writable and apart from it and from each
other; the powers of `ctxH` at `pw`. -/
def keyPowersAArch64 : Contract AArch64.isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 256⟩
    let pw : Region := ⟨s.gpr .x1, 128⟩
    let scratch : Region := ⟨s.gpr .x2, 80⟩
    s.rd = [ctx] ∧ s.wr = [pw, scratch] ∧ ctx.Disjoint pw ∧ ctx.Disjoint scratch ∧
      pw.Disjoint scratch
  post s s' := Spec.Gcm.Powers8Repr s'.mem (s.gpr .x1) (Spec.Gcm.ctxH s.mem (s.gpr .x0))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

section
variable (s₀ : State)

/-- The key context, the powers' buffer and the working space. -/
abbrev ctxR : Region := ⟨s₀.gpr .x0, 256⟩
abbrev pwR : Region := ⟨s₀.gpr .x1, 128⟩
abbrev scrR : Region := ⟨s₀.gpr .x2, 80⟩

/-- The halves of `H`. -/
abbrev hw0 : BitVec 64 := rev64 (s₀.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 240) 64)
abbrev hw1 : BitVec 64 :=
  rev64 (s₀.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64)

end

theorem ctxH_eq (s₀ : State) : Spec.Gcm.ctxH s₀.mem (s₀.gpr .x0) = hw0 s₀ ++ hw1 s₀ := by
  rw [Spec.Gcm.ctxH, ← blockAt_rev]
  congr 3
  exact BitVec.add_zero _

/-! ## The pieces of the code -/

theorem keyAddr_ok (s : State) :
    WP isa (.block keyAddr) s fun t =>
      t.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 240 ∧ Keep [.x0] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [keyAddr], ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_write, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [gpr_write, hr, ite_false]

theorem keyLoad_ok (s : State)
    (hh : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8) :
    WP isa (.block keyLoad) s fun t =>
      t.gpr ZH = rev64 (s.mem.readW (s.gpr .x0) 64) ∧
      t.gpr ZL = rev64 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 8) 64) ∧ Keep [ZH, ZL] s t := by
  obtain h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 8 := by
    have := hh 0 (by decide); rwa [show s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 from BitVec.add_zero _] at this
  obtain h8 := hh 8 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by hrun [keyLoad, ZH, ZL, h0, h8], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [ZH, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq, read_8]
  · simp only [ZL, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq, read_8]
  · simp only [ZH, ZL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]

/-- `preparedPower(Z)` stored at `x1 + off`, as two writes. -/
theorem storeEnc_ok (s : State) {off : Nat} (ho : off % 8 = 0) (hlt : off + 8 < 4096 * 8)
    (o0 : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 off) 8)
    (o8 : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (off + 8)) 8) :
    WP isa (.block (storeEnc off)) s fun t =>
      t.mem = (s.mem.writeW (s.gpr .x1 + BitVec.ofNat 64 off)
          ((s.gpr ZL <<< 1) ^^^ (((0 : BitVec 64) - s.gpr ZH >>> 63) >>> 63))).writeW
        (s.gpr .x1 + BitVec.ofNat 64 (off + 8))
          ((s.gpr ZH <<< 1 ||| s.gpr ZL >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - s.gpr ZH >>> 63))) ∧
      (∀ r, r ∉ [T, B, .x0] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain a0 : off % 8 = 0 ∧ off < 4096 * 8 := ⟨ho, by omega_using [hlt]⟩
  obtain a8 : (off + 8) % 8 = 0 ∧ off + 8 < 4096 * 8 := ⟨by omega_using [ho], hlt⟩
  apply WP.of_runBlock
  refine ⟨_, by hrun [storeEnc, ZH, ZL, T, B, o0, o8, a0, a8], ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [ZH, ZL, mem_write, write_8, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
    rw [show BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0#64 by decide,
      show BitVec.setWidth 64 (0xc200 : BitVec 16) <<< 48 = cHigh by decide]
    rfl
  · simp only [T, B, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem keyCount_ok (s : State) :
    WP isa (.block keyCount) s fun t =>
      t.gpr CNT = 7 ∧ t.gpr D = 48 ∧ Keep [CNT, D] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [keyCount, CNT, D], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [CNT, D, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]; decide
  · simp only [CNT, D, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]; decide
  · simp only [CNT, D, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]

theorem keyY_ok (s : State) :
    WP isa (.block keyY) s fun t =>
      t.gpr Y0 = s.gpr ZH ∧ t.gpr Y1 = s.gpr ZL ∧ t.gpr YX = t.gpr Y0 ^^^ t.gpr Y1 ∧
      Keep [Y0, Y1, YX] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [keyY, Y0, Y1, YX, ZH, ZL], ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [Y0, Y1, YX, ZH, ZL, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [Y0, Y1, YX, ZH, ZL, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [Y0, Y1, YX, ZH, ZL, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [Y0, Y1, YX, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem keyNext_ok (s : State) :
    WP isa (.block keyNext) s fun t =>
      t.gpr .x1 = s.gpr .x1 + s.gpr D ∧ t.gpr D = 32 - s.gpr D ∧ t.gpr CNT = s.gpr CNT - 1 ∧
      Keep [.x1, T, D, CNT] s t := by
  apply WP.of_runBlock
  refine ⟨_, by hrun [keyNext, D, CNT, T], ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [D, CNT, T, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]
  · simp only [D, CNT, T, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]; rfl
  · simp only [D, CNT, T, gpr_write, reduceCtorEq, ↓reduceIte, BitVec.setWidth_eq]; rfl
  · simp only [T, D, CNT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-! ## The powers stored -/

/-- The powers `preparedPower(Hʲ)`, `1 ≤ j ≤ K`, stored at `pw`. -/
def Stored (s₀ : State) (H : Block) (K : Nat) (m : Mem) : Prop :=
  ∀ j, 1 ≤ j → j ≤ K →
    m.readW (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff j)) 128 = preparedPower (hpow H j)

theorem pwOff_le (k : Nat) (h1 : 1 ≤ k) (h8 : k ≤ 8) : pwOff k + 16 ≤ 128 := by
  simp only [pwOff]; split <;> omega

theorem pwOff_mod (k : Nat) : pwOff k % 8 = 0 := by
  simp only [pwOff]; split <;> omega_using []

/-- Distinct powers are 16 bytes apart. -/
theorem pwOff_sep (j k : Nat) (hj : 1 ≤ j) (hj8 : j ≤ 8) (hk : 1 ≤ k) (hk8 : k ≤ 8) (hjk : j ≠ k) :
    pwOff j + 16 ≤ pwOff k ∨ pwOff k + 16 ≤ pwOff j := by
  simp only [pwOff]; split <;> split <;> omega_arith

/-- `preparedPower(Hᴷ⁺¹)` stored, from `Z = zh ++ zl = Hᴷ⁺¹`, after the powers below it. -/
theorem stored_step {s₀ : State} {H : Block} {K : Nat} (hK8 : K + 1 ≤ 8) {m : Mem}
    (hst : Stored s₀ H K m) {zh zl : BitVec 64} (hz : zh ++ zl = hpow H (K + 1)) :
    Stored s₀ H (K + 1)
      ((m.writeW (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1)))
          ((zl <<< 1) ^^^ (((0 : BitVec 64) - zh >>> 63) >>> 63))).writeW
        (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1) + 8))
          ((zh <<< 1 ||| zl >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - zh >>> 63)))) := by
  intro j hj hjK
  obtain hle := pwOff_le (K + 1) (by omega_using []) hK8
  obtain hsep8 : Mem.Sep (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1))) (64 / 8)
      (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1) + 8)) (64 / 8) :=
    Offset.sep _ (by omega_using []) (by omega_using [hle]) (by omega_using [hle])
  rcases (by omega_using [hjK] : j = K + 1 ∨ j ≤ K) with rfl | hjK'
  · rw [readW128, Offset.add_add, Mem.readW_writeW_self64, Mem.readW_writeW_sep hsep8 (by decide),
      Mem.readW_writeW_self64, enc_eq, hz]
  · have hj8 : j ≤ 8 := by omega_using [hK8, hjK]
    obtain hlj := pwOff_le j hj hj8
    obtain hs := pwOff_sep j (K + 1) hj hj8 (by omega_using []) hK8 (by omega_using [hjK'])
    rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hs]) (by omega_using [hlj]) (by omega_using [hle])) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hs]) (by omega_using [hlj]) (by omega_using [hle])) (by decide),
      hst j hj hjK']

theorem hpow_succ (H : Block) (k : Nat) : hpow H (k + 1) = Spec.Gcm.mul (hpow H k) H := rfl

theorem hpow_one (H : Block) : hpow H 1 = H :=
  Poly.φ_inj (by rw [Poly.φ_hpow, pow_one])

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [ctxR s₀]
  wr : s₀.wr = [pwR s₀, scrR s₀]
  c_pw : (ctxR s₀).Disjoint (pwR s₀)
  c_scr : (ctxR s₀).Disjoint (scrR s₀)
  pw_scr : (pwR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : keyPowersAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_h {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 240 + BitVec.ofNat 64 d) 8 := by
  rw [Offset.add_add]
  exact ⟨ctxR s₀, by simp [h.rd], contains_offset (by omega_using [hd]) (by omega_using [hd])⟩

theorem in_pw {d : Nat} (hd : d + 8 ≤ 128) : InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 d) 8 :=
  ⟨pwR s₀, by simp [h.wr], contains_offset hd (by omega_using [hd])⟩

theorem in_scr {d : Nat} (hd : d + 8 ≤ 80) : InRegions s₀.wr (s₀.gpr .x2 + BitVec.ofNat 64 d) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega_using [hd])⟩

end Pre

/-- The memory after the registers are saved. -/
abbrev mS (s₀ : State) : Mem := Spill.saveMem s₀.mem (s₀.gpr .x2) s₀.gpr saved

theorem mS_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (mS s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem read0 {s₀ : State} (hp : Pre s₀) :
    rev64 ((mS s₀).readW (s₀.gpr .x0 + BitVec.ofNat 64 240) 64) = hw0 s₀ :=
  congrArg rev64 ((mS_frame s₀).readW (r := ctxR s₀) (contains_offset (by decide) (by decide))
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.c_scr) (by decide))

theorem read1 {s₀ : State} (hp : Pre s₀) :
    rev64 ((mS s₀).readW (s₀.gpr .x0 + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 64) = hw1 s₀ :=
  congrArg rev64 ((mS_frame s₀).readW (r := ctxR s₀)
    (by rw [Offset.add_add]; exact contains_offset (by decide) (by decide))
    (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.c_scr) (by decide))

/-- The two writes of a power keep what is outside the powers' buffer. -/
theorem enc_frame {s₀ : State} (m : Mem) {off : Nat} (hle : off + 16 ≤ 128) (lo hi : BitVec 64) :
    Frame [pwR s₀] m ((m.writeW (s₀.gpr .x1 + BitVec.ofNat 64 off) lo).writeW
      (s₀.gpr .x1 + BitVec.ofNat 64 (off + 8)) hi) :=
  ((Frame.refl _ _).writeW List.mem_cons_self _
    (contains_offset (by omega_using [hle]) (by omega_using [hle]))).writeW List.mem_cons_self _
    (contains_offset (by omega_using [hle]) (by omega_using [hle]))

/-- The saved registers are apart from the powers. -/
theorem slots_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem}
    (h : Spill.Saved (s₀.gpr .x2) s₀.gpr saved m) (hf : Frame [pwR s₀] m m') :
    Spill.Saved (s₀.gpr .x2) s₀.gpr saved m' :=
  h.frame_in (lo := 0) (n := 80) (by decide) hf fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    rw [show s₀.gpr .x2 + BitVec.ofNat 64 0 = s₀.gpr .x2 from BitVec.add_zero _]
    exact hp.pw_scr.symm

/-! ## The loop -/

/-- The step of `x1` before power `k` is stored: 48 to an odd power's place, −16 to an even one's. -/
def dOf (k : Nat) : BitVec 64 := if k % 2 = 0 then 48 else 32 - 48

theorem pw_next : ∀ K < 7, BitVec.ofNat 64 (pwOff (K + 1)) + dOf (K + 1) = BitVec.ofNat 64 (pwOff (K + 2)) := by
  decide

theorem d_next : ∀ K < 7, 32 - dOf (K + 1) = dOf (K + 2) := by decide

theorem cnt_ne : ∀ K < 7, (BitVec.ofNat 64 (8 - (K + 1)) != 0) = true := by decide

/-- What holds once `K` powers are stored. -/
structure Common (s₀ : State) (K : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = s₀.gpr .x2
  x30 : s.gpr .x30 = s₀.gpr .x30
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  slots : Spill.Saved (s₀.gpr .x2) s₀.gpr saved s.mem
  stored : Stored s₀ (hw0 s₀ ++ hw1 s₀) K s.mem

/-- The loop invariant, with `K` powers stored and `Z = Hᴷ`. -/
structure LInv (s₀ : State) (K : Nat) (s : State) : Prop extends Common s₀ K s where
  x1 : s.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1))
  d : s.gpr D = dOf (K + 1)
  cnt : s.gpr CNT = BitVec.ofNat 64 (8 - K)
  masks : Masks s
  k0 : s.gpr KW0 = Holes.key0 (hw0 s₀) (hw1 s₀)
  k1 : s.gpr KW1 = Holes.key1 (hw0 s₀) (hw1 s₀)
  z : s.gpr ZH ++ s.gpr ZL = hpow (hw0 s₀ ++ hw1 s₀) K

theorem body_ok {s₀ : State} (hp : Pre s₀) {K : Nat} (hK : K < 8) {s : State}
    (hL : LInv s₀ K s) :
    WP isa (.block keyBody) s fun s' =>
      (eval (.nonzero .x CNT) s' = some false ∧ Common s₀ 8 s') ∨
      (eval (.nonzero .x CNT) s' = some true ∧ K + 1 < 8 ∧ LInv s₀ (K + 1) s') := by
  obtain hle := pwOff_le (K + 1) (by omega_using []) (by omega_using [hK])
  rw [keyBody]
  refine WP.block_append_iff.mpr (WP.mono (keyY_ok s) fun u1 ⟨y0, y1, yx, k1⟩ => ?_)
  obtain m1 : Masks u1 := k1.masks hL.masks fun j _ =>
    (by decide : ∀ r ∈ maskRegs, r ∉ [Y0, Y1, YX]) _ (K_mem j)
  refine WP.block_append_iff.mpr (WP.mono (mulCode_ok u1 m1 yx) fun u2 ⟨z2, q2, k2⟩ => ?_)
  obtain hx1₂ : u2.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1)) := by
    rw [k2.gpr (by decide), k1.gpr (by decide), hL.x1]
  obtain hm₂ : u2.mem = s.mem := k2.2.1.trans k1.2.1
  obtain hwr₂ : u2.wr = s₀.wr := k2.2.2.2.trans (k1.2.2.2.trans hL.wr)
  obtain hz₂ : u2.gpr ZH ++ u2.gpr ZL = hpow (hw0 s₀ ++ hw1 s₀) (K + 1) := by
    rw [z2, y0, y1, k1.gpr (r := KW0) (by decide), k1.gpr (r := KW1) (by decide), hL.k0, hL.k1,
      Holes.mulK_eq, hL.z, hpow_succ]
  refine WP.block_append_iff.mpr (WP.mono (storeEnc_ok u2 (off := 0) (by decide) (by decide)
    (by rw [hwr₂, hx1₂, Offset.add_add]; exact hp.in_pw (by omega_using [hle]))
    (by rw [hwr₂, hx1₂, Offset.add_add]; exact hp.in_pw (by omega_using [hle])))
    fun u3 ⟨hm₃, hk₃, hrd₃, hwr₃⟩ => ?_)
  refine WP.mono (keyNext_ok u3) fun s' ⟨nx1, nd, nc, k4⟩ => ?_
  -- the memory
  obtain hm' : s'.mem = (s.mem.writeW (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1)))
        ((u2.gpr ZL <<< 1) ^^^ (((0 : BitVec 64) - u2.gpr ZH >>> 63) >>> 63))).writeW
      (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1) + 8))
        ((u2.gpr ZH <<< 1 ||| u2.gpr ZL >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - u2.gpr ZH >>> 63))) := by
    rw [k4.2.1, hm₃, hm₂, hx1₂, Offset.add_add, Offset.add_add, Nat.add_zero, Nat.zero_add]
  -- the registers that are neither multiplied nor moved
  obtain keep : ∀ r, r ∉ [.x1, T, D, CNT] → r ∉ [T, B, .x0] → r ∉ mulRegs → r ∉ [Y0, Y1, YX] →
      s'.gpr r = s.gpr r := fun r h4 h3 h2 h1 => by
    rw [k4.gpr h4, hk₃ r h3, k2.gpr h2, k1.gpr h1]
  obtain hcommon : Common s₀ (K + 1) s' := by
    refine ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.x2],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.x30],
      by rw [k4.2.2.1, hrd₃, k2.2.2.1, k1.2.2.1, hL.rd], by rw [k4.2.2.2, hwr₃, hwr₂], ?_, ?_⟩
    · rw [hm']; exact slots_frame hp hL.slots (enc_frame _ hle _ _)
    · rw [hm']; exact stored_step (by omega_using [hK]) hL.stored hz₂
  obtain hc' : s'.gpr .x4 = BitVec.ofNat 64 (8 - (K + 1)) := by
    have := hL.cnt
    simp only [CNT] at nc this
    rw [nc, hk₃ _ (by decide), k2.gpr (by decide), k1.gpr (by decide), this,
      show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hK]), Nat.sub_sub]
  obtain hev : eval (.nonzero .x CNT) s' = some (BitVec.ofNat 64 (8 - (K + 1)) != 0) := by
    simp only [CNT, eval, State.read, Size.bits, BitVec.setWidth_eq, hc']
  by_cases hlast : K + 1 = 8
  · left
    rw [hlast] at hev hcommon
    exact ⟨hev.trans (by decide), hcommon⟩
  · right
    obtain hK7 : K < 7 := by omega_using [hK, hlast]
    refine ⟨hev.trans (congrArg some (cnt_ne K hK7)), by omega_using [hK7],
      { hcommon with x1 := ?_, d := ?_, cnt := ?_, masks := ?_, k0 := ?_, k1 := ?_, z := ?_ }⟩
    · rw [nx1, hk₃ _ (by decide), hx1₂, hk₃ _ (by decide), k2.gpr (by decide), k1.gpr (by decide),
        hL.d, BitVec.add_assoc, pw_next K hK7]
    · rw [nd, hk₃ _ (by decide), k2.gpr (by decide), k1.gpr (by decide), hL.d, d_next K hK7]
    · simp only [CNT]; exact hc'
    · intro j hj
      have := (by decide : ∀ r ∈ maskRegs,
        r ∉ [.x1, T, D, CNT] ∧ r ∉ [T, B, .x0] ∧ r ∉ mulRegs ∧ r ∉ [Y0, Y1, YX]) _ (K_mem j)
      rw [keep _ this.1 this.2.1 this.2.2.1 this.2.2.2]; exact hL.masks j hj
    · rw [k4.gpr (by decide), hk₃ _ (by decide), q2, k1.gpr (by decide), hL.k0]
    · rw [keep _ (by decide) (by decide) (by decide) (by decide), hL.k1]
    · rw [k4.gpr (r := ZH) (by decide), k4.gpr (r := ZL) (by decide), hk₃ ZH (by decide),
        hk₃ ZL (by decide), hz₂]

/-! ## The whole function -/

theorem keyPowers_wp {s₀ : State} (hp : Pre s₀) :
    WP isa keyPowers s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ keyPowersAArch64.post s₀ s' := by
  refine WP.seq ?_
  rw [show keySave = Spill.saveCode .x2 saved from rfl]
  refine Spill.save_ok (by decide) (fun p hp' => hp.in_scr
    (by have := (by decide : ∀ p ∈ saved, p.2 + 8 ≤ 80) p hp'; omega_using [this])) ?_
  refine WP.block_append_iff.mpr (WP.mono (keyAddr_ok _) fun u1 ⟨a1, k1⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (setup_ok u1 fun d hd => by
    rw [k1.2.2.1, k1.2.2.2, a1]; exact hp.in_h hd) fun u2 ⟨e0, e1, mk, k2⟩ => ?_)
  obtain hx0₂ : u2.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 240 := by rw [k2.gpr (by decide), a1]
  obtain hm₂ : u2.mem = mS s₀ := k2.2.1.trans k1.2.1
  refine WP.block_append_iff.mpr (WP.mono (keyLoad_ok u2 fun d hd => by
    rw [k2.2.2.1, k2.2.2.2, k1.2.2.1, k1.2.2.2, hx0₂]; exact hp.in_h hd) fun u3 ⟨z0, z1, k3⟩ => ?_)
  obtain hx1₃ : u3.gpr .x1 = s₀.gpr .x1 := by
    rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]
  obtain hwr₃ : u3.wr = s₀.wr := k3.2.2.2.trans (k2.2.2.2.trans k1.2.2.2)
  obtain hz₃ : u3.gpr ZH ++ u3.gpr ZL = hpow (hw0 s₀ ++ hw1 s₀) (0 + 1) := by
    rw [z0, z1, hm₂, hx0₂, read0 hp, read1 hp, hpow_one]
  refine WP.block_append_iff.mpr (WP.mono (storeEnc_ok u3 (off := 16) (by decide) (by decide)
    (by rw [hwr₃, hx1₃]; exact hp.in_pw (by decide))
    (by rw [hwr₃, hx1₃]; exact hp.in_pw (by decide))) fun u4 ⟨hm₄, hk₄, hrd₄, hwr₄⟩ => ?_)
  refine WP.mono (keyCount_ok u4) fun s₁ ⟨c1, d1, k5⟩ => ?_
  obtain keep : ∀ r, r ∉ [CNT, D] → r ∉ [T, B, .x0] → r ∉ [ZH, ZL] → r ∉ setupRegs → r ≠ .x0 →
      s₁.gpr r = s₀.gpr r := fun r h5 h4 h3 h2 h1 => by
    rw [k5.gpr h5, hk₄ r h4, k3.gpr h3, k2.gpr h2, k1.gpr (by simpa using h1)]
  obtain hm₁ : s₁.mem = ((mS s₀).writeW (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (0 + 1)))
        ((u3.gpr ZL <<< 1) ^^^ (((0 : BitVec 64) - u3.gpr ZH >>> 63) >>> 63))).writeW
      (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (0 + 1) + 8))
        ((u3.gpr ZH <<< 1 ||| u3.gpr ZL >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - u3.gpr ZH >>> 63))) := by
    rw [k5.2.1, hm₄, k3.2.1, hm₂, hx1₃]; rfl
  obtain hL₀ : LInv s₀ 1 s₁ := by
    refine ⟨⟨keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [k5.2.2.1, hrd₄, k3.2.2.1, k2.2.2.1, k1.2.2.1], by rw [k5.2.2.2, hwr₄, hwr₃], ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm₁]
      exact slots_frame hp (Spill.saveMem_saved (by decide) _ _ _) (enc_frame _ (by decide) _ _)
    · rw [hm₁]
      exact stored_step (K := 0) (by decide) (fun _ h1 h0 => absurd h0 (by omega_using [h1])) hz₃
    · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (BitVec.add_zero _).symm
    · rw [d1]; rfl
    · rw [c1]; rfl
    · intro j hj
      have := (by decide : ∀ r ∈ maskRegs, r ∉ [CNT, D] ∧ r ∉ [T, B, .x0] ∧ r ∉ [ZH, ZL]) _ (K_mem j)
      rw [k5.gpr this.1, hk₄ _ this.2.1, k3.gpr this.2.2]; exact mk j hj
    · rw [k5.gpr (by decide), hk₄ _ (by decide), k3.gpr (by decide), e0, k1.2.1, a1, read0 hp,
        read1 hp]
    · rw [k5.gpr (by decide), hk₄ _ (by decide), k3.gpr (by decide), e1, k1.2.1, a1, read0 hp,
        read1 hp]
    · rw [k5.gpr (r := ZH) (by decide), k5.gpr (r := ZL) (by decide), hk₄ ZH (by decide),
        hk₄ ZL (by decide), hz₃]
  -- the powers
  let Inv : Nat → State → Prop := fun m s => ∃ K, m = 8 - K ∧ K < 8 ∧ LInv s₀ K s
  obtain hstep : ∀ m s, Inv m s → WP isa (.block keyBody) s (fun s' =>
      (eval (.nonzero .x CNT) s' = some false ∧ Common s₀ 8 s') ∨
      (eval (.nonzero .x CNT) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨K, rfl, hK, hL⟩
    refine WP.mono (body_ok hp hK hL) fun s' h => ?_
    rcases h with ⟨he, hc⟩ | ⟨he, hK', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, 8 - (K + 1), by omega_using [hK], K + 1, rfl, hK', hL'⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) Inv hstep 7 s₁ ⟨1, rfl, by decide, hL₀⟩)
    fun s₂ hc => ?_)
  -- the registers restored
  rw [show keyRestore = Spill.restoreCode .x2 saved from rfl]
  refine WP.mono (Spill.restore_wp hc.x2 (by decide) (by decide) (fun p hp' => ?_) hc.slots)
    fun s' hR => ⟨fun r hr => ?_, ?_⟩
  · rw [hc.rd, hc.wr]
    exact ⟨scrR s₀, by simp [hp.rd, hp.wr], contains_offset
      (by have := (by decide : ∀ p ∈ saved, p.2 + 8 ≤ 80) p hp'; omega_using [this])
      (by have := (by decide : ∀ p ∈ saved, p.2 + 8 ≤ 80) p hp'; omega_using [this])⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hR.gpr_of (.inl (by decide))
      | exact hR.gpr_of (.inr hc.x30)
  · show Spec.Gcm.Powers8Repr s'.mem (s₀.gpr .x1) (Spec.Gcm.ctxH s₀.mem (s₀.gpr .x0))
    rw [hR.mem, ctxH_eq]
    intro j hj
    refine ⟨?_, ?_⟩
    · have := hc.stored (2 * j + 2) (by omega_using []) (by omega_using [hj])
      rw [show pwOff (2 * j + 2) = 32 * j by
        simp only [pwOff, show (2 * j + 2) % 2 = 0 by omega_using [], ↓reduceIte]; omega_using []] at this
      exact this
    · have := hc.stored (2 * j + 1) (by omega_using []) (by omega_using [hj])
      rw [show pwOff (2 * j + 1) = 16 + 32 * j by
        simp only [pwOff, show (2 * j + 1) % 2 = 1 by omega_using [], Nat.one_ne_zero, ↓reduceIte]; omega_using []] at this
      exact this

theorem keyPowers_correct (s : State) (hs : keyPowersAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.keyPowers s t s' ∧ abiPreserved s s' ∧
      keyPowersAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := keyPowers_wp (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem keyPowers_ct : ConstantTime isa keyPowersAArch64.pre keyPowersAArch64.pub
    Impl.Gcm.AArch64.keyPowers := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying `keyPowersAArch64`'s precondition, with zero memory. -/
def satStateK : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 80⟩]

/-- `vg_aes_gcm_store_powers_scratch`: `Spec.Gcm.storePowersContract` with
the working space, 10 doublewords, as a last argument. -/
theorem keyPowers_verified :
    Verified AArch64.target Impl.Gcm.AArch64.keyPowers
      (Sig.scratchContract AArch64.abi Spec.Gcm.storePowersSig "scratch" .u64 10
        (Curry.const (fun _ => True) _) (Spec.Gcm.storePowersPost AArch64.abi.ptrBits) false 0) :=
  Verified.of_correct keyPowers_correct keyPowers_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Gcm.storePowersSig,
      Spec.Gcm.storePowersParam, Spec.Gcm.storePowersPost, keyPowersAArch64, AArch64.abi,
      AArch64.argRegs] [satStateK] using satStateK)

/-- A state satisfying `vg_aes_gcm_store_powers`'s precondition. -/
def framedSat : State := { satStateK with wr := [⟨0x2000, 128⟩] }

theorem framedSat_pre : ∃ s, (Spec.Gcm.storePowersContract AArch64.abi 80).pre s := by
  implies_sat [Spec.Gcm.storePowersContract, Spec.Gcm.storePowersSig, Spec.Gcm.storePowersParam,
    Spec.Gcm.storePowersPost, AArch64.abi, AArch64.argRegs] [framedSat, satStateK] using framedSat

/-- `vg_aes_gcm_store_powers`: the code above with its working space in a
frame of 80 bytes, which holds only the registers it saves. -/
theorem keyPowers_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 80 .x2 Impl.Gcm.AArch64.keyPowers)
      (Spec.Gcm.storePowersContract AArch64.abi 80) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.storePowersSig) (nm := "scratch") (e := .u64)
    (n := 10) (pre := Curry.const (fun _ => True) _)
    (post := Spec.Gcm.storePowersPost AArch64.abi.ptrBits) (wa := false) (stack := 0) (bytes := 80)
    keyPowers_verified (by decide) (by decide) framedSat_pre

end VG.Proof.Gcm.AArch64.KeyPowers
