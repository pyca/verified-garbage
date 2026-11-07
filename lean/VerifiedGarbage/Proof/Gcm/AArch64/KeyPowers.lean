module

public import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.Poly
meta import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
(`vg_aes_gcm_store_powers`) against `Spec.Gcm.storePowersContract`: it
loads `H` from byte 240 of the key context into `x2:x3` and `Z`
(`keyLoad_ok`), then, for `k` from 1 to 8, stores `preparedPower(Hᵏ)` from
`Z` (`storeEnc_ok`, by `enc_eq`) and, below 8, multiplies `Z` by `H` with
the 128 steps of `vg_ghash` (`round_ok`, by `mul_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.KeyPowers

open VG VG.AArch64 VG.Impl.Gcm.AArch64 VG.Proof.Gcm VG.Proof.Gcm.AArch64
open VG.Spec.Gcm (Block blockAt hpow preparedPower)

/-! ## The encoding -/

/-- The high doubleword of `0xc2 ‖ 0¹¹⁸ ‖ 1`. -/
def cHigh : BitVec 64 := 0xc200000000000000

/-- `storeEnc`'s two doublewords, the high then the low, from `Z = zh ++ zl`. -/
theorem enc_eq (zh zl : BitVec 64) :
    ((zh <<< 1 ||| zl >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - zh >>> 63))) ++
      ((zl <<< 1) ^^^ (((0 : BitVec 64) - zh >>> 63) >>> 63)) = preparedPower (zh ++ zl) := by
  rw [neg_msb, preparedPower, ← shl1]
  have hm : (zh ++ zl).getMsbD 0 = zh.msb := by
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
  have h := Proof.Mont.read_toNat_add m 8 8 a
  have e1 : (m.readW a 128).toNat = (m.read a (8 + 8)).toNat := by
    simp only [Mem.readW, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (m.read a (8 + 8)).isLt
  have e2 : ∀ b, (m.readW b 64).toNat = (m.read b 8).toNat := fun b => by
    simp only [Mem.readW, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (m.read b 8).isLt
  rw [e1, BitVec.toNat_append, e2, e2, h, ← Nat.shiftLeft_add_eq_or_of_lt (m.read a 8).isLt,
    Nat.shiftLeft_eq]
  omega

/-! ## The contract -/

/-- `vg_aes_gcm_store_powers(ctx = x0, pw = x1)` on AArch64: the 256-byte
key context readable, the 128-byte powers' buffer writable and apart from
it; the powers of `ctxH` at `pw`. -/
def keyPowersAArch64 : Contract AArch64.isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .x0, 256⟩
    let pw : Region := ⟨s.gpr .x1, 128⟩
    s.rd = [ctx] ∧ s.wr = [pw] ∧ ctx.Disjoint pw
  post s s' := Spec.Gcm.Powers8Repr s'.mem (s.gpr .x1) (Spec.Gcm.ctxH s.mem (s.gpr .x0))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-! ## The state between rounds -/

/-- What holds from `keyLoad` on, with `H` the hash subkey. -/
structure St (s₀ : State) (H : Block) (s : State) : Prop where
  x1 : s.gpr .x1 = s₀.gpr .x1
  h : s.gpr .x2 ++ s.gpr .x3 = H
  rh : s.gpr RH = rHigh
  zero : s.gpr ZERO = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The powers `preparedPower(Hʲ)`, `1 ≤ j ≤ K`, stored at `pw`. -/
def Stored (s₀ : State) (H : Block) (K : Nat) (m : Mem) : Prop :=
  ∀ j, 1 ≤ j → j ≤ K →
    m.readW (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff j)) 128 = preparedPower (hpow H j)

theorem pwOff_le (k : Nat) (h1 : 1 ≤ k) (h8 : k ≤ 8) : pwOff k + 16 ≤ 128 := by
  simp only [pwOff]; split <;> omega

theorem pwOff_mod (k : Nat) : pwOff k % 8 = 0 := by
  simp only [pwOff]; split <;> omega

/-- Distinct powers are 16 bytes apart. -/
theorem pwOff_sep (j k : Nat) (hj : 1 ≤ j) (hj8 : j ≤ 8) (hk : 1 ≤ k) (hk8 : k ≤ 8) (hjk : j ≠ k) :
    pwOff j + 16 ≤ pwOff k ∨ pwOff k + 16 ≤ pwOff j := by
  simp only [pwOff]; split <;> split <;> omega

/-! ## Loading `H` -/

theorem ctxH_eq (m : Mem) (p : Addr) :
    Spec.Gcm.ctxH m p = rev64 (m.readW (p + BitVec.ofNat 64 240) 64) ++
      rev64 (m.readW (p + BitVec.ofNat 64 248) 64) := by
  rw [Spec.Gcm.ctxH, ← blockAt_rev]
  congr 3
  · exact BitVec.add_zero _
  · exact Offset.add_add p 240 8

theorem keyLoad_ok {s₀ : State} (hp : keyPowersAArch64.pre s₀) :
    WP isa (.block keyLoad) s₀ fun s =>
      St s₀ (Spec.Gcm.ctxH s₀.mem (s₀.gpr .x0)) s ∧
        s.gpr ZH ++ s.gpr ZL = Spec.Gcm.ctxH s₀.mem (s₀.gpr .x0) := by
  obtain ⟨hrd, -, -⟩ := hp
  have c0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 240) 8 :=
    ⟨⟨s₀.gpr .x0, 256⟩, by simp [hrd], contains_offset (by decide) (by decide)⟩
  have c8 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 248) 8 :=
    ⟨⟨s₀.gpr .x0, 256⟩, by simp [hrd], contains_offset (by decide) (by decide)⟩
  have a240 : 240 % 8 = 0 ∧ 240 < 4096 * 8 := by decide
  have a248 : 248 % 8 = 0 ∧ 248 < 4096 * 8 := by decide
  apply WP.of_runBlock
  simp only [keyLoad, ZH, ZL, RH, ZERO]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, Nat.reduceLT, Nat.reduceAdd, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, a240, a248, and_self, State.load, Size.bytes, c0, c8, State.read,
    State.write,
    BitVec.setWidth_eq, Size.bits, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  have z0 : BitVec.setWidth 64 (0 : BitVec 16) <<< 0 = 0 := by decide
  have rh0 : BitVec.setWidth 64 (57600 : BitVec 16) <<< 48 = rHigh := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp only [reduceCtorEq, ↓reduceIte]
  · simp only [reduceCtorEq, ↓reduceIte]
    rw [ctxH_eq, read_8, read_8]
  · simp only [reduceCtorEq, ↓reduceIte, RH]; exact rh0
  · simp only [reduceCtorEq, ↓reduceIte, ZERO]; exact z0
  · have oz : ∀ x : BitVec 64, (x ||| 0) = x := fun x => by simp
    rw [z0, oz, oz, ctxH_eq, read_8, read_8]

/-! ## Storing a power -/

/-- `pw + d` is in the powers' buffer for 8 bytes. -/
theorem out_pw {s₀ : State} (hp : keyPowersAArch64.pre s₀) {d : Nat} (hd : d + 8 ≤ 128) :
    InRegions s₀.wr (s₀.gpr .x1 + BitVec.ofNat 64 d) 8 :=
  ⟨⟨s₀.gpr .x1, 128⟩, by simp [hp.2.1], contains_offset hd (by omega)⟩

/-- `preparedPower(Z)` stored at `pw + off`, from `Z = zh ++ zl`, as two
writes. -/
theorem storeEnc_run {s₀ : State} (hp : keyPowersAArch64.pre s₀) {H : Block} {s : State}
    (hS : St s₀ H s) {off : Nat} (ho : off % 8 = 0) (hle : off + 16 ≤ 128) :
    WP isa (.block (storeEnc off)) s fun s' =>
      St s₀ H s' ∧ s'.gpr ZH = s.gpr ZH ∧ s'.gpr ZL = s.gpr ZL ∧
      s'.mem = (s.mem.writeW (s₀.gpr .x1 + BitVec.ofNat 64 off)
          ((s.gpr ZL <<< 1) ^^^ (((0 : BitVec 64) - s.gpr ZH >>> 63) >>> 63))).writeW
        (s₀.gpr .x1 + BitVec.ofNat 64 (off + 8))
          ((s.gpr ZH <<< 1 ||| s.gpr ZL >>> 63) ^^^ (cHigh &&& ((0 : BitVec 64) - s.gpr ZH >>> 63))) := by
  have o0 : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 off) 8 := by
    rw [hS.wr, hS.x1]; exact out_pw hp (by omega)
  have o8 : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (off + 8)) 8 := by
    rw [hS.wr, hS.x1]; exact out_pw hp (by omega)
  have a0 : off % 8 = 0 ∧ off < 4096 * 8 := ⟨ho, by omega⟩
  have a8 : (off + 8) % 8 = 0 ∧ off + 8 < 4096 * 8 := ⟨by omega, by omega⟩
  have hz := hS.zero
  simp only [ZERO] at hz
  apply WP.of_runBlock
  simp only [storeEnc, ZH, ZL, VH, VL, M, T, ZERO]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, Nat.reduceLT, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, a0, a8, and_self, State.store, Size.bytes, o0, o8, hz,
    State.read, State.write, BitVec.setWidth_eq, Size.bits, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have cH : BitVec.setWidth 64 (49664 : BitVec 16) <<< (16 * 3) = cHigh := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, hS.rd, hS.wr⟩, trivial, trivial, ?_⟩
  · simp only [reduceCtorEq, ↓reduceIte]; exact hS.x1
  · simp only [reduceCtorEq, ↓reduceIte]; exact hS.h
  · simp only [reduceCtorEq, ↓reduceIte, RH]; exact hS.rh
  · simp only [reduceCtorEq, ↓reduceIte, ZERO]; exact hz
  · rw [cH, hS.x1, write_8, write_8]

/-- `preparedPower(Hᴷ⁺¹)` stored, from `Z = Hᴷ⁺¹`, after the powers below it. -/
theorem storeEnc_ok {s₀ : State} (hp : keyPowersAArch64.pre s₀) {H : Block} {K : Nat}
    (hK8 : K + 1 ≤ 8) {s : State} (hS : St s₀ H s) (hz : s.gpr ZH ++ s.gpr ZL = hpow H (K + 1))
    (hst : Stored s₀ H K s.mem) :
    WP isa (.block (storeEnc (pwOff (K + 1)))) s fun s' =>
      St s₀ H s' ∧ s'.gpr ZH ++ s'.gpr ZL = hpow H (K + 1) ∧ Stored s₀ H (K + 1) s'.mem := by
  have hle := pwOff_le (K + 1) (by omega) hK8
  refine WP.mono (storeEnc_run hp hS (pwOff_mod _) hle) fun s' ⟨h₁, z₁, z₂, hm⟩ =>
    ⟨h₁, by rw [z₁, z₂, hz], fun j hj hjK => ?_⟩
  have hsep8 : Mem.Sep (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1))) (64 / 8)
      (s₀.gpr .x1 + BitVec.ofNat 64 (pwOff (K + 1) + 8)) (64 / 8) :=
    Offset.sep _ (by omega) (by omega) (by omega)
  rw [hm]
  rcases (by omega : j = K + 1 ∨ j ≤ K) with rfl | hjK'
  · rw [readW128, Offset.add_add, Mem.readW_writeW_self64, Mem.readW_writeW_sep hsep8 (by decide),
      Mem.readW_writeW_self64, enc_eq, hz]
  · have hj8 : j ≤ 8 := by omega
    have hlj := pwOff_le j hj hj8
    have hs := pwOff_sep j (K + 1) hj hj8 (by omega) hK8 (by omega)
    rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      hst j hj hjK']

/-! ## Multiplying by `H` -/

theorem nextMul_ok {s₀ : State} {H : Block} {s : State} (hS : St s₀ H s) :
    WP isa (.block nextMul) s fun s₁ =>
      Inner (s.gpr ZH ++ s.gpr ZL) H s 0 s₁ ∧ s₁.gpr CNT = BitVec.ofNat 64 (128 / unroll) := by
  have hz := hS.zero
  have hh := hS.h
  have hr := hS.rh
  simp only [ZERO, RH] at hz hr
  apply WP.of_runBlock
  simp only [nextMul, XH, XL, ZH, ZL, VH, VL, CNT, ZERO]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMul, Nat.reduceLT, Nat.reduceAdd, runBlock_cons, runStep_some,
    runBlock_nil, exec, hz, State.read, State.write, BitVec.setWidth_eq, Size.bits, 
    Option.some.injEq, exists_eq_left']
  have oz : ∀ x : BitVec 64, (x ||| 0) = x := fun x => by simp
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr' => ?_, rfl, rfl, rfl⟩, by decide⟩
  · simp only [reduceCtorEq, ↓reduceIte, XH, XL]
    rw [oz, oz, BitVec.shiftLeft_zero]
  · simp only [reduceCtorEq, ↓reduceIte, ZH, ZL, VH, VL]
    rw [oz, oz, hh, mulSteps_zero]
    rfl
  · simp only [reduceCtorEq, ↓reduceIte, RH]; exact hr
  · simp only [reduceCtorEq, ↓reduceIte, ZERO]; exact hz
  · simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ↓reduceIte]

theorem hpow_succ (H : Block) (k : Nat) : hpow H (k + 1) = Spec.Gcm.mul (hpow H k) H := rfl

/-- A round: `preparedPower(Hᴷ⁺¹)` stored, then `Z = Hᴷ⁺²`. -/
theorem round_ok {s₀ : State} (hp : keyPowersAArch64.pre s₀) {H : Block} {K : Nat}
    (hK8 : K + 1 ≤ 8) {s : State} (hS : St s₀ H s) (hz : s.gpr ZH ++ s.gpr ZL = hpow H (K + 1))
    (hst : Stored s₀ H K s.mem) :
    WP isa (keyRound (K + 1)) s fun s' =>
      St s₀ H s' ∧ s'.gpr ZH ++ s'.gpr ZL = hpow H (K + 2) ∧ Stored s₀ H (K + 1) s'.mem := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeEnc_ok hp hK8 hS hz hst) fun s₁ ⟨h₁, z₁, st₁⟩ => ?_
  refine WP.mono (nextMul_ok h₁) fun s₂ ⟨i₂, c₂⟩ => ?_
  refine WP.mono (mul_ok i₂ c₂) fun s' i' => ?_
  have k1 := i'.keep .x1 (by decide)
  have k2 := i'.keep .x2 (by decide)
  have k3 := i'.keep .x3 (by decide)
  refine ⟨⟨k1.trans h₁.x1, by rw [k2, k3]; exact h₁.h, i'.rh, i'.zero, i'.rd.trans h₁.rd,
    i'.wr.trans h₁.wr⟩, ?_, by rw [i'.mem]; exact st₁⟩
  have hz' := congrArg Prod.fst i'.zv
  simp only at hz'
  rw [hz', ← mul_eq, z₁, ← hpow_succ]

/-! ## The whole function -/

theorem hpow_one (H : Block) : hpow H 1 = H :=
  Poly.φ_inj (by rw [Poly.φ_hpow, pow_one])

/-- Round `K + 1` composed after the rounds before it. -/
theorem round_then {s₀ : State} (hp : keyPowersAArch64.pre s₀) {H : Block} {K : Nat}
    (hK8 : K + 1 ≤ 8) {rest : Prog isa} {Q : State → Prop} {s : State} (hS : St s₀ H s)
    (hz : s.gpr ZH ++ s.gpr ZL = hpow H (K + 1)) (hst : Stored s₀ H K s.mem)
    (hr : ∀ s', St s₀ H s' → s'.gpr ZH ++ s'.gpr ZL = hpow H (K + 2) →
      Stored s₀ H (K + 1) s'.mem → WP isa rest s' Q) :
    WP isa (.seq (keyRound (K + 1)) rest) s Q :=
  WP.seq (WP.mono (round_ok hp hK8 hS hz hst) fun s' ⟨a, b, c⟩ => hr s' a b c)

theorem keyPowers_post {s₀ : State} (hp : keyPowersAArch64.pre s₀) :
    WP isa keyPowers s₀ (keyPowersAArch64.post s₀) := by
  refine WP.seq (WP.mono (keyLoad_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  have st₀ : Stored s₀ (Spec.Gcm.ctxH s₀.mem (s₀.gpr .x0)) 0 s₁.mem :=
    fun _ h1 h0 => absurd h0 (by omega)
  rw [← hpow_one (Spec.Gcm.ctxH s₀.mem (s₀.gpr .x0))] at z₁
  refine round_then (K := 0) hp (by decide) h₁ z₁ st₀ fun s₂ h₂ z₂ st₂ => ?_
  refine round_then (K := 1) hp (by decide) h₂ z₂ st₂ fun s₃ h₃ z₃ st₃ => ?_
  refine round_then (K := 2) hp (by decide) h₃ z₃ st₃ fun s₄ h₄ z₄ st₄ => ?_
  refine round_then (K := 3) hp (by decide) h₄ z₄ st₄ fun s₅ h₅ z₅ st₅ => ?_
  refine round_then (K := 4) hp (by decide) h₅ z₅ st₅ fun s₆ h₆ z₆ st₆ => ?_
  refine round_then (K := 5) hp (by decide) h₆ z₆ st₆ fun s₇ h₇ z₇ st₇ => ?_
  refine WP.seq (WP.mono (round_ok (K := 6) hp (by decide) h₇ z₇ st₇) fun s₈ ⟨h₈, z₈, st₈⟩ => ?_)
  refine WP.mono (storeEnc_ok (K := 7) hp (by decide) h₈ z₈ st₈) fun s' ⟨_, _, st'⟩ => ?_
  intro j hj
  refine ⟨?_, ?_⟩
  · have := st' (2 * j + 2) (by omega) (by omega)
    rw [show pwOff (2 * j + 2) = 32 * j by
      simp only [pwOff, show (2 * j + 2) % 2 = 0 by omega, ↓reduceIte]; omega] at this
    exact this
  · have := st' (2 * j + 1) (by omega) (by omega)
    rw [show pwOff (2 * j + 1) = 16 + 32 * j by
      simp only [pwOff, show (2 * j + 1) % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte]; omega] at this
    exact this

theorem keyPowers_correct (s : State) (hs : keyPowersAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.keyPowers s t s' ∧ abiPreserved s s' ∧
      keyPowersAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := WP.gprs (rs := preserved) (keyPowers_post hs) (by decide) (by decide)
  exact ⟨t, s', he, ⟨h₂, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₁⟩

theorem keyPowers_ct : ConstantTime isa keyPowersAArch64.pre keyPowersAArch64.pub
    Impl.Gcm.AArch64.keyPowers := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h2

/-- A state satisfying `keyPowersAArch64`'s precondition, with zero memory. -/
def satStateK : State :=
  { Proof.Gcm.AArch64.satState with
    gpr := fun r => if r = .x0 then 0x1000 else if r = .x1 then 0x2000 else 0
    rd := [⟨0x1000, 256⟩]
    wr := [⟨0x2000, 128⟩] }

theorem keyPowers_verified :
    Verified AArch64.target Impl.Gcm.AArch64.keyPowers (Spec.Gcm.storePowersContract AArch64.abi) :=
  Verified.of_correct keyPowers_correct keyPowers_ct (by
    sig_implies [Spec.Gcm.storePowersContract, Spec.Gcm.storePowersSig, Spec.Gcm.storePowersParam,
      Spec.Gcm.storePowersPost, keyPowersAArch64, AArch64.abi, AArch64.argRegs]
      [satStateK, Proof.Gcm.AArch64.satState] using satStateK)

end VG.Proof.Gcm.AArch64.KeyPowers
