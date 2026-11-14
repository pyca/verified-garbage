module

public import VerifiedGarbage.Impl.AesCcm.Arm
public import VerifiedGarbage.Proof.AesCcm.Arm.Env
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.AesCcm.Arm.Words
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesCcm.Arm.Ctrs
import VerifiedGarbage.Proof.AesCcm.Arm.Compare
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.AesCcm.BytesAt
import Lean.Environment
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.AesGcm.Arm.Args
import VerifiedGarbage.Proof.AesCcm.Arm.CtrAt
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesGcm.Arm.Callee
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCcm.Arm.Callee
public import VerifiedGarbage.Proof.AesGcm.Arm.Blocks
public import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.Arm.Env

/-! ### `AesCcm.Arm.Header`, which only this module used -/

section

/-!
# AES-CCM on ARMv7: the encoding of the length of the associated data

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `0 < a < 2³²` (A.2.2) at its start:
`[a]₁₆` or `0xff ‖ 0xfe ‖ [a]₃₂`, from the byte-reversed `a` shifted
(`header_ok`); its length is in `r6`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Impl.AesGcm.Arm (imm addI zero16)
open VG.Proof.AesGcm.Arm (bytesAt_frame runBlock_app_of toNat32 eval_eq' Keeps z_subFlags gpr_subFlags
  c_subFlags adc_c gpr_store mem_store)
open VG.Proof.AesCcm (hdrLen bytesAt_writeW32_at bytesAt_writeW32_base be_split length_be)

theorem encodeLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : Spec.Ccm.encodeLen a = Spec.Ccm.be 2 a := by
  simp [Spec.Ccm.encodeLen, h]

theorem encodeLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xfe] ++ Spec.Ccm.be 4 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem le4_feff : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe, 0, 0] := by decide

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- `B` zeroed, then the encoding of the length `a` of the associated data
(`r5`) at its start, and its length in `r6`. -/
theorem header_ok {s : State} (he : Env k w sp R q1 s) {a : Nat} (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa header s fun s' => Env k w sp R q1 s' ∧ s'.gpr .r6 = BitVec.ofNat 32 (hdrLen a) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      (s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) ∧ Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 32) 16 =
        Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := zero16_ok L he (d := bO) (by decide) (by decide)
  simp only [bO] at hm₁
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 a := by rw [g₁ _ (by decide), h5]
  obtain ⟨s₂, run₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s₁ = some s₂ ∧
      s₂.z = !decide (65280 ≤ a) ∧ (∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [z_subFlags, c_subFlags, gpr_setReg, gpr_subFlags, z_setReg, c_setReg, ite_true, ite_false,
        reduceCtorEq, h5₁, toNat32 ha, imm, show (BitVec.ofNat 32 65280).toNat = 65280 from rfl]
      cases decide (65280 ≤ a) <;> rfl
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have hz : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
    rw [k₂.mem, hm₁]; exact store4_zero_bytes' _ _
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [k₂.mem, hm₁]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)])
    (k₂.sp.trans sp₁) (k₂.rd.trans rd₁) (k₂.wr.trans wr₁)
  have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 a := by rw [g₂ _ (by decide) (by decide), h5₁]
  have h11 := he₂.r11
  have e32 := L.wA (d := 32) (by decide)
  have e36 := L.wA (d := 36) (by decide)
  have w₀ := he₂.perm.wW (show 32 + 4 ≤ 2560 by decide)
  have w₁ := he₂.perm.wW (show 36 + 4 ≤ 2560 by decide)
  have cB : ∀ d n, 32 ≤ d → d + n ≤ 48 →
      (⟨State.addr w + BitVec.ofNat 64 32, 16⟩ : Region).Contains (State.addr w + BitVec.ofNat 64 d) n :=
    fun d n h₁ h₂ => Offset.contains _ h₁ (by omega) (by decide)
  have kg : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r a b c d e => by
    rw [g₂ r a e, g₁ r a]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show zero16 bO ++ [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0), .mov .r12 (imm 0),
      .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] = zero16 bO ++ ([.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] : List Instr) from rfl]
    exact runBlock_app_of run₁ run₂, ?_⟩)
  have hrev := le4_rev_ofNat ha
  refine WP.ite (!decide (65280 ≤ a)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ : a < 2 ^ 16 - 2 ^ 8 := by simp at ht; omega
    refine WP.of_runBlock ⟨_, by simp only [bO]; arun [h11, e32, w₀], ?_⟩
    refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_,
      ⟨k₂.rd.trans rd₁, k₂.wr.trans wr₁, k₂.sp.trans sp₁⟩, ?_, ?_⟩
    · simp [gpr_setReg, hdrLen, h₁]
    · intro r a b c d e; simp only [gpr_store, gpr_setReg, a, d, ite_false]; exact kg r a b c d e
    · simp only [mem_store, mem_setReg]
      exact fz.writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))
    · simp only [mem_store, gpr_store, mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂]
      rw [bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz, le4_shr16, hrev,
        be_split (q := 2) (by decide) (by omega), encodeLen_lo h₁, show hdrLen a = 2 by simp [hdrLen, h₁]]
      simp [Spec.Ccm.zeros, List.drop_append_of_le_length, length_be]
  · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
    have h₁ : ¬ a < 2 ^ 16 - 2 ^ 8 := by simp at hf; omega
    refine WP.of_runBlock ⟨_, by simp only [bO]; arun [h11, e32, e36, w₀, w₁], ?_⟩
    refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_,
      ⟨k₂.rd.trans rd₁, k₂.wr.trans wr₁, k₂.sp.trans sp₁⟩, ?_, ?_⟩
    · simp [gpr_setReg, hdrLen, h₁, ha]
    · intro r a b c d e; simp only [gpr_store, gpr_setReg, a, b, c, d, ite_false]; exact kg r a b c d e
    · simp only [mem_store, mem_setReg]
      exact (fz.writeW (List.mem_singleton_self _) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (cB 36 4 (by decide) (by decide))
    · simp only [mem_store, gpr_store, mem_setReg, gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂]
      rw [show State.addr w + BitVec.ofNat 64 36 = State.addr w + BitVec.ofNat 64 32 + BitVec.ofNat 64 4 by
          rw [Offset.add_add],
        bytesAt_writeW32_at _ _ _ (by decide) (by decide), bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz,
        Proof.AesCcm.le4_or, le4_shl16, le4_shr16, hrev, encodeLen_mid h₁ ha,
        show hdrLen a = 6 by simp [hdrLen, h₁, ha]]
      have hl4 := length_be 4 a
      have hfe : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe, 0, 0] := le4_feff
      rcases hb : Spec.Ccm.be 4 a with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
        rw [hb] at hl4 <;> simp at hl4
      simp [Spec.Ccm.zeros, List.replicate, hfe]

end

end VG.Proof.AesCcm.Arm

end

end

/-! ### `AesCcm.Arm.Absorb`, which only this module used -/

section

/-! ### `AesCcm.Arm.Tag`, which only this module used -/

section

/-!
# AES-CCM on ARMv7: the tag (`tag y`)

Untrusted: everything here is checked by Lean. The calls of `vg_aes_ctr32`
take the key schedule, the counter block at `W + 64` and the working space at
`W + 384` from the environment (`ctrCall_of`), and blocks apart from those.
`tag y` makes `Ctr₀` at `W + 64` and calls `vg_aes_ctr32` on the MAC state at
`W + y`, one block: the state XORed with `CIPH_K(Ctr₀)`, CCM's keystream
from `Ctr₀` (`tag_ok`), whose first `t` bytes are the MAC encrypted
(`Proof.AesCcm.take_xorFrom_zero`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (CtrCall CtrPost ctr_call below mem_store gpr_store rd_store wr_store sp_store
  encodable_of_decide runBlock_app_of covers_left covers_of_mem covers_cons bytesAt_frame)
open VG.Proof.AesCcm (xorFrom ctr32_ccm)

theorem below_blw (sp : BitVec 32) : Region.Sub (below sp) (blw sp) :=
  Offset.sub_below (State.addr sp) (a := 8) (b := 16) (by decide) (by decide)

/-- The working space of the callees, at `W + 384`. -/
abbrev scrR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 384, 2176⟩

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- A call of `vg_aes_ctr32` with the key schedule, the counter block at
`W + 64`, `n` blocks at `D` and the working space at `W + 384`. -/
theorem ctrCall_of {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32}
    {n : Nat} (h0 : s.gpr .r0 = k) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 64)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 384)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (dK : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (dC : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 384, 2048⟩)
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (wD : Covers [⟨State.addr D, 16 * n⟩] s.wr) :
    CtrCall s k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R n := by
  have e64 := L.wA (d := 64) (by decide)
  have e384 := L.wA (d := 384) (by decide)
  have hsp := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hsp]; have := L.sp16; omega_using [this], L.kw,
    by rw [L.wN (by decide)]; have := L.ww; omega_using [this], fD, by rw [L.wN (by decide)]; have := L.ww; omega_using [this], ?_, dK,
    ?_, by rw [e64]; exact dC, ?_, by rw [e384]; exact dS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e64]; exact L.k_w' (by decide)
  · rw [e384]; exact L.k_w' (by decide)
  · rw [e64, e384]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [hsp]; exact L.stk_k.sub_left (below_blw sp)
  · rw [hsp, e64]; exact (L.stk_w' (by decide)).sub_left (below_blw sp)
  · rw [hsp]; exact dB.sub_left (below_blw sp)
  · rw [hsp, e384]; exact (L.stk_w' (by decide)).sub_left (below_blw sp)
  · exact he.perm.k
  · rw [e64, e384]
    exact covers_cons (he.perm.wC (by decide)) (covers_cons wD (he.perm.wC (by decide)))

/-- `Ctr₀` at `W + 64`, and the arguments of the call in `tag y`. -/
theorem tagArgs_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    ∃ s₃, runBlock isa (([.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] : List Instr) ++ ctrAt ++ ctrArgs ++
        ([VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)] : List Instr)) s = some s₃ ∧
      CtrCall s₃ k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 384) R 1 ∧
      Env k w sp R q1 s₃ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₃.gpr r = s.gpr r) ∧
      s₃.rd = s.rd ∧ s₃.wr = s.wr ∧ s₃.sp = s.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 0 := by
  have h8 := he.r8; have h9 := he.r9; have h11 := he.r11
  -- `r0 := 0`.
  obtain ⟨s₁, run₁, h0₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] s = some s₁ ∧
      s₁.gpr .r0 = BitVec.ofNat 32 0 ∧ (∀ r, r ≠ .r0 → s₁.gpr r = s.gpr r) ∧
      (s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp) := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.2.2.2 k₁.2.1 k₁.2.2.1
  obtain ⟨s₂, run₂, hc₂, f₂, g₂, rd₂, wr₂, sp₂⟩ := ctrAt_ok L he₁ h7 h13 (by rw [k₁.1]; exact hc0) h0₁
    (Nat.pow_pos (by decide))
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) sp₂ rd₂ wr₂
  have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
  obtain ⟨s₃, run₃, a0, a1, a2, a3, a12, alr, g₃, k₃⟩ : ∃ s₃, runBlock isa (ctrArgs ++
      [VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)]) s₂ = some s₃ ∧
      s₃.gpr .r0 = k ∧ s₃.gpr .r1 = BitVec.ofNat 32 R ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 64 ∧
      s₃.gpr .r3 = w + BitVec.ofNat 32 y ∧ s₃.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₃.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₃.gpr r = s₂.gpr r) ∧
      (s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp) := by
    refine ⟨_, by simp only [ctrArgs, c1O, scrO]; arun [he₂.r9, he₂.r8, he₂.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₂.r9]
    · simp [gpr_setReg, he₂.r8]
    · simp [gpr_setReg, he₂.r11]
    · simp [gpr_setReg, he₂.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₂.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₃.2.2.2 k₃.2.1 k₃.2.2.1
  have eY := L.wA (d := y) (by omega_using [hy])
  have hqc : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16 * 1⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have C₃ := ctrCall_of L he₃ hR (n := 1) a0 a1 a2 a3 a12 alr (by rw [L.wN (by omega_using [hy])]; have := L.ww; omega_using [hy, this])
    (by rw [eY]; exact L.k_w' (by omega_using [hy])) (by rw [eY]; exact hqc)
    (by rw [eY]; exact L.w_w (.inl (by omega_using [hy])) (by omega_using [hy]) (by decide))
    (by rw [eY]; exact L.stk_w' (by omega_using [hy])) (by rw [eY]; exact he₃.perm.wC (by omega_using [hy]))
  refine ⟨s₃, by
    rw [show [.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] ++ ctrAt ++ ctrArgs ++
      [VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)] =
      [.mov .r0 (VG.Impl.AesGcm.Arm.imm 0)] ++ (ctrAt ++ (ctrArgs ++
      [VG.Impl.AesGcm.Arm.addI .r3 .r11 y, .mov .r12 (VG.Impl.AesGcm.Arm.imm 1)])) by simp]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃), C₃, he₃, fun r a b c d e f => by rw [g₃ r a b c d e f, g₂ r a b, g₁ r a],
    by rw [k₃.2.1, rd₂, k₁.2.1], by rw [k₃.2.2.1, wr₂, k₁.2.2.1], by rw [k₃.2.2.2, sp₂, k₁.2.2.2],
    by rw [k₃.1, ← k₁.1]; exact f₂, by rw [k₃.1]; exact hc₂⟩

/-- The MAC state at `W + y` XORed with `CIPH_K(Ctr₀)`. -/
theorem tag_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (tag y) s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩, ⟨State.addr w + BitVec.ofNat 64 y, 16⟩, scrR w,
        blw sp] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem (State.addr k) R) nonce 0
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16) := by
  obtain ⟨s₃, run₃, C₃, he₃, g₃, rd₃, wr₃, sp₃, f₀₃, hc₂⟩ := tagArgs_ok L he hR h7 h13 hc0 hy
  have eY := L.wA (d := y) (by omega_using [hy])
  have hqc : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16 * 1⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (ctr_call C₃) fun s₄ h => ?_
  have hsp₃ : s₃.sp = sp := he₃.sp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  -- Memory before the call: only `W + 64` changed.
  have hK₃ : Spec.Ccm.ctxCiph s₃.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R := by
    simp only [Spec.Ccm.ctxCiph]
    rw [bytesAt_frame f₀₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w' (by decide)).sub_left (Region.sub_prefix hRb)) (by omega_using [hR])]
  have hY₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 y) 16 = bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame f₀₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hqc.symm) (by decide)
  refine ⟨he₃.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, rd₃], by rw [h.wr, wr₃], fun r hr hlr => ?_, ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr hlr, g₃ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · have f₄ := h.frame
    rw [hsp₃, State.addr, ← State.addr, show State.addr (w + BitVec.ofNat 32 64) = _ from L.wA (by decide),
      eY, show State.addr (w + BitVec.ofNat 32 384) = _ from L.wA (by decide)] at f₄
    refine (f₀₃.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (f₄.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨scrR w, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨blw sp, by simp, below_blw sp⟩
  · have hc := ctr32_ccm (m := s₃.mem) (m' := s₄.mem) (K := State.addr k) (C := State.addr (w + BitVec.ofNat 32 64))
      (D := State.addr (w + BitVec.ofNat 32 y)) (R := R) (nonce := nonce) (by omega_using [h13]) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega_using [hi], Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [L.wA (by decide), hc₂]) h.out
    rw [Nat.mul_one, eY] at hc
    rw [hc, hK₃, hY₃]

end

end VG.Proof.AesCcm.Arm

end

end


/-!
# AES-CCM on ARMv7: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` take the key schedule, the MAC state at `W + y` and
the working space at `W + 384` from the environment (`updCall_of`).
`updBlock y` chains `B` (at `W + 32`) into the MAC state (`updBlock_ok`);
`absorbPad y` chains the `len` bytes at `P`, padded with zeros to whole
blocks: its whole blocks in one call (`absorbWhole_ok`), then its last
`len mod 16` bytes copied into the zeroed `B` (`absorbTail_ok`); together,
the blocks of the padded string (`absorbPad_ok`,
`Proof.AesCcm.blocks_pad16`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_cons covers_left bytesAt_frame
  runBlock_app_of and15 shr4 toNat32 ofNat_sub32 z_cmp eval_eq' Keeps z_subFlags gpr_subFlags)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.AesCcm (ctxCiph_frame bytesAt_prefix bytesAt_suffix bytesAt_writeBytes_base length_bytesAt)

/-- What the pieces of the MAC write: the MAC state at `W + y`, `B`, the
working space of the functions called and the stack below `sp`. -/
abbrev macR (w sp : BitVec 32) (y : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 32, 16⟩, scrR w, blw sp]

theorem blw16_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) : blw16 s = blw sp := by
  subst h; rfl

/-- The last bytes of a string, padded to a block, if any are left after
its whole blocks. -/
def tailBlocks (x : List Byte) : List (List Byte) :=
  if x.length % 16 = 0 then [] else [x.drop (16 * (x.length / 16)) ++ Spec.Ccm.zeros (16 - x.length % 16)]

/-- What `absorbPad`'s pieces keep: the environment, the registers holding
the string, and what they write. -/
structure Absorbed (k w sp : BitVec 32) (R q1 : Nat) (s : State) (y : Nat) (P : BitVec 32) (len : Nat)
    (Y : List Byte) (s' : State) : Prop where
  env : Env k w sp R q1 s'
  r4 : s'.gpr .r4 = P
  r5 : s'.gpr .r5 = BitVec.ofNat 32 len
  frame : Frame (macR w sp y) s.mem s'.mem
  out : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- A call of `vg_cmac_aes_update` with the key schedule, the MAC state at
`W + y`, `n` blocks at `D` and the working space at `W + 384`. -/
theorem updCall_of {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y + 16 ≤ 384) {D : BitVec 32} {n : Nat} (hn : 16 * n < 2 ^ 32) (fD : D.toNat + 16 * n ≤ 2 ^ 32)
    (dC : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint (scrR w))
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (rD : Covers [⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr))
    (h0 : s.gpr .r0 = k) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = w + BitVec.ofNat 32 y)
    (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (hlr : s.gpr .lr = w + BitVec.ofNat 32 384) :
    UArgs s k (w + BitVec.ofNat 32 y) D (w + BitVec.ofNat 32 384) R n := by
  have eY := L.wA (d := y) (by omega_arith)
  have e384 := L.wA (d := 384) (by decide)
  have hb := blw16_eq he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, hn, by rw [he.sp]; exact L.sp16, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    L.kw, ?_, fD, ?_, covers_cons he.perm.k rD, ?_⟩
  · rw [eY]; exact L.k_w' (by omega_arith)
  · rw [e384]; exact L.k_w' (by decide)
  · rw [eY]; exact dC
  · rw [e384]; exact dS
  · rw [eY, e384]; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · rw [hb]; exact L.stk_k
  · rw [hb]; exact dB
  · rw [hb, eY]; exact L.stk_w' (by omega_arith)
  · rw [hb, e384]; exact L.stk_w' (by decide)
  · rw [L.wN (by omega_arith)]; have := L.ww; omega_arith
  · rw [L.wN (by decide)]; have := L.ww; omega_arith
  · rw [eY, e384]; exact covers_cons (he.perm.wC (by omega_arith)) (he.perm.wC (by decide))

/-- The arguments of the call in `updBlock y`. -/
theorem updBlockArgs_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) : ∃ s₁, runBlock isa (updArgs y ++ [addI .r3 .r11 bO, .mov .r12 (imm 1)]) s = some s₁ ∧
      UArgs s₁ k (w + BitVec.ofNat 32 y) (w + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 384) R 1 ∧
      Env k w sp R q1 s₁ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
  obtain ⟨s₁, run₁, a0, a1, a2, a3, a12, alr, g₁, k₁⟩ : ∃ s₁, runBlock isa (updArgs y ++
      [addI .r3 .r11 bO, .mov .r12 (imm 1)]) s = some s₁ ∧
      s₁.gpr .r0 = k ∧ s₁.gpr .r1 = BitVec.ofNat 32 R ∧ s₁.gpr .r2 = w + BitVec.ofNat 32 y ∧
      s₁.gpr .r3 = w + BitVec.ofNat 32 32 ∧ s₁.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₁.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [updArgs, bO, scrO]; arun [he.r9, he.r8, he.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r9]
    · simp [gpr_setReg, he.r8]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have e32 := L.wA (d := 32) (by decide)
  have eY := L.wA (d := y) (by omega_arith)
  have dYB : (⟨State.addr w + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have U := updCall_of L he₁ hR (y := y) (by omega_arith) (D := w + BitVec.ofNat 32 32) (n := 1) (by decide)
    (by rw [L.wN (by decide)]; have := L.ww; omega_arith) (by rw [e32]; exact dYB)
    (by rw [e32]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e32]; exact L.stk_w' (by decide)) (by rw [e32]; exact covers_left (he₁.perm.wC (by decide)))
    a0 a1 a2 a3 a12 alr
  exact ⟨s₁, run₁, U, he₁, g₁, k₁⟩

/-- `B` (at `W + 32`) chained into the MAC state at `W + y`. -/
theorem updBlock_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (updBlock y) s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 y, 16⟩, scrR w, blw sp] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16) [bytesAt s.mem (State.addr w + BitVec.ofNat 64 32) 16] := by
  obtain ⟨s₁, run₁, U, he₁, g₁, k₁⟩ := updBlockArgs_ok L he hR hy
  have e32 := L.wA (d := 32) (by decide)
  have eY := L.wA (d := y) (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (upd_call U) fun s₂ h => ?_
  refine ⟨he₁.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, k₁.rd], by rw [h.wr, k₁.wr], fun r hr hlr => ?_,
    ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h.saved r hr hlr, g₁ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · have f := h.frame
    rw [blw16_eq (k₁.sp.trans he.sp), eY, L.wA (d := 384) (by decide), k₁.mem] at f
    exact f
  · have o := h.out
    rw [eY, Proof.Cmac.Stream.blocksAt_eq, Nat.mul_one, Proof.Cmac.Stream.blocks_single
      (Proof.Cmac.bytesAt_length _ _ _), k₁.mem, e32] at o
    rw [o]; rfl

omit L in
theorem sub_mac {y : Nat} {r : Region} (hr : r ∈ macR w sp y) : ∃ r' ∈ macR w sp y, Region.Sub r r' :=
  ⟨r, hr, fun _ h => h⟩

omit L in
/-- `r12 = r5 / 16`, and `Z` for no whole blocks. -/
theorem split16_ok {s : State} {len : Nat} (hl : len < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 (len / 16) ∧ s₁.z = decide (len / 16 = 0) ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, shr4 hl]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, shr4 hl]
    rw [z_cmp (by omega_arith) (by decide)]
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- `r6 = r5 mod 16`, and `Z` for no last bytes. -/
theorem split15_ok {s : State} {len : Nat} (hl : len < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    ∃ s₁, runBlock isa [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)] s = some s₁ ∧
      s₁.gpr .r6 = BitVec.ofNat 32 (len % 16) ∧ s₁.z = decide (len % 16 = 0) ∧
      (∀ r, r ≠ .r6 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  have hand := and15 (BitVec.ofNat 32 len)
  rw [toNat32 hl] at hand
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, imm, hand]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, imm, hand]
    rw [z_cmp (by omega_arith) (by decide)]
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The arguments of the call in `absorbWhole y`, for `nb` blocks at `P`. -/
theorem absArgs_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {nb : Nat} (hq : Buf w sp s P (16 * nb)) (hn : 16 * nb < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h12 : s.gpr .r12 = BitVec.ofNat 32 nb) :
    ∃ s₂, runBlock isa (updArgs y ++ ([.mov .r3 (.reg .r4)] : List Instr)) s = some s₂ ∧
      UArgs s₂ k (w + BitVec.ofNat 32 y) P (w + BitVec.ofNat 32 384) R nb ∧ Env k w sp R q1 s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
  obtain ⟨s₂, run₂, a0, a1, a2, a3, alr, g₂, k₂⟩ : ∃ s₂, runBlock isa (updArgs y ++ [.mov .r3 (.reg .r4)]) s =
      some s₂ ∧ s₂.gpr .r0 = k ∧ s₂.gpr .r1 = BitVec.ofNat 32 R ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 y ∧
      s₂.gpr .r3 = P ∧ s₂.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
    have eo : encodable (BitVec.ofNat 32 y) = true := by rcases hy with rfl | rfl <;> decide
    refine ⟨_, by simp only [updArgs, scrO]; arun [he.r9, he.r8, he.r11, eo], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r9]
    · simp [gpr_setReg, he.r8]
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, h4]
    · simp [gpr_setReg, he.r11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) k₂.sp k₂.rd k₂.wr
  exact ⟨s₂, run₂, updCall_of L he₂ hR (y := y) (by omega_arith) (D := P) (n := nb) hn hq.fit
    (hq.w.sub_right (Lay.wSub (by omega_arith))) (hq.w.sub_right (Lay.wSub (by decide))) hq.stk
    (by rw [k₂.rd, k₂.wr]; exact hq.rd) a0 a1 a2 a3
    (by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), h12]) alr, he₂, g₂, k₂⟩

/-- The whole blocks of the string. -/
theorem absorbWhole_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbWhole y) s (Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 ((bytesAt s.mem (State.addr P) len).take (16 * (len / 16)))))) := by
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ := split16_ok hl h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (len / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5],
      by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    rw [k₁.mem, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := by simpa using hf
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := ((hP (by omega_arith)).take hb).of_eq k₁.rd k₁.wr
    obtain ⟨s₂, run₂, U, he₂, g₂, k₂⟩ := absArgs_ok L he₁ hR hy hq (by omega_arith) (by rw [g₁ _ (by decide), h4]) h12₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.mono (upd_call U) fun s₃ h => ⟨he₂.of_saved h.saved h.sp h.rd h.wr, ?_, ?_, ?_, ?_,
      by rw [h.rd, k₂.rd, k₁.rd], by rw [h.wr, k₂.wr, k₁.wr]⟩
    · rw [h.saved _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), h4]
    · rw [h.saved _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₁ _ (by decide), h5]
    · have f := h.frame
      rw [blw16_eq (k₂.sp.trans (k₁.sp.trans he.sp)), L.wA (d := y) (by omega_arith), L.wA (d := 384) (by decide),
        k₂.mem, k₁.mem] at f
      exact f.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
    · have o := h.out
      rw [L.wA (d := y) (by omega_arith), Proof.Cmac.Stream.blocksAt_eq, k₂.mem, k₁.mem, bytesAt_prefix _ _ hb] at o
      rw [o]; rfl

/-- `B` zeroed, and the arguments of the copy of the last `len mod 16` bytes
at `P` into it. -/
theorem tailPre_ok {s₁ : State} (he₁ : Env k w sp R q1 s₁) {P : BitVec 32} {len : Nat}
    (hP : len ≠ 0 → Buf w sp s₁ P len) (hl : len < 2 ^ 32) (h0 : len % 16 ≠ 0) (h4₁ : s₁.gpr .r4 = P)
    (h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 len) (h6₁ : s₁.gpr .r6 = BitVec.ofNat 32 (len % 16)) :
    ∃ s₃, runBlock isa (zero16 bO ++ ([.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
        addI .r2 .r11 bO, .mov .r3 (.reg .r6)] : List Instr)) s₁ = some s₃ ∧
      s₃.mem = Proof.Cmac.store4 s₁.mem (State.addr w + BitVec.ofNat 64 32) 0 0 0 0 ∧
      LoopPre s₃ (P + BitVec.ofNat 32 (16 * (len / 16))) (w + BitVec.ofNat 32 32) (len % 16) ∧
      Env k w sp R q1 s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s₁.gpr r) ∧
      s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr ∧ s₃.sp = s₁.sp := by
  obtain ⟨s₂, run₂, hm₂, g₂, rd₂, wr₂, sp₂, -⟩ := zero16_ok L he₁ (d := bO) (by decide) (by decide)
  simp only [bO] at hm₂
  have hj : 16 * (len / 16) + len % 16 = len := by omega_arith
  have hsub : BitVec.ofNat 32 len - BitVec.ofNat 32 (len % 16) = BitVec.ofNat 32 (16 * (len / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hl]; congr 1; omega_arith
  obtain ⟨s₃, run₃, a1, a2, a3, g₃, k₃⟩ : ∃ s₃, runBlock isa [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
      addI .r2 .r11 bO, .mov .r3 (.reg .r6)] s₂ = some s₃ ∧
      s₃.gpr .r1 = P + BitVec.ofNat 32 (16 * (len / 16)) ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 32 ∧
      s₃.gpr .r3 = BitVec.ofNat 32 (len % 16) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have r4₂ : s₂.gpr .r4 = P := by rw [g₂ _ (by decide), h4₁]
    have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 len := by rw [g₂ _ (by decide), h5₁]
    have r6₂ : s₂.gpr .r6 = BitVec.ofNat 32 (len % 16) := by rw [g₂ _ (by decide), h6₁]
    have r11₂ : s₂.gpr .r11 = w := by rw [g₂ _ (by decide), he₁.r11]
    refine ⟨_, by simp only [bO]; arun [r11₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, r4₂, r5₂, r6₂, hsub, BitVec.add_comm]
    · simp [gpr_setReg, r11₂]
    · simp [gpr_setReg, r6₂]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₃ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₃ _ (by decide) (by decide) (by decide), g₂ _ (by decide)]) (k₃.sp.trans sp₂)
    (k₃.rd.trans rd₂) (k₃.wr.trans wr₂)
  have hT := ((hP (by omega_arith)).sub (j := 16 * (len / 16)) (k := len % 16) (by omega_arith) (by omega_arith)).of_eq (s' := s₃)
    (by rw [k₃.rd, rd₂]) (by rw [k₃.wr, wr₂])
  have e32 := L.wA (d := 32) (by decide)
  have eT := (hP (by omega_arith)).addr (j := 16 * (len / 16)) (by omega_arith)
  have lp : LoopPre s₃ (P + BitVec.ofNat 32 (16 * (len / 16))) (w + BitVec.ofNat 32 32) (len % 16) := by
    refine ⟨a1, a2, a3, by omega_arith, by omega_arith, hT.fit, by rw [L.wN (by decide)]; have := L.ww; omega_arith, hT.rd, ?_, ?_⟩
    · rw [e32]; exact he₃.perm.wC (by omega_arith)
    · rw [e32]; exact hT.w.sub_right (Lay.wSub (by omega_arith))
  exact ⟨s₃, by
    rw [show zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4), addI .r2 .r11 bO,
      .mov .r3 (.reg .r6)] = zero16 bO ++ ([.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
      addI .r2 .r11 bO, .mov .r3 (.reg .r6)] : List Instr) from rfl]
    exact runBlock_app_of run₂ run₃, by rw [k₃.mem, hm₂], lp, he₃, fun r a b c d => by rw [g₃ r b c d, g₂ r a],
    by rw [k₃.rd, rd₂], by rw [k₃.wr, wr₂], by rw [k₃.sp, sp₂]⟩

/-- The last bytes of the string, padded with zeros in `B`. -/
theorem absorbTail_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbTail y) s (Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (tailBlocks (bytesAt s.mem (State.addr P) len)))) := by
  have hxl := length_bytesAt s.mem (State.addr P) len
  obtain ⟨s₁, run₁, h6₁, hz, g₁, k₁⟩ := split15_ok hl h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (len % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [g₁ _ (by decide), h4], by rw [g₁ _ (by decide), h5],
      by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    simp only [k₁.mem, tailBlocks, hxl, h0, ↓reduceIte]; rfl
  · have h0 : len % 16 ≠ 0 := by simpa using hf
    obtain ⟨s₃, run₃, hm₃, lp, he₃, g₃, rd₃, wr₃, sp₃⟩ := tailPre_ok L he₁ (fun h => (hP h).of_eq k₁.rd k₁.wr) hl
      h0 (by rw [g₁ _ (by decide), h4]) (by rw [g₁ _ (by decide), h5]) h6₁
    refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
    have hT := ((hP (by omega_arith)).sub (j := 16 * (len / 16)) (k := len % 16) (by omega_arith) (by omega_arith)).of_eq (s' := s₃)
      (by rw [rd₃, k₁.rd]) (by rw [wr₃, k₁.wr])
    have e32 := L.wA (d := 32) (by decide)
    have eT := (hP (by omega_arith)).addr (j := 16 * (len / 16)) (by omega_arith)
    refine WP.seq (WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, lo⟩ => ?_)
    have he₄ := he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr
    rw [e32, eT] at hm₄
    -- What was written: only `B`.
    have fZ : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₃.mem := by
      rw [hm₃, k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have fB : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
      rw [hm₄]
      exact fZ.trans (writeBytes_frame _ _ _ (by
        rw [length_bytesAt]
        exact Offset.contains _ (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega_arith) (by decide)))
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have hK₄ : Spec.Ccm.ctxCiph s₄.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R :=
      ctxCiph_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hY₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 y) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
      bytesAt_frame fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    have hB₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
        (bytesAt s.mem (State.addr P) len).drop (16 * (len / 16)) ++ Spec.Ccm.zeros (16 - len % 16) := by
      have hs₂ : bytesAt s₃.mem (State.addr P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) =
          (bytesAt s.mem (State.addr P) len).drop (16 * (len / 16)) := by
        rw [bytesAt_frame fZ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← eT]
            exact hT.w.sub_right (Lay.wSub (by decide))) (by omega_arith),
          show len % 16 = len - 16 * (len / 16) by omega_arith, bytesAt_suffix _ _ (by omega_arith)]
      have hz : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by
        rw [hm₃]; exact store4_zero_bytes' _ _
      rw [hm₄, bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]; omega_arith) (by decide), hs₂, hz,
        List.length_drop, hxl]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      congr 2
      omega_arith
    refine WP.mono (updBlock_ok L he₄ hR hy) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ =>
      ⟨he₅, ?_, ?_, ?_, ?_, by rw [rd₅, lo.rd, rd₃, k₁.rd], by rw [wr₅, lo.wr, wr₃, k₁.wr]⟩
    · rw [g₅ _ (by decide) (by decide), lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₃ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h4]
    · rw [g₅ _ (by decide) (by decide), lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₃ _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), h5]
    · refine (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
    · rw [o₅, hY₄, hB₄, hK₄]
      simp only [tailBlocks, hxl, h0, ↓reduceIte]

omit L in
/-- A buffer missing `W` and the stack below `sp` keeps its bytes. -/
theorem buf_kept {s : State} {P : BitVec 32} {len : Nat} (hP : Buf w sp s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR w sp y) m m') :
    bytesAt m' (State.addr P) len = bytesAt m (State.addr P) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega_arith)

theorem k_macR {y : Nat} (hy : y + 16 ≤ 2560) : ∀ r ∈ macR w sp y, (⟨State.addr k, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w' hy
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.stk_k.symm

/-- The `len` bytes at `P`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
theorem absorbPad_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {P : BitVec 32} {len : Nat} (hP : len ≠ 0 → Buf w sp s P len) (hl : len < 2 ^ 32)
    (h4 : s.gpr .r4 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 len) :
    WP isa (absorbPad y) s (Absorbed k w sp R q1 s y P len
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem (State.addr P) len))))) := by
  refine WP.seq (WP.mono (absorbWhole_ok L he hR hy hP hl h4 h5) fun s₁ A₁ => ?_)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (absorbTail_ok L A₁.env hR hy (fun h => (hP h).of_eq A₁.rd A₁.wr) hl A₁.r4 A₁.r5) fun s₂ A₂ =>
    ⟨A₂.env, A₂.r4, A₂.r5, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  have hk : bytesAt s₁.mem (State.addr P) len = bytesAt s.mem (State.addr P) len := by
    rcases Nat.eq_zero_or_pos len with e | e
    · subst e; rfl
    · exact buf_kept (hP (by omega_arith)) (by omega_arith) A₁.frame
  rw [A₂.out, A₁.out, hk, ctxCiph_frame A₁.frame (k_macR L (by omega_arith)) hRb,
    ← Proof.Cmac.chain_append, Proof.AesCcm.blocks_pad16, length_bytesAt, tailBlocks, length_bytesAt]

end

end VG.Proof.AesCcm.Arm

end

end

/-! ### `AesCcm.Arm.Contract`, which only this module used -/

section

/-!
# AES-CCM on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). `seal` and `open` call `vg_cmac_aes_update` and
`vg_aes_ctr32` in frames that push their two stack arguments below the stack
pointer, and `vg_cmac_aes_update`'s own frame uses the 8 bytes below that:
so the 16 bytes below the stack pointer (`bel16`) may not overlap any
buffer.
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The 16 bytes below the stack pointer, which the calls use. -/
abbrev bel16 (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

abbrev roundsOk (s : State) : Prop :=
  (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12],
tag = [sp + 16], tag_len = [sp + 20], work = [sp + 24])`. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s 7) ∧ work.Disjoint (args s 7) ∧
    (bel16 s).Disjoint sch ∧ (bel16 s).Disjoint nonce ∧ (bel16 s).Disjoint aad ∧ (bel16 s).Disjoint data ∧
    (bel16 s).Disjoint work ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 28 ≤ 2 ^ 32 ∧ roundsOk s ∧
    valid (arg s 5).toNat (s.gpr .r3).toNat (arg s 1).toNat (arg s 3).toNat = true ∧
    tag.Disjoint data ∧ tag.Disjoint work ∧ (bel16 s).Disjoint tag ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [sch, nonce, aad, args s 7] ∧ s.wr = [data, tag, work] ∧ oneLay s ∧ tag.Disjoint (args s 7)

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨State.addr (s.gpr .r0), 240⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let work : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [sch, nonce, aad, tag, args s 7] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- The cipher of the key schedule. -/
abbrev ciph (s : State) : Spec.Ccm.Cipher := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat

/-- `vg_aes_ccm_seal`. -/
def sealArm : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ciph s) (arg s 5).toNat
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)
        (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat) =
      (bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat, bytesAt s'.mem (State.addr (arg s 4)) (arg s 5).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  decryptWith (ciph s) (arg s 5).toNat
    (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)
    (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (bytesAt s.mem (State.addr (arg s 4)) (arg s 5).toNat)

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬roundsOk s then [] else [if (openRes s).isSome then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openArm : Contract isa where
  pre := openPre
  post s s' :=
    match openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = zeros (arg s 3).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.Arm

end

end


/-!
# AES-CCM on ARMv7: the associated data (`aad y`)

Untrusted: everything here is checked by Lean. The pieces read the stack
arguments, which the writes of the pieces miss, as on entry (`Stk`).
`aadHead y` chains the first block of the formatted associated data: the
encoding of its length followed by as many of its bytes as fit, padded
(`aadHead_ok`); `aad y` that block and the rest of the associated data,
padded, if there is any (`aad_ok`): the blocks `adataBlocks`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop minLen)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok bytesAt_frame toNat32 ofNat_sub32 z_cmp eval_eq' Keeps
  z_subFlags gpr_subFlags minLen_ok add32_ofNat_assoc ArgsKeep)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks ctxCiph_frame bytesAt_prefix bytesAt_suffix
  bytesAt_writeBytes_at length_bytesAt)

/-- The stack arguments of `s` are those of the entry state `s₀`, apart from
`W` and the stack below `sp`. -/
structure Stk (w : BitVec 32) (s₀ s : State) : Prop where
  keep : ArgsKeep 7 s₀ s
  fit : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32
  rd : args s₀ 7 ∈ s₀.rd
  aw : (args s₀ 7).Disjoint ⟨State.addr w, 2560⟩

namespace Stk

variable {w : BitVec 32} {s₀ s : State} (h : Stk w s₀ s)
include h

/-- Argument `i`, at offset `4 i`. -/
theorem «at» (i : Nat) {off : Nat} (hi : i < 7) (hoff : 4 * i = off) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 = stackArg s₀ i :=
  h.keep.at h.fit h.rd i hi hoff

/-- Argument `i` is apart from `W`. -/
theorem slot_w (i : Nat) {off : Nat} (hi : i < 7) (hoff : 4 * i = off) {d n : Nat} (hd : d + n ≤ 2560) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 off), 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, n⟩ := by
  subst hoff
  have := h.fit
  have e : State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
    rw [h.keep.sp, Proof.AesGcm.Arm.argAddr_zero]; exact addr_add (by omega_arith)
  rw [e]
  exact (h.aw.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Lay.wSub hd)

theorem of_eq {s' : State} (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Stk w s₀ s' :=
  { h with keep := h.keep.of_eq hm hsp hrd hwr }

/-- After code that writes regions apart from the arguments. -/
theorem frame {s' : State} {rs : List Region} (hfr : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (args s₀ 7).Disjoint r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Stk w s₀ s' :=
  { h with keep := h.keep.frame h.fit hfr hd hsp hrd hwr }

/-- The stack below `sp` is apart from the arguments. -/
theorem blw_args {sp : BitVec 32} (hsp : s₀.sp = sp) : (args s₀ 7).Disjoint (blw sp) := by
  have := h.fit
  subst hsp
  simp only [args, Proof.AesGcm.Arm.argAddr_zero]
  exact Offset.base_disjoint_below (State.addr s₀.sp) (n := 16) (k := 4 * 7) (by omega_arith)

/-- After code that writes the MAC's regions. -/
theorem mac {sp : BitVec 32} (hsp₀ : s₀.sp = sp) {y : Nat} (hy : y + 16 ≤ 2560) {s' : State}
    (hfr : Frame (macR w sp y) s.mem s'.mem) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Stk w s₀ s' :=
  h.frame hfr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.aw.sub_right (Lay.wSub hy)
    · exact h.aw.sub_right (Lay.wSub (by decide))
    · exact h.aw.sub_right (Lay.wSub (by decide))
    · exact h.blw_args hsp₀) hsp hrd hwr

end Stk

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => seq_assoc3 h)

/-- What a piece of the MAC leaves: the environment, what it writes, the
MAC state `Y` at `W + y`, and the permissions. -/
structure MacStep (k w sp : BitVec 32) (R q1 : Nat) (s : State) (y : Nat) (Y : List Byte) (s' : State) :
    Prop where
  env : Env k w sp R q1 s'
  frame : Frame (macR w sp y) s.mem s'.mem
  out : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- The encoding of the length and the first bytes of the associated data,
padded, in `B`; `r4` and `r5` the rest. -/
theorem aadHeadPre_ok {s : State} (he : Env k w sp R q1 s) {A : BitVec 32} {a : Nat} (hA : Buf w sp s A a)
    (ha0 : 0 < a) (ha : a < 2 ^ 32) (h4 : s.gpr .r4 = A) (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa (.seq header (.seq minLen (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO,
        .dp .add .r2 .r2 (.reg .r6), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]) copyLoop))) s
      fun s₄ => Env k w sp R q1 s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
        Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem ∧
        s₄.gpr .r4 = A + BitVec.ofNat 32 (headLen a) ∧ s₄.gpr .r5 = BitVec.ofNat 32 (a - headLen a) ∧
        bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
          Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a)) := by
  have hh := Proof.AesCcm.hdrLen_le a
  have hh26 : hdrLen a = 2 ∨ hdrLen a = 6 := by
    unfold hdrLen; by_cases h : a < 2 ^ 16 - 2 ^ 8 <;> simp [h, ha]
  have hh2 : 2 ≤ hdrLen a := by omega_arith
  have hh6 : hdrLen a ≤ 6 := by omega_arith
  refine WP.seq (WP.mono (header_ok L he ha0 ha h5) fun s₁ ⟨he₁, h6₁, g₁, ⟨rd₁, wr₁, sp₁⟩, f₁, hB₁⟩ => ?_)
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 a := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  have h4₁ : s₁.gpr .r4 = A := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  refine WP.seq (WP.mono (minLen_ok s₁ h6₁ h5₁ (by omega_arith) ha) fun s₂ ⟨h3₂, g₂, k₂⟩ => ?_)
  have hn1 : min (16 - hdrLen a) a = headLen a := by unfold headLen; omega_arith
  rw [hn1] at h3₂
  have hn1' : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega_arith
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) k₂.sp k₂.rd k₂.wr
  have h11 := he₂.r11
  obtain ⟨s₃, run₃, a1, a2, a3, a4, a5, g₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (.reg .r4), addI .r2 .r11 bO,
      .dp .add .r2 .r2 (.reg .r6), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)] s₂ = some s₃ ∧
      s₃.gpr .r1 = A ∧ s₃.gpr .r2 = w + BitVec.ofNat 32 (32 + hdrLen a) ∧
      s₃.gpr .r3 = BitVec.ofNat 32 (headLen a) ∧ s₃.gpr .r4 = A + BitVec.ofNat 32 (headLen a) ∧
      s₃.gpr .r5 = BitVec.ofNat 32 (a - headLen a) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have h4₂ : s₂.gpr .r4 = A := by rw [g₂ _ (by decide) (by decide), h4₁]
    have h5₂ : s₂.gpr .r5 = BitVec.ofNat 32 a := by rw [g₂ _ (by decide) (by decide), h5₁]
    have h6₂ : s₂.gpr .r6 = BitVec.ofNat 32 (hdrLen a) := by rw [g₂ _ (by decide) (by decide), h6₁]
    refine ⟨_, by simp only [bO]; arun [h11], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h4₂]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h11, h6₂, imm, add32_ofNat_assoc]
    · simp [gpr_setReg, h3₂]
    · simp [gpr_setReg, h4₂, h3₂]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h5₂, h3₂]
      exact ofNat_sub32 hn1'.2.1 ha
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide))
    k₃.sp k₃.rd k₃.wr
  have hA₃ := (hA.take hn1'.2.1).of_eq (s' := s₃) (by rw [k₃.rd, k₂.rd, rd₁]) (by rw [k₃.wr, k₂.wr, wr₁])
  have eB := L.wA (d := 32 + hdrLen a) (by omega_arith)
  have lp : LoopPre s₃ A (w + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) := by
    refine ⟨a1, a2, a3, hn1'.1, by omega_arith, hA₃.fit, by rw [L.wN (by omega_arith)]; have := L.ww; omega_arith, hA₃.rd, ?_, ?_⟩
    · rw [eB]; exact he₃.perm.wC (by omega_arith)
    · rw [eB]; exact hA₃.w.sub_right (Lay.wSub (by omega_arith))
  refine WP.mono (copyLoop_ok s₃ lp) fun s₄ ⟨hm₄, lo⟩ => ?_
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  rw [eB] at hm₄
  have fC : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [hm₄]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains _ (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega_arith) (by omega_arith)
        (by decide))
  have fB : Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩] s.mem s₄.mem := by
    rw [← k₂.mem, ← k₃.mem] at f₁; exact f₁.trans fC
  have hAk : bytesAt s₃.mem (State.addr A) (headLen a) = (bytesAt s.mem (State.addr A) a).take (headLen a) := by
    rw [k₃.mem, k₂.mem, bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hA.w.sub_left (Region.sub_prefix hn1'.2.1)).sub_right (Lay.wSub (by decide))) (by omega_arith),
      bytesAt_prefix _ _ hn1'.2.1]
  have hB₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem (State.addr A) a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega_arith
    rw [hm₄, show State.addr w + BitVec.ofNat 64 (32 + hdrLen a) =
        State.addr w + BitVec.ofNat 64 32 + BitVec.ofNat 64 (hdrLen a) by rw [Offset.add_add],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega_arith) (by decide), length_bytesAt, hAk, k₃.mem,
      k₂.mem, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega_arith) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega_arith), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega_arith]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega_arith)
  exact ⟨he₄, by rw [lo.rd, k₃.rd, k₂.rd, rd₁], by rw [lo.wr, k₃.wr, k₂.wr, wr₁], fB,
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), a4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), a5], hB₄⟩

/-- The first block of the associated data. -/
theorem aadHead_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) {A : BitVec 32} {a : Nat} (hA : Buf w sp s A a) (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (h4 : s.gpr .r4 = A) (h5 : s.gpr .r5 = BitVec.ofNat 32 a) :
    WP isa (aadHead y) s (Absorbed k w sp R q1 s y (A + BitVec.ofNat 32 (headLen a)) (a - headLen a)
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (State.addr A) a).take (headLen a))])) := by
  refine seq_assoc4 (WP.seq (WP.mono (aadHeadPre_ok L he hA ha0 ha h4 h5)
    fun s₄ ⟨he₄, rd₄, wr₄, fB, h4₄, h5₄, hB₄⟩ => ?_))
  have hY₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 y) 16 =
      bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16 :=
    bytesAt_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok L he₄ hR hy) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, o₅⟩ =>
    ⟨he₅, ?_, ?_, (fB.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_), ?_, by rw [rd₅, rd₄],
      by rw [wr₅, wr₄]⟩
  · rw [g₅ _ (by decide) (by decide), h4₄]
  · rw [g₅ _ (by decide) (by decide), h5₄]
  · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
  · rw [o₅, hY₄, hB₄, ctxCiph_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb]

omit L in
/-- `r4` and `r5` the associated data and its length, and `Z` for none. -/
theorem aadLd_ok {s₀ s : State} (hk : Stk w s₀ s) {A : BitVec 32} {al : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (hal : al < 2 ^ 32) :
    ∃ s₁, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .cmp .r5 (imm 0)] s = some s₁ ∧ s₁.gpr .r4 = A ∧
      s₁.gpr .r5 = BitVec.ofNat 32 al ∧ s₁.z = decide (al = 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  obtain ⟨i0, v0⟩ := hk.at 0 (by decide) (show 4 * 0 = 0 from rfl)
  obtain ⟨i1, v1⟩ := hk.at 1 (by decide) (show 4 * 1 = 4 from rfl)
  refine ⟨_, by arun [i0, v0, i1, v1], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v0, eA]
  · simp [gpr_setReg, v1, eal]
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v1, eal, imm]
    rw [z_cmp hal (by decide)]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- `r4` and `r5` the data and its length. -/
theorem dataLd_ok {s₀ s : State} (hk : Stk w s₀ s) {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D)
    (en : stackArg s₀ 3 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12] s = some s₁ ∧ s₁.gpr .r4 = D ∧
      s₁.gpr .r5 = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  obtain ⟨i2, v2⟩ := hk.at 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  refine ⟨_, by arun [i2, v2, i3, v3], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2, eD]
  · simp [gpr_setReg, v3, en]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The associated data, formatted and chained. -/
theorem aad_ok {s₀ s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {y : Nat}
    (hy : y = 0 ∨ y = 112) (hk : Stk w s₀ s) {A : BitVec 32} {al : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (hal : al < 2 ^ 32) (hA : Buf w sp s A al) :
    WP isa (aad y) s (MacStep k w sp R q1 s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (bytesAt s.mem (State.addr w + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem (State.addr A) al)))) := by
  obtain ⟨s₁, run₁, h4₁, h5₁, hz, g₁, k₁⟩ := aadLd_ok hk eA eal hal
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hA₁ := hA.of_eq k₁.rd k₁.wr
  refine WP.ite (decide (al = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, by rw [k₁.mem]; exact Frame.refl _ _, ?_, k₁.rd, k₁.wr⟩
    simp only [k₁.mem, adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := by simpa using hf
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.seq (WP.mono (aadHead_ok L he₁ hR hy hA₁ (by omega_arith) hal h4₁ h5₁) fun s₂ A₂ => ?_)
    have hn1 : headLen al ≤ al := by unfold headLen; omega_arith
    have hT : al - headLen al ≠ 0 → Buf w sp s₂ (A + BitVec.ofNat 32 (headLen al)) (al - headLen al) :=
      fun e => (hA.sub (j := headLen al) (k := al - headLen al) (by omega_arith) (by omega_arith)).of_eq
        (by rw [A₂.rd, k₁.rd]) (by rw [A₂.wr, k₁.wr])
    refine WP.mono (absorbPad_ok L A₂.env hR hy hT (by omega_arith) A₂.r4 A₂.r5) fun s₃ A₃ =>
      ⟨A₃.env, by rw [← k₁.mem]; exact A₂.frame.trans A₃.frame, ?_, by rw [A₃.rd, A₂.rd, k₁.rd],
        by rw [A₃.wr, A₂.wr, k₁.wr]⟩
    have eT : bytesAt s₂.mem (State.addr (A + BitVec.ofNat 32 (headLen al))) (al - headLen al) =
        (bytesAt s.mem (State.addr A) al).drop (headLen al) := by
      rcases Nat.eq_zero_or_pos (al - headLen al) with e | e
      · rw [e, List.drop_eq_nil_of_le (by rw [length_bytesAt]; omega_arith)]; rfl
      · rw [hA.addr (j := headLen al) (by omega_arith), bytesAt_suffix _ _ hn1, buf_kept hA₁ (by omega_arith) A₂.frame,
          k₁.mem]
    rw [A₃.out, A₂.out, eT, ctxCiph_frame A₂.frame (k_macR L (by omega_arith)) hRb, k₁.mem, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end

end VG.Proof.AesCcm.Arm
