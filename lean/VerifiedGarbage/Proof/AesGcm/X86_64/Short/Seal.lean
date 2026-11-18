module

import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Small
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Gh
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
public import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Avx512

/-! ### `AesGcm.X86_64.Short.Ks`, which this module and modules that import it used -/

section

/-!
# AES-GCM's short path on x86-64: the keystream

Untrusted: everything here is checked by Lean. `keystream` encrypts the
counter blocks `J₀`, `inc₃₂(J₀)`, … four at a time in the lanes of `zmm3`
(`VaesZ.ctrsZ_ok`, `VaesZ.aesZ_ok`) and stores them at `K` (`keystream_ok`),
after `Stitch.setupC` (`Stitch.setupC_ok`) and the first half of
`StitchZ.setupZ` (`ctrZ_ok`) put the counters in the lanes of `zmm14`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Gcm.X86_64.StitchZ (shuf44_0 shuf44_1 shuf44_2 shuf44_3 paddd_two_two lane0_zlane lane1_zlane)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok aesZ_ok four ZFrame.of_keys blockAt_writeW_lane zmm_lane)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The first half of `StitchZ.setupZ`. -/
abbrev ctrZ : List Instr :=
  [.vop (.vbin .vpaddd .l256 .xmm13 .xmm14 .xmm15), .zop (.vshufi32x4 .xmm14 .xmm14 .xmm13 0x44),
   .vop (.vbin .vpaddd .l256 .xmm15 .xmm15 .xmm15), .zop (.vshufi32x4 .xmm15 .xmm15 .xmm15 0x44)]

/-- The four counters in the lanes of `zmm14`, from the two of `ymm14`, and 4
in each lane of `zmm15`. -/
theorem ctrZ_ok (s : State) (J : Block) (h14 : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 l J)
    (h15 : ∀ l < 2, s.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) :
    WP isa (.block ctrZ) s fun s' =>
      (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l J) ∧ (∀ l < 4, s'.zlane .xmm15 l = four) ∧
      ZFrame [.xmm13, .xmm14, .xmm15] s s' := by
  have c0 : s.xmm .xmm14 = Nat.repeat inc32 0 J := by
    have h := h14 0 (by decide); simp only [State.lane, ite_true] at h; exact h
  have c1 : s.ymmHi .xmm14 = Nat.repeat inc32 1 J := by
    have h := h14 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
  have i0 : s.xmm .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
    have h := h15 0 (by decide); simp only [State.lane, ite_true] at h; exact h
  have i1 : s.ymmHi .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
    have h := h15 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
  refine WP.mono (WP.zframe (is := ctrZ) (rs := [.xmm13, .xmm14, .xmm15]) (by decide)
    (Q := fun s' => (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l J) ∧ (∀ l < 4, s'.zlane .xmm15 l = four)) ?_)
    fun s' ⟨⟨a, b⟩, f⟩ => ⟨a, b, f⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, fun l hl => ?_⟩⟩
  all_goals simp only [VOp.exec]
  all_goals rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [lane0_zlane, lane1_zlane, State.zlane_setV_ne, zlane_vshufi32x4,
    VG.Proof.Gcm.X86_64.StitchZ.State.zlane_setV256, State.zlane_setV128, shuf44_0, shuf44_1, shuf44_2, shuf44_3, reduceCtorEq,
    ↓reduceIte, VBinOp.sse, Nat.one_ne_zero]
  all_goals simp only [State.zlane, State.lane, ite_true, ite_false, Nat.one_ne_zero,
    show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide]
  all_goals first
    | exact c0 | exact c1
    | (rw [c0, i0, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
    | (rw [c1, i1, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
    | (rw [i0]; exact paddd_two_two) | (rw [i1]; exact paddd_two_two)

/-- The end of a step: four keystream blocks stored at `rdx`. -/
theorem ksStore_ok (t : State) {a : Addr} (hrdx : t.gpr .rdx = a) (hw : InRegions t.wr a 64) :
    WP isa (.block [.vmovdqu32Store (at_ .rdx 0) .xmm3, .alu .add .rdx (imm 64), .alu .sub .r9 (imm 1)]) t
      fun t' => t'.mem = t.mem.writeW a (t.zmm .xmm3) ∧ t'.gpr .rdx = a + BitVec.ofNat 64 64 ∧
        t'.gpr .r9 = t.gpr .r9 - 1 ∧ t'.zf = some (t.gpr .r9 - 1 == 0) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ ZKeep [] t t' := by
  have e : t.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int) = a := by
    rw [hrdx, BitVec.ofInt_natCast, BitVec.add_zero]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [imm, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      State.store512_eq, State.ea, e, hw, ite_true, Option.bind_some]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
  · simp [gpr_setReg, gpr_arithFlags, hrdx]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [zf_arithFlags, gpr_setReg, gpr_arithFlags]
  · intro r h₁ h₂; simp [gpr_setReg, gpr_arithFlags, h₁, h₂]

/-- A step of the keystream: four counter blocks encrypted and stored at `rdx`. -/
theorem ksStep_ok {nr : Nat} {w : List Byte} {J : Block} {K : Addr} {k : Nat} (t : State)
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (hK : Keys nr w t) (hrsi : t.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : t.gpr .r10 = t.gpr .rdi + BitVec.ofNat 64 (16 * nr))
    (c14 : ∀ l < 4, t.zlane .xmm14 l = Nat.repeat inc32 (4 * k + l) J)
    (m0 : ∀ l < 4, t.zlane .xmm0 l = revMask) (i15 : ∀ l < 4, t.zlane .xmm15 l = four)
    (hrdx : t.gpr .rdx = K + BitVec.ofNat 64 (64 * k)) (hw : InRegions t.wr (K + BitVec.ofNat 64 (64 * k)) 64) :
    WP isa ksBody t fun t' =>
      (∀ l < 4, t'.zlane .xmm14 l = Nat.repeat inc32 (4 * (k + 1) + l) J) ∧
      (∀ l < 4, blockAt t'.mem (K + BitVec.ofNat 64 (64 * k) + BitVec.ofNat 64 (16 * l)) =
        aesWith nr w (Nat.repeat inc32 (4 * k + l) J)) ∧
      Frame [⟨K + BitVec.ofNat 64 (64 * k), 64⟩] t.mem t'.mem ∧
      t'.gpr .rdx = K + BitVec.ofNat 64 (64 * (k + 1)) ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.zf = some (t.gpr .r9 - 1 == 0) ∧ (∀ r, r ≠ .rdx → r ≠ .r9 → t'.gpr r = t.gpr r) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ ZKeep [.xmm3, .xmm13, .xmm14] t t' := by
  refine WP.seq (WP.mono (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) [.xmm3] t J (4 * k) (by decide)
    (by decide) c14 m0 i15) fun t₁ ⟨e₁, c₁, f₁⟩ => ?_)
  refine WP.seq (WP.mono (aesZ_ok .xmm13 [.xmm3] (by decide) (by decide) hnr (fun _ => []) [] (by simp)
    (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩) (fun _ _ _ _ _ => trivial)
    t₁ (ZFrame.of_keys hK f₁) trivial (by rw [f₁.gpr, hrsi]) (by rw [f₁.gpr, hr10]))
    fun t₂ ⟨e₂, _, f₂⟩ => ?_)
  have hrdx₂ : t₂.gpr .rdx = K + BitVec.ofNat 64 (64 * k) := by rw [f₂.gpr, f₁.gpr, hrdx]
  refine WP.mono (ksStore_ok t₂ hrdx₂ (by rw [f₂.wr, f₁.wr]; exact hw))
    fun t' ⟨m', d', r9', z', g', rd', wr', k'⟩ => ?_
  have hm₂ : t₂.mem = t.mem := by rw [f₂.mem, f₁.mem]
  have g₂ : t₂.gpr = t.gpr := by rw [f₂.gpr, f₁.gpr]
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_, ?_, by rw [r9', g₂], by rw [z', g₂],
    fun r h₁ h₂ => by rw [g' r h₁ h₂, g₂], by rw [rd', f₂.rd, f₁.rd], by rw [wr', f₂.wr, f₁.wr], ?_⟩
  · rw [k' _ (by simp) l hl, f₂.zlane _ (by decide) l hl, c₁ l hl]
    simp only [List.length_singleton]
    rw [show 4 * k + 4 * 1 + l = 4 * (k + 1) + l by omega_arith]
  · rw [m', blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl]
    refine (aesWith_eq nr _ _ _ ?_).symm
    rw [e₂ .xmm3 (List.mem_singleton_self _) l hl]
    have := e₁ 0 (by decide) l hl
    simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at this
    rw [this]
  · rw [m', hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [d', show 64 * (k + 1) = 64 * k + 64 by omega_arith, ← ofNat_add_ofNat, BitVec.add_assoc]
  · intro r hr l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k' r (by simp) l hl, f₂.zlane r (by simp [hr.1, hr.2.1]) l hl, f₁.zlane r (by simp [hr.1, hr.2.2]) l hl]

/-- `Stitch.setupC` keeps the upper lanes of the registers it does not write. -/
theorem setupC_hi (s : State) (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block VG.Impl.Gcm.X86_64.Stitch.setupC) s fun s' =>
      ∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → s'.zmmHi r = s.zmmHi r := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; obtain ⟨x, hx, h⟩ := hy; exact ⟨x, List.mem_append_right _ hx, h⟩
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; obtain ⟨x, hx, h⟩ := hc; exact ⟨x, List.mem_append_right _ hx, h⟩
  apply WP.of_runBlock
  simp only [VG.Impl.Gcm.X86_64.Stitch.setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
    runBlock_nil, exec, VOp.exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg,
    State.load128, State.lane, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  intro r h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- A register's four lanes, from its lower two and its upper half. -/
theorem zlane_of {s t : State} {r : XReg} (hl : ∀ l < 2, t.lane r l = s.lane r l) (hh : t.zmmHi r = s.zmmHi r) :
    ∀ l < 4, t.zlane r l = s.zlane r l := fun l _ => by
  simp only [State.zlane]
  split
  · exact hl l (by omega_arith)
  · rw [hh]

/-- `ksSetup`, from `W`, the key context and the state of the short path. -/
theorem ksSetup_ok {Ctx W SP : Addr} {nr nc : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hR : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 nr)
    (hnc : s.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 nc) (hnc32 : nc < 32) (hnr : nr ≤ 14)
    (m0 : ∀ l < 4, s.zlane .xmm0 l = revMask) :
    WP isa (.block ksSetup) s fun t =>
      (∀ l < 4, t.zlane .xmm14 l = Nat.repeat inc32 l (blockAt s.mem (W + BitVec.ofNat 64 16))) ∧
      (∀ l < 4, t.zlane .xmm15 l = four) ∧ (∀ l < 4, t.zlane .xmm0 l = revMask) ∧
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 nr ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * nr) ∧
      t.gpr .rdx = W + BitVec.ofNat 64 1024 ∧ t.gpr .r9 = BitVec.ofNat 64 ((nc + 4) / 4) ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm2, .xmm13, .xmm14, .xmm15] s t := by
  have r176 := he.perm.wR (d := 176) (n := 8) (by decide)
  have r280 := he.perm.wR (d := 280) (n := 8) (by decide)
  rw [show ksSetup = ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14),
      .mov .rcx (.reg .r14)] ++ ptr .r8 .r15 kO) ++ (VG.Impl.Gcm.X86_64.Stitch.setupC ++
      (ctrZ ++ [.mov .r9 (.mem (at_ .r15 ncO)), .alu .add .r9 (imm 4), .shift .shr .r9 2])) from rfl,
    WP.block_append_iff]
  obtain ⟨s₁, run₁, di₁, si₁, dx₁, cx₁, r8₁, g₁, m₁, rd₁, wr₁, xmm₁, ymm₁, zmm₁⟩ : ∃ s₁, runBlock isa
      ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14),
      .mov .rcx (.reg .r14)] ++ ptr .r8 .r15 kO) s = some s₁ ∧ s₁.gpr .rdi = Ctx ∧
      s₁.gpr .rsi = BitVec.ofNat 64 nr ∧ s₁.gpr .rdx = W + BitVec.ofNat 64 16 ∧ s₁.gpr .rcx = W + BitVec.ofNat 64 16 ∧
      s₁.gpr .r8 = W + BitVec.ofNat 64 1024 ∧
      (∀ r, r ∉ [Reg.rcx, .rdx, .rsi, .rdi, .r8] → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.xmm = s.xmm ∧ s₁.ymmHi = s.ymmHi ∧ s₁.zmmHi = s.zmmHi := by
    refine ⟨_, by xrun [he.r15, r176, kO], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, he.r13]
    · simp [gpr_setReg, gpr_arithFlags, he.r15, hR]
    · simp [gpr_setReg, gpr_arithFlags, he.r14]
    · simp [gpr_setReg, gpr_arithFlags, he.r14]
    · simp [gpr_setReg, gpr_arithFlags, he.r15]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask := fun l hl => by
    have := m0 l (by omega_arith)
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;>
      simpa [State.zlane, State.lane, g₁, xmm₁, ymm₁] using this
  have w16 : InRegions s₁.wr (W + BitVec.ofNat 64 16) 16 := by rw [wr₁]; exact he.perm.wW (by decide)
  refine WP.mono (VG.Proof.AesGcm.X86_64.WP.forall_det (P := fun (_ : Unit) => True)
    (VG.Proof.Gcm.X86_64.Stitch.setupC_ok s₁ l0 (by rw [cx₁]; exact w16) (by rw [dx₁]; exact w16))
    fun _ _ => setupC_hi s₁ (by rw [cx₁]; exact w16) (by rw [dx₁]; exact w16))
    fun s₂ ⟨⟨_, _, c14, i15, r10₂, _, rdx₂, g₂, l₂, m₂, rd₂, wr₂⟩, hi₂⟩ => ?_
  replace hi₂ := hi₂ () trivial
  have z₂ : ∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 4, s₂.zlane r l = s.zlane r l :=
    fun r h₁ h₂ h₃ h₄ l hl => by
      rw [zlane_of (l₂ r h₁ h₂ h₃ h₄) (hi₂ r h₁ h₂ h₃ h₄) l hl]
      simp only [State.zlane, State.lane, xmm₁, ymm₁, zmm₁]
  rw [m₁, dx₁] at c14
  rw [si₁, di₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at r10₂
  rw [r8₁] at rdx₂
  rw [WP.block_append_iff]
  refine WP.mono (ctrZ_ok s₂ _ c14 i15) fun s₃ ⟨c14₃, i15₃, f₃⟩ => ?_
  have r15₃ : s₃.gpr .r15 = W := by
    rw [f₃.gpr, g₂ _ (by decide) (by decide) (by decide), g₁ _ (by simp), he.r15]
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, m₂, m₁]
  have rd₃ : s₃.rd = s.rd := by rw [f₃.rd, rd₂, rd₁]
  have wr₃ : s₃.wr = s.wr := by rw [f₃.wr, wr₂, wr₁]
  apply WP.of_runBlock
  have gk : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s₃.gpr r = s₁.gpr r := fun r h₁ h₂ h₃ => by
    rw [f₃.gpr, g₂ r h₁ h₂ h₃]
  refine ⟨_, by xrun [r15₃, m₃, rd₃, wr₃, r280, ncO], ?_⟩
  refine ⟨fun l hl => c14₃ l hl, fun l hl => i15₃ l hl, fun l hl => ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_,
    m₃, rd₃, wr₃, fun r hr l hl => ?_⟩
  · show s₃.zlane .xmm0 l = revMask
    rw [f₃.zlane _ (by decide) l hl, z₂ _ (by decide) (by decide) (by decide) (by decide) l hl, m0 l hl]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false]
    rw [gk _ (by decide) (by decide) (by decide), di₁]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false]
    rw [gk _ (by decide) (by decide) (by decide), si₁]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false]
    rw [f₃.gpr, r10₂]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ite_false]
    rw [f₃.gpr, rdx₂]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, hnc]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat, shr2 _ (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr.2.2.2.2.2.2.1, ite_false]
    rw [gk r hr.1 hr.2.2.1 hr.2.2.2.2.2.2.2, g₁ r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1])]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show s₃.zlane r l = s.zlane r l
    rw [f₃.zlane _ (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]) l hl, z₂ _ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 l hl]

/-- The keystream, `⌈(nc + 1) / 4⌉` groups of four blocks from `J₀` (at the
state's start), at `K = W + 1024`. -/
theorem keystream_ok {Ctx W SP : Addr} {nr nc : Nat} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
    (hR : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 nr)
    (hnc : s.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 nc) (hnc32 : nc < 32)
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (m0 : ∀ l < 4, s.zlane .xmm0 l = revMask) :
    WP isa keystream s fun t =>
      (∀ b < 4 * ((nc + 4) / 4), blockAt t.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * b)) =
        ciphOf s.mem Ctx nr (Nat.repeat inc32 b (blockAt s.mem (W + BitVec.ofNat 64 16)))) ∧
      Frame [⟨W + BitVec.ofNat 64 1024, 512⟩] s.mem t.mem ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm2, .xmm3, .xmm13, .xmm14, .xmm15] s t ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) := by
  have hnr14 : nr ≤ 14 := by omega_arith
  refine WP.seq (WP.mono (ksSetup_ok s he hR hnc hnc32 hnr14 m0)
    fun s₁ ⟨c14, i15, m0₁, di₁, si₁, r10₁, dx₁, r9₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hnk : 1 ≤ (nc + 4) / 4 ∧ (nc + 4) / 4 ≤ 8 := by omega_arith
  generalize (nc + 4) / 4 = nk at r9₁ hnk ⊢
  have hwK : ∀ k < nk, InRegions s.wr (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (64 * k)) 64 := fun k hk => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]; exact he.perm.wW (by omega_arith)
  generalize hK : W + BitVec.ofNat 64 1024 = K at dx₁ hwK ⊢
  generalize hJ : blockAt s.mem (W + BitVec.ofNat 64 16) = J at c14 ⊢
  generalize hw : bytesAt s.mem Ctx (16 * (nr + 1)) = w
  have hcw : ciphOf s.mem Ctx nr = aesWith nr w := by rw [← hw]
  rw [hcw]
  -- Writes in `K` leave the key schedule.
  have keys : ∀ t : State, Frame [⟨K, 512⟩] s.mem t.mem → t.gpr .rdi = Ctx → t.rd = s.rd → t.wr = s.wr →
      Keys nr w t := fun t f di rd wr =>
    ⟨by rw [di, ← hw]; exact (bytesAt_frame f (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [← hK]
        exact (L.cw'.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Lay.wSub (by decide))) (by omega_arith)).symm,
      hnr14, fun j hj => by
        rw [rd, wr, di, BitVec.ofInt_natCast]; exact he.perm.ctxR (by omega_arith)⟩
  refine WP.loop (M := isa) (body := ksBody) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ k, m = nk - k ∧ k < nk ∧
      (∀ l < 4, t.zlane .xmm14 l = Nat.repeat inc32 (4 * k + l) J) ∧ (∀ l < 4, t.zlane .xmm15 l = four) ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 nr ∧
      t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * nr) ∧ t.gpr .rdx = K + BitVec.ofNat 64 (64 * k) ∧
      t.gpr .r9 = BitVec.ofNat 64 (nk - k) ∧
      (∀ b < 4 * k, blockAt t.mem (K + BitVec.ofNat 64 (16 * b)) = aesWith nr w (Nat.repeat inc32 b J)) ∧
      Frame [⟨K, 512⟩] s.mem t.mem ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm2, .xmm3, .xmm13, .xmm14, .xmm15] s t) ?_ (nk - 0) s₁
    ⟨0, rfl, by omega_arith, fun l hl => by rw [c14 l hl]; simp, i15, m0₁, di₁, si₁, r10₁, by rw [dx₁]; simp,
      r9₁, fun b hb => absurd hb (by omega_arith), by rw [m₁]; exact Frame.refl _ _, g₁, rd₁, wr₁,
      z₁.mono (by simp)⟩
  rintro m t ⟨k, rfl, hk, c14t, i15t, m0t, dit, sit, r10t, dxt, r9t, bt, ft, gt, rdt, wrt, zt⟩
  refine WP.mono (ksStep_ok t hnr (keys t ft dit rdt wrt) sit (by rw [r10t, dit]) c14t m0t i15t dxt
    (by rw [wrt]; exact hwK k hk))
    fun t' ⟨c14', bk', f', dx', r9', zf', g', rd', wr', z'⟩ => ?_
  have hr9 : t.gpr .r9 - 1 = BitVec.ofNat 64 (nk - (k + 1)) := by
    rw [r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub (by omega_arith) (by omega_arith)]; congr 1
  have f'' : Frame [⟨K, 512⟩] s.mem t'.mem := ft.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base K (by omega_arith)⟩)
  have bt' : ∀ b < 4 * (k + 1), blockAt t'.mem (K + BitVec.ofNat 64 (16 * b)) = aesWith nr w (Nat.repeat inc32 b J) := by
    intro b hb
    by_cases hb' : b < 4 * k
    · rw [← bt b hb']
      exact blockAt_frame f' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint K (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
    · have := bk' (b - 4 * k) (by omega_arith)
      rwa [BitVec.add_assoc, ofNat_add_ofNat, show 64 * k + 16 * (b - 4 * k) = 16 * b by omega_arith,
        show 4 * k + (b - 4 * k) = b by omega_arith] at this
  have gt' : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] → t'.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g' r hr.2.2.1 hr.2.2.2.2.2.2.1, gt r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]
  have zt' : ZKeep [.xmm2, .xmm3, .xmm13, .xmm14, .xmm15] s t' := zt.trans (z'.mono (by simp))
  have m0' : ∀ l < 4, t'.zlane .xmm0 l = revMask := fun l hl => by rw [z' _ (by decide) l hl, m0t l hl]
  have hz : t'.zf = some (decide (nk - k = 1)) := by
    rw [zf', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (a := nk - k) (b := 1) (by omega_arith)
      (by omega_arith)]
  by_cases he' : k + 1 = nk
  · left
    refine ⟨by simp [eval, hz]; omega_arith, fun b hb => ?_, f'', gt', by rw [rd', rdt], by rw [wr', wrt], zt', m0'⟩
    rw [bt' b (by omega_arith)]
  · right
    refine ⟨by simp [eval, hz]; omega_arith, nk - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, c14',
      fun l hl => by rw [z' _ (by decide) l hl, i15t l hl], m0', by rw [g' _ (by decide) (by decide), dit],
      by rw [g' _ (by decide) (by decide), sit], by rw [g' _ (by decide) (by decide), r10t], dx',
      by rw [r9', hr9], bt', f'', gt', by rw [rd', rdt], by rw [wr', wrt], zt'⟩

end VG.Proof.AesGcm.X86_64.Short

end

end

/-! ### `AesGcm.X86_64.Short.Bytes`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Short.Xor`, which this module and modules that import it used -/

section

/-!
# AES-GCM's short path on x86-64: the text

Untrusted: everything here is checked by Lean. `xorText g` XORs the `rcx`
bytes at `rsi` with those at `rdx` (the keystream), in place, and if `g` also
writes the result at `rdi`: 16 bytes at a time through `xmm4`, then one at a
time (`xorText_ok`); the three buffers do not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)

/-- Writes to disjoint regions commute. -/
theorem writeBytes_comm (m : Mem) (p q : Addr) (xs ys : List Byte)
    (h : (⟨p, xs.length⟩ : Region).Disjoint ⟨q, ys.length⟩) :
    writeBytes (writeBytes m p xs) q ys = writeBytes (writeBytes m q ys) p xs := by
  funext a
  simp only [writeBytes]
  by_cases h₁ : (a - p).toNat < xs.length <;> by_cases h₂ : (a - q).toNat < ys.length <;>
    simp only [h₁, h₂, ite_true, ite_false]
  exact absurd (show Region.Contains ⟨q, ys.length⟩ a 1 by simp only [Region.Contains]; omega_arith)
    (h a (by simp only [Region.Contains]; omega_arith))

/-- The bytes at `S` XORed with those at `K`. -/
def xb (m : Mem) (S K : Addr) (n : Nat) : List Byte := List.zipWith (· ^^^ ·) (bytesAt m S n) (bytesAt m K n)

theorem length_xb (m : Mem) (S K : Addr) (n : Nat) : (xb m S K n).length = n := by
  simp [xb, length_bytesAt]

theorem xb_add (m : Mem) (S K : Addr) (a b : Nat) :
    xb m S K (a + b) = xb m S K a ++ xb m (S + BitVec.ofNat 64 a) (K + BitVec.ofNat 64 a) b := by
  simp only [xb, bytesAt_add]
  rw [List.zipWith_append (by rw [length_bytesAt, length_bytesAt])]

theorem xb_succ (m : Mem) (S K : Addr) (i : Nat) :
    xb m S K (i + 1) = xb m S K i ++ [m (S + BitVec.ofNat 64 i) ^^^ m (K + BitVec.ofNat 64 i)] := by
  rw [xb_add]; simp [xb, bytesAt]

/-- What `xorText g` writes: `xs` at `S`, and if `g` at `D` too. -/
def xw (g : Bool) (m : Mem) (S D : Addr) (xs : List Byte) : Mem :=
  if g then writeBytes (writeBytes m S xs) D xs else writeBytes m S xs

/-- A 16-byte store of the XOR of two 16-byte values loaded. -/
theorem writeW_xor128 (m src : Mem) (a b c : Addr) :
    m.writeW a (src.readW b 128 ^^^ src.readW c 128) =
      writeBytes m a (List.zipWith (· ^^^ ·) (bytesAt src b 16) (bytesAt src c 16)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (128 / 8)) (BitVec.setWidth 128 (src.read b (128 / 8)) ^^^
      BitVec.setWidth 128 (src.read c (128 / 8)))) = src.read b 16 ^^^ src.read c 16 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read src b (List.mem_range.mp hj),
    Mem.extractLsb'_read src c (List.mem_range.mp hj)]

/-- The 16-byte loop's body. -/
abbrev xor16Body (g : Bool) : List Instr :=
  [.vmovdquLoad .l128 .xmm4 srcB, .vbinLoad .vpxor .l128 .xmm4 .xmm4 kB, .vmovdquStore .l128 srcB .xmm4] ++
    (if g then [.vmovdquStore .l128 dstB .xmm4] else []) ++ [.alu .add .r10 (imm 16), .alu .cmp .r10 (.reg .r8)]

theorem xor16Step_ok (g : Bool) (s : State) {S K D : Addr} {i k : Nat} (hs : s.gpr .rsi = S)
    (hk : s.gpr .rdx = K) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hk8 : s.gpr .r8 = BitVec.ofNat 64 k)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 16) (r₂ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 16)
    (w₁ : InRegions s.wr (S + BitVec.ofNat 64 i) 16) (w₂ : g → InRegions s.wr (D + BitVec.ofNat 64 i) 16) :
    ∃ s', runBlock isa (xor16Body g) s = some s' ∧
      s'.mem = xw g s.mem (S + BitVec.ofNat 64 i) (D + BitVec.ofNat 64 i)
        (xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) 16) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 16 ∧
      s'.zf = some (BitVec.ofNat 64 i + 16 - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [.xmm4] s s' := by
  obtain e₁ := ea_idx s .rsi hs hi
  obtain e₂ := ea_idx s .rdx hk hi
  obtain e₃ := ea_idx s .rdi hd hi
  cases g
  · refine ⟨_, by
      simp only [xor16Body, srcB, dstB, kB, imm, List.cons_append, List.nil_append, Bool.false_eq_true,
        ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load128,
        State.store128, State.ea, State.setV, State.lane, e₁, e₂, r₁, r₂, w₁, ite_true, Option.map_some,
        Option.bind_some]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, xw, Bool.false_eq_true, ite_false, xb]
      exact writeW_xor128 _ _ _ _ _
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk8]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
    · intro r hr l hl
      simp only [List.mem_singleton] at hr
      simp only [zlane_setReg, zlane_arithFlags]
      simp only [State.zlane, State.lane, hr, ite_false]
  · have w₂' := w₂ rfl
    refine ⟨_, by
      simp only [xor16Body, srcB, dstB, kB, imm, List.cons_append, List.nil_append, ite_true,
        runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load128,
        State.store128, State.ea, State.setV, State.lane, e₁, e₂, e₃, r₁, r₂, w₁, w₂', ite_true,
        Option.map_some, Option.bind_some]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, xw, ite_true, xb]
      rw [show ∀ a b : BitVec 128, VBinOp.vpxor.sse.eval a b = a ^^^ b from fun _ _ => rfl,
        writeW_xor128, writeW_xor128]
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk8]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
    · intro r hr l hl
      simp only [List.mem_singleton] at hr
      simp only [zlane_setReg, zlane_arithFlags]
      simp only [State.zlane, State.lane, hr, ite_false]

/-- An 8-byte store of the XOR of two 8-byte values loaded. -/
theorem writeW_xor64 (m src : Mem) (a b c : Addr) :
    m.writeW a (src.readW b 64 ^^^ src.readW c 64) =
      writeBytes m a (List.zipWith (· ^^^ ·) (bytesAt src b 8) (bytesAt src c 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (64 / 8)) (BitVec.setWidth 64 (src.read b (64 / 8)) ^^^
      BitVec.setWidth 64 (src.read c (64 / 8)))) = src.read b 8 ^^^ src.read c 8 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read src b (List.mem_range.mp hj),
    Mem.extractLsb'_read src c (List.mem_range.mp hj)]

/-- A 4-byte store of the XOR of two 4-byte values loaded. -/
theorem writeW_xor32 (m src : Mem) (a b c : Addr) :
    m.writeW a (src.readW b 32 ^^^ src.readW c 32) =
      writeBytes m a (List.zipWith (· ^^^ ·) (bytesAt src b 4) (bytesAt src c 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (32 / 8)) (BitVec.setWidth 32 (src.read b (32 / 8)) ^^^
      BitVec.setWidth 32 (src.read c (32 / 8)))) = src.read b 4 ^^^ src.read c 4 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read src b (List.mem_range.mp hj),
    Mem.extractLsb'_read src c (List.mem_range.mp hj)]

/-- `xorWord g w`: eight (if `w`) or four bytes XORed. -/
theorem xorWord_ok (g w : Bool) (s : State) {S K D : Addr} {i : Nat} (hs : s.gpr .rsi = S)
    (hk : s.gpr .rdx = K) (hd : s.gpr .rdi = D) (hi : s.gpr .r10 = BitVec.ofNat 64 i)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) (if w then 8 else 4))
    (r₂ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) (if w then 8 else 4))
    (w₁ : InRegions s.wr (S + BitVec.ofNat 64 i) (if w then 8 else 4))
    (w₂ : g → InRegions s.wr (D + BitVec.ofNat 64 i) (if w then 8 else 4)) :
    ∃ s', runBlock isa (xorWord g w) s = some s' ∧
      s'.mem = xw g s.mem (S + BitVec.ofNat 64 i) (D + BitVec.ofNat 64 i)
        (xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 (i + if w then 8 else 4) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ZKeep [] s s' := by
  obtain e₁ := ea_idx s .rsi hs hi
  obtain e₂ := ea_idx s .rdx hk hi
  obtain e₃ := ea_idx s .rdi hd hi
  obtain w₁' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) (if w then 8 else 4) := by
    obtain ⟨x, hx, hc⟩ := w₁; exact ⟨x, List.mem_append_right _ hx, hc⟩
  cases w <;> cases g <;> simp only [Bool.false_eq_true, ite_true, ite_false] at r₁ r₂ w₁ w₁' w₂ ⊢
  · refine ⟨_, by xrun [xorWord, srcB, kB, e₁, e₂, r₁, r₂, w₁], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, Bool.false_eq_true, ite_false, xb]
      rw [← writeW_xor32]; congr 1; simp
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · have w₂' := w₂ trivial
    refine ⟨_, by xrun [xorWord, srcB, kB, dstB, e₁, e₂, e₃, r₁, r₂, w₁, w₂'], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, ite_true, xb]
      rw [← writeW_xor32, ← writeW_xor32]; congr 1 <;> simp
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · refine ⟨_, by xrun [xorWord, srcB, kB, e₁, e₂, r₁, r₂, w₁], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, Bool.false_eq_true, ite_false, xb]
      rw [← writeW_xor64]
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · have w₂' := w₂ trivial
    refine ⟨_, by xrun [xorWord, srcB, kB, dstB, e₁, e₂, e₃, r₁, r₂, w₁, w₂'], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, xw, ite_true, xb]
      rw [← writeW_xor64, ← writeW_xor64]
    · simp only [gpr_setReg, ite_true, hi]; exact (BitVec.ofNat_add _ _).symm
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by simp [bytesAt]

theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  have := writeBytes_snoc m a [] b (by decide)
  rw [List.nil_append, writeBytes_nil] at this
  rw [this]; simp

/-- The byte loop's body. -/
abbrev xor1Body (g : Bool) : List Instr :=
  ([.movzx8 .rax srcB, .movzx8 .r9 kB, .alu .xor .rax (.reg .r9), .store8 srcB .rax] : List Instr) ++
    (if g then ([.store8 dstB .rax] : List Instr) else ([] : List Instr)) ++ ([.alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)] : List Instr)

theorem xor1Step_ok (g : Bool) (s : State) {S K D : Addr} {i n : Nat} (hs : s.gpr .rsi = S)
    (hk : s.gpr .rdx = K) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r₁ : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (r₂ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1)
    (w₁ : InRegions s.wr (S + BitVec.ofNat 64 i) 1) (w₂ : g → InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa (xor1Body g) s = some s' ∧
      s'.mem = xw g s.mem (S + BitVec.ofNat 64 i) (D + BitVec.ofNat 64 i)
        [s.mem (S + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)] ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ZKeep [] s s' := by
  obtain e₁ := ea_idx s .rsi hs hi
  obtain e₂ := ea_idx s .rdx hk hi
  obtain e₃ := ea_idx s .rdi hd hi
  obtain w₁' : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w₁; exact ⟨x, List.mem_append_right _ hx, hc⟩
  cases g
  · refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, BitVec.reduceSignExtend, xor1Body, srcB, dstB, kB,
        imm, List.cons_append, List.nil_append, Bool.false_eq_true, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, ite_true, ite_false, e₁, e₂, r₁, r₂, w₁]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, setWidth8_xor, xw, Bool.false_eq_true, ite_false, writeW8_eq]
    · simp [gpr_setReg, hi]
    · simp [hi, hn]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]
  · have w₂' := w₂ rfl
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, BitVec.reduceSignExtend, xor1Body, srcB, dstB, kB,
        imm, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
        wr_arithFlags, ite_true, ite_false, e₁, e₂, e₃, r₁, r₂, w₁, w₂']
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, fun _ _ _ _ => rfl⟩
    · simp only [mem_setReg, mem_arithFlags, setWidth8_xor, xw, ite_true, writeW8_eq]
    · simp [gpr_setReg, hi]
    · simp [hi, hn]
    · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]

/-- What `xorText g` needs: `n` bytes at `S` (read and written), at `K` (read)
and, if `g`, at `D` (written), apart. -/
structure XorPre (g : Bool) (s : State) (S K D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdx : s.gpr .rdx = K
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  lt : n < 2 ^ 63
  rS : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  rK : Covers [⟨K, n⟩] (s.rd ++ s.wr)
  wS : Covers [⟨S, n⟩] s.wr
  wD : g → Covers [⟨D, n⟩] s.wr
  dSK : (⟨S, n⟩ : Region).Disjoint ⟨K, n⟩
  dSD : g → (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩
  dKD : g → (⟨K, n⟩ : Region).Disjoint ⟨D, n⟩

/-- What `xorText g` leaves. -/
def XorPost (g : Bool) (s : State) (S K D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = xw g s.mem S D (xb s.mem S K n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    ZKeep [.xmm4] s s'

theorem xw_nil (g : Bool) (m : Mem) (S D : Addr) : xw g m S D [] = m := by
  cases g <;> simp [xw, writeBytes_nil]

theorem xw_frame (g : Bool) (m : Mem) (S D : Addr) (xs : List Byte) :
    Frame [⟨S, xs.length⟩, ⟨D, xs.length⟩] m (xw g m S D xs) := by
  cases g
  · exact (writeBytes_frame' m rfl).mono (by simp)
  · exact ((writeBytes_frame' m rfl).mono (by simp)).trans ((writeBytes_frame' _ rfl).mono (by simp))

/-- The bytes from `i` on of a buffer apart from `D`'s are as they were. -/
theorem xw_bytesAt {g : Bool} {m : Mem} {S D P : Addr} {xs : List Byte} {n i k : Nat} (hlen : xs.length = i)
    (hik : i + k ≤ n) (hn : n < 2 ^ 63)
    (hS : (⟨P + BitVec.ofNat 64 i, k⟩ : Region).Disjoint ⟨S, i⟩)
    (hD : g → (⟨P + BitVec.ofNat 64 i, k⟩ : Region).Disjoint ⟨D, i⟩) :
    bytesAt (xw g m S D xs) (P + BitVec.ofNat 64 i) k = bytesAt m (P + BitVec.ofNat 64 i) k := by
  cases g
  · exact bytesAt_frame (writeBytes_frame' m hlen) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hS) (by omega_arith)
  · refine bytesAt_frame (rs := [⟨S, i⟩, ⟨D, i⟩]) (((writeBytes_frame' m hlen).mono (by simp)).trans
      ((writeBytes_frame' _ hlen).mono (by simp))) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hS
    · exact hD rfl

theorem xw_append (g : Bool) (m : Mem) {S D : Addr} {n : Nat} (xs ys : List Byte) (hn : n < 2 ^ 63)
    (hxy : xs.length + ys.length ≤ n) (hd : g → (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) :
    xw g (xw g m S D xs) (S + BitVec.ofNat 64 xs.length) (D + BitVec.ofNat 64 xs.length) ys =
      xw g m S D (xs ++ ys) := by
  cases g
  · simp only [xw, Bool.false_eq_true, ite_false]
    exact writeBytes_append _ _ _ _ (by omega_arith)
  · simp only [xw, ite_true]
    rw [writeBytes_comm (writeBytes m S xs) D (S + BitVec.ofNat 64 xs.length) xs ys
      (((hd rfl).symm.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base S (by omega_arith))),
      writeBytes_append _ _ _ _ (by omega_arith), writeBytes_append _ _ _ _ (by omega_arith)]

theorem xorText_ok (g : Bool) (s : State) {S K D : Addr} {n : Nat} (h : XorPre g s S K D n) :
    WP isa (xorText g) s (XorPost g s S K D n) := by
  have hn63 := h.lt
  refine WP.seq (WP.mono (copySetup_ok s h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  -- The bytes from `i` on, at `S` and at `K`, after the first `i` written.
  obtain rdS : ∀ {xs : List Byte} {i k : Nat}, xs.length = i → i + k ≤ n →
      bytesAt (xw g s.mem S D xs) (S + BitVec.ofNat 64 i) k = bytesAt s.mem (S + BitVec.ofNat 64 i) k :=
    fun hl hik => xw_bytesAt hl hik hn63 (Offset.disjoint_base S (Nat.le_refl _) (by omega_arith))
      fun hg => ((h.dSD hg).sub_left (Offset.sub_base S hik)).sub_right (Region.sub_prefix (by omega_arith))
  obtain rdK : ∀ {xs : List Byte} {i k : Nat}, xs.length = i → i + k ≤ n →
      bytesAt (xw g s.mem S D xs) (K + BitVec.ofNat 64 i) k = bytesAt s.mem (K + BitVec.ofNat 64 i) k :=
    fun hl hik => xw_bytesAt hl hik hn63
      ((h.dSK.symm.sub_left (Offset.sub_base K hik)).sub_right (Region.sub_prefix (by omega_arith)))
      fun hg => ((h.dKD hg).sub_left (Offset.sub_base K hik)).sub_right (Region.sub_prefix (by omega_arith))
  -- After the 16-byte loop: the first `16 ⌊n / 16⌋` bytes.
  let q := n / 16
  obtain mid : WP isa (.ite .e (.block []) (.loop (.block (xor16Body g)) .ne)) s₁ fun t =>
      t.gpr .r10 = BitVec.ofNat 64 (16 * q) ∧ t.mem = xw g s.mem S D (xb s.mem S K (16 * q)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm4] s t := by
    refine WP.ite (decide (16 * q = 0)) (by simp only [eval, zf₁, q]) (fun hz => ?_) (fun hz => ?_)
    · have hq : 16 * q = 0 := of_decide_eq_true hz
      refine WP.block_nil ⟨by rw [r10₁, hq], by rw [m₁, hq]; simp [xb, bytesAt, xw_nil],
        fun r a b c d => g₁ r b d, rd₁, wr₁, z₁.mono (by simp)⟩
    · have hq : 0 < q := by have := of_decide_eq_false hz; omega_arith
      refine WP.loop (M := isa) (body := .block (xor16Body g)) (c := .ne)
        (fun (k : Nat) (t : State) => ∃ j, k = q - j ∧ j < q ∧ t.gpr .r10 = BitVec.ofNat 64 (16 * j) ∧
          t.mem = xw g s.mem S D (xb s.mem S K (16 * j)) ∧
          (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧
          t.gpr .r8 = BitVec.ofNat 64 (16 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ ZKeep [.xmm4] s t) ?_ (q - 0) _
        ⟨0, rfl, hq, by rw [r10₁], by rw [m₁]; simp [xb, bytesAt, xw_nil], fun r a b c d => g₁ r b d,
          r8₁, rd₁, wr₁, z₁.mono (by simp)⟩
      rintro k t ⟨j, rfl, hj, r10, mem, g', r8, rd, wr, z⟩
      obtain hj16 : 16 * j + 16 ≤ n := by omega_arith
      obtain gg := fun r (hr : r ∈ [Reg.rsi, .rdx, .rdi]) => g' r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      obtain ⟨t', run', mem', r10', zf', g'', rd', wr', z'⟩ := xor16Step_ok g t
        (by rw [gg .rsi (by simp), h.rsi]) (by rw [gg .rdx (by simp), h.rdx]) (by rw [gg .rdi (by simp), h.rdi])
        r10 r8
        (by rw [rd, wr]; exact in_of_covers16 h.rS hj16 (by omega_arith))
        (by rw [rd, wr]; exact in_of_covers16 h.rK hj16 (by omega_arith))
        (by rw [wr]; exact in_of_covers16 h.wS hj16 (by omega_arith))
        (fun hg => by rw [wr]; exact in_of_covers16 (h.wD hg) hj16 (by omega_arith))
      refine WP.of_runBlock ⟨t', run', ?_⟩
      obtain hlen : (xb s.mem S K (16 * j)).length = 16 * j := length_xb _ _ _ _
      obtain hsrc : xb t.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16 =
          xb s.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16 := by
        simp only [xb]; rw [mem, rdS hlen hj16, rdK hlen hj16]
      obtain hmem : t'.mem = xw g s.mem S D (xb s.mem S K (16 * (j + 1))) := by
        rw [mem', hsrc, mem, show 16 * (j + 1) = 16 * j + 16 by omega_arith, xb_add]
        have := xw_append g s.mem (xb s.mem S K (16 * j))
          (xb s.mem (S + BitVec.ofNat 64 (16 * j)) (K + BitVec.ofNat 64 (16 * j)) 16) hn63
          (by rw [length_xb, length_xb]; omega_arith) h.dSD
        rw [hlen] at this
        exact this
      obtain hz : t'.zf = some (decide (j + 1 = q)) := by
        rw [zf', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat, sub_beq (by omega_arith) (by omega_arith)]
        congr 1; simp only [decide_eq_decide]; omega_arith
      obtain gg' : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c d => by
        rw [g'' r d, g' r a b c d]
      obtain r10'' : t'.gpr .r10 = BitVec.ofNat 64 (16 * (j + 1)) := by
        rw [r10', show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]; congr 1
      by_cases he : j + 1 = q
      · left
        refine ⟨by simp [eval, hz, he], by rw [r10'', he], by rw [hmem, he], gg', by rw [rd', rd],
          by rw [wr', wr], z.trans z'⟩
      · right
        refine ⟨by simp [eval, hz, he], q - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, r10'', hmem, gg',
          by rw [g'' _ (by decide), r8], by rw [rd', rd], by rw [wr', wr], z.trans z'⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩ => ?_)
  -- The state after the first `i` bytes.
  let Mid : Nat → State → Prop := fun i t => t.gpr .r10 = BitVec.ofNat 64 i ∧
    t.mem = xw g s.mem S D (xb s.mem S K i) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    ZKeep [.xmm4] s t
  obtain regs : ∀ {t : State}, (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) →
      t.gpr .rsi = S ∧ t.gpr .rdx = K ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 n := fun g' =>
    ⟨by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rsi],
      by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rdx],
      by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rdi],
      by rw [g' _ (by decide) (by decide) (by decide) (by decide), h.rcx]⟩
  -- Eight or four bytes, through `rax`.
  obtain word : ∀ (w : Bool) {i : Nat} {t : State} {R : BitVec 64}, i + (if w then 8 else 4) ≤ n → Mid i t →
      t.gpr .r8 = R → WP isa (.block (xorWord g w)) t fun u => Mid (i + if w then 8 else 4) u ∧ u.gpr .r8 = R := by
    intro w i t R hik ⟨r10, mem, g', rd, wr, z⟩ hr8
    obtain ⟨hsi, hdx, hdi, -⟩ := regs g'
    obtain cov : ∀ {p : Addr} {rs : List Region}, Covers [⟨p, n⟩] rs →
        InRegions rs (p + BitVec.ofNat 64 i) (if w then 8 else 4) := fun hc =>
      hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hik (by omega_arith)⟩
    obtain ⟨t', run', mem', r10', g'', rd', wr', z'⟩ := xorWord_ok g w t hsi hdx hdi r10
      (by rw [rd, wr]; exact cov h.rS) (by rw [rd, wr]; exact cov h.rK) (by rw [wr]; exact cov h.wS)
      (fun hg => by rw [wr]; exact cov (h.wD hg))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    obtain hlen : (xb s.mem S K i).length = i := length_xb _ _ _ _
    obtain hsrc : xb t.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4) =
        xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4) := by
      simp only [xb]; rw [mem, rdS hlen hik, rdK hlen hik]
    obtain hmem : t'.mem = xw g s.mem S D (xb s.mem S K (i + if w then 8 else 4)) := by
      rw [mem', hsrc, mem, xb_add]
      have := xw_append g s.mem (xb s.mem S K i)
        (xb s.mem (S + BitVec.ofNat 64 i) (K + BitVec.ofNat 64 i) (if w then 8 else 4)) hn63
        (by rw [length_xb, length_xb]; omega_arith) h.dSD
      rw [hlen] at this
      exact this
    exact ⟨⟨r10', hmem, fun r a b c d => by rw [g'' r a d, g' r a b c d], by rw [rd', rd], by rw [wr', wr],
      z.trans (z'.mono (by simp))⟩, by rw [g'' _ (by decide) (by decide), hr8]⟩
  -- The bytes from `i < n` on, one at a time.
  obtain bytes : ∀ {i : Nat} {t : State}, i < n → Mid i t → WP isa (Impl.AesGcm.X86_64.Short.xorBytes g) t (XorPost g s S K D n) := by
    intro i₀ t₀ hi₀ ⟨r10₀, m₀, g₀, rd₀, wr₀, z₀⟩
    refine WP.loop (M := isa) (body := .block (xor1Body g)) (c := .ne)
      (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
        t.mem = xw g s.mem S D (xb s.mem S K i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        ZKeep [.xmm4] s t) ?_ (n - i₀) _ ⟨i₀, rfl, hi₀, r10₀, m₀, g₀, rd₀, wr₀, z₀⟩
    rintro k t ⟨i, rfl, hi, r10, mem, g', rd, wr, z⟩
    obtain ⟨hsi, hdx, hdi, hcx'⟩ := regs g'
    obtain ⟨t', run', mem', r10', zf', g'', rd', wr', z'⟩ := xor1Step_ok g t hsi hdx hdi r10 hcx'
      (by rw [rd, wr]; exact in_of_covers h.rS hi (by omega_arith))
      (by rw [rd, wr]; exact in_of_covers h.rK hi (by omega_arith))
      (by rw [wr]; exact in_of_covers h.wS hi (by omega_arith))
      (fun hg => by rw [wr]; exact in_of_covers (h.wD hg) hi (by omega_arith))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    obtain hlen : (xb s.mem S K i).length = i := length_xb _ _ _ _
    obtain hS1 := rdS hlen (show i + 1 ≤ n by omega_arith)
    obtain hK1 := rdK hlen (show i + 1 ≤ n by omega_arith)
    rw [bytesAt_one, bytesAt_one] at hS1 hK1
    obtain hmem : t'.mem = xw g s.mem S D (xb s.mem S K (i + 1)) := by
      rw [mem', mem, List.cons.inj hS1 |>.1, List.cons.inj hK1 |>.1, xb_succ]
      have := xw_append g s.mem (xb s.mem S K i)
        [s.mem (S + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)] hn63 (by rw [hlen]; simp; omega_arith) h.dSD
      rw [hlen] at this
      exact this
    obtain hz : t'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]
    obtain gg' : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → t'.gpr r = s.gpr r := fun r a b c d => by
      rw [g'' r a c d, g' r a b c d]
    obtain zk : ZKeep [.xmm4] s t' := z.trans (z'.mono (by simp))
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg', by rw [rd', rd], by rw [wr', wr], zk⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by rw [r10', succ_ofNat],
        hmem, gg', by rw [rd', rd], by rw [wr', wr], zk⟩
  -- `t`, the bytes left after the 16-byte loop, and the bits of `n` tested.
  obtain M₂ : Mid (16 * q) s₂ := ⟨r10₂, m₂, g₂, rd₂, wr₂, z₂⟩
  generalize ht : n % 16 = t
  obtain ht16 : t < 16 := by omega_arith
  obtain hn : n = 16 * q + t := by omega_arith
  obtain tst : ∀ (k : Nat), k < 16 → ∀ {i : Nat} {u : State}, Mid i u →
      WP isa (.block [.alu .test .rcx (imm k)]) u fun v => Mid i v ∧ v.zf = some (decide (t &&& k = 0)) := by
    intro k hk i u ⟨r10, m, g', rd, wr, z⟩
    obtain hcx : u.gpr .rcx = BitVec.ofNat 64 n := (regs g').2.2.2
    obtain hand : BitVec.ofNat 64 n &&& BitVec.ofNat 64 k = BitVec.ofNat 64 (t &&& k) := by
      apply BitVec.eq_of_toNat_eq
      obtain h1 : n &&& k = t &&& k := by
        obtain e := Nat.and_mod_two_pow (a := n) (b := k) (n := 4)
        rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (show k < 2 ^ 4 by omega_arith)),
          Nat.mod_eq_of_lt (show k < 2 ^ 4 by omega_arith), show 2 ^ 4 = 16 from rfl, ht] at e
        exact e
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith), ← h1, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega_arith))]
    obtain hz : (BitVec.ofNat 64 (t &&& k) == 0) = decide (t &&& k = 0) := by
      obtain hlt : t &&& k < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_left (by omega_arith)
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
      constructor
      · intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
        exact this
      · intro e; rw [e]; rfl
    apply WP.of_runBlock
    refine ⟨_, by xrun [hcx], ?_⟩
    refine ⟨⟨by simp only [gpr_arithFlags]; exact r10, by simp only [mem_arithFlags]; exact m,
      fun r a b c d => by simp [gpr_arithFlags, g' r a b c d],
      by simp only [rd_arithFlags]; exact rd, by simp only [wr_arithFlags]; exact wr, z.trans fun _ _ _ _ => rfl⟩, ?_⟩
    simp only [zf_arithFlags, imm_eq (show k < 2 ^ 31 by omega_arith), hand, hz]
  -- None left.
  refine WP.seq (WP.mono (tst 15 (by decide) M₂) fun s₃ ⟨M₃, zf₃⟩ => ?_)
  refine WP.ite (decide (t &&& 15 = 0)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : t = 0 := by
      have := of_decide_eq_true hz; revert this; revert ht16; generalize t = x; revert x; decide
    obtain ⟨-, m, g', rd, wr, z⟩ := M₃
    exact WP.block_nil ⟨by rw [m, show 16 * q = n by omega_arith], g', rd, wr, z⟩
  obtain hpos : 0 < t := by
    have := of_decide_eq_false hz; revert this; revert ht16; generalize t = x; revert x; decide
  -- Fewer than 4: one at a time.
  refine WP.seq (WP.mono (tst 12 (by decide) M₃) fun s₄ ⟨M₄, zf₄⟩ => ?_)
  refine WP.ite (decide (t &&& 12 = 0)) (by simp only [eval, zf₄]) (fun _ => bytes (by omega_arith) M₄) (fun hb => ?_)
  -- Eight bytes, if `t` has bit 8.
  refine WP.seq (WP.mono (tst 8 (by decide) M₄) fun s₅ ⟨M₅, zf₅⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u : State) => Mid (16 * q + (t &&& 8)) u)
    (WP.ite (decide (t &&& 8 = 0)) (by simp only [eval, zf₅]) (fun hb => ?_) (fun hb => ?_)) fun s₆ M₆ => ?_)
  · have h0 : t &&& 8 = 0 := of_decide_eq_true hb
    rw [h0, Nat.add_zero]; exact WP.block_nil M₅
  · have h8 : t &&& 8 = 8 := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    obtain h8le : 8 ≤ t := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    rw [h8]
    exact WP.mono (word true (R := s₅.gpr .r8) (by simp only [ite_true]; omega_arith) M₅ rfl) fun u hu => hu.1
  -- Four bytes, if `t` has bit 4.
  refine WP.seq (WP.mono (tst 4 (by decide) M₆) fun s₇ ⟨M₇, zf₇⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (u : State) => Mid (16 * q + (t &&& 8) + (t &&& 4)) u)
    (WP.ite (decide (t &&& 4 = 0)) (by simp only [eval, zf₇]) (fun hb => ?_) (fun hb => ?_)) fun s₈ M₈ => ?_)
  · have h0 : t &&& 4 = 0 := of_decide_eq_true hb
    rw [h0, Nat.add_zero]; exact WP.block_nil M₇
  · have h4 : t &&& 4 = 4 := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    obtain hle : (t &&& 8) + 4 ≤ t := by
      have := of_decide_eq_false hb
      revert this; revert ht16; generalize t = x; intro hx; revert x; decide
    rw [h4]
    exact WP.mono (word false (R := s₇.gpr .r8) (by simp only [Bool.false_eq_true, ite_false]; omega_arith) M₇ rfl)
      fun u hu => hu.1
  -- The last ones, if any, one at a time.
  obtain hsum : (t &&& 8) + (t &&& 4) + (t &&& 3) = t := by revert ht16; generalize t = x; revert x; decide
  refine WP.seq (WP.mono (tst 3 (by decide) M₈) fun s₉ ⟨M₉, zf₉⟩ => ?_)
  refine WP.ite (decide (t &&& 3 = 0)) (by simp only [eval, zf₉]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : t &&& 3 = 0 := of_decide_eq_true hz
    obtain ⟨-, m, g', rd, wr, z⟩ := M₉
    exact WP.block_nil ⟨by rw [m, show 16 * q + (t &&& 8) + (t &&& 4) = n by omega_arith], g', rd, wr, z⟩
  · have h3 : t &&& 3 ≠ 0 := of_decide_eq_false hz
    exact bytes (by omega_arith) M₉

end VG.Proof.AesGcm.X86_64.Short

end

end

/-!
# AES-GCM's short path on x86-64: the bytes

Untrusted: everything here is checked by Lean. What the short path's buffers
hold, as the specification's lists: the text XORed with the keystream blocks
at `K` is counter mode (`xb_gctr`), and the buffer `G` (zero blocks, the
additional data and the text each padded, the lengths block) has the blocks
`GHASH` absorbs (`gBlocks`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt blocks inc32 gctr zeros padLen ghashInput ofBytes toBytes)
open VG.Proof.Gcm (xorKs ksByte padded lensBlock)

theorem repeat_inc32_succ (b : Nat) (J : Block) : Nat.repeat inc32 (b + 1) J = Nat.repeat inc32 b (inc32 J) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [Nat.repeat] at ih ⊢; rw [ih]

/-- The `n` bytes at `D` XORed with the keystream at `K`, whose block `b` is
`CIPH(inc₃₂ᵇ⁺¹(J₀))` (`K` is after `K[0]`): counter mode from `inc₃₂(J₀)`. -/
theorem xb_gctr {m : Mem} {D K : Addr} {n : Nat} {ciph : Block → Block} {J : Block}
    (hK : ∀ b, 16 * b < n → blockAt m (K + BitVec.ofNat 64 (16 * b)) = ciph (Nat.repeat inc32 (b + 1) J)) :
    xb m D K n = gctr ciph (inc32 J) (bytesAt m D n) := by
  rw [Proof.Gcm.gctr_eq]
  refine Proof.Gcm.list_ext (by simp [xb, Proof.Gcm.length_xorKs, length_bytesAt]) fun i hi => ?_
  have hin : i < n := by simpa [xb, length_bytesAt] using hi
  rw [Proof.Gcm.getD_xorKs _ _ _ _ (by rw [length_bytesAt]; exact hin), Nat.zero_add]
  simp only [xb, List.getD_eq_getElem?_getD, List.getElem?_zipWith, bytesAt, List.getElem?_map,
    List.getElem?_range hin, Option.map_some, Option.getD_some]
  congr 1
  simp only [ksByte]
  rw [← repeat_inc32_succ, ← hK (i / 16) (by omega_using [hin]), Proof.Aes.toBytes_blockAt _ _ (by omega_using [] : i % 16 < 16),
    add_ofNat_ofNat, show 16 * (i / 16) + i % 16 = i by omega_using []]

theorem padLen_eq (x : Nat) : padLen x = 16 * nb16 x - x := by simp only [padLen, nb16]; omega_using []

/-- The additional data and the text, each padded to whole blocks, are
`ghashInput` padded. -/
theorem padded_layout (a c : List Byte) :
    a ++ zeros (16 * nb16 a.length - a.length) ++ c ++ zeros (16 * nb16 c.length - c.length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    simp [padded, ghashInput, padLen_eq, zeros, nb16]
  · rw [padded, Proof.Gcm.ghashInput_of_ne hc, padLen_eq, padLen_eq]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    congr 2
    simp only [nb16]; omega_using []

theorem ofBytes_zeros16 : ofBytes (zeros 16) = 0 := by decide

theorem blocks_zeros (k : Nat) : blocks (zeros (16 * k)) = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show zeros (16 * (k + 1)) = zeros (16 * k) ++ zeros 16 by
        rw [zeros, zeros, zeros, List.replicate_append_replicate, Nat.mul_succ],
      Proof.Gcm.blocks_append (by simp [Proof.Gcm.length_zeros]), ih,
      Proof.Gcm.blocks_single (Proof.Gcm.length_zeros 16), ofBytes_zeros16, List.replicate_succ']

/-- The blocks of `G`: the zero blocks, those of the additional data and the
text padded, and the lengths block. -/
theorem gBlocks (lead : Nat) (a c : List Byte) :
    blocks (zeros (16 * lead) ++ padded a c ++ lensBlock a.length c.length) =
      List.replicate lead 0 ++ blocks (padded a c) ++ [ofBytes (lensBlock a.length c.length)] := by
  rw [List.append_assoc, Proof.Gcm.blocks_append (by simp [Proof.Gcm.length_zeros]), blocks_zeros,
    Proof.Gcm.blocks_append (Proof.Gcm.length_padded a c),
    Proof.Gcm.blocks_single (Proof.Gcm.length_lensBlock _ _), List.append_assoc]

end VG.Proof.AesGcm.X86_64.Short

end

end

/-! ### `AesGcm.X86_64.Short.Layout`, which this module and modules that import it used -/

section

/-!
# AES-GCM's short path on x86-64: what `G` holds

Untrusted: everything here is checked by Lean. `G` (512 bytes) is zeroed,
then the additional data `a` is written after `lead` zero blocks, the text
`c` after the additional data's blocks, and the lengths block last: its
first `M = lead + na + nc + 1` blocks are then `lead` zero blocks, `a` and
`c` each padded with zeros to whole blocks, and the lengths block
(`gLayout`), whatever is written elsewhere (`K`, the data) in between.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)

/-- The bytes of a part of a zeroed buffer. -/
theorem bytesAt_zeros {m : Mem} {G : Addr} {o k N : Nat} (hz : bytesAt m G N = zeros N) (h : o + k ≤ N) :
    bytesAt m (G + BitVec.ofNat 64 o) k = zeros k := by
  have e := congrArg (fun l => (l.drop o).take k) hz
  rw [show N = o + (k + (N - o - k)) by omega_using [h], bytesAt_add, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
    List.take_left' (length_bytesAt _ _ _)] at e
  rw [e]; simp [zeros]

theorem disjG {G : Addr} {o k e j : Nat} (h : o + k ≤ e ∨ e + j ≤ o) (h₁ : o + k ≤ 512) (h₂ : e + j ≤ 512) :
    (⟨G + BitVec.ofNat 64 o, k⟩ : Region).Disjoint ⟨G + BitVec.ofNat 64 e, j⟩ :=
  Offset.disjoint G h (by omega_using [h₁]) (by omega_using [h₂])

/-- What `G` holds. -/
theorem gLayout {G : Addr} {lead na nc : Nat} {a c lens : List Byte} {mZ mK mX mL : Mem} {rs : List Region}
    (ha : a.length ≤ 16 * na) (hc : c.length ≤ 16 * nc)
    (hM : 16 * (lead + na + nc + 1) ≤ 512)
    (hZ : bytesAt mZ G 512 = zeros 512)
    (f₁ : Frame rs (writeBytes mZ (G + BitVec.ofNat 64 (16 * lead)) a) mK)
    (hrs : ∀ r ∈ rs, (⟨G, 512⟩ : Region).Disjoint r)
    {rsX : List Region} (fX : Frame rsX mK mX)
    (hX : ∀ r ∈ rsX, r = ⟨G + BitVec.ofNat 64 (16 * (lead + na)), c.length⟩ ∨ (⟨G, 512⟩ : Region).Disjoint r)
    (hXc : bytesAt mX (G + BitVec.ofNat 64 (16 * (lead + na))) c.length = c)
    (f₂ : Frame [⟨G + BitVec.ofNat 64 (16 * (lead + na + nc)), 16⟩] mX mL)
    (hL : bytesAt mL (G + BitVec.ofNat 64 (16 * (lead + na + nc))) 16 = lens) :
    bytesAt mL G (16 * (lead + na + nc + 1)) =
      zeros (16 * lead) ++ a ++ zeros (16 * na - a.length) ++ c ++ zeros (16 * nc - c.length) ++ lens := by
  -- A part of `G` before the lengths block, in `mL` as in `mK` unless it meets `c`'s blocks.
  have kL : ∀ o k, o + k ≤ 16 * (lead + na + nc) → bytesAt mL (G + BitVec.ofNat 64 o) k = bytesAt mX (G + BitVec.ofNat 64 o) k :=
    fun o k h => bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disjG (.inl h) (by omega_using [hM, h]) (by omega_using [hM])) (by omega_using [hM, h])
  have kX : ∀ o k, o + k ≤ 512 → (o + k ≤ 16 * (lead + na) ∨ 16 * (lead + na) + c.length ≤ o) →
      bytesAt mX (G + BitVec.ofNat 64 o) k = bytesAt mK (G + BitVec.ofNat 64 o) k := fun o k h h' => by
    refine bytesAt_frame fX (fun r hr => ?_) (by omega_using [h])
    rcases hX r hr with rfl | hd
    · exact disjG h' (by omega_using [h]) (by omega_using [hc, hM])
    · exact hd.sub_left (Offset.sub_base G h)
  have kK : ∀ o k, o + k ≤ 512 → bytesAt mK (G + BitVec.ofNat 64 o) k =
      bytesAt (writeBytes mZ (G + BitVec.ofNat 64 (16 * lead)) a) (G + BitVec.ofNat 64 o) k := fun o k h =>
    bytesAt_frame f₁ (fun r hr => (hrs r hr).sub_left (Offset.sub_base G h)) (by omega_using [h])
  have kA : ∀ o k, o + k ≤ 512 → (o + k ≤ 16 * lead ∨ 16 * lead + a.length ≤ o) →
      bytesAt (writeBytes mZ (G + BitVec.ofNat 64 (16 * lead)) a) (G + BitVec.ofNat 64 o) k = zeros k :=
    fun o k h h' => by
      rw [bytesAt_frame (writeBytes_frame' _ rfl) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact disjG h' (by omega_using [h]) (by omega_using [ha, hM])) (by omega_using [h])]
      exact bytesAt_zeros hZ h
  -- The six parts.
  have e : 16 * (lead + na + nc + 1) = 16 * lead + (a.length + ((16 * na - a.length) + (c.length +
      ((16 * nc - c.length) + 16)))) := by omega_using [ha, hc]
  rw [e, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add]
  simp only [add_ofNat_ofNat]
  rw [show 16 * lead + a.length + (16 * na - a.length) = 16 * (lead + na) by omega_using [ha],
    show 16 * (lead + na) + c.length + (16 * nc - c.length) = 16 * (lead + na + nc) by omega_using [hc], hL]
  have s₁ : bytesAt mL G (16 * lead) = zeros (16 * lead) := by
    have := kL 0 (16 * lead) (by omega_using [])
    rw [kX 0 _ (by omega_using [hM]) (.inl (by omega_using [])), kK 0 _ (by omega_using [hM]), kA 0 _ (by omega_using [hM]) (.inl (by omega_using []))] at this
    simpa using this
  have s₂ : bytesAt mL (G + BitVec.ofNat 64 (16 * lead)) a.length = a := by
    rw [kL _ _ (by omega_using [ha]), kX _ _ (by omega_using [ha, hM]) (.inl (by omega_using [ha])), kK _ _ (by omega_using [ha, hM])]
    exact bytesAt_writeBytes_self _ _ _ (by omega_using [ha, hM])
  have s₃ : bytesAt mL (G + BitVec.ofNat 64 (16 * lead + a.length)) (16 * na - a.length) =
      zeros (16 * na - a.length) := by
    rw [kL _ _ (by omega_using [ha]), kX _ _ (by omega_using [ha, hM]) (.inl (by omega_using [ha])), kK _ _ (by omega_using [ha, hM]),
      kA _ _ (by omega_using [ha, hM]) (.inr (by omega_using []))]
  have s₄ : bytesAt mL (G + BitVec.ofNat 64 (16 * (lead + na))) c.length = c := by
    rw [kL _ _ (by omega_using [hc])]; exact hXc
  have s₅ : bytesAt mL (G + BitVec.ofNat 64 (16 * (lead + na) + c.length)) (16 * nc - c.length) =
      zeros (16 * nc - c.length) := by
    rw [kL _ _ (by omega_using [hc]), kX _ _ (by omega_using [hc, hM]) (.inr (by omega_using [])), kK _ _ (by omega_using [hc, hM]),
      kA _ _ (by omega_using [hc, hM]) (.inr (by omega_using [ha]))]
  rw [s₁, s₂, s₃, s₄, s₅]
  simp only [List.append_assoc]

end VG.Proof.AesGcm.X86_64.Short

end

end

/-! ### `AesGcm.X86_64.Short.Front`, which this module and modules that import it used -/

section

/-! ### `AesGcm.X86_64.Short.Mid`, which only this module used -/

section

/-!
# AES-GCM's short path on x86-64: what the steps keep

Untrusted: everything here is checked by Lean. `SM`: after `J₀` and the
counts, what every later step of the short path keeps: the registers holding
the key context, the state and `W`, the scalars kept in `W`, `J₀`, the
additional data, the saved registers, and what has been written since the
entry (`W`, the data and the stack below `SP`). The steps write only `T`
(`W`'s first 16 bytes, the tag) and `W + 512` … `W + 2048` (`G`, `K` and the
powers), and the data (`SM.keep`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The regions the steps after the counts write: in `W` (the tags, the
tags compared and the result of the comparison, `G`, `K` and the powers),
and the data. -/
abbrev Wk (W D : Addr) (n : Nat) (r : Region) : Prop :=
  r.Sub ⟨W, 16⟩ ∨ r.Sub ⟨W + BitVec.ofNat 64 512, 1536⟩ ∨ r.Sub ⟨D, n⟩ ∨ r.Sub ⟨W + BitVec.ofNat 64 112, 16⟩ ∨
    r.Sub ⟨W + BitVec.ofNat 64 216, 8⟩ ∨ r.Sub ⟨W + BitVec.ofNat 64 240, 32⟩

/-- After `J₀` and the counts. -/
structure SM (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (tl : BitVec 64) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  r176 : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R
  r184 : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  r200 : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  r208 : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  r224 : s.mem.readW (W + BitVec.ofNat 64 224) 64 = tl
  r232 : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  r272 : s.mem.readW (W + BitVec.ofNat 64 272) 64 = BitVec.ofNat 64 (nb16 al)
  r280 : s.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 (nb16 n)
  r288 : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * grp al n)
  r296 : s.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 (4 * grp al n - (nb16 al + nb16 n + 1))
  j0 : blockAt s.mem (W + BitVec.ofNat 64 16) = J
  saved : SavedAt s.mem W s₀
  frame : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem wk_disj {W D : Addr} {n d k : Nat} (dD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (h₁ : 16 ≤ d)
    (h₂ : d + k ≤ 512) (h₃ : d + k ≤ 112 ∨ 128 ≤ d) (h₄ : d + k ≤ 216 ∨ 224 ≤ d) (h₅ : d + k ≤ 240 ∨ 272 ≤ d)
    {r : Region} (hr : Wk W D n r) : (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  rcases hr with hr | hr | hr | hr | hr | hr
  · refine Region.Disjoint.sub_right ?_ hr
    have := Offset.disjoint W (d := d) (n := k) (e := 0) (k := 16) (.inr (by omega_using [h₁])) (by omega_using [h₂]) (by omega_using [])
    simpa using this
  · exact (Offset.disjoint W (d := d) (n := k) (e := 512) (k := 1536) (.inl (by omega_using [h₂])) (by omega_using [h₂])
      (by omega_using [])).sub_right hr
  · exact (dD.symm.sub_left (Lay.wSub (by omega_using [h₂]))).sub_right hr
  · exact (Offset.disjoint W (d := d) (n := k) (e := 112) (k := 16) (by omega_using [h₃]) (by omega_using [h₂]) (by omega_using [])).sub_right hr
  · exact (Offset.disjoint W (d := d) (n := k) (e := 216) (k := 8) (by omega_using [h₄]) (by omega_using [h₂]) (by omega_using [])).sub_right hr
  · exact (Offset.disjoint W (d := d) (n := k) (e := 240) (k := 32) (by omega_using [h₅]) (by omega_using [h₂]) (by omega_using [])).sub_right hr

/-- A step that writes only in the work regions and keeps `r13`–`r15` and
`rsp`. -/
theorem SM.keep {s₀ : State} {Ctx W SP A D : Addr} {R al n : Nat} {J : Block} {tl : BitVec 64} {s s' : State}
    (S : SM s₀ Ctx W SP A D R al n J tl s) (dD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {rs : List Region} (f : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, Wk W D n r)
    (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SM s₀ Ctx W SP A D R al n J tl s' := by
  obtain kp : ∀ d, 16 ≤ d → d + 8 ≤ 512 → (d + 8 ≤ 112 ∨ 128 ≤ d) → (d + 8 ≤ 216 ∨ 224 ≤ d) →
      (d + 8 ≤ 240 ∨ 272 ≤ d) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ h₃ h₄ h₅ =>
    f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (fun r hr => wk_disj dD h₁ h₂ h₃ h₄ h₅ (hrs r hr)) (by decide)
  refine ⟨S.env.keep hg hrd hwr, by rw [kp 176 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r176,
    by rw [kp 184 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r184,
    by rw [kp 200 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r200,
    by rw [kp 208 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r208,
    by rw [kp 224 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r224,
    by rw [kp 232 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r232,
    by rw [kp 272 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r272,
    by rw [kp 280 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r280,
    by rw [kp 288 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r288,
    by rw [kp 296 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.r296,
    ?_, S.saved.frame f fun r hr => wk_disj dD (by decide) (by decide) (by decide) (by decide) (by decide) (hrs r hr),
    S.frame.trans (f.sub fun r hr => ?_), hrd.trans S.rd, hwr.trans S.wr⟩
  · rw [blockAt_frame f fun r hr => wk_disj dD (by decide) (by decide) (by decide) (by decide) (by decide) (hrs r hr)]; exact S.j0
  · rcases hrs r hr with h | h | h | h | h | h
    · exact ⟨_, List.mem_cons_self .., fun x hx => Region.sub_prefix (by decide) x (h x hx)⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩
    · exact ⟨⟨D, n⟩, by simp, h⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩
    · exact ⟨_, List.mem_cons_self .., fun x hx => Lay.wSub (by decide) x (h x hx)⟩

/-- A part of `W` that `j0` does not write. -/
theorem j0f_disj {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {d k : Nat} (h₁ : 112 ≤ d)
    (h₂ : d + k ≤ 216 ∨ 224 ≤ d) (h₃ : d + k ≤ 512) :
    ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W SP, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  have ww := L.ww
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (.inr (by omega_using [h₁])) (by omega_using [h₃]) (by omega_using [])
  · exact Offset.disjoint W (.inr (by omega_using [h₁])) (by omega_using [h₃]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h₂]) (by omega_using [h₃]) (by omega_using [])
  · exact Offset.disjoint W (.inl (by omega_using [h₃])) (by omega_using [h₃]) (by omega_using [])
  · exact (L.kw.sub_right (Lay.wSub (by omega_using [h₃]))).symm

/-- The short path's start: `J₀` of the 12-byte nonce and the counts. -/
theorem shortStart_ok {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl' : (s₀.gpr .rcx).toNat = nl) (hnl : nl = 12) (hal : (s₀.gpr .r9).toNat = al)
    (hal5 : al < 512) (hn5 : n < 512) :
    WP isa (.block (Impl.AesGcm.X86_64.j012 ++ Impl.AesGcm.X86_64.Short.sizes)) s₁
      fun s => SM s₀ Ctx W SP A D (s₀.gpr .rsi).toNat al n
        (Spec.Gcm.j0 (Spec.Gcm.ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) (s₁.mem.readW (W + BitVec.ofNat 64 224) 64) s ∧ bytesAt s.mem A al = bytesAt s₀.mem A al ∧
        bytesAt s.mem D n = bytesAt s₀.mem D n := by
  have L := C.lay
  obtain dW : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → ∀ r ∈ [oneR W],
      (⟨p, k⟩ : Region).Disjoint r :=
    fun p k h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  obtain hH₁ : blockAt s₁.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s₀.mem Ctx := by
    rw [ctxH_eq, blockAt_frame E.frame (dW _ _ (L.cw'.sub_left (Lay.ctxSub (by decide))))]
  subst hnl
  obtain hiv : bytesAt s₁.mem Np 12 = bytesAt s₀.mem Np 12 :=
    bytesAt_frame E.frame (dW _ _ C.nonce.w) (by decide)
  obtain j0in : J0In Ctx (W + BitVec.ofNat 64 16) W SP (Spec.Gcm.ctxH s₀.mem Ctx) Np 12 s₁ :=
    ⟨E.env, hH₁, by rw [E.r12, hNp], by rw [E.rbp, ← hnl', BitVec.ofNat_toNat, BitVec.setWidth_eq],
      C.nonce.of_eq E.rd E.wr⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.with_rdwr (j012_ok L (gs := 256) j0in)) fun s₂ ⟨J, rd₂, wr₂⟩ => ?_
  rw [hiv] at J
  obtain kp : ∀ d, 112 ≤ d → (d + 8 ≤ 216 ∨ 224 ≤ d) → d + 8 ≤ 512 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ h₃ =>
    J.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (j0f_disj L h₁ h₂ h₃) (by decide)
  obtain hal₁ : s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (sizes_ok s₂ J.env.r15 J.env.perm.w (by rw [kp 184 (by decide) (by decide) (by decide), hal₁])
    (by rw [kp 208 (by decide) (by decide) (by decide), E.len]) hal5 hn5)
    fun s₃ ⟨m272, m280, m288, m296, f₃, g₃, rd₃, wr₃, z₃⟩ => ?_
  obtain kp₃ : ∀ d, 112 ≤ d → (d + 8 ≤ 216 ∨ 224 ≤ d) → d + 8 ≤ 272 →
      s₃.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ h₃ => by
    rw [f₃.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by omega_using [h₃])) (by have := L.ww; omega_using [h₃]) (by have := L.ww; omega_using [])) (by decide),
      kp d h₁ h₂ (by omega_using [h₃])]
  obtain f₃' : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₂.mem s₃.mem :=
    f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  obtain f₂ : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₁.mem s₂.mem :=
    J.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
      · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩
  obtain f₁ : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s₁.mem :=
    E.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  refine ⟨⟨J.env.keep (fun r hr => ?_) rd₃ wr₃, by rw [kp₃ 176 (by decide) (by decide) (by decide)]; exact E.rounds.1,
    by rw [kp₃ 184 (by decide) (by decide) (by decide), hal₁],
    by rw [kp₃ 200 (by decide) (by decide) (by decide), E.dat],
    by rw [kp₃ 208 (by decide) (by decide) (by decide), E.len],
    by rw [kp₃ 224 (by decide) (by decide) (by decide)],
    by rw [kp₃ 232 (by decide) (by decide) (by decide), E.aad], m272, m280, m288, m296, ?_, ?_,
    f₁.trans (f₂.trans f₃'), by rw [rd₃, rd₂, E.rd], by rw [wr₃, wr₂, E.wr]⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide) (by decide)
  · rw [blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by have := L.ww; omega_using []) (by have := L.ww; omega_using [])]
    exact J.j0
  · exact (E.saved.frame J.frame (saved_j0Frame L (by decide) (.inr (by decide)))).frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by have := L.ww; omega_using []) (by have := L.ww; omega_using [])

  · have hl := C.aad.lt
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.aad.w.sub_right (Lay.wSub (by decide))) (by omega_using [hal]),
      bytesAt_frame J.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact C.aad.st
        · exact C.aad.w.sub_right (Lay.wSub (by decide))
        · exact C.aad.w.sub_right (Lay.wSub (by decide))
        · exact C.aad.w.sub_right (Lay.wSub (by decide))
        · exact C.aad.stk.symm) (by omega_using [hal]),
      bytesAt_frame E.frame (dW _ _ C.aad.w) (by omega_using [hal])]
  · have hl := C.data.ok.lt
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact C.dE.sub_right (Lay.wSub (by decide))) (by omega_using [hn5]),
      bytesAt_frame J.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact C.data.ok.st
        · exact C.dE.sub_right (Lay.wSub (by decide))
        · exact C.dE.sub_right (Lay.wSub (by decide))
        · exact C.dE.sub_right (Lay.wSub (by decide))
        · exact C.data.ok.stk.symm) (by omega_using [hn5]),
      bytesAt_frame E.frame (dW _ _ C.dE) (by omega_using [hn5])]

end VG.Proof.AesGcm.X86_64.Short

end

end


/-!
# AES-GCM's short path on x86-64: the powers, `G` and the keystream

Untrusted: everything here is checked by Lean. `front_ok`: after `J₀` and
the counts, what `seal` and `open` share: the table of powers (`powers`,
or any code `pw` that leaves the same, `PowFrom`),
`G` zeroed with the additional data copied in after its zero blocks
(`zeroG`, `copyA`), and the keystream (`keystream`), each written in its own
part of `W` (`Front`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt inc32 zeros ctxH ctxCiph)

/-- How GHASH sees the table of powers: in `tm m`, the memory `m` with the
table at `W + 1536` as GHASH reads it (`m` itself when it reads the table
there; with a prepared key context, the context's powers put there). What
it reads of the table is kept by writes in `W` below the table or in the
data, and `tm m` is `m` but for the table. -/
structure TabView (tm : Mem → Mem) (W D : Addr) (n : Nat) : Prop where
  keep : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
    (∀ r ∈ rs, (⟨W + BitVec.ofNat 64 1536, 512⟩ : Region).Disjoint r ∧
      (Region.Sub r ⟨W, 1536⟩ ∨ Region.Sub r ⟨D, n⟩)) →
    ∀ j < 8, ∀ l < 4, (tm m').readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128 =
      (tm m).readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128
  out : ∀ m, Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] m (tm m)

/-- GHASH reading the table at `W + 1536`. -/
theorem TabView.id {W D : Addr} {n : Nat} : TabView (fun m => m) W D n :=
  ⟨fun f hd j hj l hl => f.readW (r := ⟨W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩)
      (Region.contains_self _ _) (fun r hr => (hd r hr).1.sub_left (Offset.sub_base _ (by omega_arith))) (by decide),
    fun _ => Frame.refl _ _⟩

theorem TabOk.view {tm : Mem → Mem} {W D : Addr} {n : Nat} (tv : TabView tm W D n) {m m' : Mem} {H : Block}
    {g : Nat} (h : TabOk (tm m) (W + BitVec.ofNat 64 1536) H g) (hg : g ≤ 8) {rs : List Region}
    (f : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 1536, 512⟩ : Region).Disjoint r ∧
      (Region.Sub r ⟨W, 1536⟩ ∨ Region.Sub r ⟨D, n⟩)) :
    TabOk (tm m') (W + BitVec.ofNat 64 1536) H g :=
  fun j hj l hl => by rw [tv.keep f hd j (by omega_arith) l hl]; exact h j hj l hl

/-- What a GHASH code leaves, from `s` to `t`, with the table as `tm` sees
it: what `ghash_ok` says of `ghash`. -/
def GhPost (tm : Mem → Mem) (W : Addr) (g : Nat) (s t : State) : Prop :=
  t.zlane .xmm2 0 =
    (reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 0 g) ^^^
      reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 2 g)) ^^^
    (reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 1 g) ^^^
      reduceB (gacc (tm s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g 3 g)) ∧
  (∀ l, 1 ≤ l → l < 4 → t.zlane .xmm2 l = 0) ∧
  (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
  ZKeep [.xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t

/-- `gh` leaves `GhPost` for `g` groups, in the states after the entry `s₀`
with its permissions. -/
def GhFrom (gh : Prog isa) (tm : Mem → Mem) (s₀ : State) (Ctx W SP : Addr) : Prop :=
  ∀ {g : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) → 1 ≤ g → g ≤ 8 →
    (∀ l < 4, s.zlane .xmm0 l = revMask) → (∀ l < 4, s.zlane .xmm1 l = poly) →
    s.rd = s₀.rd → s.wr = s₀.wr → WP isa gh s (GhPost tm W g s)

theorem ghFrom_ghash {s₀ : State} {Ctx W SP : Addr} : GhFrom ghash (fun m => m) s₀ Ctx W SP :=
  fun s he hmp hg1 hg h0 h1 _ _ => ghash_ok s he.r15 hmp hg1 hg he.perm.w h0 h1

/-- After the powers, `G` and the keystream. -/
structure Front (tm : Mem → Mem) (s₀ : State) (Ctx W SP A D : Addr) (R al n : Nat) (J : Block) (tl : BitVec 64)
    (a : List Byte) (s : State) :
    Prop where
  sm : SM s₀ Ctx W SP A D R al n J tl s
  tab : TabOk (tm s.mem) (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) (grp al n)
  z0 : ∀ l < 4, s.zlane .xmm0 l = revMask
  z1 : ∀ l < 4, s.zlane .xmm1 l = poly
  ks : ∀ b < 4 * ((nb16 n + 4) / 4), blockAt s.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * b)) =
    ctxCiph s₀.mem Ctx R (Nat.repeat inc32 b J)
  gz : ∃ mZ, bytesAt mZ (W + BitVec.ofNat 64 512) 512 = zeros 512 ∧
    Frame [⟨W + BitVec.ofNat 64 1024, 512⟩]
      (writeBytes mZ (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1)))) a) s.mem
  dat : bytesAt s.mem D n = bytesAt s₀.mem D n

/-- What the code may write, outside the key context. -/
theorem ctx_frame {k : Nat} {s₀ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {m : Mem} (f : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem m)
    {p : Addr} {j : Nat} (hs : Region.Sub ⟨p, j⟩ ⟨Ctx, 256⟩) (hj : j ≤ 256) : bytesAt m p j = bytesAt s₀.mem p j :=
  bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact C.lay.cw'.sub_left hs
    · exact C.data.ctx.sub_left hs
    · exact C.t_c.symm.sub_left hs) (by omega_arith)

theorem ctxH_frame {k : Nat} {s₀ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {m : Mem} (f : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem m) :
    ctxH m Ctx = ctxH s₀.mem Ctx := by
  rw [ctxH_eq, ctxH_eq, blockAt, blockAt, ctx_frame C f (Lay.ctxSub (by decide)) (by decide)]

theorem ciph_frame' {k : Nat} {s₀ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) {m : Mem} (f : Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem m)
    {R : Nat} (hR : R ≤ 14) : ciphOf m Ctx R = ctxCiph s₀.mem Ctx R := by
  simp only [ciphOf, ctxCiph]
  rw [ctx_frame C f (Region.sub_prefix (by omega_arith)) (by omega_arith)]

theorem wk_T {W D : Addr} {n : Nat} : Wk W D n ⟨W + BitVec.ofNat 64 1536, 512⟩ :=
  .inr (.inl (Offset.sub W (by decide) (by decide)))

theorem wk_G {W D : Addr} {n : Nat} {o k : Nat} (h : o + k ≤ 1536) : Wk W D n ⟨W + BitVec.ofNat 64 (512 + o), k⟩ :=
  .inr (.inl (Offset.sub W (by omega_arith) (by omega_arith)))

/-- What a table of powers' code `pw` leaves, from `s` to `t`: the table at
`W + 1536`, as `tm` sees it, for the hash subkey of `s`, nothing else
written, the constants in every lane of `zmm0` and `zmm1`, and the registers
but `rax` and `r11`. -/
def PowPost (tm : Mem → Mem) (Ctx W : Addr) (g : Nat) (s t : State) : Prop :=
  TabOk (tm t.mem) (W + BitVec.ofNat 64 1536) (ctxH s.mem Ctx) g ∧
    Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem t.mem ∧
    (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
    (∀ r, r ≠ .rax → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

/-- `pw` leaves `PowPost` for `g` groups from the states the short path runs
it in after the entry `s₀`, which wrote only `W`, the data and the stack
below `SP`; and `gh` computes GHASH from the table as `tm` sees it. -/
structure PowFrom (pw gh : Prog isa) (tm : Mem → Mem) (s₀ : State) (Ctx W SP D : Addr) (n : Nat) : Prop where
  view : TabView tm W D n
  gh : GhFrom gh tm s₀ Ctx W SP
  run : ∀ {g : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) → 1 ≤ g → g ≤ 8 →
    Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem → s.rd = s₀.rd → s.wr = s₀.wr →
    WP isa pw s (PowPost tm Ctx W g s)

/-- `powers` and `ghash`, from the hash subkey at `ctx + 240`. -/
theorem powFrom_powers (hF : ShortFacts) {s₀ : State} {Ctx W SP D : Addr} {n : Nat} :
    PowFrom powers ghash (fun m => m) s₀ Ctx W SP D n :=
  ⟨TabView.id, ghFrom_ghash, fun s he h1 h2 h3 _ _ _ => hF.powers s he h1 h2 h3⟩

/-- The powers (from `pw`), `G` and the keystream, then `rest`. -/
theorem front_ok {pw gh : Prog isa} {tm : Mem → Mem} {k : Nat} {s₀ s : State} {Ctx W SP Np A D : Addr}
    {nl al n R : Nat} {J : Block} {tl : BitVec 64}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hpw : PowFrom pw gh tm s₀ Ctx W SP D n) (hR : R = (s₀.gpr .rsi).toNat)
    (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (S : SM s₀ Ctx W SP A D R al n J tl s) (haad : bytesAt s.mem A al = bytesAt s₀.mem A al)
    (hdat : bytesAt s.mem D n = bytesAt s₀.mem D n)
    {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t, Front tm s₀ Ctx W SP A D R al n J tl (bytesAt s₀.mem A al) t → WP isa rest t Q) :
    WP isa (.seq pw (.seq (.block zeroG) (.seq copyA (.seq keystream rest)))) s Q := by
  have L := C.lay
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  obtain hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega_arith
  obtain hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega_arith
  obtain hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega_arith
  obtain hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  -- The powers.
  refine WP.seq (WP.mono (hpw.run s S.env S.r288 hg1 hg8 S.frame S.rd S.wr)
    fun s₃ ⟨tab₃, fT, z0₃, z1₃, g₃, rd₃, wr₃⟩ => ?_)
  obtain S₃ := S.keep dD fT (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_T)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
  rw [ctxH_frame C S.frame] at tab₃
  obtain dT : ∀ {m m' : Mem}, Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] m m' → ∀ {p : Addr} {j : Nat},
      (⟨p, j⟩ : Region).Disjoint ⟨W, 2560⟩ → j ≤ 2 ^ 64 → bytesAt m' p j = bytesAt m p j := fun f _ _ h hj =>
    bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))) hj
  obtain haad₃ : bytesAt s₃.mem A al = bytesAt s₀.mem A al := by rw [dT fT C.aad.w (by omega_arith), haad]
  obtain hdat₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := by rw [dT fT dD (by omega_arith), hdat]
  -- `G` zeroed.
  refine WP.seq (WP.mono (zeroG_ok s₃ S₃.env.r15 (S₃.env.perm.wC (by decide)))
    fun s₄ ⟨m₄, g₄, rd₄, wr₄, z₄⟩ => ?_)
  obtain fG : Frame [⟨W + BitVec.ofNat 64 512, 512⟩] s₃.mem s₄.mem := by rw [m₄]; exact writeBytes_frame' _ (List.length_replicate ..)
  obtain S₄ := S₃.keep dD fG (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Region.sub_prefix (by decide))))
    (fun r _ => by rw [g₄]) rd₄ wr₄
  obtain tab₄ := TabOk.view hpw.view tab₃ hg8 fG fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint W (.inr (by decide)) (by decide) (by decide), .inl (Offset.sub_base W (by decide))⟩
  obtain dG : ∀ {p : Addr} {j : Nat}, (⟨p, j⟩ : Region).Disjoint ⟨W, 2560⟩ → j ≤ 2 ^ 64 →
      bytesAt s₄.mem p j = bytesAt s₃.mem p j := fun h hj =>
    bytesAt_frame fG (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))) hj
  obtain hZ : bytesAt s₄.mem (W + BitVec.ofNat 64 512) 512 = zeros 512 := by
    have := bytesAt_writeBytes_self s₃.mem (W + BitVec.ofNat 64 512) (List.replicate 512 0)
      (by rw [List.length_replicate]; decide)
    rw [List.length_replicate] at this
    rw [m₄, this]; rfl
  -- The additional data copied to `G`.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₄', run₄', di₄, si₄, cx₄, g₄', m₄', rd₄', wr₄', z₄'⟩ := copyAArgs_ok s₄ S₄.env.r15 S₄.env.perm.w S₄.r296
    S₄.r232 S₄.r184 (by omega_arith)
  refine WP.of_runBlock ⟨s₄', run₄', ?_⟩
  obtain hal63 : al < 2 ^ 63 := by omega_arith
  obtain cp : CopyPre s₄' A (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1)))) al :=
    ⟨si₄, di₄, cx₄, hal63, by rw [rd₄', wr₄', S₄.rd, S₄.wr]; exact C.aad.rd,
      by rw [wr₄']; exact S₄.env.perm.wC (by omega_arith),
      C.aad.w.sub_right (Lay.wSub (by omega_arith))⟩
  refine WP.mono (copyBytes_ok s₄' cp) fun s₅ ⟨m₅, g₅, rd₅, wr₅, z₅⟩ => ?_
  obtain ha₄ : bytesAt s₄.mem A al = bytesAt s₀.mem A al := by rw [dG C.aad.w (by omega_arith), haad₃]
  rw [m₄', ha₄] at m₅
  obtain fA : Frame [⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1))), al⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain S₅ := S₄.keep dD fA (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wk_G (by omega_arith))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [g₅ _ (by decide) (by decide) (by decide), g₄' _ (by decide) (by decide) (by decide)])
    (rd₅.trans rd₄') (wr₅.trans wr₄')
  obtain tab₅ := TabOk.view hpw.view tab₄ hg8 fA fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith), .inl (Offset.sub_base W (by omega_arith))⟩
  obtain hdat₅ : bytesAt s₅.mem D n = bytesAt s₀.mem D n := by
    rw [bytesAt_frame fA (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dD.sub_right (Lay.wSub (by omega_arith))) (by omega_arith),
      dG dD (by omega_arith), hdat₃]
  obtain zz : ∀ r, r ≠ .xmm2 → r ≠ .xmm4 → ∀ l < 4, s₅.zlane r l = s₃.zlane r l := fun r h₂ h₄ l hl => by
    rw [z₅ r (by simp [h₄]) l hl, z₄' r l, z₄ r (by simp [h₂]) l hl]
  -- The keystream.
  refine WP.seq (WP.mono (keystream_ok s₅ S₅.env L (hR ▸ S₅.r176) S₅.r280 (by omega_arith) (hR ▸ hR')
    (fun l hl => by rw [zz _ (by decide) (by decide) l hl, z0₃ l hl]))
    fun s₆ ⟨kb, fK, gK, rdK, wrK, zK, m0K⟩ => ?_)
  obtain S₆ := S₅.keep dD fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by decide) (by decide))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact gK _ (by decide)) rdK wrK
  refine hrest s₆ ⟨S₆, TabOk.view hpw.view tab₅ hg8 fK fun r hr => ?_, m0K, fun l hl => ?_, fun b hb => ?_,
    ⟨s₄.mem, hZ, by rw [← m₅]; exact fK⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Offset.disjoint W (.inr (by decide)) (by decide) (by decide), .inl (Offset.sub_base W (by decide))⟩
  · rw [zK _ (by decide) l hl, zz _ (by decide) (by decide) l hl, z1₃ l hl]
  · rw [kb b hb, S₅.j0, ciph_frame' C S₅.frame (by omega_arith), hR]
  · rw [bytesAt_frame fK (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dD.sub_right (Lay.wSub (by decide))) (by omega_arith),
      hdat₅]

end VG.Proof.AesGcm.X86_64.Short

end

end

/-!
# AES-GCM's short path on x86-64: `seal`

Untrusted: everything here is checked by Lean. After `front_ok`, the text
is encrypted in place with the keystream and copied to `G`
(`xorText true`), the lengths block ends `G` (`lens`), `GHASH` of `G`
(`ghash`), and the tag at `W` (`tagK 0`): `sealBack_ok`. With
`shortStart_ok` and `front_ok`, `sealShort_ok` leaves what `sealRun_ok`
does.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt blocks inc32 zeros ctxH ctxCiph gctr ghash ghashFrom ofBytes toBytes)
open VG.Proof.Gcm (padded lensBlock)

theorem bytesAt_toBytes' (m : Mem) (p : Addr) : bytesAt m p 16 = toBytes (blockAt m p) := by
  rw [blockAt, Proof.Cmac.toBytes_ofBytes (length_bytesAt _ _ _)]

/-- What `seal` leaves (`sealRun_ok`'s postcondition). -/
abbrev SealPost (s₀ : State) (Ctx W SP D : Addr) (n R al : Nat) (H J : Block) (a : List Byte) (s : State) :
    Prop :=
  Env Ctx (W + BitVec.ofNat 64 16) W SP s ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    SavedAt s.mem W s₀ ∧ Frame [⟨W, 2560⟩, ⟨D, n⟩, below SP 24] s₀.mem s.mem ∧
    bytesAt s.mem D n = gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) ∧
    bytesAt s.mem W 16 = toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt s.mem D n))))
      [ofBytes (lensBlock al n)] ^^^ ctxCiph s₀.mem Ctx R J)

/-- After `front_ok`: the text, `G`'s lengths block, `GHASH` and the tag. -/
theorem sealBack_ok (hF : ShortFacts) {gh : Prog isa} {tm : Mem → Mem} {k : Nat} {s₀ s : State}
    {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J : Block} {tl : BitVec 64}
    (hgh : GhFrom gh tm s₀ Ctx W SP) (htv : TabView tm W D n)
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32)
    (F : Front tm s₀ Ctx W SP A D R al n J tl (bytesAt s₀.mem A al) s) :
    WP isa (.seq (.seq (.block textArgs) (xorText true)) (.seq (sealShort.ghash' gh) (.block (tagK 0)))) s
      (SealPost s₀ Ctx W SP D n R al (ctxH s₀.mem Ctx) J (bytesAt s₀.mem A al)) := by
  have L := C.lay
  have dD := C.dE
  have h32' := h32
  simp only [nb16] at h32'
  have hg1 : 1 ≤ grp al n := by simp only [grp, nb16]; omega_arith
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega_arith
  have hmp : 4 * grp al n = (4 * grp al n - (nb16 al + nb16 n + 1)) + nb16 al + nb16 n + 1 := by
    simp only [grp, nb16]; omega_arith
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega_arith
  have hna : al ≤ 16 * nb16 al ∧ 16 * nb16 al < al + 16 := by simp only [nb16]; omega_arith
  have hnc : n ≤ 16 * nb16 n ∧ 16 * nb16 n < n + 16 := by simp only [nb16]; omega_arith
  have S := F.sm
  -- The text.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₁, run₁, di₁, si₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁, z₁⟩ := textArgs_ok s S.env.r15 S.env.perm.w S.r296 S.r272
    S.r200 S.r208 (by omega_arith)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have xp : XorPre true s₁ D (W + BitVec.ofNat 64 1040)
      (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al))) n :=
    ⟨si₁, dx₁, di₁, cx₁, by omega_arith, by rw [rd₁, wr₁, S.rd, S.wr]; exact C.data.ok.rd,
      by rw [rd₁, wr₁]; exact covers_left (S.env.perm.wC (by omega_arith)),
      by rw [wr₁, S.wr]; exact C.data.wr, fun _ => by rw [wr₁]; exact S.env.perm.wC (by omega_arith),
      dD.sub_right (Lay.wSub (by omega_arith)), fun _ => dD.sub_right (Lay.wSub (by omega_arith)),
      fun _ => Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)⟩
  refine WP.mono (xorText_ok true s₁ xp) fun s₂ ⟨m₂, g₂, rd₂, wr₂, z₂⟩ => ?_
  have S₁ := S.keep dD (rs := []) (by rw [m₁]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide) (by decide)) rd₁ wr₁
  have fX : Frame [⟨D, n⟩, ⟨W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)), n⟩]
      s₁.mem s₂.mem := by
    rw [m₂]; have := xw_frame true s₁.mem D (W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) +
      nb16 al))) (xb s₁.mem D (W + BitVec.ofNat 64 1040) n)
    rwa [length_xb] at this
  have S₂ := S₁.keep dD fX (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inr (.inl fun _ h => h))
      · exact wk_G (by omega_arith))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)) rd₂ wr₂
  -- The lengths block.
  refine WP.seq (WP.seq ?_)
  obtain ⟨s₃, run₃, fL, hL, g₃, rd₃, wr₃, z₃⟩ := lensG_ok s₂ S₂.env.r15 S₂.env.perm.w S₂.r288 (by omega_arith) (by omega_arith)
    S₂.r184 S₂.r208 (by omega_arith) (by omega_arith)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have S₃ := S₂.keep dD fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub W (by omega_arith) (by omega_arith))))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) rd₃ wr₃
  -- `GHASH` of `G`.
  have zz : ∀ r, r ≠ .xmm4 → ∀ l < 4, s₃.zlane r l = s.zlane r l := fun r h l hl => by
    rw [z₃ r l, z₂ r (by simp [h]) l hl, z₁ r l]
  refine WP.mono (hgh s₃ S₃.env S₃.r288 hg1 hg8
    (fun l hl => by rw [zz _ (by decide) l hl, F.z0 l hl]) (fun l hl => by rw [zz _ (by decide) l hl, F.z1 l hl])
    S₃.rd S₃.wr)
    fun s₄ ⟨y0, y1, g₄, m₄, rd₄, wr₄, z₄⟩ => ?_
  have S₄ := S₃.keep dD (rs := []) (by rw [m₄]; exact Frame.refl _ _) (by simp)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide)) rd₄ wr₄
  -- The tag.
  have x0 : s₄.xmm .xmm0 = revMask := by
    rw [show s₄.xmm .xmm0 = s₄.zlane .xmm0 0 from rfl, z₄ _ (by decide) 0 (by decide), zz _ (by decide) 0 (by decide),
      F.z0 0 (by decide)]
  obtain ⟨s₅, run₅, tag₅, fW, g₅, rd₅, wr₅⟩ := tagK_ok (o := 0) s₄ S₄.env.r15 S₄.env.perm.w (by decide) x0
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have S₅ := S₄.keep dD fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl (by simpa using Region.sub_prefix (base := W) (Nat.le_refl 16)))
    (fun r _ => by rw [g₅]) rd₅ wr₅
  have Ftab := F.tab
  have Fks := F.ks
  have Fdat := F.dat
  obtain ⟨mZ, hZ, fK⟩ := F.gz
  -- Shorthands for the counts and the addresses.
  generalize hl : 4 * grp al n - (nb16 al + nb16 n + 1) = lead at *
  generalize hna' : nb16 al = na at *
  generalize hnc' : nb16 n = nc at *
  generalize hg' : grp al n = g at *
  have hmp' : 4 * g = lead + na + nc + 1 := by omega_arith
  -- The ciphertext.
  generalize hc : xb s₁.mem D (W + BitVec.ofNat 64 1040) n = c at m₂
  have hcl : c.length = n := by rw [← hc, length_xb]
  have dWD : ∀ {d j : Nat}, d + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, j⟩ :=
    fun h => dD.sub_right (Lay.wSub h)
  have hct : bytesAt s₅.mem D n = c := by
    rw [bytesAt_frame fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWD (by decide)) (by omega_arith),
      m₄, bytesAt_frame fL (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWD (by omega_arith)) (by omega_arith),
      m₂]
    simp only [xw, ↓reduceIte]
    rw [bytesAt_frame (writeBytes_frame' _ hcl) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dWD (by omega_arith)) (by omega_arith), ← hcl]
    exact bytesAt_writeBytes_self _ _ _ (by omega_arith)
  have hcg : c = gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) := by
    rw [← hc, ← Fdat, ← m₁]
    refine xb_gctr fun b hb => ?_
    rw [m₁, show W + BitVec.ofNat 64 1040 + BitVec.ofNat 64 (16 * b) =
        W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (16 * (b + 1)) by
      rw [add_ofNat_ofNat, add_ofNat_ofNat, show 1040 + 16 * b = 1024 + 16 * (b + 1) by omega_arith]]
    exact Fks (b + 1) (by omega_arith)
  refine ⟨S₅.env, S₅.rd, S₅.wr, S₅.saved, S₅.frame, by rw [hct, hcg], ?_⟩
  rw [hct, bytesAt_toBytes']
  have T₁ : TabOk (tm s₁.mem) (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) g := by rw [m₁]; exact Ftab
  have T₃ : TabOk (tm s₃.mem) (W + BitVec.ofNat 64 1536) (ctxH s₀.mem Ctx) g :=
    TabOk.view htv (TabOk.view htv T₁ hg8 fX fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(dWD (by decide)).symm, .inr fun _ h => h⟩
      · exact ⟨Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith), .inl (Offset.sub_base W (by omega_arith))⟩)
      hg8 fL fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith), .inl (Offset.sub_base W (by omega_arith))⟩
  have hGv : blocksAt (tm s₃.mem) (W + BitVec.ofNat 64 512) (4 * g) = blocksAt s₃.mem (W + BitVec.ofNat 64 512) (4 * g) := by
    rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame (htv.out s₃.mem) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith)]
  have hx2 : s₄.xmm .xmm2 = ghashFrom (ctxH s₀.mem Ctx) 0 (blocksAt s₃.mem (W + BitVec.ofNat 64 512) (4 * g)) := by
    rw [show s₄.xmm .xmm2 = s₄.zlane .xmm2 0 from rfl, y0, hF.ghash T₃, hGv]
  have hK₀ : blockAt s₄.mem (W + BitVec.ofNat 64 1024) = ctxCiph s₀.mem Ctx R J := by
    rw [m₄, blockAt_frame fL (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)),
      blockAt_frame fX (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (dWD (by decide)).symm
        · exact Offset.disjoint W (.inr (by omega_arith)) (by omega_arith) (by omega_arith)), m₁]
    have := Fks 0 (by omega_arith)
    simpa [Nat.repeat] using this
  -- `G`.
  have hlay := gLayout (G := W + BitVec.ofNat 64 512) (lead := lead) (na := na) (nc := nc)
    (a := bytesAt s₀.mem A al) (c := c) (lens := lensBlock al n) (mZ := mZ) (mK := s₁.mem) (mX := s₂.mem)
    (mL := s₃.mem) (by rw [length_bytesAt]; omega_arith) (by omega_arith) (by omega_arith) hZ
    (by rw [m₁, add_ofNat_ofNat]; exact fK)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))
    (rsX := [⟨D, n⟩, ⟨W + BitVec.ofNat 64 (512 + 16 * (lead + na)), n⟩]) fX
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (dD.sub_right (Lay.wSub (by decide))).symm
      · exact .inl (by rw [hcl, add_ofNat_ofNat]))
    (by
      rw [m₂, add_ofNat_ofNat, hcl]
      simp only [xw, ↓reduceIte]
      rw [← hcl]; exact bytesAt_writeBytes_self _ _ _ (by omega_arith))
    (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega_arith]; exact fL)
    (by rw [add_ofNat_ofNat, show 512 + 16 * (lead + na + nc) = 496 + 16 * (4 * g) by omega_arith]; exact hL)
  have hpad := padded_layout (bytesAt s₀.mem A al) c
  rw [length_bytesAt, hcl, hna', hnc'] at hpad
  rw [length_bytesAt, hcl] at hlay
  have hG : bytesAt s₃.mem (W + BitVec.ofNat 64 512) (16 * (4 * g)) =
      zeros (16 * lead) ++ padded (bytesAt s₀.mem A al) c ++
        lensBlock (bytesAt s₀.mem A al).length c.length := by
    rw [hmp', hlay, ← hpad, length_bytesAt, hcl]; simp only [List.append_assoc]
  have t5 : blockAt s₅.mem W = s₄.xmm .xmm2 ^^^ blockAt s₄.mem (W + BitVec.ofNat 64 1024) := by
    simpa using tag₅
  refine congrArg toBytes ?_
  rw [t5, hx2, hK₀, Proof.Gcm.blocksAt_eq, hG, gBlocks, List.append_assoc, ghashFrom_zeros,
    Proof.Gcm.ghashFrom_append, length_bytesAt, hcl]
  rfl

/-- The short `seal`, after the entry, for a 12-byte nonce and at most 32
blocks to hash: what `sealRun_ok` leaves. -/
theorem sealShort_ok (hF : ShortFacts) {pw gh : Prog isa} {tm : Mem → Mem} {k : Nat} {s₀ s₁ : State}
    {Ctx W SP Np A D : Addr}
    {nl al n : Nat} (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (hpw : PowFrom pw gh tm s₀ Ctx W SP D n)
    (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl' : (s₀.gpr .rcx).toNat = nl) (hal' : (s₀.gpr .r9).toNat = al)
    (hnl : nl = 12) (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32) :
    WP isa (sealShort pw gh) s₁ (SealPost s₀ Ctx W SP D n (s₀.gpr .rsi).toNat al (ctxH s₀.mem Ctx)
      (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)) (bytesAt s₀.mem A al)) := by
  subst hnl
  exact WP.seq (WP.mono (shortStart_ok C E hNp hnl' rfl hal' hal5 hn5) fun s₂ ⟨S, haad, hdat⟩ =>
    front_ok C hpw rfl hal5 hn5 h32 S haad hdat fun t F => sealBack_ok hF hpw.gh hpw.view C hal5 hn5 h32 F)

end VG.Proof.AesGcm.X86_64.Short
