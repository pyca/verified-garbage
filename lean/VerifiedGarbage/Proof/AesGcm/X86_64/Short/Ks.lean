import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Xor
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn

/-!
# AES-GCM's short path on x86-64: the keystream

Untrusted: everything here is checked by Lean. `keystream` encrypts the
counter blocks `J₀`, `inc₃₂(J₀)`, … four at a time in the lanes of `zmm3`
(`VaesZ.ctrsZ_ok`, `VaesZ.aesZ_ok`) and stores them at `K` (`keystream_ok`),
after `Stitch.setupC` (`Stitch.setupC_ok`) and the first half of
`StitchZ.setupZ` (`ctrZ_ok`) put the counters in the lanes of `zmm14`.
-/

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
  all_goals rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
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
    rw [show 4 * k + 4 * 1 + l = 4 * (k + 1) + l by omega]
  · rw [m', blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl]
    refine (aesWith_eq nr _ _ _ ?_).symm
    rw [e₂ .xmm3 (List.mem_singleton_self _) l hl]
    have := e₁ 0 (by decide) l hl
    simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at this
    rw [this]
  · rw [m', hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [d', show 64 * (k + 1) = 64 * k + 64 by omega, ← ofNat_add_ofNat, BitVec.add_assoc]
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
  · exact hl l (by omega)
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
    have := m0 l (by omega)
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
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
  rw [si₁, di₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at r10₂
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
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofNat_add_ofNat, shr2 _ (by omega)]
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
  have hnr14 : nr ≤ 14 := by omega
  refine WP.seq (WP.mono (ksSetup_ok s he hR hnc hnc32 hnr14 m0)
    fun s₁ ⟨c14, i15, m0₁, di₁, si₁, r10₁, dx₁, r9₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  have hnk : 1 ≤ (nc + 4) / 4 ∧ (nc + 4) / 4 ≤ 8 := by omega
  generalize (nc + 4) / 4 = nk at r9₁ hnk ⊢
  have hwK : ∀ k < nk, InRegions s.wr (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 (64 * k)) 64 := fun k hk => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]; exact he.perm.wW (by omega)
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
        exact (L.cw'.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))) (by omega)).symm,
      hnr14, fun j hj => by
        rw [rd, wr, di, BitVec.ofInt_natCast]; exact he.perm.ctxR (by omega)⟩
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
    ⟨0, rfl, by omega, fun l hl => by rw [c14 l hl]; simp, i15, m0₁, di₁, si₁, r10₁, by rw [dx₁]; simp,
      r9₁, fun b hb => absurd hb (by omega), by rw [m₁]; exact Frame.refl _ _, g₁, rd₁, wr₁,
      z₁.mono (by simp)⟩
  rintro m t ⟨k, rfl, hk, c14t, i15t, m0t, dit, sit, r10t, dxt, r9t, bt, ft, gt, rdt, wrt, zt⟩
  refine WP.mono (ksStep_ok t hnr (keys t ft dit rdt wrt) sit (by rw [r10t, dit]) c14t m0t i15t dxt
    (by rw [wrt]; exact hwK k hk))
    fun t' ⟨c14', bk', f', dx', r9', zf', g', rd', wr', z'⟩ => ?_
  have hr9 : t.gpr .r9 - 1 = BitVec.ofNat 64 (nk - (k + 1)) := by
    rw [r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub (by omega) (by omega)]; congr 1
  have f'' : Frame [⟨K, 512⟩] s.mem t'.mem := ft.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base K (by omega)⟩)
  have bt' : ∀ b < 4 * (k + 1), blockAt t'.mem (K + BitVec.ofNat 64 (16 * b)) = aesWith nr w (Nat.repeat inc32 b J) := by
    intro b hb
    by_cases hb' : b < 4 * k
    · rw [← bt b hb']
      exact blockAt_frame f' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint K (.inl (by omega)) (by omega) (by omega))
    · have := bk' (b - 4 * k) (by omega)
      rwa [BitVec.add_assoc, ofNat_add_ofNat, show 64 * k + 16 * (b - 4 * k) = 16 * b by omega,
        show 4 * k + (b - 4 * k) = b by omega] at this
  have gt' : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] → t'.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g' r hr.2.2.1 hr.2.2.2.2.2.2.1, gt r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2])]
  have zt' : ZKeep [.xmm2, .xmm3, .xmm13, .xmm14, .xmm15] s t' := zt.trans (z'.mono (by simp))
  have m0' : ∀ l < 4, t'.zlane .xmm0 l = revMask := fun l hl => by rw [z' _ (by decide) l hl, m0t l hl]
  have hz : t'.zf = some (decide (nk - k = 1)) := by
    rw [zf', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (a := nk - k) (b := 1) (by omega)
      (by omega)]
  by_cases he' : k + 1 = nk
  · left
    refine ⟨by simp [eval, hz]; omega, fun b hb => ?_, f'', gt', by rw [rd', rdt], by rw [wr', wrt], zt', m0'⟩
    rw [bt' b (by omega)]
  · right
    refine ⟨by simp [eval, hz]; omega, nk - (k + 1), by omega, k + 1, rfl, by omega, c14',
      fun l hl => by rw [z' _ (by decide) l hl, i15t l hl], m0', by rw [g' _ (by decide) (by decide), dit],
      by rw [g' _ (by decide) (by decide), sit], by rw [g' _ (by decide) (by decide), r10t], dx',
      by rw [r9', hr9], bt', f'', gt', by rw [rd', rdt], by rw [wr', wrt], zt'⟩

end VG.Proof.AesGcm.X86_64.Short
