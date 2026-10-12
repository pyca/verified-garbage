import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec

/-!
# AES-GCM-SIV on x86-64: loops four blocks at a time

Untrusted: everything here is checked by Lean. `quadsThenOnes quad one` runs
`quad` (four blocks) while four or more of the `rcx` blocks are left, then
`one` (one block) while any are: `quadsThenOnes_ok` composes the two loops
from invariants `Q` (four at a time, which may say more than `P`) and `P`
(one at a time), indexed by the blocks done, which `cmp` and `test` keep.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (imm)

/-- A property of states that only their flags tell apart. -/
def FlagStable (P : State → Prop) : Prop :=
  ∀ (u : State) (x : BitVec 64) (c o : Bool), P u → P (arithFlags u x c o)

/-- `cmp rcx, 4` with `k` in `rcx`: CF says whether `k < 4`. -/
theorem cmp4_run (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr .rcx = BitVec.ofNat 64 k) :
    ∃ (x : BitVec 64) (o : Bool), runBlock isa [.alu .cmp .rcx (imm 4)] u =
      some (arithFlags u x (decide (k < 4)) o) := by
  have e4 : BitVec.signExtend 64 (BitVec.ofNat 32 4) = BitVec.ofNat 64 4 := by decide
  refine ⟨BitVec.ofNat 64 k - BitVec.ofNat 64 4,
    subOverflow (BitVec.ofNat 64 k) (BitVec.ofNat 64 4) (BitVec.ofNat 64 k - BitVec.ofNat 64 4), ?_⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, imm, h, Option.bind_some]
  rw [e4]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- `test rcx, rcx` with `k` in `rcx`: ZF says whether `k = 0`. -/
theorem test0_run (u : State) {k : Nat} (hk : k < 2 ^ 64) (h : u.gpr .rcx = BitVec.ofNat 64 k) :
    runBlock isa [.alu .test .rcx (.reg .rcx)] u =
      some (arithFlags u (BitVec.ofNat 64 k) false false) ∧
      (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  refine ⟨?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, Option.bind_some, h,
      BitVec.and_self]
  · by_cases hk0 : k = 0
    · subst hk0; rfl
    · have : BitVec.ofNat 64 k ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
        exact hk0 this
      rw [beq_eq_false_iff_ne.mpr this, decide_eq_false hk0]

/-- The two loops: four blocks at a time while four are left (`Q`), then one
at a time (`P`, from any block before the last). -/
theorem quadsThenOnes_ok {quad one : List Instr} {c : Nat} (hc : c < 2 ^ 63) (hc1 : 1 ≤ c)
    (P Q : Nat → State → Prop) (hP : ∀ k, FlagStable (P k)) (hQ : ∀ k, FlagStable (Q k))
    (hQP : ∀ k u, Q k u → P k u)
    (hrcx : ∀ k u, P k u → u.gpr .rcx = BitVec.ofNat 64 (c - k))
    (hquad : ∀ k, k + 4 ≤ c → ∀ u, Q k u → WP isa (.block quad) u fun u' =>
      Q (k + 4) u' ∧ u'.cf = some (decide (c - (k + 4) < 4)))
    (hone : ∀ k, k < c → ∀ u, P k u → WP isa (.loop (.block one) .ne) u (P c))
    {u : State} (h₀ : Q 0 u) :
    WP isa (quadsThenOnes quad one) u (P c) := by
  unfold quadsThenOnes
  -- The quads, from block 0: after them, `k` blocks done with `c - k < 4`.
  have quads : ∀ u, Q 0 u → u.cf = some (decide (c < 4)) →
      WP isa (.ite .b (.block []) (.loop (.block quad) .ae)) u fun u' =>
        ∃ k, k ≤ c ∧ c - k < 4 ∧ Q k u' := by
    intro u hu hcf
    refine WP.ite (decide (c < 4)) hcf (fun h4 => WP.block_nil ⟨0, Nat.zero_le _, by simpa using h4, hu⟩)
      (fun h4 => ?_)
    have h4' : ¬ c < 4 := by simpa using h4
    refine WP.loop (M := isa) (body := .block quad) (c := .ae)
      (fun (m : Nat) (v : State) => ∃ k, m = c - k ∧ k + 4 ≤ c ∧ Q k v) ?_ (c - 0) u ⟨0, rfl, by omega, hu⟩
    rintro m v ⟨k, rfl, hk, hv⟩
    refine WP.mono (hquad k hk v hv) fun v' ⟨hv', hcf'⟩ => ?_
    have ev : isa.eval .ae v' = some !(decide (c - (k + 4) < 4)) := by
      show v'.cf.map (!·) = _; rw [hcf']; rfl
    by_cases hlt : c - (k + 4) < 4
    · left
      exact ⟨by rw [ev, decide_eq_true hlt]; rfl, k + 4, hk, hlt, hv'⟩
    · right
      exact ⟨by rw [ev, decide_eq_false hlt]; rfl, c - (k + 4), by omega, k + 4, rfl, by omega, hv'⟩
  obtain ⟨x, o, run₁⟩ := cmp4_run u (k := c) (by omega) (by rw [hrcx 0 u (hQP 0 u h₀), Nat.sub_zero])
  refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
  refine WP.seq (WP.mono (quads _ (hQ 0 _ x _ o h₀) rfl) fun u₂ ⟨k, hkc, hk4, hu₂⟩ => ?_)
  have hP₂ := hQP k u₂ hu₂
  obtain ⟨run₂, hy⟩ := test0_run u₂ (k := c - k) (by omega) (hrcx k u₂ hP₂)
  refine WP.seq (WP.of_runBlock ⟨_, run₂, ?_⟩)
  have hP₃ := hP k _ (BitVec.ofNat 64 (c - k)) false false hP₂
  refine WP.ite (decide (c - k = 0)) (by rw [← hy]; rfl) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have : k = c := by simp at h0; omega
    subst this; exact hP₃
  · exact hone k (by simp at h0; omega) _ hP₃

/-! ## Four blocks reversed -/

theorem ea_at0 (s : State) (b : Reg) : s.ea (Impl.AesGcm.X86_64.at_ b 0) = s.gpr b := by
  show s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int) = s.gpr b
  rw [BitVec.ofInt_natCast]; exact BitVec.add_zero _

/-- The four blocks at `rsi` (`S`), each byte-reversed (`zmm1` holding the
mask in each lane), stored at `rdi` (`P`): GHASH reads each as the block's
128-bit little-endian value. -/
theorem revZ_ok (s : State) {S P : Addr} (hsi : s.gpr .rsi = S) (hdi : s.gpr .rdi = P)
    (hm : ∀ l < 4, s.zlane .xmm1 l = Proof.Gcm.X86_64.revMask)
    (hr : InRegions (s.rd ++ s.wr) S 64) (hw : InRegions s.wr P 64) :
    WP isa (.block [.vmovdqu32Load .xmm0 (Impl.AesGcm.X86_64.at_ .rsi 0),
        .zop (.zbin .vpshufb .xmm0 .xmm0 .xmm1), .vmovdqu32Store (Impl.AesGcm.X86_64.at_ .rdi 0) .xmm0]) s
      fun s' =>
        (∃ v : BitVec 512, s'.mem = s.mem.writeW P v) ∧
        (∀ l < 4, Spec.Gcm.blockAt s'.mem (P + BitVec.ofNat 64 (16 * l)) =
          s.mem.readW (S + BitVec.ofNat 64 (16 * l)) 128) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        (∀ r, r ≠ .xmm0 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  let v := s.mem.readW S 512
  let s₁ := s.setZ .xmm0 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.zbin .vpshufb .xmm0 .xmm0 .xmm1).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane .xmm0 l = s.mem.readW (S + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [ite_true]
    rw [pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl]
    exact Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl
  have m₁ : ∀ l < 4, s₁.zlane .xmm1 l = Proof.Gcm.X86_64.revMask := fun l hl => by
    rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
    simp only [show (XReg.xmm1 = .xmm0) = False by decide, ite_false]
    exact hm l hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_at0, hsi, hr, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (Impl.AesGcm.X86_64.at_ .rdi 0) .xmm0) s₂ =
      some (s₂.setMem (s.mem.writeW P (s₂.zmm .xmm0))) := by
    simp only [isa, exec, State.store512_eq, ea_at0, s₂, s₁, ZOp.exec_gpr, State.setZ_gpr, ZOp.exec_wr,
      State.setZ_wr, ZOp.exec_mem, State.setZ_mem, hdi, hw, ite_true]
  refine ⟨_, hst, WP.block_nil ?_⟩
  have z₂ : ∀ l < 4, s₂.zlane .xmm0 l =
      XBinOp.eval .pshufb (s.mem.readW (S + BitVec.ofNat 64 (16 * l)) 128) Proof.Gcm.X86_64.revMask :=
    fun l hl => by
      simp only [s₂, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse, l₁ l hl, m₁ l hl]
  refine ⟨⟨_, rfl⟩, fun l hl => ?_, by simp [s₂, s₁], by simp [s₂, s₁], by simp [s₂, s₁], fun r h1 l hl => ?_⟩
  · simp only [State.setMem_mem]
    rw [Proof.Aes.X86_64.VaesZ.blockAt_writeW_lane _ _ _ hl, Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl, z₂ l hl,
      Proof.Gcm.X86_64.pshufb_rev_rev]
  · simp [s₂, s₁, zlane_zbin _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, h1]

/-! ## Four keystream blocks XORed -/

/-- Lane `l` of a 64-byte write, read back. -/
theorem readW_lane512 (m : Mem) (q : Addr) (v : BitVec 512) {l : Nat} (hl : l < 4) :
    (m.writeW q v).readW (q + BitVec.ofNat 64 (16 * l)) 128 = v.extractLsb' (128 * l) 128 := by
  have e := readW_writeW_inside m q v (k := 16 * l) (n := 16) (by omega) (by decide)
  rwa [show 8 * (16 * l) = 128 * l by omega] at e

/-- The four keystream blocks at `rsi` (`S`) XORed into the four data blocks at
`r12` (`Q`). -/
theorem ksZ_ok (s : State) {S Q : Addr} (hsi : s.gpr .rsi = S) (h12 : s.gpr .r12 = Q)
    (hr : InRegions (s.rd ++ s.wr) S 64) (hw : InRegions s.wr Q 64) :
    WP isa (.block [.vmovdqu32Load .xmm1 (Impl.AesGcm.X86_64.at_ .rsi 0),
        .vmovdqu32Load .xmm0 (Impl.AesGcm.X86_64.at_ .r12 0), .zop (.zbin .vpxord .xmm1 .xmm1 .xmm0),
        .vmovdqu32Store (Impl.AesGcm.X86_64.at_ .r12 0) .xmm1]) s
      fun s' =>
        (∃ v : BitVec 512, s'.mem = s.mem.writeW Q v ∧ ∀ l < 4, v.extractLsb' (128 * l) 128 =
          s.mem.readW (Q + BitVec.ofNat 64 (16 * l)) 128 ^^^ s.mem.readW (S + BitVec.ofNat 64 (16 * l)) 128) ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' := Proof.Aes.X86_64.AesNi.inRegions_wr hw
  let vS := s.mem.readW S 512
  let vQ := s.mem.readW Q 512
  let s₁ := s.setZ .xmm1 (vS.extractLsb' 0 128) (vS.extractLsb' 128 128) (vS.extractLsb' 256 128)
    (vS.extractLsb' 384 128)
  let s₂ := s₁.setZ .xmm0 (vQ.extractLsb' 0 128) (vQ.extractLsb' 128 128) (vQ.extractLsb' 256 128)
    (vQ.extractLsb' 384 128)
  let s₃ := (ZOp.zbin .vpxord .xmm1 .xmm1 .xmm0).exec s₂
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, ea_at0, hsi, hr, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by
    simp only [isa, exec, State.load512, ea_at0, s₁, State.setZ_gpr, State.setZ_rd, State.setZ_wr, State.setZ_mem,
      h12, hw', ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (Impl.AesGcm.X86_64.at_ .r12 0) .xmm1) s₃ =
      some (s₃.setMem (s.mem.writeW Q (s₃.zmm .xmm1))) := by
    simp only [isa, exec, State.store512_eq, ea_at0, s₃, s₂, s₁, ZOp.exec_gpr, State.setZ_gpr, ZOp.exec_wr,
      State.setZ_wr, ZOp.exec_mem, State.setZ_mem, h12, hw, ite_true]
  refine ⟨_, hst, WP.block_nil ⟨⟨_, rfl, fun l hl => ?_⟩, by simp [s₃, s₂, s₁], by simp [s₃, s₂, s₁],
    by simp [s₃, s₂, s₁]⟩⟩
  rw [Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl]
  simp only [s₃, zlane_zbin _ _ _ _ _ _ hl, ite_true, ZBinOp.sse]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [show (XReg.xmm1 = .xmm0) = False by decide, ite_false, ite_true]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  rw [pick4_lanes (fun i => vS.extractLsb' (128 * i) 128) hl, pick4_lanes (fun i => vQ.extractLsb' (128 * i) 128) hl,
    Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl, Proof.Aes.X86_64.VaesZ.load512_lane _ _ hl,
    Proof.Aes.X86_64.AesNi.eval_pxor, BitVec.xor_comm]

/-! ## The pointers and the count -/

/-- `add a, 64; add b, 64; sub rcx, 4; cmp rcx, 4` with `k ≥ 4` in `rcx`. -/
theorem adv4_run (u : State) {a b : Reg} (ha : a ≠ .rcx) (hb : b ≠ .rcx) (hab : a ≠ b) {k : Nat} (hk4 : 4 ≤ k)
    (hk : k < 2 ^ 63) (hcx : u.gpr .rcx = BitVec.ofNat 64 k) :
    ∃ u', runBlock isa [.alu .add a (imm 64), .alu .add b (imm 64), .alu .sub .rcx (imm 4),
        .alu .cmp .rcx (imm 4)] u = some u' ∧
      u'.gpr a = u.gpr a + BitVec.ofNat 64 64 ∧ u'.gpr b = u.gpr b + BitVec.ofNat 64 64 ∧
      u'.gpr .rcx = BitVec.ofNat 64 (k - 4) ∧ u'.cf = some (decide (k - 4 < 4)) ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ .rcx → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ x l, u'.zlane x l = u.zlane x l) := by
  have e64 : BitVec.signExtend 64 (BitVec.ofNat 32 64) = BitVec.ofNat 64 64 := by decide
  have e4 : BitVec.signExtend 64 (BitVec.ofNat 32 4) = BitVec.ofNat 64 4 := by decide
  have s4 : BitVec.ofNat 64 k - BitVec.ofNat 64 4 = BitVec.ofNat 64 (k - 4) :=
    Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega)
  have hba : b ≠ a := fun h => hab h.symm
  have hcb : Reg.rcx ≠ b := fun h => hb h.symm
  have hca : Reg.rcx ≠ a := fun h => ha h.symm
  refine ⟨_, rfl, ?_⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, imm, e64, e4,
    Option.bind_some, gpr_setReg, gpr_arithFlags, ite_true, ha, hb, hab, hba, hca, hcb, ite_false, hcx, s4,
    cf_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
    BitVec.toNat_ofNat]
  refine ⟨trivial, trivial, trivial, ?_, fun r h₁ h₂ h₃ => by simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃,
    ite_false], trivial, trivial, trivial, fun _ _ => rfl⟩
  rw [Nat.mod_eq_of_lt (by omega : k - 4 < 2 ^ 64)]

/-! ## The mask -/

/-- The byte-reversal mask in the four lanes of `zmm1`, and the count in
`rcx`. -/
theorem revMaskZ_ok (s : State) :
    WP isa (.block (revMaskZ ++ ([.mov .rcx (.reg .r14)] : List Instr))) s fun s' =>
      (∀ l < 4, s'.zlane .xmm1 l = Proof.Gcm.X86_64.revMask) ∧ s'.gpr .rcx = s.gpr .r14 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [revMaskZ, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Proof.Gcm.X86_64.Pclmul.const_ok .xmm1 _ s (by decide)) fun s₁ ⟨x₁, O⟩ => ?_
  apply WP.of_runBlock
  refine ⟨_, rfl, fun l hl => ?_, ?_, fun r h₁ h₂ => ?_, O.mem, O.rd, O.wr⟩
  · have hz : ∀ (u : State) (r : Reg) (v : BitVec 64) (x : XReg) (l : Nat), (u.setReg r v).zlane x l =
        u.zlane x l := fun _ _ _ _ _ => rfl
    rw [hz]
    simp only [zlane_vshufi32x4 _ _ _ _ _ _ hl, ite_true, shuf4Lanes]
    have e : ∀ j < 4, ((0 : BitVec 8).extractLsb' (2 * j) 2).toNat = 0 := by decide
    rw [e l hl]
    split <;> (rw [show s₁.zlane .xmm1 0 = s₁.xmm .xmm1 from rfl, x₁]; rfl)
  · simp only [isa, exec, readSrc, State.setReg, ite_true, ZOp.exec_gpr, State.setZ_gpr]
    exact O.gpr _ (by decide)
  · simp only [isa, exec, State.setReg, h₂, ite_false, ZOp.exec_gpr, State.setZ_gpr]
    exact O.gpr r h₁

end VG.Proof.AesGcmSiv.X86_64
