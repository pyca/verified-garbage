import VerifiedGarbage.Proof.AesCcm.Arm.CtrAt
import VerifiedGarbage.Proof.AesCcm.Arm.Callee

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
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hsp]; have := L.sp16; omega_arith, L.kw,
    by rw [L.wN (by decide)]; have := L.ww; omega_arith, fD, by rw [L.wN (by decide)]; have := L.ww; omega_arith, ?_, dK,
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
  have eY := L.wA (d := y) (by omega_arith)
  have hqc : (⟨State.addr w + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 y, 16 * 1⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have C₃ := ctrCall_of L he₃ hR (n := 1) a0 a1 a2 a3 a12 alr (by rw [L.wN (by omega_arith)]; have := L.ww; omega_arith)
    (by rw [eY]; exact L.k_w' (by omega_arith)) (by rw [eY]; exact hqc)
    (by rw [eY]; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
    (by rw [eY]; exact L.stk_w' (by omega_arith)) (by rw [eY]; exact he₃.perm.wC (by omega_arith))
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
  have eY := L.wA (d := y) (by omega_arith)
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
      exact (L.k_w' (by decide)).sub_left (Region.sub_prefix hRb)) (by omega_arith)]
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
      (D := State.addr (w + BitVec.ofNat 32 y)) (R := R) (nonce := nonce) (by omega_arith) (j := 0) (k := 1)
      (fun i hi => by
        rw [show i = 0 by omega_arith, Nat.zero_add]
        show Spec.Gcm.ofBytes _ = _
        rw [L.wA (by decide), hc₂]) h.out
    rw [Nat.mul_one, eY] at hc
    rw [hc, hK₃, hY₃]

end

end VG.Proof.AesCcm.Arm
