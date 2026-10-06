import VerifiedGarbage.Proof.AesCcm.Arm.Compare
import VerifiedGarbage.Proof.AesCcm.Arm.Words

/-!
# AES-CCM on ARMv7: `Ctr₀` (`ctrs`)

Untrusted: everything here is checked by Lean. `ctrs` zeroes the block at
`W + 48`, writes `q − 1 = 14 − n` to its first byte (and to `r10`) and copies
the nonce after it: `Ctr₀` (`ctrs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Impl.AesGcm.Arm (imm addI zero16 copyLoop)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre copyLoop_ok covers_left bytesAt_frame
  mem_store store8_eq store32_eq gpr_store rd_store wr_store sp_store encodable_of_decide)

theorem store4_zero_bytes' (m : Mem) (p : Addr) : bytesAt (store4 m p 0 0 0 0) p 16 = Spec.Ccm.zeros 16 := by
  rw [Proof.Cmac.bytesAt_store4]; decide

/-- The bytes of `Ctr₀`, as `ctrs` builds them. -/
theorem ctr0_list (xs : List Byte) (h13 : xs.length ≤ 13) :
    ((BitVec.ofNat 8 (14 - xs.length) :: (Spec.Ccm.zeros 16).drop 1).take 1 ++ xs ++
      (BitVec.ofNat 8 (14 - xs.length) :: (Spec.Ccm.zeros 16).drop 1).drop (1 + xs.length)) =
      Spec.Ccm.ctrBlock xs 0 := by
  rw [Spec.Ccm.ctrBlock, be_zero, show 15 - xs.length - 1 = 14 - xs.length by omega,
    show 1 + xs.length = xs.length + 1 by omega, List.drop_succ_cons, List.take_succ_cons, List.take_zero]
  simp only [Spec.Ccm.zeros, List.drop_replicate, List.cons_append, List.nil_append]

theorem setWidth_ofNat8 {x : Nat} (_h : x < 256) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega)]

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 32 by omega)]
  omega

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- `ctrs`: `Ctr₀` for the `nl`-byte nonce at `N` in the block at `W + 48`,
and `q − 1` in `r10`. -/
theorem ctrs_ok {s : State} (he : Env k w sp R q1 s) {N : BitVec 32} {nl : Nat} (hN : Buf w sp s N nl)
    (h2 : s.gpr .r2 = N) (h3 : s.gpr .r3 = BitVec.ofNat 32 nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 48) 16 =
        Spec.Ccm.ctrBlock (bytesAt s.mem (State.addr N) nl) 0 ∧
      s'.gpr .r10 = BitVec.ofNat 32 (14 - nl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 48, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁, -⟩ := zero16_ok L he (d := c0O) (by decide) (by decide)
  simp only [c0O] at hm₁
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have wB := (he.perm.of_eq rd₁ wr₁).wW (show 48 + 1 ≤ 2560 by decide)
  have e48 := L.wA (d := 48) (by decide)
  have e49 := L.wA (d := 49) (by decide)
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, h10₂, hm₂, g₂, rd₂, wr₂, sp₂⟩ : ∃ s₂, runBlock isa [.mov .r10 (imm 14),
      .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O, .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)] s₁ = some s₂ ∧
      s₂.gpr .r1 = N ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 49 ∧ s₂.gpr .r3 = BitVec.ofNat 32 nl ∧
      s₂.gpr .r10 = BitVec.ofNat 32 (14 - nl) ∧
      s₂.mem = s₁.mem.writeW (State.addr w + BitVec.ofNat 64 48) (BitVec.ofNat 8 (14 - nl)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r10 → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      s₂.sp = s₁.sp := by
    have g3 : s₁.gpr .r3 = BitVec.ofNat 32 nl := by rw [g₁ _ (by decide), h3]
    have e14 : BitVec.ofNat 32 14 - BitVec.ofNat 32 nl = BitVec.ofNat 32 (14 - nl) :=
      sub_ofNat32 (by omega) (by decide)
    refine ⟨_, by simp only [c0O]; arun [h11, g3, e48, wB], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, g₁ .r2 (by decide), h2]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g3]
    · simp [gpr_setReg, e14]
    · simp [mem_setReg, gpr_setReg, e14, setWidth_ofNat8 (show 14 - nl < 256 by omega)]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  have hN₂ : Buf w sp s₂ N nl := hN.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have lp : LoopPre s₂ N (w + BitVec.ofNat 32 49) nl := by
    refine ⟨h1₂, h2₂, h3₂, by omega, by omega, hN.fit, by rw [L.wN (by decide)]; have := L.ww; omega,
      hN₂.rd, ?_, ?_⟩
    · rw [e49]; exact (he.perm.of_eq (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])).wC (by omega)
    · rw [e49]; exact hN.w.sub_right (Lay.wSub (by omega))
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show (zero16 c0O ++ [.mov .r10 (imm 14), .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O,
      .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)]) = zero16 c0O ++ [.mov .r10 (imm 14),
      .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O, .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)] from rfl]
    exact Proof.AesGcm.Arm.runBlock_app_of run₁ run₂, ?_⟩)
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  -- The nonce is as on entry: only `W + 48` was written.
  have fW : Frame [⟨State.addr w + BitVec.ofNat 64 48, 16⟩] s.mem s₂.mem := by
    rw [hm₂, hm₁]
    refine (Proof.Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have nN : bytesAt s₂.mem (State.addr N) nl = bytesAt s.mem (State.addr N) nl :=
    bytesAt_frame fW (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hN.w.sub_right (Lay.wSub (by decide))) (by omega)
  rw [nN, e49] at hm₃
  have hlen := length_bytesAt s.mem (State.addr N) nl
  refine ⟨?_, ?_, ?_, ?_, lo.rd.trans (rd₂.trans rd₁), lo.wr.trans (wr₂.trans wr₁), lo.sp.trans (sp₂.trans sp₁)⟩
  · rw [hm₃, show State.addr w + BitVec.ofNat 64 49 = (State.addr w + BitVec.ofNat 64 48) + BitVec.ofNat 64 1 by
      rw [Offset.add_add]]
    rw [bytesAt_writeBytes_at _ _ _ (by rw [hlen]; omega) (by decide), hm₂,
      bytesAt_writeW8_base _ _ _ (by decide) (by decide), hm₁, store4_zero_bytes']
    have := ctr0_list (bytesAt s.mem (State.addr N) nl) (by rw [hlen]; exact h13)
    rw [hlen] at this
    rw [hlen]; exact this
  · rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h10₂]
  · rw [hm₃]
    refine fW.trans ((writeBytes_frame _ _ _ (R := ⟨State.addr w + BitVec.ofNat 64 49, nl⟩) ?_).sub
      fun r hr => ?_)
    · rw [hlen]; exact Region.contains_self _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  · intro r a b c d e f
    rw [lo.other r a b c d f, g₂ r b c e, g₁ r a]

end

end VG.Proof.AesCcm.Arm
