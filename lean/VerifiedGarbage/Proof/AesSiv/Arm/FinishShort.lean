import VerifiedGarbage.Proof.AesSiv.Arm.S2vLoop

/-!
# AES-SIV on ARMv7: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` copies `P` onto the zeroed tail at `W + 32` and
puts `0x80` after it, so the tail is `pad(P)`, doubles `D` into `W + 192`
and XORs it into the tail (`shortTail_ok`); `shortMac out` finalizes the
tail, one complete block, from a zero state at `W + out`
(`shortMac_ok`), which is S2V's end (`Siv.s2vFinish_short`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (z_cmp gpr_subFlags z_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags
  bytesAt_frame covers_left covers_off eval_eq' Keeps LoopPre LoopOut copyLoop_ok in_off)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok dbl_wp dblMem dblMem_bytes dblMem_frame b80)
open VG.Proof.MdStream.Arm (wp_mov wp_add wp_strb op2_imm op2_reg)
open VG.Proof.AesSiv (chain_blocks_nil)
open VG.Proof.AesCcm.Arm (blw)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- The tail after `shortTail`: `pad(P) ⊕ dbl(D)`. -/
theorem shortTail_ok {s : State} (he : Env c w sp R s) {P : BitVec 32} {n : Nat} (hP : Buf w sp s P n)
    (hn : n < 16) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa shortTail s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (wR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 =
        Spec.Cmac.xor (Spec.Siv.pad (bytesAt s.mem (State.addr P) n))
          (Spec.Siv.dbl (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16)) := by
  have ww := L.ww
  have eT := L.wA (d := tailOff) (by decide)
  have hlen : (bytesAt s.mem (State.addr P) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  -- The tail zeroed, and the arguments of the copy.
  rw [shortTail]
  refine WP.seq (zero16_ok L he (d := tailOff) (by decide) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_)
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, hz₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [mov .r1 .r6, addI .r2 .r11 tailOff,
      mov .r3 .r5, .cmp .r5 (imm 0)] s₁ = some s₂ ∧ s₂.gpr .r1 = P ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 tailOff ∧
      s₂.gpr .r3 = BitVec.ofNat 32 n ∧ s₂.z = decide (n = 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
    have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
    have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
    refine ⟨_, by simp only [mov, tailOff]; arun [h11₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6₁]
    · simp [gpr_setReg, h11₁]
    · simp [gpr_setReg, h5₁]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5₁]
      exact z_cmp (by omega) (by decide)
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  -- The copy, if any: the tail is `P` followed by zeros.
  have pmem : bytesAt s₁.mem (State.addr P) n = bytesAt s.mem (State.addr P) n := by
    rw [m₁]
    exact bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.fit; omega)
  have copied : WP isa (.ite .eq (.block []) copyLoop) s₂ fun s₃ =>
      s₃.mem = writeBytes s₁.mem (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₃.gpr r = s₂.gpr r) ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp := by
    by_cases h0 : n = 0
    · subst h0
      refine WP.ite true (eval_eq' (by rw [hz₂]; rfl)) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨?_, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
      rw [k₂.mem]; simp [bytesAt, writeBytes_nil]
    · refine WP.ite false (eval_eq' (by rw [hz₂]; simp [h0])) (fun h => by cases h) fun _ => ?_
      have lp : LoopPre s₂ P (w + BitVec.ofNat 32 tailOff) n :=
        ⟨h1₂, h2₂, h3₂, by omega, by omega, hP.fit, by rw [L.wN (by decide)]; simp only [tailOff]; omega,
          by rw [k₂.rd, k₂.wr, rd₁, wr₁]; exact hP.rd,
          by rw [eT, k₂.wr, wr₁]; exact he.perm.wC (by simp only [tailOff]; omega),
          by rw [eT]; exact hP.w.sub_right (Lay.wSub (by simp only [tailOff]; omega))⟩
      refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨m₃, lo⟩ => ?_
      refine ⟨by rw [m₃, k₂.mem, eT, pmem], lo.other, lo.rd, lo.wr, lo.sp⟩
  refine WP.seq (WP.mono copied fun s₃ ⟨m₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  -- `0x80` after `P`, and `r6 := W`.
  have h11₃ : s₃.gpr .r11 = w := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide), he.r11]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide), h5]
  refine wp_add (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  have a80 : State.addr (s₅.gpr .r2 + BitVec.ofNat 32 tailOff) =
      State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 n := by
    rw [u₅.other _ (by decide), u₄.gpr, h11₃, h5₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      L.wA (by simp only [tailOff]; omega),
      Offset.add_add, Nat.add_comm]
  refine wp_strb (by decide) a80 (by
      rw [u₅.wr, u₄.wr, wr₃, k₂.wr, wr₁, Offset.add_add]
      exact in_off he.perm.w (by simp only [tailOff]; omega) (by decide)) fun s₆ v₆ => ?_
  refine wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  have h6₇ : s₇.gpr .r6 = w := by rw [u₇.gpr, v₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  have h11₇ : s₇.gpr .r11 = w := by
    rw [u₇.other _ (by decide), v₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  have hrw : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by
    rw [u₇.rd, u₇.wr, v₆.rd, v₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rd₃, wr₃, k₂.rd, k₂.wr, rd₁, wr₁]
  have hw₇ : s₇.wr = s.wr := by rw [u₇.wr, v₆.wr, u₅.wr, u₄.wr, wr₃, k₂.wr, wr₁]
  have m₇ : s₇.mem = (writeBytes (Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 tailOff))
      (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n)).writeW
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 n) (0x80 : Byte) := by
    have b : (BitVec.setWidth 8 (BitVec.ofNat 32 128) : Byte) = 0x80 := by decide
    rw [u₇.mem, v₆.mem, u₅.gpr, u₅.mem, u₄.mem, m₃, m₁, b]
  refine dbl_wp (K := w) h6₇ (src := dOff) (dst := dbOff) (by decide) (by decide) (by simp only [dOff]; omega)
    (by simp only [dbOff]; omega) (by rw [hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [hw₇]; exact he.perm.wC (by decide)) fun s₈ g₈ m₈ rd₈ wr₈ sp₈ => ?_
  have h11₈ : s₈.gpr .r11 = w := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11₇]
  rw [xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h11₈]; simp only [tailOff]; omega)
    (by rw [h11₈]; simp only [dbOff]; omega) (by rw [h11₈]; simp only [tailOff]; omega)
    (by rw [h11₈, rd₈, wr₈, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₈, rd₈, wr₈, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h11₈, wr₈, hw₇]; exact he.perm.wC (by decide)) fun s₉ g₉ => WP.block_nil ?_
  -- The registers.
  have gT : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r6 → r ≠ .r12 → r ≠ .lr →
      s₉.gpr r = s.gpr r := fun r a0 a1 a2 a3 a4 a6 a12 alr => by
    rw [g₉.gpr r a12 alr, g₈ r a0 a1 a2 a3 a4 a12, u₇.other r a6, v₆.gpr, u₅.other r a12, u₄.other r a2,
      g₃ r a0 a1 a2 a3 a12, g₂ r a1 a2 a3, g₁ r a12]
  have rd₉ : s₉.rd = s.rd := by rw [g₉.rd, rd₈, u₇.rd, v₆.rd, u₅.rd, u₄.rd, rd₃, k₂.rd, rd₁]
  have wr₉ : s₉.wr = s.wr := by rw [g₉.wr, wr₈, hw₇]
  have sp₉ : s₉.sp = s.sp := by rw [g₉.sp, sp₈, u₇.sp, v₆.sp, u₅.sp, u₄.sp, sp₃, k₂.sp, sp₁]
  -- The memory.
  have dTB : (⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 dbOff, 16⟩ := L.w_w (.inl (by decide)) (by decide) (by decide)
  have m₉ : s₉.mem = Proof.Cmac.xor4Mem (dblMem s₇.mem (State.addr w) dOff dbOff)
      (State.addr w + BitVec.ofNat 64 tailOff) (State.addr w + BitVec.ofNat 64 tailOff)
      (State.addr w + BitVec.ofNat 64 dbOff) := by rw [g₉.mem, m₈, h11₈]
  have f₇ : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩] s.mem s₇.mem := by
    rw [m₇]
    refine ((Proof.Cmac.frame_store4 _ _ _ _ _).trans (writeBytes_frame _ _ _ ?_)).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    rw [hlen]
    simpa using Offset.contains_base (State.addr w + BitVec.ofNat 64 tailOff) (d := 0) (n := n) (k := 16)
      (by omega) (by decide)
  have f₉ : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩, ⟨State.addr w + BitVec.ofNat 64 dbOff, 16⟩]
      s.mem s₉.mem := by
    rw [m₉]
    exact ((f₇.mono (by simp)).trans ((dblMem_frame _ _ _ _).mono (by simp))).trans
      ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact gT _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) sp₉ rd₉ wr₉, rd₉, wr₉, fun r hr h4 h6 hlr => ?_,
    f₉.sub fun r hr => ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact gT r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 h6 a.2.2.2.2 hlr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · have dD : (⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint
        ⟨State.addr w + BitVec.ofNat 64 tailOff, 16⟩ := L.w_w (.inr (by decide)) (by decide) (by decide)
    have pad := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 tailOff))
      (State.addr w + BitVec.ofNat 64 tailOff) (bytesAt s.mem (State.addr P) n) (by rw [hlen]; exact hn)
      (Proof.Cmac.zero4_bytes _ _)
    rw [hlen] at pad
    rw [m₉, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dTB),
      dblMem_bytes, bytesAt_frame (dblMem_frame _ _ _ _) (p := State.addr w + BitVec.ofNat 64 tailOff) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dTB) (by omega),
      bytesAt_frame f₇ (p := State.addr w + BitVec.ofNat 64 dOff) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dD) (by omega),
      m₇, pad, Spec.Siv.pad, hlen, Spec.Siv.dbl, show 16 - n - 1 = 15 - n by omega]
    rfl

omit L in
/-- The CMAC of one block. -/
theorem cmacWith_one (ciph : Spec.Cmac.Cipher) (k1 k2 T : List Byte) (hT : T.length = 16) :
    Spec.Siv.cmacWith ciph k1 k2 T = ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2 T) (Spec.Cmac.zeros 16)) := by
  rw [Siv.cmacWith_chained, hT, show Spec.Cmac.chainedLen 16 16 = 0 from rfl, List.take_zero, List.drop_zero,
    chain_blocks_nil, Proof.Cmac.xor_comm]

/-- `shortArgs out`: the state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_finalize` of the tail, one complete block. -/
theorem shortArgs_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (.block (shortArgs out)) s fun s₂ => Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 out) ∧
      FArgs s₂ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  rw [shortArgs, List.append_assoc]
  refine zero16_ok L he (d := out) (by omega) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  obtain ⟨s₂, run₂, he₂, g₂, k₂, F⟩ : ∃ s₂, runBlock isa (macArgs out ++ [addI .r3 .r11 tailOff, .mov .r12 (imm 16)])
      s₁ = some s₂ ∧ Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ ∧
      FArgs s₂ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) 16 R := by
    refine ⟨_, by simp only [macArgs, csOff, tailOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11, eo], ?_⟩
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine fargs_of L ?_ hR (st := out) (by omega) (n := 16) (by decide)
      (by rw [L.wN (by decide)]; simp only [tailOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [eT]; exact L.w_w (by omega) (by decide) (by omega)
    · rw [eT]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eT]; exact L.stk_w' (by decide)
    · rw [eT]; exact covers_left (he₁.perm.wC (by decide))
    · simp [gpr_setReg, he₁.r10]
    · simp [gpr_setReg, he₁.r9]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₁.r11]
  exact WP.of_runBlock ⟨s₂, run₂, he₂, fun r a b c' d e f => by rw [g₂ r a b c' d e f, g₁ r e],
    by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁], by rw [k₂.mem, m₁], F⟩

/-- `shortMac out`: the CMAC of the tail, one block, at `W + out`. -/
theorem shortMac_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (shortMac out) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.ctxMac s.mem (State.addr c) R (bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) 16) := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  have eO := L.wA (d := out) (by omega)
  rw [shortMac]
  refine WP.seq (WP.mono (shortArgs_ok L he hR hout) fun s₂ ⟨he₂, g₂, rd₂, wr₂, m₂, F⟩ => ?_)
  refine WP.mono (fin_call F) fun s₃ h₃ => ?_
  have hb := blw16_eq (s := s₂) he₂.sp
  have f₃ := h₃.frame
  rw [eO, L.wA (d := 256) (by decide), hb] at f₃
  have f₁ : Frame (oR w sp out) s.mem s₂.mem := by
    rw [m₂]
    exact (Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  have f₃' : Frame (oR w sp out) s₂.mem s₃.mem := by
    exact f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨blw sp, by simp, fun _ h => h⟩
  have fT := f₁.trans f₃'
  refine ⟨he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr, by rw [h₃.rd, rd₂], by rw [h₃.wr, wr₂],
    fun r hr hlr => ?_, fT, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  · -- What the call reads is as on entry.
    have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 out, 16⟩] s.mem s₂.mem := by
      rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have hRb := rounds_le hR
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₂.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' hd (by omega)) (by omega)
    have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega)
    rw [BitVec.add_zero] at sch
    have tl : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) 16 :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (by omega) (by decide) (by omega)) (by decide)
    have z : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
      rw [m₂, Proof.Cmac.zero4_bytes]
    have out₃ := h₃.out
    rw [eO, eT, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide), tl, z] at out₃
    rw [out₃, Spec.Siv.ctxMac, Spec.Siv.schedCiph, cmacWith_one _ _ _ _ (Proof.Cmac.bytesAt_length _ _ _)]
    rfl

/-- S2V's end for a string `P` shorter than a block, into `W + out`. -/
theorem short_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (hn : n < 16) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (.seq shortTail (shortMac out)) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  refine WP.seq (WP.mono (shortTail_ok L he hP hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, f₁, t₁⟩ => ?_)
  refine WP.mono (shortMac_ok L he₁ hR hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
  refine ⟨he₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h4 h6 hlr => by rw [g₂ r hr hlr, g₁ r hr h4 h6 hlr],
    (frame_oR out f₁).trans f₂, ?_⟩
  rw [o₂, t₁, ctxMac_frame f₁ (dis_wR L.c_w L.stk_c) (rounds_le hR),
    Siv.s2vFinish_short _ _ (by rw [Proof.Cmac.bytesAt_length]; exact hn), Siv.xor_eq, Proof.Cmac.xor_comm]

end

end VG.Proof.AesSiv.Arm
