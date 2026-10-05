import VerifiedGarbage.Proof.AesOcb.Arm.Seal
import VerifiedGarbage.Proof.AesGcm.Arm.Compare

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `open` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at
`W + t2O` (`tag`); then the received tag, padded with zeros at `W`
(`recv_ok`); the first `tag_len` bytes of the tag, padded with zeros at
`W + vO`, compared with it (`cmp_ok`); the data ANDed with `0 − ok`
(`mask_ok`); and `restore` (`open_wp`), as on AArch64
(`Proof.AesOcb.AArch64.open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.Ocb (blockAtMem_frame length_bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Proof.AesGcm.Arm (below SavedAt restore_ok copyLoop_ok LoopPre covers_left covers_prefix covers_of_mem
  store4_zero_tail bytes_words words_eq_iff cmp_value runBlock_app_of Keeps add_ofNat_assoc add_ofNat_zero
  bytesAt_writeBytes_prefix writeBytes_frame' z_subFlags gpr_subFlags mem_subFlags z_cmp eval_eq' eval_ne' addr_i
  dec32 z_dec in_of_covers bytesAt_succ mem_store gpr_store add32_ofNat_assoc)

/-! ## The received tag -/

/-- `recv`: the received tag, the `tl` bytes at `T`, padded with zeros at
`W`. -/
theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    WP isa recv s fun t => bytesAt t.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.T) p.tl ++ zeros (16 - p.tl) ∧
      Frame [⟨State.addr p.W, 16⟩] s.mem t.mem ∧ Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  unfold recv
  refine WP.seq (WP.block_append (WP.mono (zero16_wp (s := s) (o := tagO) (by decide)
    (by rw [E.r11]; simp only [tagO]; omega) (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11, show State.addr p.W + BitVec.ofNat 64 tagO = State.addr p.W from BitVec.add_zero _] at R₁
  have E₁ : Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fz : Frame [⟨State.addr p.W, 16⟩] s.mem s₁.mem := by rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have A₁ : Args p s₁.mem := A.frame L fz fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_args.symm.sub_right (Region.sub_prefix (by decide))
  have a₁₆ := E₁.perm.argR' L (k := 16) (by decide)
  have a₂₀ := E₁.perm.argR' L (k := 20) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₁.sp, a₁₆, a₂₀, A₁.a16, A₁.a20], ?_⟩
  have tW : (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.W, 16⟩ :=
    L.t_w.sub_right (Region.sub_prefix (by decide))
  refine WP.mono (copyLoop_ok _ (S := p.T) (D := p.W) (n := p.tl)
    ⟨by simp [gpr_setReg, E₁.sp, A₁.a16], by simp [gpr_setReg, E₁.r11], by simp [gpr_setReg, E₁.sp, A₁.a20],
      L.tl1, by omega, L.tw, by omega, by simp only [rd_setReg, wr_setReg]; exact E₁.perm.tag,
      by simp only [wr_setReg]; exact covers_prefix E₁.perm.w (by omega),
      tW.sub_right (Region.sub_prefix (by omega))⟩) fun t ⟨m, O⟩ => ?_
  have hT : bytesAt s₁.mem (State.addr p.T) p.tl = bytesAt s.mem (State.addr p.T) p.tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact tW)
      (by omega)
  have hlen := length_bytesAt s₁.mem (State.addr p.T) p.tl
  simp only [mem_setReg] at m
  refine ⟨?_, ?_, E₁.keep (fun r hr => ?_) (by rw [O.sp]; rfl) (by rw [O.rd]; rfl) (by rw [O.wr]; rfl),
    by rw [O.rd]; exact R₁.rd, by rw [O.wr]; exact R₁.wr⟩
  · rw [m, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, hT, R₁.mem]
    have := store4_zero_tail s.mem (State.addr p.W) t16
    exact congrArg _ this
  · rw [m]
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  · simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      (rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg])

/-! ## The comparison -/

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W` and `W + vO` are equal. -/
theorem cmpTail_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr p.W) 16 =
        bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 vO) 16 then 1 else 0) ∧
      Others [.r0, .r1, .r2] s s' ∧ Keeps s s' := by
  have h11 := E.r11
  have r₀ := E.perm.wR (show 0 + 4 ≤ 2560 by decide)
  have r₁ := E.perm.wR (show 4 + 4 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 8 + 4 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 12 + 4 ≤ 2560 by decide)
  have q₀ := E.perm.wR (show 240 + 4 ≤ 2560 by decide)
  have q₁ := E.perm.wR (show 244 + 4 ≤ 2560 by decide)
  have q₂ := E.perm.wR (show 248 + 4 ≤ 2560 by decide)
  have q₃ := E.perm.wR (show 252 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr p.W + BitVec.ofNat 64 (4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr p.W + BitVec.ofNat 64 (240 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorT .r0 0 ++ xorT .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ Others [.r0, .r1, .r2] s s₁ ∧ s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorT]; orun [h11, L.wA, r₀, r₁, q₀, q₁], by others_tac, ?_, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    simp [gpr_setReg, a, b, m]
  have h11₁ : s₁.gpr .r11 = p.W := by rw [g₁ _ (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, h1₂, k₂⟩ : ∃ s₂, runBlock isa (xorT .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++
      xorT .r1 3) s₁ = some s₂ ∧ Others [.r0, .r1, .r2] s₁ s₂ ∧
      s₂.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2 ∧ s₂.gpr .r1 = a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorT]; orun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], by others_tac, ?_, ?_,
      by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · simp [gpr_setReg, a, b, m, hm₁]
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1),
      .dp .sub .r0 .r1 (.reg .r0)] s₂ = some s₃ ∧ Others [.r0, .r1] s₂ s₃ ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - (((s₂.gpr .r0 ||| s₂.gpr .r1) ||| (BitVec.ofNat 32 0 - (s₂.gpr .r0 ||| s₂.gpr .r1))) >>> 31) ∧
      Keeps s₂ s₃ := by
    refine ⟨_, by orun [], by others_tac, ?_, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorT .r0 0 ++ xorT .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorT .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorT .r1 3) ++
      [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1),
        .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, h1₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m, Nat.mul_zero, BitVec.add_zero]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃ r (by simp [hr.1, hr.2.1]), g₂ r (by simp [hr.1, hr.2.1, hr.2.2]), g₁ r (by simp [hr.1, hr.2.1, hr.2.2])]

/-- `cmp`: the first `tl` bytes of the tag at `W + t2O`, padded with zeros
at `W + vO`, compared with the received tag at `W`. -/
theorem cmp_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) :
    WP isa cmp s fun t => t.gpr .r0 = (if bytesAt s.mem (State.addr p.W) 16 =
        bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl) then 1 else 0) ∧
      Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem t.mem ∧ Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  unfold cmp
  refine WP.seq (WP.block_append (WP.mono (zero16_wp (s := s) (o := vO) (by decide)
    (by rw [E.r11]; simp only [vO]; omega) (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have E₁ : Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have fz : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have A₁ : Args p s₁.mem := A.frame L fz fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.args_w' (by decide)
  have a₂₀ := E₁.perm.argR' L (k := 20) (by decide)
  have e₁ : encodable (BitVec.ofNat 32 176) = true := by decide
  have e₂ : encodable (BitVec.ofNat 32 240) = true := by decide
  obtain ⟨s₂, run₂, r1₂, r2₂, r3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 t2O, addI .r2 .r11 vO, .ldrSp .r3 20] s₁ =
      some s₂ ∧ s₂.gpr .r1 = p.W + BitVec.ofNat 32 t2O ∧ s₂.gpr .r2 = p.W + BitVec.ofNat 32 vO ∧
      s₂.gpr .r3 = BitVec.ofNat 32 p.tl ∧ Others [.r1, .r2, .r3] s₁ s₂ ∧ Keeps s₁ s₂ :=
    ⟨_, by orun [E₁.r11, E₁.sp, a₂₀, A₁.a20, e₁, e₂], by simp [gpr_setReg, E₁.r11, t2O],
      by simp [gpr_setReg, E₁.r11, vO], by simp [gpr_setReg, E₁.sp, A₁.a20], by others_tac,
      by exact ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have E₂ : Env p s₂ := E₁.of_others g₂ k₂.sp k₂.rd k₂.wr
  have eS := L.wA (d := t2O) (by decide)
  have eD := L.wA (d := vO) (by decide)
  have dSD : (⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩ :=
    L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (copyLoop_ok s₂ (S := p.W + BitVec.ofNat 32 t2O) (D := p.W + BitVec.ofNat 32 vO) (n := p.tl)
    ⟨r1₂, r2₂, r3₂, L.tl1, by omega, by rw [L.wN (by decide)]; simp only [t2O]; omega,
      by rw [L.wN (by decide)]; simp only [vO]; omega, by rw [eS]; exact E₂.perm.wCR (by simp only [t2O]; omega),
      by rw [eD]; exact E₂.perm.wC (by simp only [vO]; omega),
      by rw [eS, eD]; exact (dSD.sub_left (Region.sub_prefix t16)).sub_right (Region.sub_prefix t16)⟩)
    fun s₃ ⟨m₃, O₃⟩ => ?_)
  rw [eS, eD] at m₃
  have E₃ : Env p s₃ := E₂.keep (fun r hr => by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact O₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    O₃.sp O₃.rd O₃.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := cmpTail_ok L E₃
  have hlen := length_bytesAt s₂.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := by
    have fz' : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₂.mem := by rw [k₂.mem]; exact fz
    rw [m₃]
    exact fz'.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  have hS : bytesAt s₂.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl =
      bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl := by
    rw [k₂.mem]
    exact Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dSD.sub_left (Region.sub_prefix t16)) (by omega)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [k₄.mem]; exact f₃, E₃.keep (fun r hr => g₄ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) k₄.sp k₄.rd k₄.wr,
    by rw [k₄.rd, O₃.rd, k₂.rd, R₁.rd], by rw [k₄.wr, O₃.wr, k₂.wr, R₁.wr]⟩
  have hW : bytesAt s₃.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.W) 16 :=
    Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := 16) (d := vO) (k := 16) (.inl (by decide)) (by decide) (by decide))
      (by decide)
  have hV : bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 vO) 16 =
      bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl) := by
    rw [m₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, hS, k₂.mem, R₁.mem]
    exact congrArg _ (store4_zero_tail s.mem _ t16)
  rw [h0₄, hW, hV]

/-! ## The mask -/

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1, .subs .r5 .r5 (imm 1)]

theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {c : Bool} (h4 : s.gpr .r4 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if c then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if c then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by orun [h4, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      mask_byte]
  · simp [gpr_setReg, h4, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- `mask`: every byte of the data ANDed with `0 − ok`, for `ok ∈ {0, 1}` in
`r0`. -/
theorem mask_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem) {c : Bool}
    (h0 : s.gpr .r0 = if c then 1 else 0) :
    WP isa mask s fun t => Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .r0 = s.gpr .r0 ∧
      t.mem = writeBytes s.mem (State.addr p.D) (if c then bytesAt s.mem (State.addr p.D) p.n else zeros p.n) := by
  have hn := L.dw
  have hn32 := L.n_lt
  have i2 := E.perm.argR' L (k := 8) (by decide)
  have i3 := E.perm.argR' L (k := 12) (by decide)
  obtain ⟨s₁, run₁, h4₁, h5₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r0), .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r4 = p.D ∧ s₁.gpr .r5 = BitVec.ofNat 32 p.n ∧ s₁.gpr .r1 = 0 - (if c then 1 else 0) ∧
      s₁.z = decide (p.n = 0) ∧ Others [.r1, .r4, .r5] s s₁ ∧ Keeps s s₁ := by
    refine ⟨_, by orun [E.sp, i2, i3, A.a8, A.a12], ?_, ?_, ?_, ?_, by others_tac, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp [gpr_setReg, E.sp, A.a8]
    · simp [gpr_setReg, E.sp, A.a12]
    · simp [gpr_setReg, h0, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, E.sp, A.a12, imm]
      rw [z_cmp hn32 (by decide)]
  have E₁ : Env p s₁ := E.of_others g₁ k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (p.n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : p.n = 0 := by simpa using hb
    refine ⟨E₁, k₁.rd, k₁.wr, g₁ _ (by decide), ?_⟩
    rw [k₁.mem, hn0]; cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < p.n := by have : p.n ≠ 0 := by simpa using hb
                           omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ t.gpr .r4 = p.D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (p.n - j) ∧
      t.mem = writeBytes s.mem (State.addr p.D) (if c then bytesAt s.mem (State.addr p.D) j else zeros j) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (p.n - 0) _
    ⟨0, rfl, hn0, by rw [h4₁, add_ofNat_zero], by rw [h5₁]; rfl,
      by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr, k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r4, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r4', r5', z', g', rd', wr', sp'⟩ := maskStep_ok t (c := c) r4 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers (covers_left E.perm.d) hj (by omega))
    (by rw [wr, aD]; exact in_of_covers E.perm.d hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr p.D + BitVec.ofNat 64 j) = s.mem (State.addr p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr p.D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (State.addr p.D)
      (if c then bytesAt s.mem (State.addr p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.z = decide (j + 1 = p.n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = p.n) := eval_ne' hz
  by_cases hjn : j + 1 = p.n
  · left
    refine ⟨by rw [ev]; simp [hjn], E₁.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], by rw [gg _ (by decide) (by decide) (by decide), g₁ _ (by decide)], by rw [hmem, hjn]⟩
  · right
    refine ⟨by rw [ev]; simp [hjn], p.n - (j + 1), by omega, j + 1, rfl, by omega, r4',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-! ## `open` -/

/-- `vg_aes_ocb_open`, for its arguments. -/
theorem open_wp' {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧
      match Spec.Ocb.decryptWith (ciphOf p s₀.mem) (invOf p s₀.mem) (lstarOf p s₀.mem) p.tl
          (bytesAt s₀.mem (State.addr p.N) p.nl) (aadOf p s₀.mem) (bytesAt s₀.mem (State.addr p.D) p.n)
          (bytesAt s₀.mem (State.addr p.T) p.tl) with
      | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr p.D) p.n = pt
      | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr p.D) p.n = Spec.Ocb.zeros p.n := by
  have hn := L.n_lt
  have t16 := L.tl16
  unfold «open» front
  refine WP.seq (WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (pre_wp' L P A hsp h0 h1 h2 h3 hW))
    fun s₃ P₃ => ?_))))
  refine WP.seq (WP.mono (bodyOpen_ok L P₃.env P₃.args P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar]))
    fun s₄ B => ?_)
  have F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut L B.frame
  refine WP.mono (tag_ok L B.env (.inr rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut L (.inr ⟨by decide, by decide⟩) T₅.frame
  have A₅ : Args p s₅.mem := (P₃.args.mut L F₄).mut L F₅
  -- The received tag, at `W`.
  refine WP.seq (WP.mono (recv_ok L T₅.env A₅) fun s₆ ⟨b₆, f₆, E₆, rd₆, wr₆⟩ => ?_)
  have F₆ : Frame (mutR p) s₅.mem s₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok L E₆ (A₅.mut L F₆)) fun s₇ ⟨h0₇, f₇, E₇, rd₇, wr₇⟩ => ?_)
  have F₇ : Frame (mutR p) s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact w_mut L (.inr ⟨by decide, by decide⟩)
  let c : Bool := decide (bytesAt s₆.mem (State.addr p.W) 16 =
    bytesAt s₆.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl))
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₇ ((A₅.mut L F₆).mut L F₇) (c := c) (by
    rw [h0₇]; simp only [c]; split <;> simp_all)) fun s₈ ⟨E₈, rd₈, wr₈, g0₈, m₈⟩ => ?_)
  have F₈ : Frame [⟨State.addr p.D, p.n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have sv₈ : SavedAt s₈.mem p.W s₀ :=
    ((((P₃.saved.frame F₄ (saved_mut L)).frame F₅ (saved_mut L)).frame F₆ (saved_mut L)).frame F₇
      (saved_mut L)).frame F₈ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.d_w' (by decide)).symm
  -- `restore`.
  refine WP.mono (restore_ok E₈.r11 L.ww (covers_left E₈.perm.w) sv₈ (by rw [E₈.sp, hsp]))
    fun s' ⟨ab, hm, hr0, _, _⟩ => ⟨ab, ?_⟩
  have x0 : s'.gpr .r0 = if c then 1 else 0 := by
    rw [hr0, g0₈, h0₇]; simp only [c]; split <;> simp_all
  have c₃ : ciphOf p s₃.mem = ciphOf p s₀.mem := by simp only [ciphOf, P₃.sched]
  have i₃ : invOf p s₃.mem = invOf p s₀.mem := by simp only [invOf, P₃.sched]
  have c₄ : ciphOf p s₄.mem = ciphOf p s₀.mem := by simp only [ciphOf, sched_mut L F₄, P₃.sched]
  have hout := B.out
  rw [c₃, i₃, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [c₃, i₃, P₃.lstar, P₃.data] at hck
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ciphOf p s₀.mem) (lstarOf p s₀.mem) (aadOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.sum]
  have tagv := T₅.val
  rw [hck, hofs, ld₄, sum₄, c₄] at tagv
  have d₇ : bytesAt s₇.mem (State.addr p.D) p.n = bytesAt s₄.mem (State.addr p.D) p.n := by
    rw [Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.d_w.sub_right (Region.sub_prefix (by decide))) (by omega)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (by ddisj L) (by omega)
  have d₈ : bytesAt s'.mem (State.addr p.D) p.n = if c then bytesAt s₄.mem (State.addr p.D) p.n else zeros p.n := by
    rw [hm, m₈, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) (by omega), length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₇]
  have recv : bytesAt s₆.mem (State.addr p.W) 16 = bytesAt s₀.mem (State.addr p.T) p.tl ++ zeros (16 - p.tl) := by
    rw [b₆, tag_mut L F₅, tag_mut L F₄, P₃.tag]
  have t2₆ : bytesAt s₆.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl =
      bytesAt s₅.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L.w_w (a := t2O) (n := p.tl) (d := 0) (k := 16) (.inr (by decide)) (by simp only [t2O]; omega)
        (by decide))) (by omega)
  have hc : ∀ x : Block, bytesAt s₅.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl = (Spec.Ocb.toBytes x).take p.tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take p.tl = bytesAt s₀.mem (State.addr p.T) p.tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [recv, t2₆, hx, decide_eq_true_iff, List.append_cancel_right_eq, eq_comm]
  rw [x0, d₈, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, rfl⟩
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, rfl⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp {s : State} (h : openArm.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' :=
  open_wp' (lay_of h.2.2) (openPerm h) (args_of s) rfl rfl (ofNat_toNat32' _).symm rfl (ofNat_toNat32' _).symm rfl

end VG.Proof.AesOcb.Arm
