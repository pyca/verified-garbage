module

public import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.AesOcb.Arm.CTFn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import Batteries.Logic
public import VerifiedGarbage.Impl.AesOcb.Arm
public import VerifiedGarbage.Proof.AesOcb.Arm.Env
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.AesGcm.Arm.Blocks
public import VerifiedGarbage.Proof.AesOcb.Arm.Body
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesOcb.Arm.RestTag
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Aes.Ct32.Layers
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesOcb.Arm.Hash
import VerifiedGarbage.Proof.AesOcb.Arm.HashChunk
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Ocb.Contract
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-! ### `AesOcb.Arm.Verified`, which only this module used -/

section

/-! ### `AesOcb.Arm.Open`, which only this module used -/

section

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

@[expose] public section

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
    (by rw [E.r11]; simp only [tagO]; omega_arith) (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11, show State.addr p.W + BitVec.ofNat 64 tagO = State.addr p.W from BitVec.add_zero _] at R₁
  obtain E₁ : Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  obtain fz : Frame [⟨State.addr p.W, 16⟩] s.mem s₁.mem := by rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain A₁ : Args p s₁.mem := A.frame L fz fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_args.symm.sub_right (Region.sub_prefix (by decide))
  obtain a₁₆ := E₁.perm.argR' L (k := 16) (by decide)
  obtain a₂₀ := E₁.perm.argR' L (k := 20) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₁.sp, a₁₆, a₂₀, A₁.a16, A₁.a20], ?_⟩
  obtain tW : (⟨State.addr p.T, p.tl⟩ : Region).Disjoint ⟨State.addr p.W, 16⟩ :=
    L.t_w.sub_right (Region.sub_prefix (by decide))
  refine WP.mono (copyLoop_ok _ (S := p.T) (D := p.W) (n := p.tl)
    ⟨by simp [gpr_setReg, E₁.sp, A₁.a16], by simp [gpr_setReg, E₁.r11], by simp [gpr_setReg, E₁.sp, A₁.a20],
      L.tl1, by omega_arith, L.tw, by omega_arith, by simp only [rd_setReg, wr_setReg]; exact E₁.perm.tag,
      by simp only [wr_setReg]; exact covers_prefix E₁.perm.w (by omega_arith),
      tW.sub_right (Region.sub_prefix (by omega_arith))⟩) fun t ⟨m, O⟩ => ?_
  obtain hT : bytesAt s₁.mem (State.addr p.T) p.tl = bytesAt s.mem (State.addr p.T) p.tl :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact tW)
      (by omega_arith)
  obtain hlen := length_bytesAt s₁.mem (State.addr p.T) p.tl
  simp only [mem_setReg] at m
  refine ⟨?_, ?_, E₁.keep (fun r hr => ?_) (by rw [O.sp]; rfl) (by rw [O.rd]; rfl) (by rw [O.wr]; rfl),
    by rw [O.rd]; exact R₁.rd, by rw [O.wr]; exact R₁.wr⟩
  · rw [m, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by omega_arith), hlen, hT, R₁.mem]
    have := store4_zero_tail s.mem (State.addr p.W) t16
    exact congrArg _ this
  · rw [m]
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
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
  obtain r₀ := E.perm.wR (show 0 + 4 ≤ 2560 by decide)
  obtain r₁ := E.perm.wR (show 4 + 4 ≤ 2560 by decide)
  obtain r₂ := E.perm.wR (show 8 + 4 ≤ 2560 by decide)
  obtain r₃ := E.perm.wR (show 12 + 4 ≤ 2560 by decide)
  obtain q₀ := E.perm.wR (show 240 + 4 ≤ 2560 by decide)
  obtain q₁ := E.perm.wR (show 244 + 4 ≤ 2560 by decide)
  obtain q₂ := E.perm.wR (show 248 + 4 ≤ 2560 by decide)
  obtain q₃ := E.perm.wR (show 252 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr p.W + BitVec.ofNat 64 (4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr p.W + BitVec.ofNat 64 (240 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorT .r0 0 ++ xorT .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ Others [.r0, .r1, .r2] s s₁ ∧ s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorT]; orun [h11, L.wA, r₀, r₁, q₀, q₁], by others_tac, ?_, by exact ⟨rfl, rfl, rfl, rfl⟩⟩
    simp [gpr_setReg, a, b, m]
  obtain h11₁ : s₁.gpr .r11 = p.W := by rw [g₁ _ (by decide), h11]
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
    (by rw [E.r11]; simp only [vO]; omega_arith) (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  obtain E₁ : Env p s₁ := E.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  obtain fz : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain A₁ : Args p s₁.mem := A.frame L fz fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.args_w' (by decide)
  obtain a₂₀ := E₁.perm.argR' L (k := 20) (by decide)
  obtain e₁ : encodable (BitVec.ofNat 32 176) = true := by decide
  obtain e₂ : encodable (BitVec.ofNat 32 240) = true := by decide
  obtain ⟨s₂, run₂, r1₂, r2₂, r3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 t2O, addI .r2 .r11 vO, .ldrSp .r3 20] s₁ =
      some s₂ ∧ s₂.gpr .r1 = p.W + BitVec.ofNat 32 t2O ∧ s₂.gpr .r2 = p.W + BitVec.ofNat 32 vO ∧
      s₂.gpr .r3 = BitVec.ofNat 32 p.tl ∧ Others [.r1, .r2, .r3] s₁ s₂ ∧ Keeps s₁ s₂ :=
    ⟨_, by orun [E₁.r11, E₁.sp, a₂₀, A₁.a20, e₁, e₂], by simp [gpr_setReg, E₁.r11, t2O],
      by simp [gpr_setReg, E₁.r11, vO], by simp [gpr_setReg, E₁.sp, A₁.a20], by others_tac,
      by exact ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain E₂ : Env p s₂ := E₁.of_others g₂ k₂.sp k₂.rd k₂.wr
  obtain eS := L.wA (d := t2O) (by decide)
  obtain eD := L.wA (d := vO) (by decide)
  obtain dSD : (⟨State.addr p.W + BitVec.ofNat 64 t2O, 16⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩ :=
    L.w_w (.inl (by decide)) (by decide) (by decide)
  refine WP.seq (WP.mono (copyLoop_ok s₂ (S := p.W + BitVec.ofNat 32 t2O) (D := p.W + BitVec.ofNat 32 vO) (n := p.tl)
    ⟨r1₂, r2₂, r3₂, L.tl1, by omega_arith, by rw [L.wN (by decide)]; simp only [t2O]; omega_arith,
      by rw [L.wN (by decide)]; simp only [vO]; omega_arith, by rw [eS]; exact E₂.perm.wCR (by simp only [t2O]; omega_arith),
      by rw [eD]; exact E₂.perm.wC (by simp only [vO]; omega_arith),
      by rw [eS, eD]; exact (dSD.sub_left (Region.sub_prefix t16)).sub_right (Region.sub_prefix t16)⟩)
    fun s₃ ⟨m₃, O₃⟩ => ?_)
  rw [eS, eD] at m₃
  obtain E₃ : Env p s₃ := E₂.keep (fun r hr => by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact O₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    O₃.sp O₃.rd O₃.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := cmpTail_ok L E₃
  obtain hlen := length_bytesAt s₂.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl
  obtain f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₃.mem := by
    obtain fz' : Frame [⟨State.addr p.W + BitVec.ofNat 64 vO, 16⟩] s.mem s₂.mem := by rw [k₂.mem]; exact fz
    rw [m₃]
    exact fz'.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  obtain hS : bytesAt s₂.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl =
      bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl := by
    rw [k₂.mem]
    exact Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dSD.sub_left (Region.sub_prefix t16)) (by omega_arith)
  refine WP.of_runBlock ⟨s₄, run₄, ?_, by rw [k₄.mem]; exact f₃, E₃.keep (fun r hr => g₄ r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) k₄.sp k₄.rd k₄.wr,
    by rw [k₄.rd, O₃.rd, k₂.rd, R₁.rd], by rw [k₄.wr, O₃.wr, k₂.wr, R₁.wr]⟩
  obtain hW : bytesAt s₃.mem (State.addr p.W) 16 = bytesAt s.mem (State.addr p.W) 16 :=
    Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := 16) (d := vO) (k := 16) (.inl (by decide)) (by decide) (by decide))
      (by decide)
  obtain hV : bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 vO) 16 =
      bytesAt s.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl) := by
    rw [m₃, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by omega_arith), hlen, hS, k₂.mem, R₁.mem]
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
                           omega_arith
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
    (by rw [rd, wr, aD]; exact in_of_covers (covers_left E.perm.d) hj (by omega_arith))
    (by rw [wr, aD]; exact in_of_covers E.perm.d hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr p.D + BitVec.ofNat 64 j) = s.mem (State.addr p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr p.D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  have hmem : t'.mem = writeBytes s.mem (State.addr p.D)
      (if c then bytesAt s.mem (State.addr p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
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
    refine ⟨by rw [ev]; simp [hjn], p.n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, r4',
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
  obtain F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut L B.frame
  refine WP.mono (tag_ok L B.env (.inr rfl)) fun s₅ T₅ => ?_
  obtain F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut L (.inr ⟨by decide, by decide⟩) T₅.frame
  obtain A₅ : Args p s₅.mem := (P₃.args.mut L F₄).mut L F₅
  -- The received tag, at `W`.
  refine WP.seq (WP.mono (recv_ok L T₅.env A₅) fun s₆ ⟨b₆, f₆, E₆, rd₆, wr₆⟩ => ?_)
  obtain F₆ : Frame (mutR p) s₅.mem s₆.mem := f₆.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok L E₆ (A₅.mut L F₆)) fun s₇ ⟨h0₇, f₇, E₇, rd₇, wr₇⟩ => ?_)
  obtain F₇ : Frame (mutR p) s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact w_mut L (.inr ⟨by decide, by decide⟩)
  let c : Bool := decide (bytesAt s₆.mem (State.addr p.W) 16 =
    bytesAt s₆.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl ++ zeros (16 - p.tl))
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₇ ((A₅.mut L F₆).mut L F₇) (c := c) (by
    rw [h0₇]; simp only [c]; split <;> simp_all)) fun s₈ ⟨E₈, rd₈, wr₈, g0₈, m₈⟩ => ?_)
  obtain F₈ : Frame [⟨State.addr p.D, p.n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain sv₈ : SavedAt s₈.mem p.W s₀ :=
    ((((P₃.saved.frame F₄ (saved_mut L)).frame F₅ (saved_mut L)).frame F₆ (saved_mut L)).frame F₇
      (saved_mut L)).frame F₈ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (L.d_w' (by decide)).symm
  -- `restore`.
  refine WP.mono (restore_ok E₈.r11 L.ww (covers_left E₈.perm.w) sv₈ (by rw [E₈.sp, hsp]))
    fun s' ⟨ab, hm, hr0, _, _⟩ => ⟨ab, ?_⟩
  obtain x0 : s'.gpr .r0 = if c then 1 else 0 := by
    rw [hr0, g0₈, h0₇]; simp only [c]; split <;> simp_all
  obtain c₃ : ciphOf p s₃.mem = ciphOf p s₀.mem := by simp only [ciphOf, P₃.sched]
  obtain i₃ : invOf p s₃.mem = invOf p s₀.mem := by simp only [invOf, P₃.sched]
  obtain c₄ : ciphOf p s₄.mem = ciphOf p s₀.mem := by simp only [ciphOf, sched_mut L F₄, P₃.sched]
  have hout := B.out
  rw [c₃, i₃, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [c₃, i₃, P₃.lstar, P₃.data] at hck
  obtain ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ciphOf p s₀.mem) (lstarOf p s₀.mem) (aadOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.sum]
  have tagv := T₅.val
  rw [hck, hofs, ld₄, sum₄, c₄] at tagv
  obtain d₇ : bytesAt s₇.mem (State.addr p.D) p.n = bytesAt s₄.mem (State.addr p.D) p.n := by
    rw [Proof.Cmac.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega_arith),
      Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.d_w.sub_right (Region.sub_prefix (by decide))) (by omega_arith)]
    exact Proof.Cmac.bytesAt_frame T₅.frame (by ddisj L) (by omega_arith)
  obtain d₈ : bytesAt s'.mem (State.addr p.D) p.n = if c then bytesAt s₄.mem (State.addr p.D) p.n else zeros p.n := by
    rw [hm, m₈, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) (by omega_arith), length_mask,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₇]
  obtain recv : bytesAt s₆.mem (State.addr p.W) 16 = bytesAt s₀.mem (State.addr p.T) p.tl ++ zeros (16 - p.tl) := by
    rw [b₆, tag_mut L F₅, tag_mut L F₄, P₃.tag]
  obtain t2₆ : bytesAt s₆.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl =
      bytesAt s₅.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using (L.w_w (a := t2O) (n := p.tl) (d := 0) (k := 16) (.inr (by decide)) (by simp only [t2O]; omega_arith)
        (by decide))) (by omega_arith)
  obtain hc : ∀ x : Block, bytesAt s₅.mem (State.addr p.W + BitVec.ofNat 64 t2O) p.tl = (Spec.Ocb.toBytes x).take p.tl →
      (c = true ↔ (Spec.Ocb.toBytes x).take p.tl = bytesAt s₀.mem (State.addr p.T) p.tl) := fun x hx => by
    show decide (_ = _) = true ↔ _
    rw [recv, t2₆, hx, decide_eq_true_iff, List.append_cancel_right_eq, eq_comm]
  rw [x0, d₈, hout, Proof.Ocb.decryptWith_eq]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega_arith
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ t16, tagv] at hc
    obtain hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, rfl⟩
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega_arith
    simp only [h', hr, ↓reduceIte] at tagv ⊢
    rw [bytesAt_take_block _ _ t16, tagv] at hc
    obtain hc := hc _ rfl
    by_cases hk : c = true
    · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
    · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, rfl⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp {s : State} (h : openArm.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openArm.post s s' :=
  open_wp' (lay_of h.2.2) (openPerm h) (args_of s) rfl rfl (ofNat_toNat32' _).symm rfl (ofNat_toNat32' _).symm rfl

end VG.Proof.AesOcb.Arm

end

end


/-!
# AES-OCB on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`), with 8 bytes of stack: each call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` pushes two words.
`Frame.lean` allocates the working space.
-/

@[expose] public section

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Impl.AesOcb.Arm

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte
nonce, no associated data, no data, a 4-byte tag at `0x3000` and `work` at
0. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8014 then 4 else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 28⟩], wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem seal_verified : Verified Arm.target «seal» (Proof.AesOcb.sealScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => seal_wp hs) seal_ct (by
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealArm, sealPre, oneLay, onePub, bel, arg, args, roundsOk, ciph, lstar, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified : Verified Arm.target «open» (Proof.AesOcb.openScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => open_wp hs) open_ct
    { pre := by
        sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, openArm, openPre, oneLay, onePub, openLeak, bel, arg, args, roundsOk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Proof.AesOcb.openRoundsPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [openArm, openRes, ciph, inv, lstar, Arm.State.addr] at h
        obtain e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, openArm, openPre, oneLay, onePub, openLeak, openRes, ciph, inv, lstar, bel, arg, args,
          roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, hl⟩
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0
        · exact a1
        · exact a2
        · exact a3
        · exact a4
        · exact a5
        · exact a6
      sat := by
        sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Spec.Ocb.openLeak, openArm, openPre, oneLay, onePub, openLeak, bel, arg, args, roundsOk, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesOcb.Arm

end

end


/-!
# AES-OCB on ARMv7, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratch`): their working space is their seventh stack
argument, after `aad`, `aad_len`, `data`, `len`, `tag` and `tag_len`, so the
frame of 2592 bytes holds a copy of those six words, the address of the
working space, the saved `lr` and the working space. The copies are read
only where the pre- and postconditions read the buffers, and `open`'s leak,
whether it succeeds, reads only its buffers (`Proof/AesOcb/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Impl.AesOcb.Arm

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract Arm.abi 2600).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»)
      (Proof.AesOcb.sealRoundsContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.sealPre Arm.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) seal_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _)
    (Proof.AesOcb.sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract Arm.abi 2600).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Proof.AesOcb.openRoundsContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ocb.openPre Arm.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak Arm.abi.ptrBits))
    (m := 6) open_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _)
    (Proof.AesOcb.openPostOut_local _) openFrameSat_pre
    (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.Arm
