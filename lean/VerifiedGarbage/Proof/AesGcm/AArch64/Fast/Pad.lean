module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Flush
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# AES-GCM on AArch64, the path for TLS records: padded blocks

Untrusted: everything here is checked by Lean. `padMul` copies the `x13`
bytes (at most 16) at `x12` into `T`, zeroed first, and multiplies `T` into
`Y` (`padMul_ok`): GHASH continued over the bytes padded to a block
(`padStep`, `ghashFrom_pad`). The copy writes no vector register
(`WP.keepV`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes)
open VG.Proof.Gcm (blocks_append)

/-- Code that writes no vector register keeps them all. -/
theorem WP.keepV {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : (instrs c).all (fun i => (vdstOf i).isNone) = true) : WP isa c s fun s' => Q s' ∧ s'.v = s.v := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, funext fun r => Exec.vec (fun i hi e => ?_) he⟩
  have := List.all_eq_true.mp hc i hi
  rw [e] at this
  cases this

theorem copy_novec : (instrs copy).all (fun i => (vdstOf i).isNone) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

/-- GHASH continued over the bytes `b` (at most a block) padded with zeros. -/
def padStep (H y : Block) (b : List Byte) : Block :=
  if b = [] then y else Spec.Gcm.mul (y ^^^ ofBytes (b ++ zeros (16 - b.length))) H

theorem ghashFrom_pad (H y : Block) {b : List Byte} (hb : b.length ≤ 16) :
    ghashFrom H y (blocks (b ++ zeros (padLen b.length))) = padStep H y b := by
  by_cases h0 : b = []
  · subst h0; rfl
  · have hl : 0 < b.length := List.length_pos_iff.mpr h0
    have hp : padLen b.length = 16 - b.length := by simp only [padLen]; omega
    rw [hp, Proof.Gcm.blocks_single (by simp [Spec.Gcm.zeros]; omega)]
    simp only [padStep, h0, ↓reduceIte]
    rfl

/-- `padMul`: the `n` bytes at `P`, padded in `T`, multiplied into `Y`. -/
theorem padMul_ok (hM : MulKey) {Ctx St W SP : Addr} {H y : Block} {P : Addr} {n : Nat} {s : State} (he : Env Ctx St W SP s) (hk : HKey H s)
    (hy : s.v Y = ext8 y y) (h12 : s.gpr .x12 = P) (h13 : s.gpr .x13 = BitVec.ofNat 64 n) (hn : n ≤ 16)
    (hP : Covers [⟨P, n⟩] (s.rd ++ s.wr)) (hPW : (⟨P, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 16⟩) :
    WP isa Impl.AesGcm.AArch64.Fast.padMul s fun s' =>
      s'.v Y = ext8 (padStep H y (bytesAt s.mem P n)) (padStep H y (bytesAt s.mem P n)) ∧ HKey H s' ∧ Env Ctx St W SP s' ∧
      Others [.x9, .x11, .x12, .x13, .x14, .x15] s s' ∧ Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ [A, LO, MID, HI, T, Y] → s'.v r = s.v r) := by
  unfold Impl.AesGcm.AArch64.Fast.padMul
  refine WP.ite (decide (n = 0)) (eval_zero h13 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by rw [show bytesAt s.mem P 0 = [] from rfl]; exact hy, hk, he, fun _ _ => rfl,
      Frame.refl _ _, fun _ _ => rfl⟩
  have h0 : n ≠ 0 := by simpa using hf
  have w₁ := he.perm.wW (show 96 + 8 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 104 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, m₁, x11₁, r₁⟩ : ∃ s₁, runBlock isa (Impl.AesGcm.AArch64.Fast.zeroT ++ [ptr .x11 .x19 tO]) s =
      some s₁ ∧ s₁.mem = (s.mem.writeW (W + BitVec.ofNat 64 96) (0 : BitVec 64)).writeW
        (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 96 ∧ Others [.x9, .x11] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.v = s.v := by
    refine ⟨_, by simp only [Impl.AesGcm.AArch64.Fast.zeroT]; arun [he.x19, w₁, w₂], ?_⟩
    refine ⟨?_, by simp [gpr_write, he.x19], by others_tac, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.mem_write, Mem.writeW, BitVec.setWidth_eq, add_ofNat_assoc]; rfl
  obtain ⟨og₁, sp₁, rd₁, wr₁, v₁⟩ := r₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ P (W + BitVec.ofNat 64 96) n := by
    refine ⟨by omega, by rw [rd₁, wr₁]; exact hP, by rw [wr₁]; exact he.perm.wC (by omega),
      hPW.sub_right (Region.sub_prefix (by omega))⟩
  refine WP.seq (WP.mono (WP.keepV (copy_ok s₁ (by rw [og₁ _ (by decide), h12]) x11₁
    (by rw [og₁ _ (by decide), h13]) lp) copy_novec) fun s₂ ⟨⟨m₂, g₂, sp₂, rd₂, wr₂⟩, v₂⟩ => ?_)
  have fz : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hPo : bytesAt s₁.mem P n = bytesAt s.mem P n :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hPW) (by omega)
  have hlen := length_bytesAt s₁.mem P n
  have hT : bytesAt s₂.mem (W + BitVec.ofNat 64 96) 16 = bytesAt s.mem P n ++ zeros (16 - n) := by
    rw [m₂, bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hPo]
    congr 1
    have := zeroT_bytes s.mem (W + BitVec.ofNat 64 96)
    rw [← m₁, show (16 : Nat) = n + (16 - n) by omega, bytesAt_add] at this
    have e := congrArg (List.drop n) this
    rw [List.drop_left' (length_bytesAt _ _ _)] at e
    rw [e, show n + (16 - n) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  have gg : ∀ r, r ∉ [Reg.x9, .x11, .x12, .x13, .x14, .x15] → s₂.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    have h₁ : r ∉ loopRegs := by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩
    have h₂ : r ∉ [Reg.x9, .x11] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1⟩
    rw [g₂ r h₁, og₁ r h₂]
  have he₂ : Env Ctx St W SP s₂ := he.keep (fun r hr => gg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have vv : s₂.v = s.v := by rw [v₂, v₁]
  have hk₂ : HKey H s₂ := hk.of_v (by rw [vv]) (by rw [vv]) (by rw [vv])
  refine WP.mono (mulT_ok hM (y := y) hk₂ (by rw [vv]; exact hy) (by rw [he₂.x19]; exact he₂.perm.wR (by decide)))
    fun s₃ ⟨y₃, hk₃, o₃⟩ => ⟨?_, hk₃, he₂.keep (fun r _ => by rw [o₃.gpr]) o₃.sp o₃.rd o₃.wr,
      fun r hr => by rw [o₃.gpr, gg r hr], ?_, fun r hr => by rw [o₃.v r hr, vv]⟩
  · have hne : bytesAt s.mem P n ≠ [] := fun e => h0 (by simpa [length_bytesAt] using congrArg List.length e)
    rw [y₃, he₂.x19, blockAt, show tO = 96 from rfl, hT]
    simp only [padStep, hne, ↓reduceIte, length_bytesAt]
  · rw [o₃.mem, m₂]
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- GHASH of the padded input, from that of the additional data padded and
the whole blocks `w` of the text, and its last bytes `t`. -/
theorem ghash_padded (H : Block) (a w t : List Byte) (hw : w.length % 16 = 0) (ht : t.length < 16) :
    ghash H (blocks (Proof.Gcm.padded a (w ++ t))) =
      padStep H (ghash H (blocks (a ++ zeros (padLen a.length) ++ w))) t := by
  by_cases hc : w ++ t = []
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hc
    simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_nil, List.append_nil, padStep, ↓reduceIte, List.nil_append]
  · have hX : (a ++ zeros (padLen a.length) ++ w).length % 16 = 0 := by
      simp only [List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length
      omega
    have hp : padLen (a ++ zeros (padLen a.length) ++ (w ++ t)).length = padLen t.length := by
      have h := hX
      simp only [List.length_append, Proof.Gcm.length_zeros] at h ⊢
      simp only [padLen] at h ⊢; omega
    rw [Proof.Gcm.padded, Proof.Gcm.ghashInput_of_ne hc, hp, ← List.append_assoc, List.append_assoc _ t,
      blocks_append hX, ghash, Proof.Gcm.ghashFrom_append, ← ghash, ghashFrom_pad H _ (by omega)]

end VG.Proof.AesGcm.AArch64.Fast
