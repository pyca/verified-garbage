module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Pad
public import VerifiedGarbage.Proof.AesGcm.AArch64.Tail.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on AArch64, the path for TLS records: the last bytes, from the end of the text

Untrusted: everything here is checked by Lean. `padMulT` absorbs the `x13`
bytes at `x12` padded to a block, as `padMul` does (`padMulT_ok`, with the
same result): by `padMul` for a text (of `x26` bytes) shorter than a block,
and otherwise by `Tail.padVec`, from the 16 bytes that end the text, moved
down into the padded block (`Tail.pad_vec`) in a register.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Impl.AesGcm.AArch64.Tail (idxName idxTable padVec shift fill)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes)

theorem syms_write' (s : State) (sz : Size) (r : Reg) (x : BitVec sz.bits) : (s.write sz r x).syms = s.syms := rfl
theorem syms_setV' (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).syms = s.syms := rfl
theorem idxTable_length' : idxTable.length = 4 := rfl

/-- The 16 bytes that end the last `m < 16` bytes of a readable text of `N`
bytes at `D₀` (`padMulT_ok`'s `hbig`). -/
theorem pad_big {rs : List Region} {D₀ P : Addr} {N m : Nat} (h : Covers [⟨D₀, N⟩] rs) (hN : N < 2 ^ 64)
    (hP : P = D₀ + BitVec.ofNat 64 (N - m)) (hm : m < 16) :
    16 ≤ N → m ≠ 0 → m < 16 ∧ ∃ E, E + BitVec.ofNat 64 (16 - m) = P ∧ InRegions rs E 16 := fun h16 _ =>
  ⟨hm, D₀ + BitVec.ofNat 64 (N - 16), by rw [hP, Offset.add_add]; congr 2; omega, in_off h (by omega) hN⟩

/-- `padVec`'s loads: the 16 bytes ending the `r` bytes at `x12`, moved down
into the padded block in `A`. -/
theorem padPre_run {E : Addr} {r : Nat} (hr : r < 16) {s : State}
    (h12 : s.gpr .x12 = E + BitVec.ofNat 64 (16 - r)) (h13 : s.gpr .x13 = BitVec.ofNat 64 r)
    (hE : InRegions (s.rd ++ s.wr) E 16) :
    ∃ s', runBlock isa (fill ++ shift .x13 A .x11 ++ ([.ldrqTbl T .x11 16 idxName idxTable, .vop (.add .b16 T T A),
        .sub .x .x11 .x12 .x9, .ldrq A .x11 0, .vop (.tbl A A T)] : List Instr)) s = some s' ∧
      s'.v A = Tail.downV (s.mem.read E 16) r ∧ (∀ v, v ≠ A → v ≠ T → s'.v v = s.v v) ∧
      Others [.x9, .x11] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h16 : (BitVec.setWidth 64 (16#16) <<< 0 : BitVec 64) = BitVec.ofNat 64 16 := by decide
  have hsub : BitVec.ofNat 64 16 - BitVec.ofNat 64 r = BitVec.ofNat 64 (16 - r) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  have hx11 : E + BitVec.ofNat 64 (16 - r) - BitVec.ofNat 64 (16 - r) = E := BitVec.add_sub_cancel _ _
  refine ⟨_, by
    simp only [fill, shift, List.replicate, List.cons_append, List.nil_append]
    arun [h12, h13, h16, hsub, hx11, hE, VOp.eval, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.wr_setV, RegUpd.rd_setV,
      RegUpd.sp_setV, RegUpd.rd_write, syms_write', syms_setV', idxTable_length', Nat.reduceDiv, RegUpd.v_write, BitVec.add_zero]
    , ?_⟩
  refine ⟨rfl, fun v h₁ h₂ => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [RegUpd.v_setV, RegUpd.v_write, h₁, h₂]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, RegUpd.gpr_setV, hr]

/-- `padMulT`: `padMul`'s result, for `n` bytes at `P` that, if the text (of
`N` bytes, in `x26`) is at least a block long and `n` is not zero, end 16
bytes at `E` the code may read. -/
theorem padMulT_ok (hM : MulKey) {Ctx St W SP : Addr} {H y : Block} {P : Addr} {n N : Nat} {s : State}
    (he : Env Ctx St W SP s) (hk : HKey H s)
    (hy : s.v Y = ext8 y y) (h12 : s.gpr .x12 = P) (h13 : s.gpr .x13 = BitVec.ofNat 64 n) (hn : n ≤ 16)
    (hP : Covers [⟨P, n⟩] (s.rd ++ s.wr)) (hPW : (⟨P, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 96, 16⟩)
    (h26 : s.gpr .x26 = BitVec.ofNat 64 N) (hN : N < 2 ^ 64)
    (hbig : 16 ≤ N → n ≠ 0 → n < 16 ∧ ∃ E, E + BitVec.ofNat 64 (16 - n) = P ∧ InRegions (s.rd ++ s.wr) E 16) :
    WP isa Impl.AesGcm.AArch64.Fast.padMulT s fun s' =>
      s'.v Y = ext8 (padStep H y (bytesAt s.mem P n)) (padStep H y (bytesAt s.mem P n)) ∧ HKey H s' ∧
      Env Ctx St W SP s' ∧
      Others [.x9, .x11, .x12, .x13, .x14, .x15] s s' ∧ Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s'.mem ∧
      (∀ r, r ∉ [A, LO, MID, HI, T, Y] → s'.v r = s.v r) := by
  refine WP.ite (decide (n = 0)) (eval_zero h13 (by omega)) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : n = 0 := of_decide_eq_true ht
    subst h0
    exact WP.block_nil ⟨by rw [show bytesAt s.mem P 0 = [] from rfl]; exact hy, hk, he, fun _ _ => rfl,
      Frame.refl _ _, fun _ _ => rfl⟩
  have h0 : n ≠ 0 := of_decide_eq_false hf'
  obtain ⟨s₁, run₁, x9₁, r₁, v₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x9 .x26 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (N / 16) ∧ Regs [.x9] s s₁ ∧ s₁.v = s.v := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩, rfl⟩
    simp [gpr_write, h26, lsr_ofNat _ _ hN]
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => r₁.others r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) r₁.sp r₁.rd r₁.wr
  have hk₁ : HKey H s₁ := hk.of_v (by rw [v₁]) (by rw [v₁]) (by rw [v₁])
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (N / 16 = 0)) (eval_zero x9₁ (by omega)) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (padMul_ok hM (y := y) he₁ hk₁ (by rw [v₁]; exact hy) (by rw [r₁.others _ (by decide), h12])
      (by rw [r₁.others _ (by decide), h13]) hn (by rw [r₁.rd, r₁.wr]; exact hP) hPW)
      fun s' ⟨y', k', e', o', f', v'⟩ => ⟨by rw [y', r₁.mem], k', e', fun r hr => by
        rw [o' r hr, r₁.others r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1)],
        by rw [← r₁.mem]; exact f', fun r hr => by rw [v' r hr, v₁]⟩
  have hbN : 16 ≤ N := by have := of_decide_eq_false hf; omega
  obtain ⟨hn16, E, hE, hEr⟩ := hbig hbN h0
  obtain ⟨s₂, run₂, a₂, v₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := padPre_run (s := s₁) (E := E) hn16
    (by rw [r₁.others _ (by decide), h12, hE]) (by rw [r₁.others _ (by decide), h13])
    (by rw [r₁.rd, r₁.wr]; exact hEr)
  have vv : ∀ v, v ≠ A → v ≠ T → s₂.v v = s.v v := fun v h₁ h₂ => by rw [v₂ v h₁ h₂, v₁]
  have hk₂ : HKey H s₂ := hk.of_v (vv _ (by decide) (by decide)) (vv _ (by decide) (by decide))
    (vv _ (by decide) (by decide))
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have hpv : padVec = (fill ++ shift .x13 A .x11 ++ [.ldrqTbl T .x11 16 idxName idxTable, .vop (.add .b16 T T A),
      .sub .x .x11 .x12 .x9, .ldrq A .x11 0, .vop (.tbl A A T)]) ++
      (([.vop (.logic .eor A A Y)] : List Instr) ++ Impl.Gcm.AArch64.Pmull.mul Y A (sReg 1) (tReg 1)) := by
    simp [padVec]
  rw [hpv, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₂) fun s₃ ⟨e₃, o₃⟩ => ?_
  have hk₃ : HKey H s₃ := hk₂.of_vonly o₃ (by decide) (by decide) (by decide)
  refine WP.mono (mulV_ok Y A (sReg 1) (tReg 1) s₃ free_A (sReg_free _) (tReg_free _) hk₃.sw hk₃.c)
    fun s₄ ⟨m₄, o₄⟩ => ⟨?_, hk₃.of_vonly o₄ (by decide) (by decide) (by decide),
      he₂.keep (fun r _ => by rw [o₄.gpr, o₃.gpr]) (by rw [o₄.sp, o₃.sp]) (by rw [o₄.rd, o₃.rd])
        (by rw [o₄.wr, o₃.wr]), fun r hr => ?_, ?_, fun r hr => ?_⟩
  · have hne : bytesAt s.mem P n ≠ [] := fun e => h0 (by simpa [length_bytesAt] using congrArg List.length e)
    have hY₂ : s₂.v Y = s.v Y := vv Y (by decide) (by decide)
    rw [m₄, e₃, a₂, hY₂, hy, r₁.mem, Tail.pad_vec _ _ (by omega) hn16, hE, rev64b_read, ← ext8_xor, hk₃.t, hM,
      BitVec.xor_comm, Tail.blockAt_padMem _ _ hn]
    simp only [padStep, hne, ↓reduceIte, length_bytesAt]
  · rw [o₄.gpr, o₃.gpr, g₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.1, hr.2.1⟩),
      r₁.others r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1)]
  · rw [o₄.mem, o₃.mem, m₂, r₁.mem]; exact Frame.refl _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₄.v r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]), o₃.v r (by simp [hr.1]),
      vv r hr.1 hr.2.2.2.2.1]

end VG.Proof.AesGcm.AArch64.Fast
