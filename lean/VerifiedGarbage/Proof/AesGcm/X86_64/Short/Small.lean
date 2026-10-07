import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Gh

/-!
# AES-GCM's short path on x86-64: the counts, the buffers' setup and the tag

Untrusted: everything here is checked by Lean. `sizes_ok`: the counts of
blocks kept in `W`; `zeroG_ok`: `G` zeroed; `copyAArgs_ok`, `textArgs_ok`:
the arguments of `copyBytes` and `xorText`; `lens_ok`: the lengths block at
the end of `G`; `tagK_ok`: the tag, `GHASH ⊕ K[0]`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- The blocks of `k` bytes. -/
abbrev nb16 (k : Nat) : Nat := (k + 15) / 16

/-- The groups of four blocks to hash: the additional data's, the text's and
the lengths block, rounded up. -/
abbrev grp (al n : Nat) : Nat := (nb16 al + nb16 n + 4) / 4

theorem shl2_ofNat {a : Nat} (h : a * 4 < 2 ^ 64) : BitVec.ofNat 64 a <<< 2 = BitVec.ofNat 64 (4 * a) := by
  rw [shl_ofNat h, Nat.mul_comm]

/-- `sizes`: `na`, `nc`, `m' = 4 g` and `m' - (na + nc + 1)` at `W + 272` … `W + 296`. -/
theorem sizes_ok {W : Addr} {al n : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (hn : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (hal5 : al < 512) (hn5 : n < 512) :
    WP isa (.block sizes) s fun t =>
      t.mem.readW (W + BitVec.ofNat 64 272) 64 = BitVec.ofNat 64 (nb16 al) ∧
      t.mem.readW (W + BitVec.ofNat 64 280) 64 = BitVec.ofNat 64 (nb16 n) ∧
      t.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * grp al n) ∧
      t.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 (4 * grp al n - (nb16 al + nb16 n + 1)) ∧
      Frame [⟨W + BitVec.ofNat 64 272, 32⟩] s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ∀ r l, t.zlane r l = s.zlane r l := by
  have r184 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off hw (by decide) (by decide))
  have r208 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off hw (by decide) (by decide))
  have w272 : InRegions s.wr (W + BitVec.ofNat 64 272) 8 := in_off hw (by decide) (by decide)
  have w280 : InRegions s.wr (W + BitVec.ofNat 64 280) 8 := in_off hw (by decide) (by decide)
  have w288 : InRegions s.wr (W + BitVec.ofNat 64 288) 8 := in_off hw (by decide) (by decide)
  have w296 : InRegions s.wr (W + BitVec.ofNat 64 296) 8 := in_off hw (by decide) (by decide)
  have hna : nb16 al ≤ 32 := by simp only [nb16]; omega
  have hnc : nb16 n ≤ 32 := by simp only [nb16]; omega
  have hg : grp al n ≤ 17 ∧ nb16 al + nb16 n + 1 ≤ 4 * grp al n := by simp only [grp, nb16]; omega
  have e₁ : (BitVec.ofNat 64 al + BitVec.ofNat 64 15) >>> 4 = BitVec.ofNat 64 (nb16 al) := by
    rw [ofNat_add_ofNat, shr4 _ (by omega)]
  have e₂ : (BitVec.ofNat 64 n + BitVec.ofNat 64 15) >>> 4 = BitVec.ofNat 64 (nb16 n) := by
    rw [ofNat_add_ofNat, shr4 _ (by omega)]
  have e₃ : (BitVec.ofNat 64 (nb16 al) + BitVec.ofNat 64 (nb16 n) + BitVec.ofNat 64 1 + BitVec.ofNat 64 3) >>> 2 =
      BitVec.ofNat 64 (grp al n) := by
    rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat, shr2 _ (by omega)]
  have e₄ : BitVec.ofNat 64 (grp al n) <<< 2 = BitVec.ofNat 64 (4 * grp al n) := shl2_ofNat (by omega)
  have e₅ : BitVec.ofNat 64 (4 * grp al n) - (BitVec.ofNat 64 (nb16 al) + BitVec.ofNat 64 (nb16 n) + BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (4 * grp al n - (nb16 al + nb16 n + 1)) := by
    rw [ofNat_add_ofNat, ofNat_add_ofNat, ofNat_sub (by omega) (by omega)]
  apply WP.of_runBlock
  refine ⟨_, by xrun [sizes, execShift, h15, hal, hn, r184, r208, w272, w280, w288, w296, naO, ncO, mpO, leadO], ?_⟩
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 a) (64 / 8) (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep W h (by omega) (by omega)
  have q₁ := sep 272 280 (by decide) (by decide) (by decide)
  have q₂ := sep 272 288 (by decide) (by decide) (by decide)
  have q₃ := sep 272 296 (by decide) (by decide) (by decide)
  have q₄ := sep 280 288 (by decide) (by decide) (by decide)
  have q₅ := sep 280 296 (by decide) (by decide) (by decide)
  have q₆ := sep 288 296 (by decide) (by decide) (by decide)
  have c : ∀ d, 272 ≤ d → d + 8 ≤ 304 →
      (⟨W + BitVec.ofNat 64 272, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  have q₀ := sep 208 272 (by decide) (by decide) (by decide)
  have rdn : (s.mem.writeW (W + BitVec.ofNat 64 272) ((BitVec.ofNat 64 al + 15#64) >>> 4)).readW
      (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by rw [Mem.readW_writeW_sep q₀ (by decide), hn]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, fun _ _ => rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    rw [Mem.readW_writeW_sep q₃ (by decide), Mem.readW_writeW_sep q₂ (by decide),
      Mem.readW_writeW_sep q₁ (by decide), Mem.readW_writeW_self64, e₁]
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    rw [Mem.readW_writeW_sep q₅ (by decide), Mem.readW_writeW_sep q₄ (by decide), Mem.readW_writeW_self64,
      rdn, e₂]
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    rw [Mem.readW_writeW_sep q₆ (by decide), Mem.readW_writeW_self64, rdn, e₁, e₂, e₃, e₄]
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    rw [Mem.readW_writeW_self64, rdn, e₁, e₂, e₃, e₄, e₅]
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 272 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 280 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 288 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 296 (by decide) (by decide)))
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄]

theorem getLsbD_zero' (w k : Nat) : (0 : BitVec w).getLsbD k = false := by simp

/-- A 64-byte store of zero is a write of 64 zero bytes. -/
theorem writeW_zero512 (m : Mem) (a : Addr) : m.writeW a (0 : BitVec 512) = writeBytes m a (List.replicate 64 0) := by
  rw [Mem.writeW, write_eq_writeBytes]
  refine congrArg (writeBytes m a) ?_
  apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_replicate])
  intro j h₁ h₂
  rw [List.getElem_map, List.getElem_replicate]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, getLsbD_zero', Bool.and_false]

/-- `k` 64-byte stores of `zmm2` (zero) from `W + 512`. -/
theorem storesZ_ok {W : Addr} (k : Nat) (hk : k ≤ 8) (t : State) (h15 : t.gpr .r15 = W)
    (h2 : t.zmm .xmm2 = 0) (hw : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] t.wr) :
    WP isa (.block ((List.range k).map fun i => .vmovdqu32Store (at_ .r15 (gO + 64 * i)) .xmm2)) t fun t' =>
      t'.mem = writeBytes t.mem (W + BitVec.ofNat 64 512) (List.replicate (64 * k) 0) ∧ t'.gpr = t.gpr ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.xmm = t.xmm ∧ t'.ymmHi = t.ymmHi ∧ t'.zmmHi = t.zmmHi := by
  induction k with
  | zero => exact WP.block_nil ⟨by simp [writeBytes_nil], rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t₁ ⟨m₁, g₁, rd₁, wr₁, x₁, y₁, z₁⟩ => ?_
    have ea : t₁.gpr .r15 + BitVec.ofInt 64 ((gO + 64 * k : Nat) : Int) =
        W + BitVec.ofNat 64 512 + BitVec.ofNat 64 (64 * k) := by
      rw [g₁, h15, BitVec.ofInt_natCast, add_ofNat_ofNat]; rfl
    have hz : t₁.zmm .xmm2 = 0 := by rw [← h2]; simp only [State.zmm, State.ymm, x₁, y₁, z₁]
    have hin : InRegions t₁.wr (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 (64 * k)) 64 := by
      rw [wr₁]; exact in_off hw (by omega) (by decide)
    rw [List.map_singleton, WP.block_cons_iff]
    refine ⟨t₁.setMem (t₁.mem.writeW (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 (64 * k)) (0 : BitVec 512)),
      by simp only [isa, exec, State.store512_eq, State.ea, at_, ea, hin, ite_true, hz], WP.block_nil ?_⟩
    refine ⟨?_, by rw [State.setMem_gpr, g₁], by rw [State.setMem_rd, rd₁], by rw [State.setMem_wr, wr₁],
      by rw [← x₁]; rfl, by rw [← y₁]; rfl, by rw [← z₁]; rfl⟩
    rw [State.setMem_mem, m₁, writeW_zero512]
    have := writeBytes_append t.mem (W + BitVec.ofNat 64 512) (List.replicate (64 * k) 0) (List.replicate 64 0)
      (by simp; omega)
    rw [List.length_replicate, List.replicate_append_replicate] at this
    rw [this, show 64 * k + 64 = 64 * (k + 1) by omega]

/-- `zeroG`: `G` (`W + 512`, 512 bytes) zeroed, through `zmm2`. -/
theorem zeroG_ok {W : Addr} (t : State) (h15 : t.gpr .r15 = W) (hw : Covers [⟨W + BitVec.ofNat 64 512, 512⟩] t.wr) :
    WP isa (.block zeroG) t fun t' =>
      t'.mem = writeBytes t.mem (W + BitVec.ofNat 64 512) (List.replicate 512 0) ∧ t'.gpr = t.gpr ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ ZKeep [.xmm2] t t' := by
  rw [zeroG, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (storesZ_ok 8 (by decide) _ h15 ?_ hw) fun t' ⟨m', g', rd', wr', x', y', z'⟩ =>
    ⟨m', g', rd', wr', fun r hr l hl => ?_⟩
  · have hl : ∀ l < 4, ((ZOp.zbin .vpxord .xmm2 .xmm2 .xmm2).exec t).zlane .xmm2 l = 0 := fun l hl => by
      rw [zlane_zbin _ _ _ _ _ _ hl]
      simp only [ite_true, ZBinOp.sse, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, BitVec.xor_self]
      rfl
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    have e := congrArg (fun v : BitVec 128 => v.getLsbD (j % 128))
      ((VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ .xmm2 (l := j / 128) (by omega)).trans (hl (j / 128) (by omega)))
    simp only [BitVec.getLsbD_extractLsb', show j % 128 < 128 by omega, decide_true, Bool.true_and,
      show 128 * (j / 128) + j % 128 = j by omega, getLsbD_zero'] at e
    rw [e, getLsbD_zero']
  · have hz : t'.zlane r l = ((ZOp.zbin .vpxord .xmm2 .xmm2 .xmm2).exec t).zlane r l := by
      simp only [State.zlane, State.lane, x', y', z']
    rw [hz, zlane_zbin _ _ _ _ _ _ hl]
    simp only [List.mem_singleton] at hr
    simp [hr]

/-- The arguments of `copyBytes` in `copyA`: `G` after the zero blocks, the
additional data and its length. -/
theorem copyAArgs_ok {W A : Addr} {al lead : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (hlead : s.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 lead)
    (hA : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al) (hl : lead < 32) :
    ∃ t, runBlock isa [.mov .rdi (.mem (at_ .r15 leadO)), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15),
        .alu .add .rdi (imm gO), .mov .rsi (.mem (at_ .r15 aadO)), .mov .rcx (.mem (at_ .r15 alenO))] s = some t ∧
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * lead) ∧ t.gpr .rsi = A ∧ t.gpr .rcx = BitVec.ofNat 64 al ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ∀ r l, t.zlane r l = s.zlane r l := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 296) 8 := in_left (in_off hw (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 232) 8 := in_left (in_off hw (by decide) (by decide))
  have r₃ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off hw (by decide) (by decide))
  have e : BitVec.ofNat 64 lead <<< 4 = BitVec.ofNat 64 (16 * lead) := by
    rw [shl_ofNat (by omega)]; congr 1; omega
  refine ⟨_, by xrun [execShift, h15, hlead, hA, hal, r₁, r₂, r₃, leadO, gO, e], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false, h15]
    rw [BitVec.add_comm (BitVec.ofNat 64 (16 * lead)) W, add_ofNat_ofNat, Nat.add_comm]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r a b c; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a, b, c]
  all_goals first | rfl | exact fun _ _ => rfl

/-- `gText` and the rest of the arguments of `xorText` (`textArgs`): the
text's blocks in `G`, the data, `K[1]` and the length. -/
theorem textArgs_ok {W D : Addr} {n lead na : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (hlead : s.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 lead)
    (hna : s.mem.readW (W + BitVec.ofNat 64 272) 64 = BitVec.ofNat 64 na)
    (hD : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hn : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (hl : lead + na < 64) :
    ∃ t, runBlock isa textArgs s = some t ∧
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (lead + na)) ∧ t.gpr .rsi = D ∧
      t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧ t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ ∀ r l, t.zlane r l = s.zlane r l := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 296) 8 := in_left (in_off hw (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 272) 8 := in_left (in_off hw (by decide) (by decide))
  have r₃ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 200) 8 := in_left (in_off hw (by decide) (by decide))
  have r₄ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off hw (by decide) (by decide))
  have e : (BitVec.ofNat 64 lead + BitVec.ofNat 64 na) <<< 4 = BitVec.ofNat 64 (16 * (lead + na)) := by
    rw [ofNat_add_ofNat, shl_ofNat (by omega)]; congr 1; omega
  refine ⟨_, by xrun [textArgs, gText, execShift, h15, hlead, hna, hD, hn, r₁, r₂, r₃, r₄, leadO, naO, gO, kO, e],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false, h15]
    rw [BitVec.add_comm (BitVec.ofNat 64 (16 * (lead + na))) W, add_ofNat_ofNat, Nat.add_comm]
  · simp [gpr_setReg]
  · simp [gpr_setReg, gpr_arithFlags, h15]
  · simp [gpr_setReg]
  · intro r a b c d; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a, b, c, d]
  all_goals first | rfl | exact fun _ _ => rfl

/-- `lens`: the lengths block, `[8 a]₆₄ ‖ [8 n]₆₄`, as the last block of `G`
(`m'` blocks). -/
theorem lensG_ok {W : Addr} {al n mp : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 mp)
    (hmp1 : 1 ≤ mp) (hmp32 : mp ≤ 32)
    (hal : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al)
    (hn : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (hal5 : al < 2 ^ 60) (hn5 : n < 2 ^ 60) :
    ∃ t, runBlock isa Short.lens s = some t ∧
      Frame [⟨W + BitVec.ofNat 64 (496 + 16 * mp), 16⟩] s.mem t.mem ∧
      bytesAt t.mem (W + BitVec.ofNat 64 (496 + 16 * mp)) 16 = Proof.Gcm.lensBlock al n ∧
      (∀ r, r ≠ .rdi → r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ∀ r l, t.zlane r l = s.zlane r l := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 288) 8 := in_left (in_off hw (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off hw (by decide) (by decide))
  have r₃ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off hw (by decide) (by decide))
  let L := W + BitVec.ofNat 64 (496 + 16 * mp)
  have w₁ : InRegions s.wr L 8 := in_off hw (by omega) (by decide)
  have w₂ : InRegions s.wr (L + BitVec.ofNat 64 8) 8 := by
    rw [add_ofNat_ofNat]; exact in_off hw (by omega) (by decide)
  have e₁ : BitVec.ofNat 64 mp <<< 4 + W + BitVec.ofNat 64 496 = L := by
    rw [shl_ofNat (by omega), BitVec.add_comm _ W, add_ofNat_ofNat]; congr 2; omega
  have e₂ : BitVec.ofNat 64 al <<< 3 = BitVec.ofNat 64 (8 * al) := by rw [shl_ofNat (by omega)]; congr 1; omega
  have e₃ : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by rw [shl_ofNat (by omega)]; congr 1; omega
  refine ⟨_, by xrun [Short.lens, execShift, h15, hmp, hal, hn, r₁, r₂, r₃, mpO, gO, e₁, e₂, e₃, w₁, w₂,
    BitVec.add_zero], ?_⟩
  have rdn : ∀ v : BitVec 64, (s.mem.writeW L v).readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n :=
    fun v => by rw [Mem.readW_writeW_sep (Offset.sep W (.inl (by omega)) (by omega) (by omega)) (by decide), hn]
  refine ⟨?_, ?_, ?_, rfl, rfl, fun _ _ => rfl⟩
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
    exact Proof.Cmac.frame_store2 _ _ _
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
    rw [rdn, e₃, Proof.Cmac.bytesAt_store2, bswap64_eq, Proof.Gcm.le8_byteRev64, Proof.Gcm.le8_byteRev64,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Proof.Gcm.be64_mod, Proof.Gcm.be64_mod]; rfl
  · intro r a b; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a, b]

/-- `tagK o`: `GHASH ⊕ K[0]` (`GHASH` in `xmm2`) stored at `W + o`. -/
theorem tagK_ok {W : Addr} {o : Nat} (s : State) (h15 : s.gpr .r15 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    (ho : o + 16 ≤ 512) (h0 : s.xmm .xmm0 = VG.Proof.Gcm.X86_64.revMask) :
    ∃ t, runBlock isa (tagK o) s = some t ∧
      blockAt t.mem (W + BitVec.ofNat 64 o) = s.xmm .xmm2 ^^^ blockAt s.mem (W + BitVec.ofNat 64 1024) ∧
      Frame [⟨W + BitVec.ofNat 64 o, 16⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have eK : s.gpr .r15 + BitVec.ofInt 64 ((kO : Nat) : Int) = W + BitVec.ofNat 64 1024 := by
    rw [h15, BitVec.ofInt_natCast]; rfl
  have eo : s.gpr .r15 + BitVec.ofInt 64 ((o : Nat) : Int) = W + BitVec.ofNat 64 o := by
    rw [h15, BitVec.ofInt_natCast]
  have rK : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 1024) 16 := in_left (in_off hw (by decide) (by decide))
  have wo : InRegions s.wr (W + BitVec.ofNat 64 o) 16 := in_off hw (by omega) (by decide)
  refine ⟨_, by
    simp only [tagK, at_, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, State.load128,
      State.store128, State.ea, eK, eo, rK, wo, ite_true, Option.map_some, Option.bind_some, State.setV,
      State.lane, reduceCtorEq, ↓reduceIte]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VBinOp.sse, h0, ite_true]
    rw [show XBinOp.eval .pxor (XBinOp.eval .pshufb (s.xmm .xmm2) VG.Proof.Gcm.X86_64.revMask)
        (s.mem.readW (W + BitVec.ofNat 64 1024) 128) =
        XBinOp.eval .pshufb (s.xmm .xmm2 ^^^ blockAt s.mem (W + BitVec.ofNat 64 1024))
          VG.Proof.Gcm.X86_64.revMask by
      rw [VG.Proof.Gcm.X86_64.pshufb_rev_xor, VG.Proof.Gcm.X86_64.blockAt_eq,
        VG.Proof.Gcm.X86_64.pshufb_rev_rev]; rfl,
      VG.Proof.Gcm.X86_64.blockAt_store]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  all_goals rfl

/-- The arguments of `copyBytes` in `copyC`: the text's blocks in `G`, the
data and its length. -/
theorem copyCArgs_ok {W D : Addr} {n lead na : Nat} (s : State) (h15 : s.gpr .r15 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (hlead : s.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 lead)
    (hna : s.mem.readW (W + BitVec.ofNat 64 272) 64 = BitVec.ofNat 64 na)
    (hD : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hn : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n) (hl : lead + na < 64) :
    ∃ t, runBlock isa (gText ++ ([.mov .rsi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 lenO))] : List Instr)) s =
        some t ∧
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (lead + na)) ∧ t.gpr .rsi = D ∧ t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ ∀ r l, t.zlane r l = s.zlane r l := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 296) 8 := in_left (in_off hw (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 272) 8 := in_left (in_off hw (by decide) (by decide))
  have r₃ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 200) 8 := in_left (in_off hw (by decide) (by decide))
  have r₄ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off hw (by decide) (by decide))
  have e : (BitVec.ofNat 64 lead + BitVec.ofNat 64 na) <<< 4 = BitVec.ofNat 64 (16 * (lead + na)) := by
    rw [ofNat_add_ofNat, shl_ofNat (by omega)]; congr 1; omega
  refine ⟨_, by xrun [gText, execShift, h15, hlead, hna, hD, hn, r₁, r₂, r₃, r₄, leadO, naO, gO, e],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false, h15]
    rw [BitVec.add_comm (BitVec.ofNat 64 (16 * (lead + na))) W, add_ofNat_ofNat, Nat.add_comm]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r a b c; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, a, b, c]
  all_goals first | rfl | exact fun _ _ => rfl

end VG.Proof.AesGcm.X86_64.Short
