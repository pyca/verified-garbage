module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Groups
public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# AES-GCM on AArch64, the path for TLS records: GHASH in registers

Untrusted: everything here is checked by Lean. `seal`'s path for TLS records
(`Impl/AesGcm/AArch64/Fast.lean`) keeps `H'` in registers as
`vg_ghash_aes` does (`HKey`, `keyV`: `Proof/Gcm/AArch64/Pmull/Groups.lean`), computed once
(`key_ok`) or reloaded from the working space (`reload_ok`), and multiplies
the block at `T` into the accumulator `Y` in `v0` (`mulT_ok`), which holds
`y` with its halves swapped (`ext8 y y`), as loaded. That `mul` by the key
multiplies by `H` is the one fact of algebra these proofs need: they take
it as a hypothesis (`MulKey`), proven in `Pmull/Ghash.lean`
(`mulV_keyV`), so that they do not import the algebra.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI A T C Y tReg sReg poly)
open VG.Spec.Gcm (Block blockAt)

theorem ext8_zero : ext8 0 0 = 0 := by
  rw [ext8_eq]; decide

theorem ext8_xor (a b : BitVec 128) : ext8 (a ^^^ b) (a ^^^ b) = ext8 a a ^^^ ext8 b b := by
  rw [ext8_eq, ext8_eq, ext8_eq, vdword_xor, vdword_xor, BitVec.xor_append]

/-- The registers hold the reduction constant, and `H'` for the hash subkey
`H` (`keyV H`) as it is and with its halves swapped. -/
structure HKey (H : Block) (s : State) : Prop where
  c : s.v C = ofVDwords poly poly
  t : s.v (tReg 1) = keyV H
  sw : s.v (sReg 1) = ext8 (s.v (tReg 1)) (s.v (tReg 1))

/-- `HKey` depends only on its three registers. -/
theorem HKey.of_v {H : Block} {s s' : State} (h : HKey H s) (hc : s'.v C = s.v C)
    (ht : s'.v (tReg 1) = s.v (tReg 1)) (hs : s'.v (sReg 1) = s.v (sReg 1)) : HKey H s' :=
  ⟨by rw [hc, h.c], by rw [ht, h.t], by rw [hs, ht, h.sw]⟩

/-- `HKey` is kept by what writes only other vector registers. -/
theorem HKey.of_vonly {H : Block} {rs : List VReg} {s s' : State} (h : HKey H s) (o : VOnly rs s s')
    (hc : C ∉ rs) (ht : tReg 1 ∉ rs) (hs : sReg 1 ∉ rs) : HKey H s' :=
  h.of_v (o.v C hc) (o.v _ ht) (o.v _ hs)

theorem c_nmem : C ∉ [A, LO, MID, HI, T, Y] := by decide
theorem t1_nmem : tReg 1 ∉ [A, LO, MID, HI, T, Y] := by decide
theorem s1_nmem : sReg 1 ∉ [A, LO, MID, HI, T, Y] := by decide

/-- `mulT`: `Y ← mul(Y ⊕ T, H')`, the block at `T` (`x19 + 96`) absorbed. -/
theorem mulT_ok (hM : MulKey) {H y : Block} {s : State} (hk : HKey H s) (hy : s.v Y = ext8 y y)
    (hT : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.tO) 16) :
    WP isa (.block Impl.AesGcm.AArch64.Fast.mulT) s fun s' =>
      s'.v Y = ext8 (Spec.Gcm.mul (y ^^^ blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.tO)) H)
        (Spec.Gcm.mul (y ^^^ blockAt s.mem (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.tO)) H) ∧
        HKey H s' ∧ VOnly [A, LO, MID, HI, T, Y] s s' := by
  simp only [Impl.AesGcm.AArch64.Fast.mulT, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x19 _ s (by decide) (by decide) hT) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (eor_ok A A Y s₁) fun s₂ ⟨e₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  have hk₂ : HKey H s₂ := hk.of_vonly o₁₂ (by decide) (by decide) (by decide)
  refine WP.mono (mulV_ok Y A (sReg 1) (tReg 1) s₂ free_A (sReg_free _) (tReg_free _) hk₂.sw hk₂.c)
    fun s₃ ⟨m₃, o₃⟩ => ⟨?_, hk₂.of_vonly o₃ (by decide) (by decide) (by decide),
      (o₁₂.trans o₃).weaken⟩
  have hY₁ : s₁.v Y = s.v Y := o₁.v Y (by decide)
  rw [m₃, e₂, l₁, hY₁, hy, rev64b_read, ← ext8_xor, hk₂.t, hM, BitVec.xor_comm]

/-- A block runs one way: what two proofs of it give holds together. -/
theorem WP.block_and {is : List Instr} {s : State} {P Q : State → Prop} (hp : WP isa (.block is) s P)
    (hq : WP isa (.block is) s Q) : WP isa (.block is) s fun s' => P s' ∧ Q s' := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨WP.block_nil_iff.mp hp, WP.block_nil_iff.mp hq⟩
  | cons i is ih =>
    obtain ⟨s₁, e₁, hp₁⟩ := WP.block_cons_iff.mp hp
    obtain ⟨s₂, e₂, hq₂⟩ := WP.block_cons_iff.mp hq
    rw [e₁, Option.some.injEq] at e₂
    subst e₂
    exact WP.block_cons_iff.mpr ⟨s₁, e₁, ih hp₁ hq₂⟩

/-- `consts` keeps the stack pointer. -/
theorem consts_sp (s : State) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.consts) s fun s' => s'.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.AArch64.Pmull.consts, tReg, sReg, runBlock_cons, runStep_some, runBlock_nil,
    exec_movz_x (show 16 * 3 < 64 by decide), exec_movz_x (show 16 * 0 < 64 by decide),
    exec_dup_d2, exec_ins_d2 (show 0 < 2 by decide), exec_ins_d2 (show 1 < 2 by decide),
    Option.some.injEq, exists_eq_left', sp_setV, sp_write]

/-- `H'` and its halves swapped, from the hash subkey `H` loaded from `x0`. -/
theorem key_ok {H : Block} {s : State} (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (hH : blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 0) = H) :
    WP isa (.block Impl.AesGcm.AArch64.Fast.key) s fun s' =>
      HKey H s' ∧ (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ∉ [A, C, tReg 2, sReg 2, LO, MID, HI, T, sReg 1, tReg 1] → s'.v r = s.v r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  simp only [Impl.AesGcm.AArch64.Fast.key, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .x0 0 s rfl (by decide) hin) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.block_and (consts_ok s₁) (consts_sp s₁))
    fun s₂ ⟨⟨c₂, t₂, w₂, kv₂, kg₂, m₂, rd₂, wr₂⟩, sp₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulV_ok (sReg 1) A (sReg 2) (tReg 2) s₂ free_A (sReg_free _) (tReg_free _)
    (by rw [w₂, t₂]) c₂) fun s₃ ⟨m₃, o₃⟩ => ?_
  refine WP.mono (swap_ok (tReg 1) (sReg 1) s₃) fun s₄ ⟨w₄, o₄⟩ => ?_
  have hA₂ : s₂.v A = s₁.v A := kv₂ A (by decide) (ne_tReg 2) (ne_sReg 2)
  have s1₄ : s₄.v (sReg 1) = s₃.v (sReg 1) :=
    o₄.v _ (by simp only [List.mem_singleton]; exact fun e => tReg_ne_sReg _ _ e.symm)
  have hC : s₄.v C = s₂.v C := by
    rw [o₄.v C (by simp only [List.mem_singleton]; exact ne_tReg 1),
      o₃.v C (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, by decide, by decide, ne_sReg 1⟩)]
  refine ⟨⟨by rw [hC, c₂], ?_, by rw [s1₄, w₄, ext8_ext8]⟩, fun r h5 h6 h7 => ?_, fun r hr => ?_,
    by rw [o₄.mem, o₃.mem, m₂, o₁.mem], by rw [o₄.rd, o₃.rd, rd₂, o₁.rd],
    by rw [o₄.wr, o₃.wr, wr₂, o₁.wr], ?_⟩
  · rw [w₄, m₃, hA₂, l₁, t₂, rev64b_read, hH]
    rfl
  · rw [o₄.gpr, o₃.gpr, kg₂ r h5 h6 h7, o₁.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨hA, hC', ht2, hs2, hlo, hmid, hhi, hT, hs1, ht1⟩ := hr
    rw [o₄.v r (by simp only [List.mem_singleton]; exact ht1),
      o₃.v r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hlo, hmid, hhi, hT, hs1⟩),
      kv₂ r hC' ht2 hs2,
      o₁.v r (by simp only [List.mem_singleton]; exact hA)]
  · rw [o₄.sp, o₃.sp, sp₂, o₁.sp]

/-- `H'` and its halves swapped stored at `x19 + hO`, and `Y = 0`. -/
theorem keep_ok {s : State}
    (w₀ : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16)
    (w₁ : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16) :
    WP isa (.block Impl.AesGcm.AArch64.Fast.keep) s fun s' =>
      s'.mem = (s.mem.write (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 (s.v (tReg 1))).write
        (s.gpr .x19 + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 (s.v (sReg 1)) ∧
      s'.v Y = 0 ∧ (∀ r, r ≠ Y → s'.v r = s.v r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (by decide) (by decide) w₀, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (t := sReg 1) (n := .x19) (off := Impl.AesGcm.AArch64.Fast.hO + 16)
    (by decide) (by decide) (by exact w₁), ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_movi0 Y _, WP.block_nil ?_⟩
  exact ⟨rfl, by simp only [v_setV, ite_true], fun r hr => by simp only [v_setV, hr, ite_false], rfl, rfl,
    rfl, rfl⟩

/-- `H'`, its halves swapped and the reduction constant, reloaded. -/
theorem reload_ok {H : Block} {t : BitVec 128} {s : State}
    (r₀ : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16)
    (r₁ : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16)
    (h₀ : s.mem.read (s.gpr .x19 + BitVec.ofNat 64 Impl.AesGcm.AArch64.Fast.hO) 16 = t)
    (h₁ : s.mem.read (s.gpr .x19 + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Fast.hO + 16)) 16 = ext8 t t)
    (ht : t = keyV H) :
    WP isa (.block Impl.AesGcm.AArch64.Fast.hReload) s fun s' =>
      HKey H s' ∧ (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ∉ [tReg 1, sReg 1, C] → s'.v r = s.v r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.AArch64.Fast.hReload, runBlock_cons, runStep_some, runBlock_nil,
    exec_ldrq (by decide) (by decide) r₀, exec_ldrq (s := s.setV _ _) (by decide) (by decide) r₁,
    exec_movz_x (show 16 * 3 < 64 by decide), exec_dup_d2, Option.some.injEq, exists_eq_left',
    gpr_setV, mem_setV, rd_setV, wr_setV, sp_setV, mem_write, rd_write, wr_write]
  refine ⟨⟨?_, ?_, ?_⟩, fun r h5 => ?_, fun r hr => ?_, trivial, trivial, trivial, rfl⟩
  · simp only [v_setV, v_write, ite_true, gpr_write_x, gpr_setV]; decide
  · simp only [v_setV, v_write, tReg, sReg, h₀, reduceCtorEq, ite_false, ite_true]; exact ht
  · simp only [v_setV, v_write, tReg, sReg, h₀, h₁, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_write_x, gpr_setV, h5, ite_false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, tReg, sReg] at hr
    simp only [v_setV, v_write, tReg, sReg, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `Y` stored at `x20 + 16`, as `vg_ghash` keeps it. -/
theorem storeY_ok {y : Block} {s : State} (hy : s.v Y = ext8 y y)
    (hw : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 16) 16) :
    WP isa (.block Impl.AesGcm.AArch64.Fast.storeY) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x20 + BitVec.ofNat 64 16) 16 (VRevOp.eval .rev64b (s.v Y)) ∧
      blockAt s'.mem (s.gpr .x20 + BitVec.ofNat 64 16) = y ∧ VOnly [Y] { s with mem := s'.mem } s' := by
  refine WP.block_cons_iff.mpr ⟨_, exec_rev64b Y Y s, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_strq (s := s.setV Y _) (by decide) (by decide) hw, WP.block_nil ?_⟩
  refine ⟨by simp only [mem_setV, gpr_setV, v_setV, ite_true], ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩⟩
  · simp only [mem_setV, gpr_setV, v_setV, ite_true, blockAt_store, hy, ext8_ext8]
  · simp only [List.mem_singleton] at hr; simp only [v_setV, hr, ite_false]

end VG.Proof.AesGcm.AArch64.Fast
