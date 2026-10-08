import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Impl.AesGcm.X86_64.BlocksTo

/-!
# AES-GCM out of place on x86-64: copying blocks (`BlocksTo.copyBlocks`)

Untrusted: everything here is checked by Lean. `copyBlocks` copies `k ≥ 1`
blocks from `rsi` to `rdi`, 16 bytes at a time through `xmm0`, with the
index in `r10` and the blocks left in `rcx` (`copyBlocks_wp`); the buffers do
not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.BlocksTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.BlocksTo VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)

/-- What the loop needs of the state: `k` blocks at `Sp` to copy to `Dp`. -/
structure CopyPre (s : State) (Sp Dp : Addr) (k : Nat) : Prop where
  rsi : s.gpr .rsi = Sp
  rdi : s.gpr .rdi = Dp
  rcx : s.gpr .rcx = BitVec.ofNat 64 k
  pos : 1 ≤ k
  lt : 16 * k < 2 ^ 64
  rd : Covers [⟨Sp, 16 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨Dp, 16 * k⟩] s.wr
  disj : (⟨Sp, 16 * k⟩ : Region).Disjoint ⟨Dp, 16 * k⟩

theorem copyStep_ok (s : State) {Sp Dp : Addr} {j w : Nat} (hs : s.gpr .rsi = Sp) (hd : s.gpr .rdi = Dp)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 j) (hcx : s.gpr .rcx = BitVec.ofNat 64 w)
    (rq : InRegions (s.rd ++ s.wr) (Sp + BitVec.ofNat 64 j) 16) (wq : InRegions s.wr (Dp + BitVec.ofNat 64 j) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm0 srcB, .movdquStore dstB .xmm0, .alu .add .r10 (imm 16),
        .alu .sub .rcx (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (Dp + BitVec.ofNat 64 j) (s.mem.readW (Sp + BitVec.ofNat 64 j) 128) ∧
      s'.gpr .r10 = BitVec.ofNat 64 j + 16 ∧ s'.gpr .rcx = BitVec.ofNat 64 w - 1 ∧
      s'.zf = some (BitVec.ofNat 64 w - 1 == 0) ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ : s.gpr .rsi + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Sp + BitVec.ofNat 64 j := by
    rw [hs, h10, BitVec.mul_one]; simp
  have e₂ : s.gpr .rdi + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Dp + BitVec.ofNat 64 j := by
    rw [hd, h10, BitVec.mul_one]; simp
  refine ⟨_, by mrun [srcB, dstB, e₁, e₂, rq, wq], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setXmm, xmm_setXmm', ite_true]
  · simp [gpr_setReg, gpr_setXmm, h10]
  · simp [gpr_setReg, gpr_setXmm, hcx]
  · simp [gpr_setReg, gpr_setXmm, hcx]
  · intro r h₁ h₂; simp [gpr_setReg, gpr_setXmm, h₁, h₂]
  all_goals rfl

/-- What the loop keeps: the first `j` bytes copied. -/
structure CInv (s t : State) (Sp Dp : Addr) (j : Nat) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem Dp (bytesAt s.mem Sp j)
  keep : ∀ r, r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The block at `Sp + j` is not in the bytes copied so far. -/
theorem CInv.readW {s t : State} {Sp Dp : Addr} {j L : Nat} (h : CInv s t Sp Dp j)
    (hd : (⟨Sp, L⟩ : Region).Disjoint ⟨Dp, L⟩) (hj : j + 16 ≤ L) (hL : L < 2 ^ 64) :
    t.mem.readW (Sp + BitVec.ofNat 64 j) 128 = s.mem.readW (Sp + BitVec.ofNat 64 j) 128 := by
  refine Mem.readW_congr fun k hk => ?_
  rw [h.mem]
  refine (writeBytes_frame s.mem Dp (bytesAt s.mem Sp j) (R := ⟨Dp, j⟩)
    (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Offset.add_add] at hcon
  exact hd _ (Offset.contains_base Sp (show j + k + 1 ≤ L by omega) (by omega))
    (Region.sub_prefix (show j ≤ L by omega) _ hcon)

theorem copyBlocks_wp (s : State) {Sp Dp : Addr} {k : Nat} (h : CopyPre s Sp Dp k) :
    WP isa copyBlocks s fun s' => s'.mem = writeBytes s.mem Dp (bytesAt s.mem Sp (16 * k)) ∧
      (∀ r, r ≠ .r10 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  have hL := h.lt
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ CInv s t Sp Dp (16 * i) ∧
      t.gpr .rcx = BitVec.ofNat 64 (k - i)) ?_ (k - 0) _
    ⟨0, rfl, h.pos, ⟨r10₁, by simp [bytesAt, writeBytes_nil, mem_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁],
      rfl, rfl⟩, by simp [gpr_setReg, h.rcx]⟩
  rintro w t ⟨i, rfl, hi, ht, hcx⟩
  have hin : 16 * i + 16 ≤ 16 * k := by omega
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 16 * k⟩] rs) : InRegions rs (P + BitVec.ofNat 64 (16 * i)) 16 :=
    hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hin (by omega)⟩
  obtain ⟨t', run', mem', r10', rcx', zf', g', rd', wr'⟩ := copyStep_ok t (Sp := Sp) (Dp := Dp) (j := 16 * i)
    (w := k - i) (by rw [ht.keep _ (by decide) (by decide), h.rsi]) (by rw [ht.keep _ (by decide) (by decide), h.rdi])
    ht.r10 hcx (by rw [ht.rd, ht.wr]; exact cov _ _ h.rd) (by rw [ht.wr]; exact cov _ _ h.wr)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hb : (List.range 16).map (fun j => (s.mem.readW (Sp + BitVec.ofNat 64 (16 * i)) 128).extractLsb' (8 * j) 8) =
      bytesAt s.mem (Sp + BitVec.ofNat 64 (16 * i)) 16 := by
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    rw [← Mem.extractLsb'_read s.mem _ (n := 16) hj]
    rfl
  have hmem : t'.mem = writeBytes s.mem Dp (bytesAt s.mem Sp (16 * (i + 1))) := by
    rw [mem', ht.readW h.disj hin (by omega), ht.mem, writeW_eq_writeBytes, hb,
      show 16 * (i + 1) = 16 * i + 16 by omega, bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), Proof.Cmac.bytesAt_length]
  have hsub : BitVec.ofNat 64 (k - i) - 1 = BitVec.ofNat 64 (k - (i + 1)) := by
    rw [show k - i = (k - (i + 1)) + 1 by omega, ← succ_ofNat, BitVec.add_sub_cancel]
  have hcx' : t'.gpr .rcx = BitVec.ofNat 64 (k - (i + 1)) := by rw [rcx', hsub]
  have hz : t'.zf = some (decide (i + 1 = k)) := by
    rw [zf', hsub]
    by_cases he : i + 1 = k
    · rw [he, Nat.sub_self]; simp
    · have : BitVec.ofNat 64 (k - (i + 1)) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [toNat_ofNat_of_lt (by omega)] at this; simp at this; omega
      rw [beq_eq_false_iff_ne.mpr this]; simp [he]
  have ht' : CInv s t' Sp Dp (16 * (i + 1)) :=
    ⟨by rw [r10', show 16 * (i + 1) = 16 * i + 16 by omega, BitVec.ofNat_add]; rfl, hmem,
      fun r h₁ h₂ => by rw [g' r h₁ h₂, ht.keep r h₁ h₂], by rw [rd', ht.rd], by rw [wr', ht.wr]⟩
  by_cases he : i + 1 = k
  · left
    refine ⟨(maskBlocks_wp.eval_ne hz).trans (by simp [he]), ?_, ht'.keep, ht'.rd, ht'.wr⟩
    rw [ht'.mem, he]
  · right
    exact ⟨(maskBlocks_wp.eval_ne hz).trans (by simp [he]), k - (i + 1), by omega, i + 1, rfl, by omega, ht', hcx'⟩

end VG.Proof.AesGcm.X86_64.BlocksTo
