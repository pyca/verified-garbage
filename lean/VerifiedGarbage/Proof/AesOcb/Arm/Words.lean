import VerifiedGarbage.Proof.AesOcb.Arm.Callee
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Dbl
import VerifiedGarbage.Proof.Ocb.Spec

/-!
# AES-OCB on ARMv7: blocks a word at a time

Untrusted: everything here is checked by Lean. The straight-line pieces the
functions build blocks with, each leaving its memory and writing only some
registers (`Ran`): the XOR of two blocks into a third, a word at a time
(`xorB`, which is AES-CMAC's `xorBlk`: `Cmac.xor4Mem`, `blockAtMem_xor4`),
a block zeroed (`zero16`: `Cmac.zero4`), copied (`copy16`) and doubled
(`dbl`: `dblMem`, `blockAtMem_dbl`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.AesGcm.Arm (in_left in_off covers_left mem_store)

/-- What a straight-line piece leaves: the memory `m`, and only the registers
`rs` written. -/
structure Ran (rs : List Reg) (m : Mem) (s s' : State) : Prop where
  mem : s'.mem = m
  gpr : Others rs s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Ran.mono {rs rs' : List Reg} {m : Mem} {s s' : State} (h : Ran rs m s s') (hr : ∀ r ∈ rs, r ∈ rs') :
    Ran rs' m s s' :=
  ⟨h.mem, fun r h' => h.gpr r fun h'' => h' (hr r h''), h.sp, h.rd, h.wr⟩

/-! ## XOR -/

theorem xorB_eq (pb qb cb : Reg) (pd qd cd : Nat) :
    xorB pb qb cb pd qd cd = Proof.CmacAes.Arm.xorBlk .r0 .r1 pb qb cb pd qd cd := rfl

/-- `cb + cd ← (pb + pd) ⊕ (qb + qd)`, through `r0` and `r1`. -/
theorem xorB_wp {pb qb cb : Reg} {pd qd cd : Nat} {s : State}
    (hp₁ : pb ≠ .r0) (hp₂ : pb ≠ .r1) (hq₁ : qb ≠ .r0) (hq₂ : qb ≠ .r1) (hc₁ : cb ≠ .r0) (hc₂ : cb ≠ .r1)
    (hpd : pd + 12 < 4096) (hqd : qd + 12 < 4096) (hcd : cd + 12 < 4096)
    (fp : (s.gpr pb).toNat + pd + 16 ≤ 2 ^ 32) (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32)
    (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨State.addr (s.gpr pb) + BitVec.ofNat 64 pd, 16⟩] (s.rd ++ s.wr))
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr) :
    WP isa (.block (xorB pb qb cb pd qd cd)) s (Ran [.r0, .r1]
      (Proof.Cmac.xor4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr pb) + BitVec.ofNat 64 pd) (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) s) := by
  rw [xorB_eq, ← List.append_nil (Proof.CmacAes.Arm.xorBlk ..)]
  refine Proof.CmacAes.Arm.xorBlk_ok (by decide) hp₁ hp₂ hq₁ hq₂ hc₁ hc₂ hpd hqd hcd fp fq fc rP rQ wC
    fun s' st => WP.block_nil_iff.mpr ⟨st.mem, fun r hr => ?_, st.sp, st.rd, st.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact st.gpr r hr.1 hr.2

/-- The block of an XOR. -/
theorem blockAtMem_xor4 (m : Mem) {c p q : Addr} (hp : Proof.Cmac.Sep4 c p) (hq : Proof.Cmac.Sep4 c q) :
    blockAtMem (Proof.Cmac.xor4Mem m c p q) c = blockAtMem m p ^^^ blockAtMem m q := by
  rw [blockAtMem, Proof.Cmac.xor4Mem_bytes m hp hq, ← Proof.Ocb.xor_eq,
    Proof.Ocb.ofBytes_xor (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)]
  rfl

/-! ## Zeros -/

theorem zero16_eq (o : Nat) : Impl.AesGcm.Arm.zero16 o = .mov .r0 (.imm 0) :: Proof.CmacAes.Arm.zeroBlk .r0 .r11 o := rfl

/-- `W + o ← 0`, through `r0`. -/
theorem zero16_wp {o : Nat} {s : State} (ho : o + 12 < 4096) (fb : (s.gpr .r11).toNat + o + 16 ≤ 2 ^ 32)
    (wB : Covers [⟨State.addr (s.gpr .r11) + BitVec.ofNat 64 o, 16⟩] s.wr) :
    WP isa (.block (Impl.AesGcm.Arm.zero16 o)) s
      (Ran [.r0] (Proof.Cmac.zero4 s.mem (State.addr (s.gpr .r11) + BitVec.ofNat 64 o)) s) := by
  rw [zero16_eq]
  refine WP.block_cons_iff.mpr ⟨s.setReg .r0 0, by simp [isa, exec, Op2.eval]; decide, ?_⟩
  rw [← List.append_nil (Proof.CmacAes.Arm.zeroBlk ..)]
  refine Proof.CmacAes.Arm.zeroBlk_ok (by simp [gpr_setReg]) ho (by simpa [gpr_setReg] using fb)
    (by simpa [gpr_setReg, wr_setReg] using wB) fun s' hg hm hrd hwr hsp => WP.block_nil_iff.mpr ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [hm]; simp [gpr_setReg, mem_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hg]; simp [gpr_setReg, hr]
  · rw [hsp]; rfl
  · rw [hrd]; rfl
  · rw [hwr]; rfl

theorem blockAtMem_zero4 (m : Mem) (c : Addr) : blockAtMem (Proof.Cmac.zero4 m c) c = 0 := by
  rw [blockAtMem, Proof.Cmac.zero4_bytes]; decide

/-! ## Copies -/

/-- The memory after `copy16`: the four words at `s` stored at `d`. -/
def copyMem (m : Mem) (s d : Addr) : Mem :=
  Proof.Cmac.store4 m d (m.readW s 32) (m.readW (s + BitVec.ofNat 64 4) 32) (m.readW (s + BitVec.ofNat 64 8) 32)
    (m.readW (s + BitVec.ofNat 64 12) 32)

theorem blockAtMem_copy (m : Mem) (s d : Addr) : blockAtMem (copyMem m s d) d = blockAtMem m s := by
  rw [blockAtMem, blockAtMem, copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

/-- `W + d ← W + s`, through `r0`–`r3`. -/
theorem copy16_wp {sO dO : Nat} {t : State} {W : Addr} (h11 : State.addr (t.gpr .r11) = W)
    (hs : sO + 12 < 4096) (hd : dO + 12 < 4096) (fw : (t.gpr .r11).toNat + 2560 ≤ 2 ^ 32)
    (hs' : sO + 16 ≤ 2560) (hd' : dO + 16 ≤ 2560)
    (rS : Covers [⟨W + BitVec.ofNat 64 sO, 16⟩] (t.rd ++ t.wr)) (wD : Covers [⟨W + BitVec.ofNat 64 dO, 16⟩] t.wr) :
    WP isa (.block (copy16 sO dO)) t (Ran [.r0, .r1, .r2, .r3]
      (copyMem t.mem (W + BitVec.ofNat 64 sO) (W + BitVec.ofNat 64 dO)) t) := by
  have ea : ∀ k, k < 2560 → State.addr (t.gpr .r11 + BitVec.ofNat 32 k) = W + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega), h11]
  have r₀ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 sO) 4 := Proof.CmacAes.Arm.in_word0 rS
  have r₁ := Proof.CmacAes.Arm.in_word rS (i := 4) (by decide)
  have r₂ := Proof.CmacAes.Arm.in_word rS (i := 8) (by decide)
  have r₃ := Proof.CmacAes.Arm.in_word rS (i := 12) (by decide)
  rw [Offset.add_add] at r₁ r₂ r₃
  have w₀ : InRegions t.wr (W + BitVec.ofNat 64 dO) 4 := Proof.CmacAes.Arm.in_word0 wD
  have w₁ := Proof.CmacAes.Arm.in_word wD (i := 4) (by decide)
  have w₂ := Proof.CmacAes.Arm.in_word wD (i := 8) (by decide)
  have w₃ := Proof.CmacAes.Arm.in_word wD (i := 12) (by decide)
  rw [Offset.add_add] at w₁ w₂ w₃
  have o₀ : sO < 4096 := by omega
  have o₁ : sO + 4 < 4096 := by omega
  have o₂ : sO + 8 < 4096 := by omega
  have o₃ : sO + 12 < 4096 := by omega
  have d₀ : dO < 4096 := by omega
  have d₁ : dO + 4 < 4096 := by omega
  have d₂ : dO + 8 < 4096 := by omega
  have d₃ : dO + 12 < 4096 := by omega
  refine WP.of_runBlock ⟨_, by
    simp only [copy16]
    orun [o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃, ea sO (by omega), ea (sO + 4) (by omega), ea (sO + 8) (by omega), ea (sO + 12) (by omega), ea dO (by omega),
      ea (dO + 4) (by omega), ea (dO + 8) (by omega), ea (dO + 12) (by omega), r₀, r₁, r₂, r₃, w₀, w₁, w₂,
      w₃, hs, hd], ⟨?_, by others_tac, by rfl, by rfl, by rfl⟩⟩
  simp only [mem_setReg, mem_store, copyMem, Proof.Cmac.store4, Offset.add_add]

/-! ## Doubling -/

/-- The memory after doubling the block at `P` into `C`: the block as four
byte-reversed words (`Cmac.dblMem`'s). -/
def dblMem (m : Mem) (P C : Addr) : Mem :=
  let b₀ := byteRev32 (m.readW P 32)
  let b₁ := byteRev32 (m.readW (P + BitVec.ofNat 64 4) 32)
  let b₂ := byteRev32 (m.readW (P + BitVec.ofNat 64 8) 32)
  let b₃ := byteRev32 (m.readW (P + BitVec.ofNat 64 12) 32)
  Proof.Cmac.store4 m C (byteRev32 (Proof.Cmac.dblW0 b₀ b₁))
    (byteRev32 (Proof.Cmac.dblW0 b₁ b₂)) (byteRev32 (Proof.Cmac.dblW0 b₂ b₃)) (byteRev32 (Proof.Cmac.dblW3 b₀ b₃))

theorem dblMem_frame (m : Mem) (P C : Addr) : Frame [⟨C, 16⟩] m (dblMem m P C) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_frame (m : Mem) (s d : Addr) : Frame [⟨d, 16⟩] m (copyMem m s d) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem blockAtMem_dbl (m : Mem) (P C : Addr) :
    blockAtMem (dblMem m P C) C = Spec.Ocb.double (blockAtMem m P) := by
  simp only [dblMem, blockAtMem]
  rw [Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_rev4, Proof.Cmac.dbl_words4, ← Proof.Cmac.ofBytes_rev4,
    Proof.Ocb.double_eq]
  exact Proof.Cmac.ofBytes_toBytes _

/-- The mask of the reduction, as `dbl` computes it. -/
theorem mask_eq (b : BitVec 32) :
    ((b >>> 31) - BitVec.ofNat 32 1 &&& BitVec.ofNat 32 0x87) ^^^ BitVec.ofNat 32 0x87 =
      ((0 : BitVec 32) - (b >>> 31)) &&& 0x87 := by
  have h : b >>> 31 = 0 ∨ b >>> 31 = 1 := by
    have : (b >>> 31).toNat < 2 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := b.isLt; omega
    rcases (show (b >>> 31).toNat = 0 ∨ (b >>> 31).toNat = 1 by omega) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases h with h | h <;> rw [h] <;> decide

theorem rev_eq (a : BitVec 32) : rev a = byteRev32 a := rfl

/-- `W + d ← double(b + s)`, through `r0`–`r3` and `r12`. -/
theorem dbl_wp {b : Reg} {sO dO : Nat} {t : State} {P W : Addr} (hb : b ≠ .r0 ∧ b ≠ .r1 ∧ b ≠ .r2)
    (hP : State.addr (t.gpr b) = P) (h11 : State.addr (t.gpr .r11) = W)
    (hs : sO + 12 < 4096) (hd : dO + 12 < 4096) (fb : (t.gpr b).toNat + sO + 16 ≤ 2 ^ 32)
    (fw : (t.gpr .r11).toNat + dO + 16 ≤ 2 ^ 32)
    (rS : Covers [⟨P + BitVec.ofNat 64 sO, 16⟩] (t.rd ++ t.wr)) (wD : Covers [⟨W + BitVec.ofNat 64 dO, 16⟩] t.wr) :
    WP isa (.block (dbl b sO dO)) t (Ran [.r0, .r1, .r2, .r3, .r12]
      (dblMem t.mem (P + BitVec.ofNat 64 sO) (W + BitVec.ofNat 64 dO)) t) := by
  obtain ⟨b0, b1, b2⟩ := hb
  have eb : ∀ k, k ≤ sO + 12 → State.addr (t.gpr b + BitVec.ofNat 32 k) = P + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega), hP]
  have ew : ∀ k, k ≤ dO + 12 → State.addr (t.gpr .r11 + BitVec.ofNat 32 k) = W + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega), h11]
  have r₀ : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 sO) 4 := Proof.CmacAes.Arm.in_word0 rS
  have r₁ := Proof.CmacAes.Arm.in_word rS (i := 4) (by decide)
  have r₂ := Proof.CmacAes.Arm.in_word rS (i := 8) (by decide)
  have r₃ := Proof.CmacAes.Arm.in_word rS (i := 12) (by decide)
  rw [Offset.add_add] at r₁ r₂ r₃
  have w₀ : InRegions t.wr (W + BitVec.ofNat 64 dO) 4 := Proof.CmacAes.Arm.in_word0 wD
  have w₁ := Proof.CmacAes.Arm.in_word wD (i := 4) (by decide)
  have w₂ := Proof.CmacAes.Arm.in_word wD (i := 8) (by decide)
  have w₃ := Proof.CmacAes.Arm.in_word wD (i := 12) (by decide)
  rw [Offset.add_add] at w₁ w₂ w₃
  have o₀ : sO < 4096 := by omega
  have o₁ : sO + 4 < 4096 := by omega
  have o₂ : sO + 8 < 4096 := by omega
  have o₃ : sO + 12 < 4096 := by omega
  have d₀ : dO < 4096 := by omega
  have d₁ : dO + 4 < 4096 := by omega
  have d₂ : dO + 8 < 4096 := by omega
  have d₃ : dO + 12 < 4096 := by omega
  refine WP.of_runBlock ⟨_, by
    simp only [dbl]
    orun [o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃, b0, b1, b2, eb sO (by omega), eb (sO + 4) (by omega), eb (sO + 8) (by omega), eb (sO + 12) (by omega),
      ew dO (by omega), ew (dO + 4) (by omega), ew (dO + 8) (by omega), ew (dO + 12) (by omega),
      r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, hs, hd], ⟨?_, by others_tac, by rfl, by rfl, by rfl⟩⟩
  simp only [mem_setReg, mem_store, dblMem, Proof.Cmac.store4, rev_eq, mask_eq, gpr_setReg, ite_true, ite_false,
    reduceCtorEq, b0, b1, b2, Offset.add_add]
  rfl

end VG.Proof.AesOcb.Arm
