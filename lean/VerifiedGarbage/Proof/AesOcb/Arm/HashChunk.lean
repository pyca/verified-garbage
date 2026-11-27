module

public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesOcb.Arm.Calls
public import VerifiedGarbage.Impl.AesOcb.Arm
public import VerifiedGarbage.Proof.AesOcb.Arm.Env
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ocb.Nonce
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Arm.Words
public import VerifiedGarbage.Proof.Cmac.Dbl32

/-! ### `AesOcb.Arm.NonceBlock`, which this module and modules that import it used -/

section

/-! ### `AesOcb.Arm.Words`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: blocks a word at a time

Untrusted: everything here is checked by Lean. The straight-line pieces the
functions build blocks with, each leaving its memory and writing only some
registers (`Ran`): the XOR of two blocks into a third, a word at a time
(`xorB`, which is AES-CMAC's `xorBlk`: `Cmac.xor4Mem`, `blockAtMem_xor4`),
a block zeroed (`zero16`: `Cmac.zero4`), copied (`copy16`) and doubled
(`dbl`: `dblMem`, `blockAtMem_dbl`).
-/

@[expose] public section

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
    rw [addr_add (by omega_using [fw, hk]), h11]
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
  have o₀ : sO < 4096 := by omega_using [hs]
  have o₁ : sO + 4 < 4096 := by omega_using [hs]
  have o₂ : sO + 8 < 4096 := by omega_using [hs]
  have o₃ : sO + 12 < 4096 := by omega_using [hs]
  have d₀ : dO < 4096 := by omega_using [hd]
  have d₁ : dO + 4 < 4096 := by omega_using [hd]
  have d₂ : dO + 8 < 4096 := by omega_using [hd]
  have d₃ : dO + 12 < 4096 := by omega_using [hd]
  refine WP.of_runBlock ⟨_, by
    simp only [copy16]
    orun [o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃, ea sO (by omega_using [hs']), ea (sO + 4) (by omega_using [hs']), ea (sO + 8) (by omega_using [hs']), ea (sO + 12) (by omega_using [hs']), ea dO (by omega_using [hd']),
      ea (dO + 4) (by omega_using [hd']), ea (dO + 8) (by omega_using [hd']), ea (dO + 12) (by omega_using [hd']), r₀, r₁, r₂, r₃, w₀, w₁, w₂,
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
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := b.isLt; omega_using []
    rcases (show (b >>> 31).toNat = 0 ∨ (b >>> 31).toNat = 1 by omega_using [this]) with h | h
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
    rw [addr_add (by omega_using [fb, hk]), hP]
  have ew : ∀ k, k ≤ dO + 12 → State.addr (t.gpr .r11 + BitVec.ofNat 32 k) = W + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by omega_using [fw, hk]), h11]
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
  have o₀ : sO < 4096 := by omega_using [hs]
  have o₁ : sO + 4 < 4096 := by omega_using [hs]
  have o₂ : sO + 8 < 4096 := by omega_using [hs]
  have o₃ : sO + 12 < 4096 := by omega_using [hs]
  have d₀ : dO < 4096 := by omega_using [hd]
  have d₁ : dO + 4 < 4096 := by omega_using [hd]
  have d₂ : dO + 8 < 4096 := by omega_using [hd]
  have d₃ : dO + 12 < 4096 := by omega_using [hd]
  refine WP.of_runBlock ⟨_, by
    simp only [dbl]
    orun [o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃, b0, b1, b2, eb sO (by omega_using []), eb (sO + 4) (by omega_using []), eb (sO + 8) (by omega_using []), eb (sO + 12) (by omega_using []),
      ew dO (by omega_using []), ew (dO + 4) (by omega_using []), ew (dO + 8) (by omega_using []), ew (dO + 12) (by omega_using []),
      r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, hs, hd], ⟨?_, by others_tac, by rfl, by rfl, by rfl⟩⟩
  simp only [mem_setReg, mem_store, dblMem, Proof.Cmac.store4, rev_eq, mask_eq, gpr_setReg, ite_true, ite_false,
    reduceCtorEq, b0, b1, b2, Offset.add_add]
  rfl

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`), as on AArch64
(`Proof.AesOcb.AArch64.nonceBlock_ok`): zeros, the 1 before where the nonce
goes, the nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into
the first byte, and the last byte split into `bottom` and the rest. The 16
bytes are followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)
open VG.Proof.AesGcm.Arm (copyLoop_ok LoopPre in_left in_off and15 mem_store rd_store wr_store sp_store gpr_store add_ofNat_zero setWidth8_32)

theorem ofNat_shl4 (a : Nat) : BitVec.ofNat 32 a <<< 4 = BitVec.ofNat 32 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  congr 1; omega_using []

theorem or_byte32 (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 b ||| BitVec.ofNat 32 v) = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 32 by omega_using [hi], hi,
    decide_true, Bool.true_and]

theorem and_byte32 (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 b &&& BitVec.ofNat 32 v) = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 32 by omega_using [hi], hi,
    decide_true, Bool.true_and]

theorem and63_32 (b : Byte) : BitVec.setWidth 32 b &&& BitVec.ofNat 32 63 = BitVec.ofNat 32 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_using []),
    show (63 : Nat) % 2 ^ 32 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega_using [h]) (by decide)

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega_using [hL, ho, h]), List.getElem?_append_left (by simp; omega_using [hL, ho, h]),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega_using [h]]
  · rw [List.getElem?_append_left (by simp; omega_using [hL, hk]), List.getElem?_append_right (by simp; omega_using [])]
    simp [show min k L.length = k by omega_using [hL, hk]]
  · rw [List.getElem?_append_right (by simp; omega_using [h])]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega_using [h], ↓reduceIte]
    congr 2; omega_using [hL, ho, h]

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 4⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 32 = BitVec.ofNat 32 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : Others [.r0, .r1, .r2, .r3, .r12] s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem w127 (W : BitVec 32) {nl : Nat} (h : nl ≤ 15) :
    W + BitVec.ofNat 32 127 - BitVec.ofNat 32 nl = W + BitVec.ofNat 32 (127 - nl) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega_using [h])]

theorem w128 (W : BitVec 32) {nl : Nat} (h : nl ≤ 15) :
    W + BitVec.ofNat 32 (127 - nl) + BitVec.ofNat 32 1 = W + BitVec.ofNat 32 (128 - nl) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using [h]

theorem nonceBlock_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (h4 : s.gpr .r4 = p.N) (h5 : s.gpr .r5 = BitVec.ofNat 32 p.nl) :
    WP isa nonceBlock s (NoncePost (State.addr p.W) p.tl (bytesAt s.mem (State.addr p.N) p.nl) s) := by
  have fw := L.ww
  have h1 := L.nl1
  have h15 := L.nl15
  obtain nl32 : p.nl < 2 ^ 32 := by omega_arith
  unfold nonceBlock
  refine WP.seq (WP.block_append (WP.mono (zero16_wp (o := tmpO) (by decide) (by rw [E.r11]; simp only [tmpO]; omega_arith)
    (by rw [E.r11]; exact E.perm.wC (by decide))) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  obtain r11₁ : s₁.gpr .r11 = p.W := by rw [R₁.gpr _ (by decide), E.r11]
  obtain r4₁ : s₁.gpr .r4 = p.N := by rw [R₁.gpr _ (by decide), h4]
  obtain r5₁ : s₁.gpr .r5 = BitVec.ofNat 32 p.nl := by rw [R₁.gpr _ (by decide), h5]
  obtain ea : State.addr (p.W + BitVec.ofNat 32 (127 - p.nl)) = State.addr p.W + BitVec.ofNat 64 (127 - p.nl) :=
    addr_add (by omega_arith)
  obtain w₁ : InRegions s₁.wr (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) 1 := by
    rw [R₁.wr]; exact E.perm.wW (d := 127 - p.nl) (n := 1) (by omega_arith)
  obtain eD : State.addr (p.W + BitVec.ofNat 32 (128 - p.nl)) = State.addr p.W + BitVec.ofNat 64 (128 - p.nl) :=
    addr_add (by omega_arith)
  refine WP.of_runBlock ⟨_, by orun [r11₁, r4₁, r5₁, w127 _ h15, add_ofNat_zero, ea, w₁, w128 _ h15], ?_⟩
  refine WP.seq (WP.mono (copyLoop_ok _ (S := p.N) (D := p.W + BitVec.ofNat 32 (128 - p.nl)) (n := p.nl)
    ⟨by simp [gpr_setReg, r4₁], by simp [gpr_setReg], by simp [gpr_setReg, r5₁], h1, nl32, L.nw,
      by rw [L.wN (by omega_arith)]; omega_arith, by simp only [rd_setReg, wr_setReg, rd_store, wr_store, R₁.rd, R₁.wr]; exact E.perm.non,
      by simp only [wr_setReg, wr_store, R₁.wr, eD]; exact E.perm.wC (d := 128 - p.nl) (n := p.nl) (by omega_arith),
      by rw [eD]; exact L.n_w' (by omega_arith)⟩) fun s₃ ⟨m₃, O₃⟩ => ?_)
  simp only [mem_store, mem_setReg, eD] at m₃
  -- what the first two pieces wrote
  obtain e127 : State.addr p.W + BitVec.ofNat 64 (127 - p.nl) =
      State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - p.nl) := by
    rw [Offset.add_add, show 112 + (15 - p.nl) = 127 - p.nl by omega_arith]
  obtain e128 : State.addr p.W + BitVec.ofNat 64 (128 - p.nl) =
      State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - p.nl) := by
    rw [Offset.add_add, show 112 + (16 - p.nl) = 128 - p.nl by omega_arith]
  obtain f₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] s.mem
      (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1))) := by
    rw [R₁.mem]
    refine (Proof.Cmac.frame_store4 _ _ _ _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [e127]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 112, 16⟩] s.mem s₃.mem := by
    rw [m₃]
    refine fun x hx => (writeBytes_frame _ _ _ ?_ x hx).trans (f₂ x hx)
    rw [length_bytesAt, e128]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain A₃ : Args p s₃.mem := A.frame L f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.args_w' (by decide))
  obtain sp₃ : s₃.sp = p.SP := by rw [O₃.sp]; simp [sp_setReg, sp_store, R₁.sp, E.sp]
  obtain rd₃ : s₃.rd = s.rd := by rw [O₃.rd]; simp [rd_setReg, rd_store, R₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [O₃.wr]; simp [wr_setReg, wr_store, R₁.wr]
  obtain r11₃ : s₃.gpr .r11 = p.W := by
    rw [O₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, gpr_store, r11₁]
  obtain P₃ : Perm p s₃ := E.perm.of_eq rd₃ wr₃
  obtain a₂₀ := P₃.argR' L (k := 20) (by decide)
  obtain rb₀ : InRegions (s₃.rd ++ s₃.wr) (State.addr p.W + BitVec.ofNat 64 112) 1 := P₃.wR (by decide)
  obtain wb₀ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 112) 1 := P₃.wW (by decide)
  obtain rb₁ : InRegions (s₃.rd ++ s₃.wr) (State.addr p.W + BitVec.ofNat 64 127) 1 := P₃.wR (by decide)
  obtain wb₁ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 127) 1 := P₃.wW (by decide)
  obtain wb₂ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 208) 4 := P₃.wW (by decide)
  obtain ne : (State.addr p.W + BitVec.ofNat 64 127 = State.addr p.W + BitVec.ofNat 64 112) = False := by
    simp only [eq_iff_iff, iff_false]
    intro h
    have := congrArg (· - State.addr p.W) h
    simp only [Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  obtain ew : ∀ k, k < 2560 → State.addr (p.W + BitVec.ofNat 32 k) = State.addr p.W + BitVec.ofNat 64 k :=
    fun k hk => L.wA hk
  obtain e112 := ew 112 (by decide)
  obtain e127' := ew 127 (by decide)
  obtain e208 := ew 208 (by decide)
  refine WP.of_runBlock ⟨_, by orun [r11₃, sp₃, A₃.a20, a₂₀, e112, e127', e208, rb₀, wb₀, rb₁, wb₁, wb₂,
    WriteBytes.writeW8_apply, ne], ?_⟩
  obtain htl : p.tl < 2 ^ 32 := by have := L.tl16; omega_arith
  simp only [and15, toNat_ofNat32 htl, ofNat_shl4, or_byte32, and_byte32, and63_32]
  -- the bytes at `W + tmpO`, step by step
  obtain hlen : (bytesAt s.mem (State.addr p.N) p.nl).length = p.nl := length_bytesAt _ _ _
  obtain eN : bytesAt (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1)))
      (State.addr p.N) p.nl = bytesAt s.mem (State.addr p.N) p.nl :=
    Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.n_w' (by decide)) (by omega_arith)
  rw [eN] at m₃
  obtain L₁ : bytesAt s₁.mem (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := by
    rw [R₁.mem]; exact Proof.Cmac.zero4_bytes _ _
  obtain L₂ : bytesAt (s₁.mem.writeW (State.addr p.W + BitVec.ofNat 64 (127 - p.nl)) (BitVec.setWidth 8 (BitVec.ofNat 32 1)))
      (State.addr p.W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ Spec.Ocb.zeros p.nl := by
    rw [e127, bytesAt_writeW8_at _ _ _ (by omega_arith) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - p.nl) 16 = 15 - p.nl by omega_arith,
      show 16 - (15 - p.nl + 1) = p.nl by omega_arith]
    rfl
  obtain L₃ : bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - p.nl) ++ [1] ++ bytesAt s.mem (State.addr p.N) p.nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega_arith) (by decide), L₂, hlen]
    rw [show 16 - p.nl + p.nl = 16 by omega_arith]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_append, List.length_singleton, List.append_assoc]
    simp only [show min (16 - p.nl) (15 - p.nl) = 15 - p.nl by omega_arith, show 16 - p.nl - (15 - p.nl) = 1 by omega_arith,
      show 16 - (15 - p.nl) = p.nl + 1 by omega_arith, show 15 - p.nl + (1 + p.nl) = 16 by omega_arith]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - p.nl - 16 = 0 by omega_arith, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ p.nl + 1 by simp), show p.nl - (p.nl + 1 - 1) = 0 by omega_arith,
      List.append_nil]
  obtain L₃d : ∀ k < 16, (bytesAt s₃.mem (State.addr p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      nbase (bytesAt s.mem (State.addr p.N) p.nl) k := fun k hk => by
    have := Proof.Ocb.nbase_list (bytesAt s.mem (State.addr p.N) p.nl) (by rw [hlen]; omega_arith) (by rw [hlen]; omega_arith) hk
    rw [hlen] at this; rw [L₃]; exact this
  obtain b0 : s₃.mem (State.addr p.W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem (State.addr p.N) p.nl) 0 := by
    have := getD_bytesAt_eq s₃.mem (State.addr p.W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  obtain e127' : State.addr p.W + BitVec.ofNat 64 127 = State.addr p.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add _ 112 15).symm
  obtain b15 : s₃.mem (State.addr p.W + BitVec.ofNat 64 127) = nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) 15 := by
    rw [e127', getD_bytesAt_eq s₃.mem (State.addr p.W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  obtain fr208 : ∀ (M : Mem) (v : BitVec 32), Frame [⟨State.addr p.W + BitVec.ofNat 64 208, 4⟩] M
      (M.writeW (State.addr p.W + BitVec.ofNat 64 208) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain L₄d : ∀ k < 16, (bytesAt (((s₃.mem.writeW (State.addr p.W + BitVec.ofNat 64 112)
        (s₃.mem (State.addr p.W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (p.tl % 16)))).writeW
        (State.addr p.W + BitVec.ofNat 64 208)
        (BitVec.ofNat 32 ((s₃.mem (State.addr p.W + BitVec.ofNat 64 127)).toNat % 64))).writeW
        (State.addr p.W + BitVec.ofNat 64 127) (s₃.mem (State.addr p.W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192))
        (State.addr p.W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) 15 &&& 0xc0
      else nb p.tl (bytesAt s.mem (State.addr p.N) p.nl) k := by
    intro k hk
    rw [b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr208 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 208) (k := 4) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega_arith, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega_arith]
        exact L₃d (k + 1) hk
  obtain fs₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 botO, 4⟩]
      s.mem s₃.mem := f₃.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [tmpO])
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_store, tmpO, botO]
    refine ((fs₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · exact contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · simp only [mem_store, tmpO]
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _)]
    refine Proof.Cmac.ext16 (length_bytesAt _ _ _) (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega_arith) (by omega_arith) hk]
  · simp only [mem_store, botO]
    rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, b15, Proof.Ocb.nonceN_bottom _ _ (by omega_arith) (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_store, gpr_setReg, hr.1, hr.2.1, ↓reduceIte]
    rw [O₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_store, gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ↓reduceIte]
    exact R₁.gpr r (by simp [hr.1])
  · simp only [sp_store, sp_setReg]; rw [O₃.sp]; simp [sp_store, sp_setReg, R₁.sp]
  · simp only [rd_store, rd_setReg]; exact rd₃
  · simp only [wr_store, wr_setReg]; exact wr₃

end VG.Proof.AesOcb.Arm

end

end

/-! ### `AesOcb.Arm.HashFill`, which this module and modules that import it used -/

section

/-! ### `AesOcb.Arm.LNtz`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `r6`), shifted right
once more each time (in `lr`), is even: `ntz(i)` times (`lNtz_ok`), as on
AArch64 (`Proof.AesOcb.AArch64.lNtz_ok`). The invariant: after `j`
doublings, `W + lO` holds `L_j`, `lr` is `i / 2^j`, which is positive, and
`ntz(i) = j + ntz(i / 2^j)`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.Arm (eval_eq' z_cmp0 z_subFlags)

theorem and1 {v : Nat} (hv : v < 2 ^ 32) :
    BitVec.ofNat 32 v &&& BitVec.ofNat 32 1 = BitVec.ofNat 32 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat32 hv, show (BitVec.ofNat 32 1).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_ofNat32 (by omega_using [])]

theorem shr1 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 1 = BitVec.ofNat 32 (v / 2) := by
  rw [ofNat_lsr32 hv]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : Others ntzRegs s s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `r12 ← lr ∧ 1` and `Z` set if it is zero, with `v` in `lr`. -/
theorem low1_wp (s : State) {v : Nat} (hv : v < 2 ^ 32) (hlr : s.gpr .lr = BitVec.ofNat 32 v) :
    WP isa (.block low1) s fun s' => s'.z = decide (v % 2 = 0) ∧ Ran [.r12] s.mem s s' := by
  refine WP.of_runBlock ⟨_, by orun [low1], ?_, by rfl, by others_tac, by rfl, by rfl, by rfl⟩
  simp only [z_subFlags, gpr_setReg, ite_true, hlr, and1 hv, BitVec.sub_zero]
  exact z_cmp0 (by omega_using [])

theorem lNtz_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 32) (h6 : s.gpr .r6 = BitVec.ofNat 32 i)
    (hl0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost (State.addr p.W) l i s) := by
  have fw := L.ww
  unfold lNtz
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (copy16_wp (W := State.addr p.W) (by rw [E.r11])
    (by decide) (by decide) (by rw [E.r11]; omega_using [fw]) (by decide) (by decide) (E.perm.wCR (by decide))
    (E.perm.wC (by decide))) fun s₁ R₁ => ?_)))
  have g₁ : ∀ r, r ∉ [Reg.r0, .r1, .r2, .r3] → s₁.gpr r = s.gpr r := R₁.gpr
  refine WP.block_cons_iff.mpr ⟨s₁.setReg .lr (s₁.gpr .r6), by simp [isa, exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (low1_wp _ hi' (by simp [gpr_setReg, g₁ .r6 (by decide), h6])) fun s₂ ⟨z₂, R₂⟩ => ?_
  -- The state before the loop.
  obtain post_of : ∀ t : State, Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      Others ntzRegs s₂ t → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr →
      LNtzPost (State.addr p.W) l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        R₂.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2), g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1,
          hr.2.2.2.1])], sp, rd, wr⟩
  obtain fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by
    rw [R₂.mem, mem_setReg, R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain v₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l 0 := by
    rw [R₂.mem, mem_setReg, R₁.mem, blockAtMem_copy, hl0]
  obtain sp₂ : s₂.sp = s.sp := by rw [R₂.sp, sp_setReg, R₁.sp]
  obtain rd₂ : s₂.rd = s.rd := by rw [R₂.rd, rd_setReg, R₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [R₂.wr, wr_setReg, R₁.wr]
  obtain lr₂ : s₂.gpr .lr = BitVec.ofNat 32 i := by
    rw [R₂.gpr _ (by decide), gpr_setReg_self, g₁ _ (by decide), h6]
  obtain r11₂ : s₂.gpr .r11 = p.W := by
    rw [R₂.gpr _ (by decide), gpr_setReg_of_ne (h := by decide), g₁ _ (by decide), E.r11]
  refine WP.ite (decide (i % 2 = 0)) (eval_eq' z₂) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂ rd₂ wr₂))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega_using [hb])]
  obtain he : i % 2 = 0 := of_decide_eq_true hb
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) ∧
      Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l j ∧
      Others ntzRegs s₂ t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ 0) _
    ⟨0, rfl, by simpa using hi, by simpa using he, by simp, by simpa using lr₂, fr₂, v₂,
      fun _ _ => rfl, sp₂, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, lrt, fr, v, g, sp, rd, wr⟩
  obtain hv : i / 2 ^ j < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  obtain r11t : t.gpr .r11 = p.W := by rw [g _ (by decide), r11₂]
  obtain Pt : Perm p t := E.perm.of_eq rd wr
  refine WP.block_append (WP.block_append (WP.mono (dbl_wp (b := .r11) (W := State.addr p.W)
    (P := State.addr p.W) (by decide) (by rw [r11t]) (by rw [r11t]) (by decide) (by decide)
    (by rw [r11t]; simp only [lO]; omega_using [fw]) (by rw [r11t]; simp only [lO]; omega_using [fw]) (Pt.wCR (by decide)) (Pt.wC (by decide))) fun t₁ D₁ => ?_))
  obtain e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain lr₁ : t₁.gpr .lr = BitVec.ofNat 32 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), lrt]
  refine WP.block_cons_iff.mpr ⟨t₁.setReg .lr (t₁.gpr .lr >>> 1), by simp [isa, exec, Op2.eval], WP.block_nil ?_⟩
  refine WP.mono (low1_wp _ (v := i / 2 ^ (j + 1)) (by omega_using [hv, e]) (by simp [gpr_setReg, lr₁, shr1 hv, e]))
    fun t₃ ⟨z₃, R₃⟩ => ?_
  obtain fr' : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [R₃.mem, mem_setReg, D₁.mem]
    exact fun x hx => (dblMem_frame _ _ _ x hx).trans (fr x hx)
  obtain v' : blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [R₃.mem, mem_setReg, D₁.mem, blockAtMem_dbl, v]; rfl
  obtain g' : Others ntzRegs s₂ t₃ := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.2.2.2.2.1]), gpr_setReg_of_ne (h := hr.2.2.2.2.2),
      D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  obtain sp' : t₃.sp = s.sp := by rw [R₃.sp, sp_setReg, D₁.sp, sp]
  obtain rd' : t₃.rd = s.rd := by rw [R₃.rd, rd_setReg, D₁.rd, rd]
  obtain wr' : t₃.wr = s.wr := by rw [R₃.wr, wr_setReg, D₁.wr, wr]
  obtain lr₃ : t₃.gpr .lr = BitVec.ofNat 32 (i / 2 ^ (j + 1)) := by
    rw [R₃.gpr _ (by decide), gpr_setReg_self, lr₁, shr1 hv, e]
  obtain hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega_using []
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega_using [hpos], j + 1, rfl,
      by rw [e]; omega_using [hpos, hev], hodd, hntz', lr₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_eq' z₃).trans (by simp [hodd]), post_of t₃ fr' ?_ g' sp' rd' wr'⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega_using [hodd])]

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: filling the buffer of `HASH` (`hashFill`)

Untrusted: everything here is checked by Lean. `hashFill` computes the next
offset of `HASH`, `Offset_{i+1} = Offset_i ⊕ L_{ntz(i+1)}` (`lNtz_ok`,
`xorB_wp`), and writes the next block of the associated data XORed with it
to the next slot of the buffer at `W + bufO` (`hashFill_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashFill_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.Arm (z_subFlags dec32 z_dec)

/-- The registers `hashFill` writes. -/
abbrev fillRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r8, .r12, .lr]

theorem w_A {p : Prm} (L : Lay p) {k : Nat} (h : 16 + k ≤ p.al) :
    State.addr (p.A + BitVec.ofNat 32 k) = State.addr p.A + BitVec.ofNat 64 k :=
  addr_add (by have := L.aw; omega_using [h, this])

/-- What one `hashFill` leaves. -/
structure FillPost (p : Prm) (l : Block) (j i c : Nat) (t t' : State) : Prop where
  frame : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
    ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t.mem t'.mem
  oh : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1)
  buf : blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i)) =
    blockAtMem t.mem (State.addr p.A + BitVec.ofNat 64 (16 * (j + i))) ^^^ offAt 0 l (j + i + 1)
  r4 : t'.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i + 1))
  r6 : t'.gpr .r6 = BitVec.ofNat 32 (j + i + 2)
  r8 : t'.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * (i + 1))
  r5 : t'.gpr .r5 = BitVec.ofNat 32 (c - (i + 1))
  z : t'.z = decide (i + 1 = c)
  gpr : Others fillRegs t t'
  sp : t'.sp = t.sp
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr

theorem hashFill_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {l : Block} {j i c : Nat} (hi : i < c)
    (hc : c ≤ 16) (hj : 16 * (j + i + 1) ≤ p.al)
    (h6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)) (h4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)))
    (h8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)) (h5 : t.gpr .r5 = BitVec.ofNat 32 (c - i))
    (hl0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hoh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i)) :
    WP isa hashFill t (FillPost p l j i c t) := by
  have fw := L.ww
  have fa := L.aw
  have al32 := L.al_lt
  obtain hb : bufO + 16 * i + 16 ≤ 512 := by simp only [bufO]; omega_using [hi, hc]
  unfold hashFill
  refine WP.seq (WP.mono (lNtz_ok (i := j + i + 1) L E (by omega_using []) (by omega_using [hj, fa]) h6 hl0) fun t₁ P₁ => ?_)
  obtain E₁ : Env p t₁ := E.of_others P₁.gpr P₁.sp P₁.rd P₁.wr
  have g₁ : Others ntzRegs t t₁ := P₁.gpr
  -- the offset
  refine WP.block_append (WP.block_append (WP.mono (xorB_wp (s := t₁) (pb := .r11) (qb := .r11) (cb := .r11)
    (pd := ohO) (qd := lO) (cd := ohO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [E₁.r11]; simp only [ohO]; omega_using [fw])
    (by rw [E₁.r11]; simp only [lO]; omega_using [fw]) (by rw [E₁.r11]; simp only [ohO]; omega_using [fw])
    (by rw [E₁.r11]; exact E₁.perm.wCR (by decide)) (by rw [E₁.r11]; exact E₁.perm.wCR (by decide))
    (by rw [E₁.r11]; exact E₁.perm.wC (by decide))) fun t₂ R₂ => ?_))
  rw [E₁.r11] at R₂
  obtain E₂ : Env p t₂ := E₁.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  obtain oh₂ : blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 l (j + i + 1) := by
    rw [R₂.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by decide)) (by decide) (by decide))), P₁.val,
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), hoh]
    rfl
  obtain g₂ : ∀ r, r ∉ ntzRegs → t₂.gpr r = t.gpr r := fun r hr => by
    obtain h' : r ∉ [Reg.r0, .r1] := fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h <;> simp [h])
    rw [R₂.gpr r h', g₁ r hr]
  obtain fr₂ : Frame [⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩]
      t.mem t₂.mem := by
    rw [R₂.mem]; exact (P₁.frame.mono (by simp)).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).mono (by simp))
  -- the block of the associated data
  obtain eA : State.addr (p.A + BitVec.ofNat 32 (16 * (j + i))) = State.addr p.A + BitVec.ofNat 64 (16 * (j + i)) :=
    w_A L (by omega_using [hj])
  obtain eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * i)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i) :=
    L.wA (by omega_using [hb])
  obtain r4₂ : t₂.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [g₂ _ (by decide), h4]
  obtain r8₂ : t₂.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [g₂ _ (by decide), h8]
  obtain hj' : 16 * (j + i) + 16 ≤ p.al := by omega_using [hj]
  obtain dA : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Sub ⟨State.addr p.A, p.al⟩ :=
    Offset.sub_base _ (by omega_using [hj])
  refine WP.mono (xorB_wp (s := t₂) (pb := .r4) (qb := .r11) (cb := .r8) (pd := 0) (qd := ohO) (cd := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [r4₂, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (j + i)) (by omega_using [hj, fa]),
      Nat.mod_eq_of_lt (by omega_using [hj, fa])]; omega_using [hj, fa])
    (by rw [E₂.r11]; simp only [ohO]; omega_using [fw]) (by rw [r8₂, L.wN (by omega_using [hb])]; omega_using [fw, hb])
    (by rw [r4₂, eA, BitVec.add_zero]; exact Proof.AesGcm.Arm.covers_off E₂.perm.aad hj' (by omega_using [fa]))
    (by rw [E₂.r11]; exact E₂.perm.wCR (by decide))
    (by rw [r8₂, eB, BitVec.add_zero]; exact E₂.perm.wC (by omega_using [hb]))) fun t₃ R₃ => ?_
  rw [r4₂, r8₂, E₂.r11, eA, eB, BitVec.add_zero, BitVec.add_zero] at R₃
  obtain fB : Frame [⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩] t₂.mem t₃.mem := by
    rw [R₃.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain dAW : (⟨State.addr p.A + BitVec.ofNat 64 (16 * (j + i)), 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩ := (L.a_w' (by omega_using [hb])).sub_left dA
  obtain g₃ : ∀ r, r ∉ fillRegs → t₃.gpr r = t.gpr r := fun r hr => by
    simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.1, hr.2.1]), g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2])]
  obtain r4₃ : t₃.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i)) := by rw [R₃.gpr _ (by decide), r4₂]
  obtain r8₃ : t₃.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i) := by rw [R₃.gpr _ (by decide), r8₂]
  obtain r6₃ : t₃.gpr .r6 = BitVec.ofNat 32 (j + i + 1) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h6]
  obtain r5₃ : t₃.gpr .r5 = BitVec.ofNat 32 (c - i) := by rw [R₃.gpr _ (by decide), g₂ _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [r4₃, r8₃, r6₃, r5₃], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact (fr₂.mono (by simp)).trans (fB.mono (by simp))
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [blockAtMem_frame fB (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by simp only [ohO, bufO]; omega_using [])) (by decide) (by omega_using [hb])), oh₂]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₃.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.of_disjoint dAW.symm)
      (Proof.Cmac.Sep4.of_disjoint (L.w_w (.inr (by simp only [ohO, bufO]; omega_using [])) (by omega_using [hb]) (by decide))),
      blockAtMem_frame fr₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (L.a_w' (by decide)).sub_left dA), oh₂]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * (j + i) + 16 = 16 * (j + i + 1) by omega_using []]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, ← BitVec.ofNat_add]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 256 + 16 * i + 16 = bufO + 16 * (i + 1) by simp only [bufO]; omega_using []]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hi (by omega_using [hc])]
  · simp only [z_setReg, z_subFlags, dec32 hi (by omega_using [hc]), z_dec hi (by omega_using [hc])]
  · simp only [fillRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, ite_false,
      Proof.AesGcm.Arm.gpr_subFlags]
    exact g₃ r (by simp [fillRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2])
  · simp only [sp_setReg, Proof.AesGcm.Arm.sp_subFlags]; rw [R₃.sp, R₂.sp, P₁.sp]
  · simp only [rd_setReg, Proof.AesGcm.Arm.rd_subFlags]; rw [R₃.rd, R₂.rd, P₁.rd]
  · simp only [wr_setReg, Proof.AesGcm.Arm.wr_subFlags]; rw [R₃.wr, R₂.wr, P₁.wr]

end VG.Proof.AesOcb.Arm

end

end

/-! ### `AesOcb.Arm.PadTo`, which the modules that import this one used -/

section

/-!
# AES-OCB on ARMv7: `pad(S)` (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes
`pad(S) = S ‖ 1 ‖ zeros` (§4.1), for the `n` bytes `S` at `r4`
(`0 < n < 16`), to `W + d`: zeros, the bytes copied (`copyLoop`), and `0x80`
after them (`padTo_ok`), as on AArch64 (`Proof.AesOcb.AArch64.padTo_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)
open VG.Proof.AesGcm.Arm (copyLoop_ok LoopPre mem_store gpr_store rd_store wr_store sp_store)

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.r0, .r1, .r2, .r3, .r12]

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `r4`, `0 < n < 16`. -/
theorem padTo_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {S : BitVec 32} {n d : Nat} (hn : 0 < n)
    (hn' : n < 16) (hd : d + 16 ≤ 2560) (he : encodable (BitVec.ofNat 32 d) = true)
    (h4 : s.gpr .r4 = S) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (fS : S.toNat + n ≤ 2 ^ 32)
    (hS : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) = pad (bytesAt s.mem (State.addr S) n) ∧
      Others padRegs s t ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega_using [hd])
  unfold padTo
  refine WP.seq (WP.block_append (WP.mono (zero16_wp (s := s) (o := d) (by omega_using [hd]) (by rw [E.r11]; omega_using [hd, fw])
    (by rw [E.r11]; exact E.perm.wC hd)) fun s₁ R₁ => ?_))
  rw [E.r11] at R₁
  have r11₁ : s₁.gpr .r11 = p.W := by rw [R₁.gpr _ (by decide), E.r11]
  have r4₁ : s₁.gpr .r4 = S := by rw [R₁.gpr _ (by decide), h4]
  have r5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [R₁.gpr _ (by decide), h5]
  refine WP.of_runBlock ⟨_, by orun [he, r11₁, r4₁, r5₁], ?_⟩
  have eS : bytesAt s₁.mem (State.addr S) n = bytesAt s.mem (State.addr S) n := by
    rw [R₁.mem]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega_using [hn'])
  have z₁ : bytesAt s₁.mem (State.addr p.W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [R₁.mem]; exact Proof.Cmac.zero4_bytes _ _
  refine WP.seq (WP.mono (copyLoop_ok _ (S := S) (D := p.W + BitVec.ofNat 32 d) (n := n)
    ⟨by simp [gpr_setReg, r4₁], by simp [gpr_setReg], by simp [gpr_setReg, r5₁], hn, by omega_using [hn'], fS,
      by rw [L.wN (by omega_using [hd])]; omega_using [hn', hd, fw], by simp only [rd_setReg, wr_setReg, R₁.rd, R₁.wr]; exact hS,
      by simp only [wr_setReg, R₁.wr, ed]; exact Proof.AesGcm.Arm.covers_prefix (E.perm.wC hd) (by omega_using [hn']),
      by rw [ed]; exact hSD.sub_right (Region.sub_prefix (by omega_using [hn']))⟩) fun s₃ ⟨m₃, O₃⟩ => ?_)
  simp only [mem_setReg, ed] at m₃
  rw [eS] at m₃
  have edn : State.addr (p.W + BitVec.ofNat 32 d + BitVec.ofNat 32 n + BitVec.ofNat 32 0) =
      State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n := by
    rw [BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add, L.wA (by omega_using [hn', hd]), Offset.add_add]
  have w₃ : InRegions s₃.wr (State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [O₃.wr]; simp only [wr_setReg, R₁.wr, Offset.add_add]; exact E.perm.wW (d := d + n) (n := 1) (by omega_using [hn', hd])
  refine WP.of_runBlock ⟨_, by orun [O₃.r2, edn, w₃], ?_⟩
  have hlen : (bytesAt s.mem (State.addr S) n).length = n := length_bytesAt _ _ _
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (State.addr p.W + BitVec.ofNat 64 d)
      (bytesAt s.mem (State.addr S) n)).writeW (State.addr p.W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b =
      writeBytes m (State.addr p.W + BitVec.ofNat 64 d) (bytesAt s.mem (State.addr S) n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega_using [hn', hlen]), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [mem_store, mem_setReg]
    rw [m₃, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega_using [hn'])) x hx]
    have F1 : Frame [⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩] s.mem s₁.mem := by
      rw [R₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    exact F1 x hx
  · simp only [mem_store, mem_setReg]
    rw [m₃, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega_using [hn']) (by decide), z₁]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega_using []]
    rfl
  · simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_store, gpr_setReg, hr.1, ite_false]
    rw [O₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2]
    simp only [gpr_setReg, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false]
    exact R₁.gpr r (by simp [hr.1])
  · simp only [sp_store, sp_setReg]; rw [O₃.sp]; simp [sp_setReg, R₁.sp]
  · simp only [rd_store, rd_setReg]; rw [O₃.rd]; simp [rd_setReg, R₁.rd]
  · simp only [wr_store, wr_setReg]; rw [O₃.wr]; simp [wr_setReg, R₁.wr]

end VG.Proof.AesOcb.Arm

end

end

/-! ### `AesOcb.Arm.Mut`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: what the pieces write

Untrusted: everything here is checked by Lean. The pieces after the entry
write only `W` but for our caller's saved registers, the stack below `SP`
and the data (`mutR`), which miss the key context, the nonce, the
associated data, the tag (`open`'s received one), the stack arguments and the
saved registers: those are the same in every state after the entry
(`sched_mut`, `lstar_mut`, `bytes_mut`, `Args.mut`, `saved_mut`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm
open VG.Spec.Ocb (Block blockAtMem)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (below)

/-- What the pieces after the entry write. -/
abbrev mutR (p : Prm) : List Region :=
  [⟨State.addr p.W, 128⟩, ⟨State.addr p.W + BitVec.ofNat 64 164, 2396⟩, below p.SP, ⟨State.addr p.D, p.n⟩]

/-- Our caller's saved registers in `W`. -/
abbrev savedR (p : Prm) : Region := ⟨State.addr p.W + BitVec.ofNat 64 128, 36⟩

section
variable {p : Prm} (L : Lay p)
include L

omit L in
/-- A part of `W` but the saved registers is in `mutR`. -/
theorem w_mut (_L : Lay p) {a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ mutR p, Region.Sub ⟨State.addr p.W + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr p.W + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega_using [h])⟩

omit L in
theorem below_mut (_L : Lay p) : ∃ r' ∈ mutR p, Region.Sub (below p.SP) r' := ⟨_, by simp, fun _ h => h⟩

omit L in
theorem data_mut (_L : Lay p) {a l : Nat} (h : a + l ≤ p.n) :
    ∃ r' ∈ mutR p, Region.Sub ⟨State.addr p.D + BitVec.ofNat 64 a, l⟩ r' :=
  ⟨_, by simp, Offset.sub_base _ h⟩

omit L in
/-- A region apart from `W`, the stack below `SP` and the data misses `mutR`. -/
theorem disj_mut (_L : Lay p) {r : Region} (hw : r.Disjoint ⟨State.addr p.W, 2560⟩) (hb : (below p.SP).Disjoint r)
    (hd : r.Disjoint ⟨State.addr p.D, p.n⟩) : ∀ r' ∈ mutR p, r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Region.sub_prefix (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hb.symm
  · exact hd

theorem saved_mut : ∀ r ∈ mutR p, (savedR p).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 36) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.bw' (by decide)).symm
  · exact (L.d_w' (by decide)).symm

theorem args_mut : ∀ r ∈ mutR p, (argR p.SP).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_args.symm.sub_right (Region.sub_prefix (by decide))
  · exact L.args_w' (by decide)
  · exact L.args_below
  · exact L.d_args.symm

theorem k_mut : ∀ r ∈ mutR p, (⟨State.addr p.K, 256⟩ : Region).Disjoint r :=
  disj_mut L L.k_w L.bk L.k_d

theorem sched_mut {m m' : Mem} (h : Frame (mutR p) m m') : sched p m' = sched p m :=
  Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L r hr).sub_left
    (Region.sub_prefix (by have := L.rounds_le; omega_using [this]))) (by have := L.rounds_le; omega_using [this])

theorem lstar_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    Spec.Ocb.ctxLstar m' (State.addr p.K) = Spec.Ocb.ctxLstar m (State.addr p.K) := by
  unfold Spec.Ocb.ctxLstar
  exact Proof.Ocb.blockAtMem_frame h fun r hr => (k_mut L r hr).sub_left (Offset.sub_base _ (by decide))

theorem aad_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    bytesAt m' (State.addr p.A) p.al = bytesAt m (State.addr p.A) p.al :=
  Proof.Cmac.bytesAt_frame h (disj_mut L L.a_w L.ba L.a_d) (by have := L.al_lt; omega_using [this])

theorem tag_mut {m m' : Mem} (h : Frame (mutR p) m m') :
    bytesAt m' (State.addr p.T) p.tl = bytesAt m (State.addr p.T) p.tl :=
  Proof.Cmac.bytesAt_frame h (disj_mut L L.t_w L.bt L.t_d) (by have := L.tl16; omega_using [this])

/-- A block of the associated data. -/
theorem aadBlk_mut {m m' : Mem} (h : Frame (mutR p) m m') {k : Nat} (hk : k + 16 ≤ p.al) :
    blockAtMem m' (State.addr p.A + BitVec.ofNat 64 k) = blockAtMem m (State.addr p.A + BitVec.ofNat 64 k) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => (disj_mut L L.a_w L.ba L.a_d r hr).sub_left (Offset.sub_base _ hk)

theorem Args.mut {m m' : Mem} (A : Args p m) (h : Frame (mutR p) m m') : Args p m' :=
  A.frame L h (args_mut L)

end

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: a chunk of `HASH` (`hashChunk`)

Untrusted: everything here is checked by Lean. After `j` of the `m` whole
blocks of the associated data `a`, `HInv` holds: the sum and the offset of
`HASH` are `Sum_j` and `Offset_j` (`Proof.Ocb.hsum`, `Proof.Ocb.offAt`), `r4`
points at block `j`, `r6` is `j + 1` and `r7` is `m − j`. `hashChunk` takes
`c = min(16, m − j)` blocks: fills the buffer with each block XORed with its
offset (`fill_ok`), enciphers the buffer, adds it to the sum (`sum_ok`), and
leaves `HInv` at `j + c` (`hashChunk_ok`), as on AArch64
(`Proof.AesOcb.AArch64.hashChunk_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz)
open VG.Proof.Ocb (offAt hsum blockAtMem_frame)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 dec32 z_dec mem_store gpr_store rd_store wr_store
  sp_store)

/-- The associated data in the memory `m`. -/
abbrev aadOf (p : Prm) (m : Mem) : List Byte := bytesAt m (State.addr p.A) p.al

/-- `ENCIPHER(K, ·)` of the key context in the memory `m`. -/
abbrev ciphOf (p : Prm) (m : Mem) : Cipher := Spec.Ocb.aesWith p.R (sched p m)

/-- `L_*` of the key context in the memory `m`. -/
abbrev lstarOf (p : Prm) (m : Mem) : Block := Spec.Ocb.ctxLstar m (State.addr p.K)

/-- What `HASH` writes: the sum, `L_{ntz(i)}`, its offset and the count of a
chunk, the buffer and the working space of the functions called, and the
stack below `SP`. -/
abbrev hashR (p : Prm) : List Region :=
  [⟨State.addr p.W + BitVec.ofNat 64 48, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 96, 16⟩,
   ⟨State.addr p.W + BitVec.ofNat 64 192, 24⟩, ⟨State.addr p.W + BitVec.ofNat 64 256, 2304⟩,
   Proof.AesGcm.Arm.below p.SP]

theorem hashR_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (hashR p) m m') : Frame (mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact below_mut L

/-- A part of one of the parts of `W` that `HASH` writes. -/
theorem w_hash {p : Prm} {a l b k : Nat} (hb : (⟨State.addr p.W + BitVec.ofNat 64 b, k⟩ : Region) ∈ hashR p)
    (h : b ≤ a ∧ a + l ≤ b + k) (_hk : b + k ≤ 2560) :
    ∃ r' ∈ hashR p, Region.Sub ⟨State.addr p.W + BitVec.ofNat 64 a, l⟩ r' :=
  ⟨_, hb, Offset.sub _ h.1 (by omega_arith)⟩

/-- What holds of `HASH` after `j` of the whole blocks of the associated data,
from the state `t₀` at its start. -/
structure HInv (p : Prm) (t₀ t : State) (j : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  le : j ≤ p.al / 16
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) j
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (lstarOf p t₀.mem) j
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * j)
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + 1)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j)
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t₀.mem) 0

/-- Block `i` of the associated data, in a state after `t₀`. -/
theorem aadBlk {p : Prm} (L : Lay p) {t₀ : State} {m : Mem} (h : Frame (mutR p) t₀.mem m) {i : Nat}
    (hi : i < p.al / 16) :
    blockAtMem m (State.addr p.A + BitVec.ofNat 64 (16 * i)) = blockAt (aadOf p t₀.mem) i := by
  rw [Proof.Ocb.blockAt_bytesAt _ _ (by omega_arith), aadBlk_mut L h (by omega_arith)]

/-! ## Filling the buffer -/

/-- The fill loop after `i` of the `c` blocks of a chunk from block `j`. -/
structure FillInv (p : Prm) (t₀ : State) (j c : Nat) (t : State) (i : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + i))
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + i + 1)
  r8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * i)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (c - i)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j - c)
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (lstarOf p t₀.mem) (j + i)
  buf : ∀ k < i, blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k)) =
    blockAt (aadOf p t₀.mem) (j + k) ^^^ offAt 0 (lstarOf p t₀.mem) (j + k + 1)
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) j
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t₀.mem) 0
  cnt : t.mem.readW (State.addr p.W + BitVec.ofNat 64 cnO) 32 = BitVec.ofNat 32 c

theorem fill_step {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    {t : State} {i : Nat} (hi : i < c) (F : FillInv p t₀ j c t i) :
    WP isa hashFill t fun t' => FillInv p t₀ j c t' (i + 1) ∧ t'.z = decide (i + 1 = c) := by
  refine WP.mono (hashFill_ok L F.env hi hc (by omega_arith) F.r6 F.r4 F.r8 F.r5 F.l0 F.oh) fun t' P => ?_
  obtain hfr : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩], ∃ r' ∈ hashR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_hash (b := 96) (k := 16) (by simp) (by decide) (by decide)
    · exact w_hash (b := 192) (k := 24) (by simp) (by decide) (by decide)
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by simp only [bufO]; omega_arith, by simp only [bufO]; omega_arith⟩
        (by decide)
  obtain kept : ∀ {d k : Nat}, d + k ≤ 2560 →
      (∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨State.addr p.W + BitVec.ofNat 64 ohO, 16⟩,
        ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * i), 16⟩],
        (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r) →
      bytesAt t'.mem (State.addr p.W + BitVec.ofNat 64 d) k = bytesAt t.mem (State.addr p.W + BitVec.ofNat 64 d) k :=
    fun hd h => Proof.Cmac.bytesAt_frame P.frame h (by omega_arith)
  obtain kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ lO ∨ lO + 16 ≤ d) → (d + 16 ≤ ohO ∨ ohO + 16 ≤ d) →
      (d + 16 ≤ bufO + 16 * i ∨ bufO + 16 * i + 16 ≤ d) →
      blockAtMem t'.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h₁ h₂ h₃ => by
      unfold blockAtMem
      rw [kept hd (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.w_w h₁ hd (by decide)
        · exact L.w_w h₂ hd (by decide)
        · exact L.w_w h₃ hd (by simp only [bufO]; omega_arith))]
  refine ⟨⟨F.env.of_others P.gpr P.sp P.rd P.wr, F.frame.trans (P.frame.sub hfr), by rw [P.rd, F.rd],
    by rw [P.wr, F.wr], by rw [P.r4]; congr 2, by rw [P.r6]; congr 1, P.r8, P.r5,
    by rw [P.gpr _ (by decide), F.r7], by rw [P.oh]; rfl, fun k hk => ?_, ?_, ?_, ?_⟩, P.z⟩
  · rcases (show k < i ∨ k = i by omega_arith) with hk | rfl
    · rw [kblk (by simp only [bufO]; omega_arith) (.inr (by simp only [lO, bufO]; omega_arith))
        (.inr (by simp only [ohO, bufO]; omega_arith)) (.inl (by omega_arith)), F.buf k hk]
    · rw [P.buf, aadBlk L (hashR_mut L F.frame) (by omega_arith)]
  · rw [kblk (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by simp only [sumO, bufO]; omega_arith)), F.sum]
  · rw [kblk (by decide) (.inl (by decide)) (.inl (by decide)) (.inl (by simp only [l0O, bufO]; omega_arith)), F.l0]
  · rw [P.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 cnO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by simp only [cnO, bufO]; omega_arith)) (by decide) (by simp only [bufO]; omega_arith)) (by decide),
      F.cnt]

theorem fill_ok {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 16)
    (hjc : j + c ≤ p.al / 16) {t : State} (F : FillInv p t₀ j c t 0) :
    WP isa (.loop hashFill .ne) t fun t' => FillInv p t₀ j c t' c := by
  refine WP.loop (M := isa) (fun k t' => ∃ i, k = c - i ∧ i < c ∧ FillInv p t₀ j c t' i) ?_ (c - 0) t
    ⟨0, rfl, hc0, F⟩
  rintro k t' ⟨i, rfl, hi, Fi⟩
  refine WP.mono (fill_step L hc hjc hi Fi) fun t'' ⟨F', z⟩ => ?_
  by_cases h : i + 1 = c
  · left
    refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
    subst h; exact F'
  · right
    exact ⟨(eval_ne' z).trans (by simp [h]), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, F'⟩

/-! ## Adding the buffer to the sum -/

/-- The sum loop after `k` of the `c` enciphered blocks of a chunk from block
`j`. -/
structure SumInv (p : Prm) (t₀ : State) (j c : Nat) (t : State) (k : Nat) : Prop where
  env : Env p t
  frame : Frame (hashR p) t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  r4 : t.gpr .r4 = p.A + BitVec.ofNat 32 (16 * (j + c))
  r6 : t.gpr .r6 = BitVec.ofNat 32 (j + c + 1)
  r8 : t.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * k)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (c - k)
  r7 : t.gpr .r7 = BitVec.ofNat 32 (p.al / 16 - j - c)
  oh : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 ohO) = offAt 0 (lstarOf p t₀.mem) (j + c)
  buf : ∀ k' < c, blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k')) =
    ciphOf p t₀.mem (blockAt (aadOf p t₀.mem) (j + k') ^^^ offAt 0 (lstarOf p t₀.mem) (j + k' + 1))
  sum : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    hsum (ciphOf p t₀.mem) (lstarOf p t₀.mem) (aadOf p t₀.mem) (j + k)
  l0 : blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p t₀.mem) 0

theorem sum_step {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc : c ≤ 16)
    {t : State} {k : Nat} (hk : k < c) (S : SumInv p t₀ j c t k) :
    WP isa (.block (xorB .r11 .r8 .r11 sumO 0 sumO ++ [Impl.AesGcm.Arm.addI .r8 .r8 16, .subs .r5 .r5 (Impl.AesGcm.Arm.imm 1)]))
      t fun t' => SumInv p t₀ j c t' (k + 1) ∧ t'.z = decide (k + 1 = c) := by
  have fw := L.ww
  obtain eB : State.addr (p.W + BitVec.ofNat 32 (bufO + 16 * k)) = State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k) :=
    L.wA (by simp only [bufO]; omega_arith)
  refine WP.block_append (WP.mono (xorB_wp (s := t) (pb := .r11) (qb := .r8) (cb := .r11) (pd := sumO) (qd := 0)
    (cd := sumO) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [S.env.r11]; simp only [sumO]; omega_arith) (by rw [S.r8, L.wN (by simp only [bufO]; omega_arith)]; simp only [bufO]; omega_arith)
    (by rw [S.env.r11]; simp only [sumO]; omega_arith) (by rw [S.env.r11]; exact S.env.perm.wCR (by decide))
    (by rw [S.r8, eB, BitVec.add_zero]; exact S.env.perm.wCR (by simp only [bufO]; omega_arith))
    (by rw [S.env.r11]; exact S.env.perm.wC (by decide))) fun t₁ R₁ => ?_)
  rw [S.env.r11, S.r8, eB, BitVec.add_zero] at R₁
  obtain dSB : (⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 (bufO + 16 * k), 16⟩ :=
    L.w_w (.inl (by simp only [sumO, bufO]; omega_arith)) (by decide) (by simp only [bufO]; omega_arith)
  obtain r5₁ : t₁.gpr .r5 = BitVec.ofNat 32 (c - k) := by rw [R₁.gpr _ (by decide), S.r5]
  obtain r8₁ : t₁.gpr .r8 = p.W + BitVec.ofNat 32 (bufO + 16 * k) := by rw [R₁.gpr _ (by decide), S.r8]
  refine WP.of_runBlock ⟨_, by orun [r5₁, r8₁], ?_⟩
  obtain fr : Frame [⟨State.addr p.W + BitVec.ofNat 64 sumO, 16⟩] t.mem t₁.mem := by
    rw [R₁.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  obtain kblk : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ sumO ∨ sumO + 16 ≤ d) →
      blockAtMem t₁.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd h => blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w h hd (by decide)
  refine ⟨⟨S.env.of_others (rs := [.r0, .r1, .r5, .r8]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, hr.2.2.1, hr.2.2.2, ↓reduceIte]
      exact R₁.gpr r (by simp [hr.1, hr.2.1])) (by simp [sp_setReg, Proof.AesGcm.Arm.sp_subFlags, R₁.sp])
      (by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, R₁.rd]) (by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, R₁.wr]),
    ?_, by simp [rd_setReg, Proof.AesGcm.Arm.rd_subFlags, R₁.rd, S.rd], by simp [wr_setReg, Proof.AesGcm.Arm.wr_subFlags, R₁.wr, S.wr],
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r4 (by decide), S.r4],
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r6 (by decide), S.r6], ?_, ?_,
    by simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, R₁.gpr .r7 (by decide), S.r7], ?_, fun k' hk' => ?_, ?_, ?_⟩,
    ?_⟩
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    exact S.frame.trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact w_hash (b := 48) (k := 16) (by simp) (by decide) (by decide))
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 2
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, dec32 hk (by omega_arith)]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by decide) (.inr (by decide)), S.oh]
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by simp only [bufO]; omega_arith) (.inr (by simp only [sumO, bufO]; omega_arith)), S.buf k' hk']
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [R₁.mem, blockAtMem_xor4 _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint dSB), S.sum, S.buf k hk]
    rfl
  · simp only [mem_setReg, Proof.AesGcm.Arm.mem_subFlags]
    rw [kblk (by decide) (.inr (by decide)), S.l0]
  · simp only [z_setReg, z_subFlags, dec32 hk (by omega_arith), z_dec hk (by omega_arith)]

theorem sum_ok {p : Prm} (L : Lay p) {t₀ : State} {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 16) {t : State}
    (S : SumInv p t₀ j c t 0) : WP isa hashSum t fun t' => SumInv p t₀ j c t' c := by
  refine WP.loop (M := isa) (fun k t' => ∃ i, k = c - i ∧ i < c ∧ SumInv p t₀ j c t' i) ?_ (c - 0) t
    ⟨0, rfl, hc0, S⟩
  rintro k t' ⟨i, rfl, hi, Si⟩
  refine WP.mono (sum_step L hc hi Si) fun t'' ⟨S', z⟩ => ?_
  by_cases h : i + 1 = c
  · left
    refine ⟨(eval_ne' z).trans (by simp [h]), ?_⟩
    subst h; exact S'
  · right
    exact ⟨(eval_ne' z).trans (by simp [h]), c - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, S'⟩

/-! ## The chunk -/

/-- The start of a chunk of `c` blocks from block `j`, once `c` is in `r5`:
`c` saved at `W + cnO`, the blocks left in `r7` and the buffer in `r8`. -/
theorem chunkHead_ok {p : Prm} (L : Lay p) {t₀ : State} {t : State} {j c : Nat}
    (H : HInv p t₀ t j) (_hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 c) :
    WP isa (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), Impl.AesGcm.Arm.addI .r8 .r11 bufO]) t fun t' => FillInv p t₀ j c t' 0 := by
  have fw := L.ww
  have al32 := L.al_lt
  have E := H.env
  obtain eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  obtain wC : InRegions t.wr (State.addr p.W + BitVec.ofNat 64 212) 4 := E.perm.wW (by decide)
  obtain kblk0 : ∀ {d : Nat}, d + 16 ≤ 2560 → (d + 16 ≤ cnO ∨ cnO + 4 ≤ d) → ∀ m : Mem, ∀ v : BitVec 32,
      blockAtMem (m.writeW (State.addr p.W + BitVec.ofNat 64 212) v) (State.addr p.W + BitVec.ofNat 64 d) =
        blockAtMem m (State.addr p.W + BitVec.ofNat 64 d) := fun hd h m v =>
    blockAtMem_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.w_w h hd (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.r11, h5, eC, wC, H.r7], ?_⟩
  refine ⟨H.env.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl), ?_, by simp [rd_setReg, rd_store, H.rd],
    by simp [wr_setReg, wr_store, H.wr], by simp [gpr_setReg, gpr_store, H.r4], by simp [gpr_setReg, gpr_store, H.r6], ?_,
    by simp [gpr_setReg, gpr_store, h5], ?_,
    ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store]
    exact H.frame.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact w_hash (b := 192) (k := 24) (by simp) (by decide) (by decide))
  · simp [gpr_setReg, gpr_store, E.r11, bufO]
  · simp only [gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, H.r7, h5]
    rw [Offset.ofNat_sub_ofNat (by omega_arith)]
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.oh]; simp
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.sum]
  · simp only [mem_setReg, mem_store]; rw [kblk0 (by decide) (.inl (by decide)), H.l0]
  · simp only [mem_setReg, mem_store, cnO, Mem.readW_writeW_self32]

/-- The state at the chunk's call. -/
abbrev chunkCallSt (p : Prm) (c : Nat) (t : State) : State :=
  ((((t.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12 (p.W + BitVec.ofNat 32 scrO)).setReg .r2
    (p.W + BitVec.ofNat 32 bufO)).setReg .r3 (BitVec.ofNat 32 c)

/-- The arguments of the chunk's call. -/
theorem chunkArgs_run {p : Prm} (L : Lay p) {t₀ t : State} {j c : Nat} (F : FillInv p t₀ j c t c) :
    runBlock isa (callArgs ++ [Impl.AesGcm.Arm.addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]) t =
      some (chunkCallSt p c t) := by
  have E₂ := F.env
  obtain eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  obtain rC : InRegions (t.rd ++ t.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₂.perm.wR (by decide)
  have cnt : t.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := F.cnt
  orun [callArgs, E₂.r9, E₂.r10, E₂.r11, eC, rC, cnt]

/-- The chunk's call, set up. -/
theorem chunkCall_blk {p : Prm} (L : Lay p) {t₀ t : State} {j c : Nat} (F : FillInv p t₀ j c t c) (hc : c ≤ 16) :
    BlkCall (chunkCallSt p c t) p.K (p.W + BitVec.ofNat 32 bufO) (p.W + BitVec.ofNat 32 scrO) p.R c ∧
      Env p (chunkCallSt p c t) := by
  have fw := L.ww
  have E₂ := F.env
  obtain eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  obtain E' : Env p (chunkCallSt p c t) :=
    E₂.of_others (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by decide)]; simp only [bufO]; omega_arith)
      (by rw [eB]; exact E₂.perm.wC (by simp only [bufO]; omega_arith)) (by rw [eB]; exact L.k_w' (by simp only [bufO]; omega_arith))
      (by rw [eB]; exact L.w_w (.inl (by simp only [scrO, bufO]; omega_arith)) (by simp only [bufO]; omega_arith) (by decide))
      (by rw [eB]; exact L.bw' (by simp only [bufO]; omega_arith)), E'⟩

/-- The rest of a chunk, from its call. -/
theorem chunkTail_ok {p : Prm} (L : Lay p) {t₀ t₂ : State} {j c : Nat} (F : FillInv p t₀ j c t₂ c)
    (hc0 : 0 < c) (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16) :
    WP isa (.seq encFrame
      (.seq (.block [Impl.AesGcm.Arm.addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
      (.seq hashSum (.block [.cmp .r7 (Impl.AesGcm.Arm.imm 0)]))))
      (chunkCallSt p c t₂) fun t' => HInv p t₀ t' (j + c) ∧ t'.z = decide (p.al / 16 - (j + c) = 0) := by
  have fw := L.ww
  have al32 := L.al_lt
  have E₂ := F.env
  obtain eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  obtain eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have cnt : t₂.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := F.cnt
  obtain hB := blkFrame_ok encF L (t := chunkCallSt p c t₂)
    (D := p.W + BitVec.ofNat 32 bufO) (n := c) (chunkCall_blk L F hc).2 (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg])
      (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by decide)]; simp only [bufO]; omega_arith)
      (by rw [eB]; exact E₂.perm.wC (by simp only [bufO]; omega_arith)) (by rw [eB]; exact L.k_w' (by simp only [bufO]; omega_arith))
      (by rw [eB]; exact L.w_w (.inl (by simp only [scrO, bufO]; omega_arith)) (by simp only [bufO]; omega_arith) (by decide))
      (by rw [eB]; exact L.bw' (by simp only [bufO]; omega_arith))
  rw [eB] at hB
  refine WP.seq (WP.mono (encFrame_eq ▸ hB) fun t₃ C₃ => ?_)
  -- what the call leaves
  obtain g₃ : ∀ r ∈ keptRegs, t₃.gpr r = t₂.gpr r := fun r hr => by
    rw [C₃.saved r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  obtain E₃ : Env p t₃ := E₂.keep (fun r hr => g₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))
    (by rw [C₃.sp]; rfl) (by rw [C₃.rd]; rfl) (by rw [C₃.wr]; rfl)
  obtain frC : ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 bufO, 16 * c⟩ : Region),
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, Proof.AesGcm.Arm.below p.SP], ∃ r' ∈ hashR p, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by simp only [bufO]; omega_arith⟩ (by decide)
    · exact w_hash (b := 256) (k := 2304) (by simp) ⟨by decide, by decide⟩ (by decide)
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain fr₃ : Frame (hashR p) t₀.mem t₃.mem := F.frame.trans (C₃.frame.sub frC)
  obtain kW : ∀ {d k : Nat}, d + k ≤ bufO → (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint
      ⟨State.addr p.W + BitVec.ofNat 64 bufO, 16 * c⟩ ∧
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩ ∧
      (⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (Proof.AesGcm.Arm.below p.SP) := fun hd =>
    ⟨L.w_w (.inl hd) (by simp only [bufO] at hd ⊢; omega_arith) (by simp only [bufO]; omega_arith),
      L.w_w (.inl (by simp only [bufO, scrO] at hd ⊢; omega_arith)) (by simp only [bufO] at hd ⊢; omega_arith) (by decide),
      (L.bw' (by simp only [bufO] at hd ⊢; omega_arith)).symm⟩
  obtain kblk : ∀ {d : Nat}, d + 16 ≤ bufO →
      blockAtMem t₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem t₂.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun hd => blockAtMem_frame C₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [(kW hd).1, (kW hd).2.1, (kW hd).2.2]
  obtain cnt₃ : t₃.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := by
    rw [C₃.frame.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 212, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [(kW (by decide)).1, (kW (by decide)).2.1, (kW (by decide)).2.2]) (by decide)]
    exact cnt
  obtain rC₃ : InRegions (t₃.rd ++ t₃.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₃.perm.wR (by decide)
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E₃.r11, eC, rC₃, cnt₃], ?_⟩)
  obtain hsched : sched p t₂.mem = sched p t₀.mem := sched_mut L (hashR_mut L F.frame)
  refine WP.seq (WP.mono (sum_ok L (t₀ := t₀) (j := j) (c := c) hc0 hc ?S0) fun t₄ S => ?_)
  case S0 =>
    refine ⟨E₃.of_others (rs := [.r5, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl),
      by simp only [mem_setReg]; exact fr₃, by simp [rd_setReg, C₃.rd, F.rd], by simp [wr_setReg, C₃.wr, F.wr],
      by simp [gpr_setReg, g₃ .r4 (by decide), F.r4], by simp [gpr_setReg, g₃ .r6 (by decide), F.r6],
      by simp [gpr_setReg, E₃.r11, bufO], by simp [gpr_setReg],
      by simp [gpr_setReg, g₃ .r7 (by decide), F.r7], ?_, fun k hk => ?_, ?_, ?_⟩
    · simp only [mem_setReg]; rw [kblk (by decide), F.oh]
    · simp only [mem_setReg]
      have := C₃.out k hk
      simp only [mem_setReg, Offset.add_add] at this
      rw [this, F.buf k hk, encF_ciph]
      simp only [mem_setReg, hsched]
    · simp only [mem_setReg]; rw [kblk (by decide), F.sum]; simp
    · simp only [mem_setReg]; rw [kblk (by decide), F.l0]
  -- the end
  refine WP.of_runBlock ⟨_, by orun [S.r7], ?_⟩
  refine ⟨⟨S.env.of_others (rs := []) (by others_tac) (by rfl) (by rfl) (by rfl), S.frame, S.rd, S.wr, hjc,
    S.sum, S.oh, S.r4, S.r6, by simp only [Proof.AesGcm.Arm.gpr_subFlags, S.r7]; congr 1; omega_arith, S.l0⟩, ?_⟩
  simp only [z_subFlags, S.r7, BitVec.sub_zero, z_cmp0 (show p.al / 16 - j - c < 2 ^ 32 by omega_arith)]
  congr 1; apply propext; omega_arith


/-- A chunk of `c` blocks from block `j`, once `c` is in `r5`. -/
theorem chunkRest_ok {p : Prm} (L : Lay p) {t₀ : State} {t : State} {j c : Nat}
    (H : HInv p t₀ t j) (hc0 : 0 < c) (hc : c ≤ 16) (hjc : j + c ≤ p.al / 16)
    (h5 : t.gpr .r5 = BitVec.ofNat 32 c) :
    WP isa (.seq (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), Impl.AesGcm.Arm.addI .r8 .r11 bufO])
      (.seq (.loop hashFill .ne)
      (.seq (.block (callArgs ++ [Impl.AesGcm.Arm.addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]))
      (.seq encFrame
      (.seq (.block [Impl.AesGcm.Arm.addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
      (.seq hashSum (.block [.cmp .r7 (Impl.AesGcm.Arm.imm 0)])))))))
      t fun t' => HInv p t₀ t' (j + c) ∧ t'.z = decide (p.al / 16 - (j + c) = 0) :=
  WP.seq (WP.mono (chunkHead_ok L H hc hjc h5) fun _ F₁ => WP.seq (WP.mono (fill_ok L hc0 hc hjc F₁)
    fun _ F₂ => WP.seq (WP.of_runBlock ⟨_, chunkArgs_run L F₂, chunkTail_ok L F₂ hc0 hc hjc⟩)))

theorem hashChunk_ok {p : Prm} (L : Lay p) {t₀ : State} {t : State} {j : Nat}
    (H : HInv p t₀ t j) (hj : j < p.al / 16) :
    WP isa hashChunk t fun t' => HInv p t₀ t' (j + min 16 (p.al / 16 - j)) ∧
      t'.z = decide (p.al / 16 - (j + min 16 (p.al / 16 - j)) = 0) := by
  have al32 := L.al_lt
  obtain m32 : p.al / 16 - j < 2 ^ 32 := by omega_arith
  unfold hashChunk
  obtain z₁ : (BitVec.ofNat 32 (p.al / 16 - j) >>> 4 == 0) = decide (p.al / 16 - j < 16) := by
    rw [ofNat_lsr32 m32, z_cmp0 (by omega_arith)]; congr 1; apply propext; omega_arith
  refine WP.seq (WP.of_runBlock ⟨_, by orun [H.r7], ?_⟩)
  obtain Hk : ∀ {t' : State}, t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      Others [.r5, .r12] t t' → HInv p t₀ t' j := fun hm hrd hwr hsp ho =>
    ⟨H.env.of_others ho hsp hrd hwr, by rw [hm]; exact H.frame, by rw [hrd, H.rd], by rw [hwr, H.wr], H.le,
      by rw [hm]; exact H.sum, by rw [hm]; exact H.oh, by rw [ho _ (by decide), H.r4], by rw [ho _ (by decide), H.r6],
      by rw [ho _ (by decide), H.r7], by rw [hm]; exact H.l0⟩
  refine WP.seq (WP.ite (decide (p.al / 16 - j < 16))
    (eval_eq' (by simp only [z_subFlags, gpr_setReg, ite_true, H.r7, BitVec.sub_zero, z₁])) (fun hb => ?_)
    (fun hb => ?_))
  · have hlt : p.al / 16 - j < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by orun [H.r7], ?_⟩
    obtain e : min 16 (p.al / 16 - j) = p.al / 16 - j := by omega_arith
    rw [e]
    exact chunkRest_ok L (Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac)) (by omega_arith) (by omega_arith) (by omega_arith)
      (by simp [gpr_setReg, H.r7])
  · have hlt : ¬ p.al / 16 - j < 16 := by simpa using hb
    refine WP.of_runBlock ⟨_, by orun [], ?_⟩
    obtain e : min 16 (p.al / 16 - j) = 16 := by omega_arith
    rw [e]
    exact chunkRest_ok L (Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac)) (by omega_arith) (by omega_arith) (by omega_arith)
      (by simp [gpr_setReg])

end VG.Proof.AesOcb.Arm