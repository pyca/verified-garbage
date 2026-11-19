module

public import VerifiedGarbage.Impl.AesOcb.AArch64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.AesOcb.AArch64.Env
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args
public import VerifiedGarbage.Proof.Ocb.Stretch
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Ocb.Nonce
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys

/-! ### `AesOcb.AArch64.NonceBlock`, which this module and modules that import it used -/

section

/-! ### `AesOcb.AArch64.PadTo`, which this module and modules that import it used -/

section

/-! ### `AesOcb.AArch64.Words`, which this module and modules that import it used -/

section

/-!
# AES-OCB on AArch64: blocks of `W`, two words at a time

Untrusted: everything here is checked by Lean. `zero16`, `copy16`, `xor16`
and `dbl` write a block of `W` (`BlkStep`): zeros, a copy, the XOR with a
block and `double` of a block (`zero16_ok`, `copy16_ok`, `xor16_ok`,
`dbl_ok`), as blocks of memory (`blockAtMem`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double)
open VG.Proof.Cmac (le8 le8_readW xor_words bytesAt_store2)
open VG.Proof.AesGcm.AArch64 (in_left)

/-- What a step writing the block at `W + d` does: it writes only there,
the block `v`, and keeps the registers but `clob`. -/
structure BlkStep (W : Addr) (d : Nat) (v : Block) (clob : List Reg) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem blockAtMem_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    blockAtMem ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p = Spec.Ocb.ofBytes (le8 w₀ ++ le8 w₁) := by
  rw [blockAtMem, bytesAt_store2]

/-- The two words of a block, XORed with those of another, are the XOR of
the blocks. -/
theorem blockAtMem_xor_words (m : Mem) (p q : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64 ^^^ m.readW q 64) ++
      le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)) =
      blockAtMem m p ^^^ blockAtMem m q := by
  rw [xor_words, ← Proof.Ocb.xor_eq, Proof.Ocb.ofBytes_xor (by simp [Spec.Aes.bytesAt])
    (by simp [Spec.Aes.bytesAt])]
  rfl

theorem blockAtMem_words (m : Mem) (p : Addr) :
    Spec.Ocb.ofBytes (le8 (m.readW p 64) ++ le8 (m.readW (p + BitVec.ofNat 64 8) 64)) = blockAtMem m p := by
  rw [le8_readW, le8_readW, ← Proof.Cmac.bytesAt_split]; rfl

theorem addr8 (p : Addr) (d : Nat) : p + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (d + 8) :=
  Offset.add_add p d 8

theorem imm0 : BitVec.setWidth 64 (BitVec.ofNat 16 0) <<< (16 * 0) = (0 : BitVec 64) := by decide

/-- `zero16 d`: `W + d ← 0`. -/
theorem zero16_ok {W : Addr} {s : State} {d : Nat} (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧ BlkStep W d 0 [.x9] s s' := by
  refine ⟨_, by orun [zero16, h19, w₀, w₁, hd.1, Nat.add_mod_right, show d < 32768 by omega_arith, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [imm0]; rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · simp only [imm0]; rw [← addr8 W d, blockAtMem_store2]; decide
  · simp only [List.mem_singleton] at hr
    simp only [gpr_write, hr, ite_false]

/-- `copy16 a d`: `W + d ← W + a`. -/
theorem copy16_ok {W : Addr} {s : State} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (copy16 a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 a)) [.x9, .x10] s s' := by
  refine ⟨_, by orun [copy16, h19, r₀, r₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right, show a < 32768 by omega_arith,
    show d < 32768 by omega_arith, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← addr8 W d, blockAtMem_store2, ← addr8 W a, blockAtMem_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]

/-- `xor16 b a d`: `W + d ← W + d ⊕ (B + a)`, `B` in `b`. -/
theorem xor16_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W) (hb : s.gpr b = B)
    (hb9 : b ≠ .x9) (hb10 : b ≠ .x10) (hb11 : b ≠ .x11)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (xor16 b a d) s = some s' ∧
      BlkStep W d (blockAtMem s.mem (W + BitVec.ofNat 64 d) ^^^ blockAtMem s.mem (B + BitVec.ofNat 64 a))
        [.x9, .x10, .x11, .x12] s s' := by
  have v₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_left w₀
  have v₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (d + 8)) 8 := in_left w₁
  refine ⟨_, by orun [xor16, h19, hb, hb9, hb10, hb11, r₀, r₁, v₀, v₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right,
    show a < 32768 by omega_arith, show d < 32768 by omega_arith, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← addr8 W d, blockAtMem_store2, ← addr8 B a, blockAtMem_xor_words]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `double` of the block at `p`, from its byte-reversed words. -/
theorem dbl_mem (m : Mem) (p : Addr) :
    let hi := rev64 (m.readW p 64)
    let lo := rev64 (m.readW (p + BitVec.ofNat 64 8) 64)
    Spec.Ocb.ofBytes (le8 (rev64 (Proof.CmacAes.AArch64.dblHi hi lo)) ++
      le8 (rev64 (Proof.CmacAes.AArch64.dblLo hi lo))) = double (blockAtMem m p) := by
  intro hi lo
  rw [Proof.CmacAes.AArch64.le8_rev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes,
    Proof.CmacAes.AArch64.dbl_words, Proof.Ocb.double_eq]
  congr 1
  have e0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p
  have := Proof.Gcm.AArch64.blockAt_rev m p
  rw [e0] at this
  exact this

/-- `dbl b a d`: `W + d ← double(B + a)`, `B` in `b`. -/
theorem dbl_ok {W B : Addr} {s : State} {b : Reg} {a d : Nat} (ha : a % 8 = 0 ∧ a + 8 < 32768)
    (hd : d % 8 = 0 ∧ d + 8 < 32768) (h19 : s.gpr .x19 = W) (hb : s.gpr b = B) (hb9 : b ≠ .x9)
    (r₀ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 a) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (a + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 d) 8) (w₁ : InRegions s.wr (W + BitVec.ofNat 64 (d + 8)) 8) :
    ∃ s', runBlock isa (dbl b a d) s = some s' ∧
      BlkStep W d (double (blockAtMem s.mem (B + BitVec.ofNat 64 a))) [.x9, .x10, .x11, .x12, .x13] s s' := by
  refine ⟨_, by orun [dbl, h19, hb, hb9, r₀, r₁, w₀, w₁, ha.1, hd.1, Nat.add_mod_right,
    show a < 32768 by omega_arith, show d < 32768 by omega_arith, ha.2, hd.2], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← addr8 W d]; exact Proof.Cmac.frame_store2 _ _ _
  · rw [← addr8 W d, blockAtMem_store2, ← addr8 B a]
    exact dbl_mem _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: padding a string (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `x23` to `W + d`: zeros, the bytes
(AES-GCM's `copyLoop`), and `0x80` after them (`padTo_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.AesGcm.AArch64 (copyLoop_ok LoopPre in_left in_off)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)

theorem write1 (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v = m.writeW a (v : Byte) := by
  simp [Mem.writeW]

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega_using [h]) (by decide)

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- The 16 bytes of a block that is zero. -/
theorem bytesAt_of_zero {m : Mem} {p : Addr} (h : blockAtMem m p = 0) : bytesAt m p 16 = Spec.Ocb.zeros 16 := by
  rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt m p 16), ← toBytes_zero, ← h]; rfl

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.x9, .x11, .x12, .x13, .x14, .x15]

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `x23`, `0 < n < 16`. -/
theorem padTo_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr) {S : Addr}
    {n d : Nat} (hn : 0 < n) (hn' : n < 16) (hd : d % 8 = 0 ∧ d + 16 ≤ 512) (h23 : s.gpr .x23 = S)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 d) = pad (bytesAt s.mem S n) ∧
      (∀ r, r ∉ padRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wW : ∀ {e k : Nat}, e + k ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := d) ⟨hd.1, by omega_using [hd]⟩ h19 (wW (by omega_using [hd])) (wW (by omega_using [hd]))
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [Impl.AesGcm.AArch64.ptr .x11 .x19 d, Impl.AesGcm.AArch64.mov .x12 .x23,
        Impl.AesGcm.AArch64.mov .x13 .x24] s₁ = some s₂ ∧
      s₂.gpr .x11 = W + BitVec.ofNat 64 d ∧ s₂.gpr .x12 = S ∧ s₂.gpr .x13 = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    have h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
    have h23₁ : s₁.gpr .x23 = S := by rw [B₁.gpr _ (by decide), h23]
    have h24₁ : s₁.gpr .x24 = BitVec.ofNat 64 n := by rw [B₁.gpr _ (by decide), h24]
    refine ⟨_, by orun [show d < 4096 by omega_using [hd]], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h19₁]
    · simp [gpr_write, h23₁]
    · simp [gpr_write, h24₁]
    · simp [gpr_write, h1, h2, h3]
    all_goals rfl
  have hS₂ : Covers [⟨S, n⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hS
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact Proof.AesGcm.AArch64.covers_off hw (by omega_using [hn', hd]) (by decide)
  have hSD' : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ := hSD.sub_right (Region.sub_prefix (by omega_using [hn']))
  have eS : bytesAt s₂.mem S n = bytesAt s.mem S n := by
    rw [m₂]
    exact Proof.Cmac.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega_using [hn'])
  have z₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact bytesAt_of_zero B₁.val
  unfold padTo
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ hn ⟨by omega_using [hn'], hS₂, hD₂, hSD'⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, _, x11₃, g₃, sp₃, rd₃, wr₃⟩ := h₃
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact wW (by omega_using [hn', hd])
  refine WP.of_runBlock ⟨_, by orun [x11₃, w₃, write1], ?_⟩
  have hlen : (bytesAt s.mem S n).length = n := length_bytesAt _ _ _
  have key : ∀ (m : Mem) (b : Byte), (writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n)).writeW
      (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) b = writeBytes m (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [b]) :=
    fun m b => by rw [writeBytes_snoc _ _ _ _ (by omega_using [hn', hlen]), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, by rw [sp₃, sp₂, B₁.sp], by rw [rd₃, rd₂, B₁.rd], by rw [wr₃, wr₂, B₁.wr]⟩
  · dsimp only
    rw [m₃, eS, key]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega_using [hn'])) x hx, m₂]
    exact B₁.frame x hx
  · dsimp only
    rw [m₃, eS, key, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega_using [hn']) (by decide), z₂]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega_using []]
    rfl
  · simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    dsimp only
    rw [gpr_write_of_ne _ _ _ hr.1, g₃ r (by simp [Proof.AesGcm.AArch64.loopRegs, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
      g₂ r hr.2.1 hr.2.2.1 hr.2.2.2.1, B₁.gpr r (by simp [hr.1])]

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the 1 before where the nonce goes, the
nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into the first
byte, and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base
  toNat_ofNat_of_lt)
open VG.Proof.AesGcm.AArch64 (copyLoop_ok in_left in_off read_one and15 lsl4_ofNat)

theorem or_byte (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) ||| BitVec.ofNat 64 v)) =
      b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 32 by omega_arith,
    show i < 64 by omega_arith, hi, decide_true, Bool.true_and]

theorem and_byte (b : Byte) (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.ofNat 64 v)) =
      b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 32 by omega_arith,
    show i < 64 by omega_arith, hi, decide_true, Bool.true_and]

theorem and63 (b : Byte) :
    BitVec.setWidth 64 (BitVec.setWidth 32 b) &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_arith), Nat.mod_eq_of_lt (a := b.toNat) (by omega_arith),
    show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega_arith), List.getElem?_append_left (by simp; omega_arith),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega_arith]
  · rw [List.getElem?_append_left (by simp; omega_arith), List.getElem?_append_right (by simp; omega_arith)]
    simp [show min k L.length = k by omega_arith]
  · rw [List.getElem?_append_right (by simp; omega_arith)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega_arith, ↓reduceIte]
    congr 2; omega_arith

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The first block of `nonceBlock`: zeros, and the nonce's address and length. -/
theorem nonceHead_ok {W N : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr) {nl : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl) :
    ∃ s₁, runBlock isa (zero16 tmpO ++ [ld .x12 .x19 nO, ld .x13 .x19 nlO]) s = some s₁ ∧
      s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x13 → s₁.gpr r = s.gpr r) ∧
      Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s₁.mem ∧ blockAtMem s₁.mem (W + BitVec.ofNat 64 tmpO) = 0 ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain wW : ∀ {e k : Nat}, e + k ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := zero16_ok (s := s) (d := tmpO) (by decide) h19 (wW (by decide)) (wW (by decide))
  obtain h19₁ : s₁.gpr .x19 = W := by rw [B₁.gpr _ (by decide), h19]
  obtain kept : ∀ {d}, (d + 8 ≤ 112 ∨ 128 ≤ d) → d + 8 ≤ 512 →
      s₁.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    B₁.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [tmpO]; exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  obtain r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nO) 8 := by rw [B₁.rd, B₁.wr]; exact in_left (wW (by decide))
  obtain r₂ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 nlO) 8 := by rw [B₁.rd, B₁.wr]; exact in_left (wW (by decide))
  obtain hN₁ := (kept (d := nO) (by decide) (by decide)).trans hN
  obtain hnl₁ := (kept (d := nlO) (by decide) (by decide)).trans hnl
  simp only [nO, nlO] at r₁ r₂ hN₁ hnl₁
  obtain ⟨s₂, run₂, h₂⟩ : ∃ s₂, runBlock isa [ld .x12 .x19 nO, ld .x13 .x19 nlO] s₁ = some s₂ ∧ s₂ = _ :=
    ⟨_, by orun [h19₁, r₁, r₂], rfl⟩
  subst h₂
  refine ⟨_, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_, ?_, fun r h1 h2 h3 => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19₁, hN₁]
  · simp [gpr_write, h19₁, hnl₁]
  · simp only [gpr_write, h2, h3, ite_false]; exact B₁.gpr r (by simp [h1])
  · exact B₁.frame
  · exact B₁.val
  · exact B₁.sp
  · exact B₁.rd
  · exact B₁.wr

/-- The second block: the 1 before where the nonce goes, and the arguments of
the copy. -/
theorem nonceOne_ok {W N : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr) {nl : Nat}
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (h12 : s.gpr .x12 = N) (h13 : s.gpr .x13 = BitVec.ofNat 64 nl) :
    ∃ s₁, runBlock isa [Impl.AesGcm.AArch64.ptr .x11 .x19 (tmpO + 16), .sub .x .x11 .x11 .x13,
        .subImm .x .x14 .x11 1, Impl.AesGcm.AArch64.imm .x9 1, .strb .x9 .x14 0] s = some s₁ ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 (128 - nl) ∧ s₁.gpr .x12 = N ∧ s₁.gpr .x13 = BitVec.ofNat 64 nl ∧
      (∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x14 → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  obtain e1 : W + 128#64 - BitVec.ofNat 64 nl = W + BitVec.ofNat 64 (128 - nl) := Offset.add_ofNat_sub W (by omega_arith)
  obtain e2 : W + BitVec.ofNat 64 (128 - nl) - 1#64 = W + BitVec.ofNat 64 (127 - nl) := by
    rw [Offset.add_ofNat_sub W (by omega_arith)]; congr 2; omega_arith
  obtain w : InRegions s.wr (W + BitVec.ofNat 64 (127 - nl)) 1 := in_off hw (by omega_arith) (by decide)
  refine ⟨_, by orun [h19, h13, e1, e2, w, write1], ?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h19, h13, e1]
  · simp [gpr_write, h12]
  · simp [gpr_write, h13]
  · simp [gpr_write, a, b, c]
  all_goals rfl

/-- The last block: `TAGLEN mod 128` into the first byte, `bottom`, and the
last byte's bits cleared. -/
theorem nonceTail_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr) {t : Nat}
    (ht : t < 2 ^ 64) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) :
    ∃ s₁, runBlock isa [ld .x10 .x19 tlO, Impl.AesGcm.AArch64.imm .x11 15, .logic .and .x .x10 .x10 .x11,
        .lsl .x .x10 .x10 4, .ldrb .x9 .x19 tmpO, .logic .orr .x .x9 .x9 .x10, .strb .x9 .x19 tmpO,
        .ldrb .x9 .x19 (tmpO + 15), Impl.AesGcm.AArch64.imm .x11 63, .logic .and .x .x10 .x9 .x11,
        st .x19 botO .x10, Impl.AesGcm.AArch64.imm .x11 0xc0, .logic .and .x .x9 .x9 .x11,
        .strb .x9 .x19 (tmpO + 15)] s = some s₁ ∧
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 112)
          (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16)))).writeW (W + BitVec.ofNat 64 288)
          (BitVec.ofNat 64 ((s.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  obtain r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 tlO) 8 := in_left (in_off hw (by decide) (by decide))
  obtain r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 1 := in_left (in_off hw (by decide) (by decide))
  obtain w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 1 := in_off hw (by decide) (by decide)
  obtain r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 127) 1 := in_left (in_off hw (by decide) (by decide))
  obtain w₂ : InRegions s.wr (W + BitVec.ofNat 64 127) 1 := in_off hw (by decide) (by decide)
  obtain w₃ : InRegions s.wr (W + BitVec.ofNat 64 288) 8 := in_off hw (by decide) (by decide)
  obtain ne : (W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112) = False := by
    simp only [eq_iff_iff, iff_false]
    intro h
    have := congrArg (· - W) h
    simp only [Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  simp only [tlO] at r₀ htl
  refine ⟨_, by orun [h19, r₀, htl, r₁, w₁, r₂, w₂, w₃, write1, read_one, WriteBytes.writeW8_apply, ne], ?_,
    fun r a b c => ?_, ?_, ?_, ?_⟩
  · simp only [and15, toNat_ofNat_of_lt ht, lsl4_ofNat, or_byte, and_byte, and63]
  · simp [gpr_write, a, b, c]
  all_goals rfl

theorem nonceBlock_ok {T : Nat} {K W : Addr} (L : Lay T K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr)
    {N : Addr} {nl t : Nat} (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB : Buf T W s N nl) :
    WP isa nonceBlock s (NoncePost W t (bytesAt s.mem N nl) s) := by
  obtain hT := L.hT
  obtain ⟨s₁, run₁, x12₁, x13₁, g₁, f₁, z₁, sp₁, rd₁, wr₁⟩ := nonceHead_ok h19 hw hN hnl
  obtain h19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide) (by decide) (by decide), h19]
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ :=
    nonceOne_ok h19₁ (by rw [wr₁]; exact hw) h1 h15 x12₁ x13₁
  obtain hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, rd₁, wr₁]; exact hB.rd
  obtain hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂, wr₁]; exact Proof.AesGcm.AArch64.covers_off hw (by omega_arith) (by decide)
  obtain hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega_arith))
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [show W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) by
      rw [Offset.add_add]; congr 2; omega_arith]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by have := ocbOffs; omega))) (by omega_arith),
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by have := ocbOffs; omega))) (by omega_arith)]
  unfold nonceBlock
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.seq (WP.mono (copyLoop_ok s₂ x12₂ x11₂ x13₂ (by omega_arith) ⟨by omega_arith, hS₂, hD₂, hSD⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, _, _, g₃, sp₃, rd₃, wr₃⟩ := h₃
  rw [eN] at m₃
  obtain h19₃ : s₃.gpr .x19 = W := by
    rw [g₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide), h19₁]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  obtain fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact contains_pre _ (by omega_arith))
  obtain htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t := by
    obtain k : ∀ {rs : List Region} {m m' : Mem}, Frame rs m m' →
        (∀ r ∈ rs, (⟨W + BitVec.ofNat 64 tlO, 8⟩ : Region).Disjoint r) →
        m'.readW (W + BitVec.ofNat 64 tlO) 64 = m.readW (W + BitVec.ofNat 64 tlO) 64 :=
      fun h hd => h.readW (r := ⟨W + BitVec.ofNat 64 tlO, 8⟩) (Region.contains_self _ _) hd (by decide)
    rw [k fr₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by simp only [tlO]; omega_arith)) (by have := ocbOffs; omega)
          (by omega_arith)),
      k f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)),
      k f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)), htl]
  obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := nonceTail_ok h19₃ (by rw [wr₃']; exact hw) ht htl₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  -- the bytes at `W + tmpO`, step by step
  obtain hlen : (bytesAt s.mem N nl).length = nl := length_bytesAt _ _ _
  obtain L₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := bytesAt_of_zero z₁
  obtain e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega_arith]
  obtain e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega_arith]
  obtain L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - nl) ++ [1] ++ Spec.Ocb.zeros (nl) := by
    rw [m₂, e127, bytesAt_writeW8_at _ _ _ (by omega_arith) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - nl) 16 = 15 - nl by omega_arith,
      show 16 - (15 - nl + 1) = nl by omega_arith]
  obtain L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega_arith) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega_arith]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_append, List.length_singleton, List.append_assoc]
    simp only [show min (16 - nl) (15 - nl) = 15 - nl by omega_arith, show 16 - nl - (15 - nl) = 1 by omega_arith,
      show 16 - (15 - nl) = nl + 1 by omega_arith, show 15 - nl + (1 + nl) = 16 by omega_arith]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - nl - 16 = 0 by omega_arith, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ nl + 1 by simp), show nl - (nl + 1 - 1) = 0 by omega_arith,
      List.append_nil]
  obtain L₃d : ∀ k < 16, (bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega_arith) (by rw [hlen]; omega_arith) hk
      rw [hlen] at this; rw [L₃]; exact this
  obtain b0 : s₃.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  obtain e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add W 112 15).symm
  obtain b15 : s₃.mem (W + BitVec.ofNat 64 127) = nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  obtain fr288 : ∀ (M : Mem) (v : BitVec 64), Frame [⟨W + BitVec.ofNat 64 288, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 288) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₄, b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr288 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 288) (k := 8) (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega))
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
  obtain hlen16 := length_bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16
  obtain f₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
    ((f₁.trans f₂).mono (fun r hr => by simp at hr; simp [hr])).trans ((fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact Offset.sub_base _ (by omega_arith)⟩))
  refine ⟨?_, ?_, ?_, fun r hr => ?_, by rw [sp₄, sp₃, sp₂, sp₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃']⟩
  · rw [m₄]
    refine ((f₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · show blockAtMem s₄.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega_arith) (by omega_arith) hk]
  · show s₄.mem.readW (W + BitVec.ofNat 64 288) 64 = _
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15, Proof.Ocb.nonceN_bottom _ _ (by omega_arith) (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ r hr.1 hr.2.1 hr.2.2.1, g₃ r (by simp [Proof.AesGcm.AArch64.loopRegs, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]), g₂ r hr.1 hr.2.2.1 hr.2.2.2.2.2.1, g₁ r hr.1 hr.2.2.2.1 hr.2.2.2.2.1]

end VG.Proof.AesOcb.AArch64

end

end

/-! ### `AesOcb.AArch64.Nonce`, which the modules that import this one used -/

section

/-! ### `AesOcb.AArch64.Offset0`, which only this module used -/

section

/-!
# AES-OCB on AArch64: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` loads `Ktop` as
two byte-reversed words, computes the third word of `Stretch`
(`Proof.Ocb.stretch_words`), shifts the three words left by `bottom` in six
masked stages (`stage_ok`, `Proof.Ocb.shl_stages`), and stores the top two,
byte-reversed, to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf sel_mask shl3 toNat_ofNat_of_lt)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_v {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 64 v >>> k) &&& 1#64 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv]),
    show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  obtain h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega_using [h]

theorem sel_mask0 (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& (0#64 - (if b = true then 1 else 0))) = if b then x' else x := sel_mask x x' b

/-- One stage: the three words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok (s : State) {k a v : Nat} (hk6 : k < 64) (ha : 0 < a) (ha' : a < 64) (hv : v < 64)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧
      s'.gpr .x9 ++ s'.gpr .x10 ++ s'.gpr .x11 = shlIf (v.testBit k) a (s.gpr .x9 ++ s.gpr .x10 ++ s.gpr .x11) ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x13, .x14, .x15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain c1 : 64 - a < 64 := by omega_using [ha]
  refine ⟨_, by orun [stage, h12, hk6, ha', c1, List.flatMap_cons, List.flatMap_nil], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, h12, bit_v hv, BitVec.setWidth_eq]
    rw [sel_mask0, sel_mask0, sel_mask0]
    unfold shlIf
    split
    · exact shl3 _ _ _ ha ha'
    · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
  all_goals rfl

/-- The top two of three words. -/
theorem top2 (x y z : BitVec 64) : (x ++ y ++ z).extractLsb' 64 128 = x ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega_using [], ↓reduceIte, show 64 + i - 64 = i by omega_using []]

/-- `Stretch`. -/
def stretch (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- What `offset0` leaves. -/
structure Off0Post (W : Addr) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 o0O, 16⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem offset0_ok {T : Nat} {K W : Addr} (L : Lay T K W) {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr)
    {v : Nat} (hv : v < 64) (hbot : s.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      Off0Post W ((stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  obtain hT := L.hT
  obtain rr : ∀ {d : Nat}, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 :=
    fun h => in_left (in_off hw h (by decide))
  simp only [botO] at hbot
  obtain ⟨s₁, run₁, w₁, x12₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .x9 .x19 tmpO, .rev .x9 .x9, ld .x10 .x19 (tmpO + 8), .rev .x10 .x10,
       .lsl .x .x11 .x9 8, .lsr .x .x13 .x10 56, .logic .orr .x .x11 .x11 .x13,
       .logic .eor .x .x11 .x11 .x9, ld .x12 .x19 botO] s = some s₁ ∧
      s₁.gpr .x9 ++ s₁.gpr .x10 ++ s₁.gpr .x11 = stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) ∧
      s₁.gpr .x12 = BitVec.ofNat 64 v ∧
      (∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13] → s₁.gpr r = s.gpr r) ∧
      s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    obtain r₀ := rr (d := 112) (by decide)
    obtain r₁ := rr (d := 120) (by decide)
    obtain r₂ := rr (d := 288) (by decide)
    refine ⟨_, by orun [h19, r₀, r₁, r₂], ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
      obtain hb : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) =
          rev64 (s.mem.readW (W + BitVec.ofNat 64 112) 64) ++ rev64 (s.mem.readW (W + BitVec.ofNat 64 120) 64) := by
        have := Proof.Gcm.AArch64.blockAt_rev s.mem (W + BitVec.ofNat 64 112)
        rw [BitVec.add_zero, Offset.add_add] at this
        exact this.symm
      rw [stretch, hb, Proof.Ocb.stretch_words]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, hbot]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]
    all_goals rfl
  -- the six stages
  obtain keep : ∀ {t t' : State}, (∀ r, r ∉ [.x9, .x10, .x11, .x13, .x14, .x15] → t'.gpr r = t.gpr r) →
      t.gpr .x12 = BitVec.ofNat 64 v → t'.gpr .x12 = BitVec.ofNat 64 v := fun g h => by rw [g _ (by decide), h]
  obtain ⟨s₂, run₂, w₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := stage_ok s₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv x12₁
  obtain ⟨s₃, run₃, w₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := stage_ok s₂ (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (keep g₂ x12₁)
  obtain ⟨s₄, run₄, w₄, g₄, m₄, sp₄, rd₄, wr₄⟩ := stage_ok s₃ (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (keep g₃ (keep g₂ x12₁))
  obtain ⟨s₅, run₅, w₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := stage_ok s₄ (k := 3) (a := 8) (by decide) (by decide) (by decide) hv
    (keep g₄ (keep g₃ (keep g₂ x12₁)))
  obtain ⟨s₆, run₆, w₆, g₆, m₆, sp₆, rd₆, wr₆⟩ := stage_ok s₅ (k := 4) (a := 16) (by decide) (by decide) (by decide) hv
    (keep g₅ (keep g₄ (keep g₃ (keep g₂ x12₁))))
  obtain ⟨s₇, run₇, w₇, g₇, m₇, sp₇, rd₇, wr₇⟩ := stage_ok s₆ (k := 5) (a := 32) (by decide) (by decide) (by decide) hv
    (keep g₆ (keep g₅ (keep g₄ (keep g₃ (keep g₂ x12₁)))))
  obtain hw7 : s₇.gpr .x9 ++ s₇.gpr .x10 ++ s₇.gpr .x11 =
      stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [w₇, w₆, w₅, w₄, w₃, w₂, w₁, Proof.Ocb.shl_stages _ hv]
  obtain hO : s₇.gpr .x9 ++ s₇.gpr .x10 =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [← top2 _ _ (s₇.gpr .x11), hw7, Proof.Ocb.offset_shl _ (by omega_using [hv])]
  obtain hm₇ : s₇.mem = s.mem := by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁]
  obtain hsp₇ : s₇.sp = s.sp := by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]
  obtain hrd₇ : s₇.rd = s.rd := by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
  obtain hwr₇ : s₇.wr = s.wr := by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
  obtain g₁₇ : ∀ r, r ∉ [.x9, .x10, .x11, .x12, .x13, .x14, .x15] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain h' : r ∉ [Reg.x9, .x10, .x11, .x13, .x14, .x15] := by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]
    rw [g₇ r h', g₆ r h', g₅ r h', g₄ r h', g₃ r h', g₂ r h',
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]
  obtain h19₇ : s₇.gpr .x19 = W := by rw [g₁₇ _ (by decide), h19]
  obtain ww : ∀ {d : Nat}, d + 8 ≤ 512 → InRegions s₇.wr (W + BitVec.ofNat 64 d) 8 :=
    fun h => by rw [hwr₇]; exact in_off hw h (by decide)
  obtain ⟨s₈, run₈, m₈, g₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.rev .x9 .x9, .rev .x10 .x10, st .x19 ofsO .x9,
      st .x19 (ofsO + 8) .x10, st .x19 o0O .x9, st .x19 (o0O + 8) .x10] s₇ = some s₈ ∧
      s₈.mem = (((s₇.mem.writeW (W + BitVec.ofNat 64 16) (rev64 (s₇.gpr .x9))).writeW (W + BitVec.ofNat 64 24)
        (rev64 (s₇.gpr .x10))).writeW (W + BitVec.ofNat 64 304) (rev64 (s₇.gpr .x9))).writeW
        (W + BitVec.ofNat 64 312) (rev64 (s₇.gpr .x10)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s₈.gpr r = s₇.gpr r) ∧ s₈.sp = s₇.sp ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    obtain w₁₆ := ww (d := 16) (by decide)
    obtain w₂₄ := ww (d := 24) (by decide)
    obtain w₃₀₄ := ww (d := 304) (by decide)
    obtain w₃₁₂ := ww (d := 312) (by decide)
    refine ⟨_, by orun [h19₇, w₁₆, w₂₄, w₃₀₄, w₃₁₂], ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    · simp [gpr_write, h1, h2]
    all_goals rfl
  obtain val : Spec.Ocb.ofBytes (Proof.Cmac.le8 (rev64 (s₇.gpr .x9)) ++ Proof.Cmac.le8 (rev64 (s₇.gpr .x10))) =
      (stretch (blockAtMem s.mem (W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [Proof.CmacAes.AArch64.le8_rev, ← Proof.Ocb.toBytes_eq, Proof.Ocb.ofBytes_toBytes, hO]
  obtain run : runBlock isa offset0 s = some s₈ := by
    unfold offset0
    rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇, Option.bind_some, run₈]
  obtain f304 : ∀ M : Mem, Frame [⟨W + BitVec.ofNat 64 304, 16⟩] M
      ((M.writeW (W + BitVec.ofNat 64 304) (rev64 (s₇.gpr .x9))).writeW (W + BitVec.ofNat 64 312)
        (rev64 (s₇.gpr .x10))) := fun M => by
    rw [← addr8 W 304]; exact Proof.Cmac.frame_store2 _ _ _
  refine ⟨s₈, run, ?_, ?_, ?_, fun r hr => ?_, by rw [sp₈, hsp₇], by rw [rd₈, hrd₇], by rw [wr₈, hwr₇]⟩
  · rw [m₈, ← hm₇]
    show Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 304, 16⟩] _ _
    exact ((((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains W (e := 16) (k := 16) (d := 24) (n := 8) (by decide) (by decide)
        (by decide))).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (contains_pre _ (by decide))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains W (e := 304) (k := 16) (d := 312) (n := 8) (by decide) (by decide) (by decide))
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 16) = _
    rw [m₈, Proof.Ocb.blockAtMem_frame (f304 _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (a := 16) (n := 16) (d := 304) (k := 16) (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega))]
    rw [show W + BitVec.ofNat 64 24 = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 from (addr8 W 16).symm,
      blockAtMem_store2, val]
  · show blockAtMem s₈.mem (W + BitVec.ofNat 64 304) = _
    rw [m₈, show W + BitVec.ofNat 64 312 = W + BitVec.ofNat 64 304 + BitVec.ofNat 64 8 from (addr8 W 304).symm,
      blockAtMem_store2, val]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈ r hr.1 hr.2.1, g₁₇ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2])]

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxInv ctxLstar)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.Ocb (blockAtMem_frame)

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {T : Nat} {K W D : Addr} {n : Nat} (L : Lay T K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR T W D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [Proof.Cmac.bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hR])]

theorem ctxLstar_mut {T : Nat} {K W D : Addr} {n : Nat} (L : Lay T K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR T W D n) m m') : ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => (k_mut L hD r hr).sub_left (Lay.kSub (by decide))

/-- What `nonce` writes: `[16, 160)` and `[288, T)` of `W`. -/
abbrev nonceR (T : Nat) (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 16, 144⟩, wB T W]

theorem nonceR_mut {T : Nat} {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (nonceR T W) m m') :
    Frame (mutR T W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact in_mutA (by decide)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `nonce` leaves. -/
structure NonceOk (T : Nat) (K W D : Addr) (R n : Nat) (SP : Addr) (o : Block) (s s' : State) : Prop where
  env : Env T K W D R n SP s'
  frame : Frame (nonceR T W) s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  keep : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
    blockAtMem s'.mem (W + BitVec.ofNat 64 d) = blockAtMem s.mem (W + BitVec.ofNat 64 d)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {T : Nat} {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay T K W) {s : State}
    (E : Env T K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {N : Addr} {nl t : Nat}
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15)
    (ht : t < 2 ^ 64) (hB : Buf T W s N nl) (hKD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (hv : v.scratch ≤ T - 512 := by assumption) :
    WP isa (nonce (callees v)) s
      (NonceOk T K W D R n SP (Spec.Ocb.offset0 (ctxCiph s.mem K R) t (bytesAt s.mem N nl)) s) := by
  obtain hT := L.hT
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E.x19 (E.perm.w5 L) hN hnl htl h1 h15 ht hB) fun s₁ P₁ => ?_)
  obtain E₁ : Env T K W D R n SP s₁ := E.others P₁.gpr P₁.sp P₁.rd P₁.wr
  obtain F₁ : Frame (nonceR T W) s.mem s₁.mem := P₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by have := ocbOffs; omega)⟩
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOkW v.encNoFrames hv L E₁ hR
    (oneBlock_ok E₁.x19 tmpO (by decide)) (dstW L E₁.perm (d := tmpO) (n := 1) (by decide))) fun s₂ P₂ => ?_)
  obtain E₂ : Env T K W D R n SP s₂ := E₁.of_saved P₂.saved P₂.sp P₂.rd P₂.wr
  obtain F₂ : Frame (nonceR T W) s₁.mem s₂.mem := P₂.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by have := ocbOffs; omega)⟩
  obtain ktop : blockAtMem s₂.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem K R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [P₂.enc0, P₁.blk]
    exact congrFun (ctxCiph_mut L hKD (nonceR_mut F₁) hR) _
  obtain hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  obtain bot₂ : s₂.mem.readW (W + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨W + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)
      · exact L.w_w (.inl (by decide)) (by have := ocbOffs; omega) (by have := ocbOffs; omega)) (by decide), P₁.bot]
  obtain ⟨s₃, run₃, P₃⟩ := offset0_ok L E₂.x19 (E₂.perm.w5 L) hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨E₂.others P₃.gpr P₃.sp P₃.rd P₃.wr,
    F₁.trans (F₂.trans (P₃.frame.sub fun r hr => ?_)), ?_, ?_, fun {d} h₁ h₂ => ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by have := ocbOffs; omega)⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [blockAtMem_frame P₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [ofsO, o0O]; omega_arith) (by omega) (by have := ocbOffs; omega)),
      blockAtMem_frame P₂.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (by simp only [tmpO]; omega_using [h₂]) (by omega) (by have := ocbOffs; omega)
        · exact L.w_w (by omega) (by omega) (by have := ocbOffs; omega)),
      blockAtMem_frame P₁.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact L.w_w (by simp only [tmpO, botO]; omega_using [h₂]) (by omega) (by have := ocbOffs; omega))]

end VG.Proof.AesOcb.AArch64

end

end

/-!
# AES-OCB on AArch64: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `x25`), shifted right
once more each time (in `x11`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `x11` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt)

theorem and1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v &&& 1#64 = BitVec.ofNat 64 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_of_lt hv, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_ofNat_of_lt (by omega_using [])]

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_of_lt hv, toNat_ofNat_of_lt (by omega_using [hv]), Nat.shiftRight_eq_div_pow]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ∉ ntzRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `x12 ← x14 ∧ 1`, after `x14 ← v`. -/
theorem low1_ok (s : State) {v : Nat} (hv : v < 2 ^ 64) (h14 : s.gpr .x14 = BitVec.ofNat 64 v) :
    ∃ s', runBlock isa low1 s = some s' ∧ s'.gpr .x12 = BitVec.ofNat 64 (v % 2) ∧ s'.gpr .x14 = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [low1], ?_, ?_, fun r h1 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h14, and1 hv]
  · simp [gpr_write, h14]
  · simp [gpr_write, h1]
  all_goals rfl

/-- Continue the public-index doubling loop from any already computed L_a. -/
theorem lNtzLoop_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 512⟩] s.wr) {l : Block} {i a : Nat} (hi' : i < 2^64)
    (hpos : 0 < i / 2^a) (he : i / 2^a % 2 = 0) (hntz : ntz i = a + ntz (i / 2^a))
    (h14 : s.gpr .x14 = BitVec.ofNat 64 (i / 2^a))
    (hl : blockAtMem s.mem (W + BitVec.ofNat 64 lO) = lAt l a) :
    WP isa (.loop (.block (dbl .x19 lO lO ++ ([.lsr .x .x14 .x14 1] : List Instr) ++ low1)) (.zero .x .x12)) s
      (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ∉ ntzRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (i / 2 ^ a) _
    ⟨a, rfl, hpos, he, hntz, h14, Frame.refl _ _, hl, fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, x14, fr, v, g, sp, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h19t : t.gpr .x19 = W := by rw [g _ (by decide), h19]
  obtain ⟨t₁, runt₁, D₁⟩ := dbl_ok (s := t) (b := .x19) (a := lO) (d := lO) (by decide) (by decide) h19t h19t
    (by decide) (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (by rw [wr]; exact wW (by decide)) (by rw [wr]; exact wW (by decide))
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  obtain ⟨t₂, runt₂, x14₂', g₂', m₂', sp₂'', rd₂'', wr₂''⟩ : ∃ t₂, runBlock isa [.lsr .x .x14 .x14 1] t₁ = some t₂ ∧
      t₂.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) ∧ (∀ r, r ≠ .x14 → t₂.gpr r = t₁.gpr r) ∧ t₂.mem = t₁.mem ∧
      t₂.sp = t₁.sp ∧ t₂.rd = t₁.rd ∧ t₂.wr = t₁.wr := by
    have x14₁ : t₁.gpr .x14 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), x14]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, x14₁, shr1 hv, e]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨t₃, runt₃, x12₃, x14₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := low1_ok t₂ (by omega_using [hv, e]) x14₂'
  refine WP.of_runBlock ⟨t₃, by rw [runBlock_append, runBlock_append, runt₁, Option.bind_some, runt₂,
    Option.bind_some, runt₃], ?_⟩
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [m₃, m₂']
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by rw [m₃, m₂', D₁.val, v]; rfl
  have g' : ∀ r, r ∉ ntzRegs → t₃.gpr r = s.gpr r := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃ r hr.2.2.2.1, g₂' r hr.2.2.2.2.2, D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [sp₃, sp₂'', D₁.sp, sp]
  have rd' : t₃.rd = s.rd := by rw [rd₃, rd₂'', D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [wr₃, wr₂'', D₁.wr, wr]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega_using []
  have hv' : i / 2 ^ (j + 1) < 2 ^ 64 := by omega_using [hv, e]
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_zero x12₃ (by omega_using [])).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega_using [hpos], j + 1, rfl,
      by rw [e]; omega_using [hpos, hev], hodd, hntz', x14₃, fr', v', g', sp', rd', wr'⟩
  · left
    refine ⟨(eval_zero x12₃ (by omega_using [])).trans (by simp [hodd]), ⟨fr', ?_, g', sp', rd', wr'⟩⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega_using [hodd])]


theorem lNtz_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 512⟩] s.wr) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 64) (h25 : s.gpr .x25 = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨s₁, run₁, B₁⟩ := copy16_ok (s := s) (a := l0O) (d := lO) (by decide) (by decide) h19
    (Proof.AesGcm.AArch64.in_left (wW (by decide))) (Proof.AesGcm.AArch64.in_left (wW (by decide)))
    (wW (by decide)) (wW (by decide))
  obtain ⟨s₁', run₁', x14₁', g₁', m₁', sp₁', rd₁', wr₁'⟩ : ∃ s', runBlock isa [Impl.AesGcm.AArch64.mov .x14 .x25] s₁ =
      some s' ∧ s'.gpr .x14 = BitVec.ofNat 64 i ∧ (∀ r, r ≠ .x14 → s'.gpr r = s₁.gpr r) ∧ s'.mem = s₁.mem ∧
      s'.sp = s₁.sp ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
    have h25₁ : s₁.gpr .x25 = BitVec.ofNat 64 i := by rw [B₁.gpr _ (by decide), h25]
    refine ⟨_, by orun [], ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h25₁]
    · simp [gpr_write, h]
    all_goals rfl
  obtain ⟨s₂, run₂, x12₂, x14₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := low1_ok s₁' hi' x14₁'
  have post_of : ∀ t : State, Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem →
      blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i) →
      (∀ r, r ∉ ntzRegs → t.gpr r = s₂.gpr r) → t.sp = s.sp →
      t.rd = s.rd → t.wr = s.wr → LNtzPost W l i s t := fun t fr v g sp rd wr =>
    ⟨fr, v, fun r hr => by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]),
        g₂ r hr.2.2.2.1, g₁' r hr.2.2.2.2.2, B₁.gpr r (by simp [hr.1, hr.2.1])], sp, rd, wr⟩
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [m₂, m₁']; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [m₂, m₁', B₁.val, hl0]
  have sp₂' : s₂.sp = s.sp := by rw [sp₂, sp₁', B₁.sp]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁', B₁.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁', B₁.wr]
  have h19₂ : s₂.gpr .x19 = W := by rw [g₂ _ (by decide), g₁' _ (by decide), B₁.gpr _ (by decide), h19]
  unfold lNtz
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, runBlock_append, run₁, Option.bind_some, run₁',
    Option.bind_some, run₂], ?_⟩)
  refine WP.ite (decide (i % 2 = 0)) (eval_zero x12₂ (by omega_using [])) (fun hb => ?_)
    (fun hb => WP.block_nil (post_of s₂ fr₂ ?_ (fun _ _ => rfl) sp₂' rd₂' wr₂'))
  rotate_left
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega_using [hb])]
  have he : i % 2 = 0 := of_decide_eq_true hb
  exact WP.mono (lNtzLoop_ok h19₂ (by rw [wr₂']; exact hw) hi' (a := 0)
    (by simpa using hi) (by simpa using he) (by simp) (by simpa using x14₂) v₂) fun t P =>
      post_of t (fr₂.trans P.frame) P.val P.gpr (P.sp.trans sp₂') (P.rd.trans rd₂') (P.wr.trans wr₂')

end VG.Proof.AesOcb.AArch64
