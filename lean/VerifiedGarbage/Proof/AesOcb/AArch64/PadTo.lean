module

public import VerifiedGarbage.Impl.AesOcb.AArch64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesOcb.AArch64.Env
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.CmacAes.AArch64.Subkeys
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash

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
theorem padTo_ok {W : Addr} {s : State} (h19 : s.gpr .x19 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr}
    {n d : Nat} (hn : 0 < n) (hn' : n < 16) (hd : d % 8 = 0 ∧ d + 16 ≤ 2560) (h23 : s.gpr .x23 = S)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s fun t => Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem (W + BitVec.ofNat 64 d) = pad (bytesAt s.mem S n) ∧
      (∀ r, r ∉ padRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
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
