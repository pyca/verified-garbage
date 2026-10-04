import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32

/-!
# Interleaved counter mode and GHASH: the setting

The interleaved loops (`Impl.Gcm.X86_64.Stitch`) start from a state `s₀`
whose registers hold the key context (`rdi`), the number of rounds (`rsi`),
the counter (`rdx`), `Y` (`rcx`), the data (`r8`), the number of blocks
(`r9`, a multiple of 16) and the working space (`r11`). `SPre s₀` is what
they need of it: the regions they read and write are accessible, disjoint
where one is written, and do not wrap around.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom)

/-! ## Accesses within the regions -/

theorem ofNat_toNat_le (off : Nat) : (BitVec.ofNat 64 off).toNat ≤ off := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _

/-- `n` bytes at `off` from the start of an accessible run of `L ≥ off + n`
bytes are accessible. -/
theorem in_sub {rs : List Region} {b : Addr} {L off n : Nat} (h : InRegions rs b L)
    (ho : off + n ≤ L) : InRegions rs (b + BitVec.ofNat 64 off) n := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  unfold Region.Contains at *
  have e : b + BitVec.ofNat 64 off - r.base = (b - r.base) + BitVec.ofNat 64 off := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 off),
      ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add]
  have := Nat.mod_le ((b - r.base).toNat + (BitVec.ofNat 64 off).toNat) (2 ^ 64)
  have := ofNat_toNat_le off
  omega

theorem in_sub_int {rs : List Region} {b : Addr} {L off n : Nat} (h : InRegions rs b L)
    (ho : off + n ≤ L) : InRegions rs (b + BitVec.ofInt 64 (off : Int)) n := by
  rw [show BitVec.ofInt 64 (off : Int) = BitVec.ofNat 64 off from BitVec.ofInt_natCast ..]
  exact in_sub h ho

theorem in_rdwr {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs' a n) :
    InRegions (rs ++ rs') a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## What both loops' proofs share -/

open VG.Spec.Gcm (mul blocksAt)

theorem ghash_append16 (h y : Block) (f : Nat → Block) (g : Nat) :
    ghashFrom h y ((List.range (16 * (g + 1))).map f) =
      ghashFrom h (ghashFrom h y ((List.range (16 * g)).map f)) ((List.range 16).map fun i => f (16 * g + i)) := by
  rw [show 16 * (g + 1) = 16 * g + 16 by omega, List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

theorem ghash16 (h y : Block) (X : Nat → Block) :
    ghashFrom h y ((List.range 16).map X) = mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((y ^^^ X 0)) h ^^^ X 1) h ^^^ X 2) h ^^^ X 3) h ^^^ X 4) h ^^^ X 5) h ^^^ X 6) h ^^^ X 7) h ^^^ X 8) h ^^^ X 9) h ^^^ X 10) h ^^^ X 11) h ^^^ X 12) h ^^^ X 13) h ^^^ X 14) h ^^^ X 15) h := by
  simp only [ghashFrom, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The end of a body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 32`. -/
theorem nextE_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 32)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, e32,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The end of a decryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 16`. -/
theorem nextD_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 16)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- A block disjoint from a region written is kept. -/
theorem blockAt_writeW_sep' {m : Mem} {p : Addr} {R : Region} {w : Nat} {v : BitVec w}
    (hd : Region.Disjoint ⟨p, 16⟩ R) (hw : w / 8 = R.len) : blockAt (m.writeW R.base v) p = blockAt m p := by
  rw [VG.Proof.Gcm.X86_64.blockAt_eq, VG.Proof.Gcm.X86_64.blockAt_eq,
    Mem.readW_writeW_sep (hd.sep (Region.contains_self _ _) (by rw [hw]; exact Region.contains_self _ _)) (by decide)]

/-- `vpshufb x, x', ymm0` and a 16-byte store of `x` to `[b]`. -/
theorem store16_ok (x x' : XReg) (b : Reg) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions s.wr (s.gpr b) 16) :
    WP isa (.block [.vop (.vbin .vpshufb .l128 x x' .xmm0), .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ b 0) x])
      s fun s' => s'.mem = s.mem.writeW (s.gpr b) (XBinOp.eval .pshufb (s.lane x' 0) revMask) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ x → ∀ l < 2, s'.lane r l = s.lane r l) := by
  have hin' : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  simp only [State.lane] at h0
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.setV, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, VBinOp.sse, State.lane, ite_true, hin', h0, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp, rfl, rfl, rfl, fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hr]

/-- The blocks of the data, after all of them are encrypted. -/
theorem blocks_ctr32 {s₀ : State} {m : Mem} (hb : ∀ k < nb s₀, blockAt m (bAddr s₀ k) = ctb s₀ k) :
    blocksAt m (dp s₀) (nb s₀) = Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (dp s₀) (nb s₀)) := by
  apply List.ext_getElem
  · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nb s₀ := by simpa [blocksAt] using h₁
    simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
      List.getElem_zipWith, List.length_map, List.length_range]
    exact hb k hk

end VG.Proof.Gcm.X86_64.Stitch
