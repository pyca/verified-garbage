import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Exec

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec`. -/
section

/-!
# Interleaved counter mode and GHASH: what the loops need and do

Untrusted: everything here is checked by Lean. Interleaved loops (such as
`Impl.Gcm.X86_64.Stitch`) start from a state `s₀` whose registers hold the
key context (`rdi`), the number of rounds (`rsi`), the counter (`rdx`), `Y`
(`rcx`), the data (`r8`), the number of blocks (`r9`, a multiple of 16) and
the working space (`r11`). `SPre s₀` is what they need of it, and `EPost`,
`DPost` what they do (`StitchOk`). This module states them without the
algebra their proofs need (`Proof/Gcm/Poly.lean`), so that the functions
calling the loops are proven for any loops and proof of `StitchOk`, which
only the instances that use them import.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom)

section
variable (s₀ : State)

/-- The key context: the key schedule, and the hash subkey at `+ 240`. -/
abbrev kp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev cp : Addr := s₀.gpr .rdx
abbrev yp : Addr := s₀.gpr .rcx
abbrev dp : Addr := s₀.gpr .r8
abbrev nb : Nat := (s₀.gpr .r9).toNat
/-- The working space: the powers. -/
abbrev pp : Addr := s₀.gpr .r11
abbrev kR : Region := ⟨VG.Proof.Gcm.X86_64.Stitch.kp s₀, 256⟩
abbrev cR : Region := ⟨VG.Proof.Gcm.X86_64.Stitch.cp s₀, 16⟩
abbrev yR : Region := ⟨VG.Proof.Gcm.X86_64.Stitch.yp s₀, 16⟩
abbrev dR : Region := ⟨VG.Proof.Gcm.X86_64.Stitch.dp s₀, 16 * VG.Proof.Gcm.X86_64.Stitch.nb s₀⟩
abbrev pR : Region := ⟨VG.Proof.Gcm.X86_64.Stitch.pp s₀, 256⟩
/-- The key schedule, and `CIPH_K`. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.kp s₀) (16 * (VG.Proof.Gcm.X86_64.Stitch.nr s₀ + 1))
abbrev ciph : VG.Spec.Gcm.Block → VG.Spec.Gcm.Block := VG.Spec.Gcm.aesWith (VG.Proof.Gcm.X86_64.Stitch.nr s₀) (VG.Proof.Gcm.X86_64.Stitch.sch s₀)
abbrev cb : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.cp s₀)
/-- The hash subkey, and `Y`. -/
abbrev hk : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.kp s₀ + 240)
abbrev y₀ : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀)
/-- Block `k` of the data, where it starts, and encrypted. -/
abbrev bAddr (k : Nat) : Addr := VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev blk (k : Nat) : VG.Spec.Gcm.Block := VG.Spec.Gcm.blockAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k)
abbrev ctb (k : Nat) : VG.Spec.Gcm.Block := VG.Proof.Gcm.X86_64.Stitch.blk s₀ k ^^^ VG.Proof.Gcm.X86_64.Stitch.ciph s₀ (Nat.repeat inc32 k (VG.Proof.Gcm.X86_64.Stitch.cb s₀))

end

structure SPre (s₀ : State) : Prop where
  rounds : VG.Proof.Gcm.X86_64.Stitch.nr s₀ = 10 ∨ VG.Proof.Gcm.X86_64.Stitch.nr s₀ = 12 ∨ VG.Proof.Gcm.X86_64.Stitch.nr s₀ = 14
  nb16 : 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀
  nbm : VG.Proof.Gcm.X86_64.Stitch.nb s₀ % 16 = 0
  k_in : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Gcm.X86_64.Stitch.kp s₀) 256
  c_in : InRegions s₀.wr (VG.Proof.Gcm.X86_64.Stitch.cp s₀) 16
  y_in : InRegions s₀.wr (VG.Proof.Gcm.X86_64.Stitch.yp s₀) 16
  d_in : InRegions s₀.wr (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (16 * VG.Proof.Gcm.X86_64.Stitch.nb s₀)
  p_in : InRegions s₀.wr (VG.Proof.Gcm.X86_64.Stitch.pp s₀) 256
  d_k : (VG.Proof.Gcm.X86_64.Stitch.dR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.kR s₀)
  d_c : (VG.Proof.Gcm.X86_64.Stitch.dR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.cR s₀)
  d_y : (VG.Proof.Gcm.X86_64.Stitch.dR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.yR s₀)
  d_p : (VG.Proof.Gcm.X86_64.Stitch.dR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.pR s₀)
  p_k : (VG.Proof.Gcm.X86_64.Stitch.pR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.kR s₀)
  p_c : (VG.Proof.Gcm.X86_64.Stitch.pR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.cR s₀)
  p_y : (VG.Proof.Gcm.X86_64.Stitch.pR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.yR s₀)
  c_y : (VG.Proof.Gcm.X86_64.Stitch.cR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.yR s₀)
  c_k : (VG.Proof.Gcm.X86_64.Stitch.cR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.kR s₀)
  y_k : (VG.Proof.Gcm.X86_64.Stitch.yR s₀).Disjoint (VG.Proof.Gcm.X86_64.Stitch.kR s₀)
  wrap_d : (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * VG.Proof.Gcm.X86_64.Stitch.nb s₀ ≤ 2 ^ 64
  wrap_k : (VG.Proof.Gcm.X86_64.Stitch.kp s₀).toNat + 256 ≤ 2 ^ 64
  wrap_p : (VG.Proof.Gcm.X86_64.Stitch.pp s₀).toNat + 256 ≤ 2 ^ 64

/-- What the encryption leaves: the data encrypted, the counter advanced, `Y`
continued over the ciphertext, nothing else written but the working space. -/
structure EPost (s₀ s : State) : Prop where
  data : VG.Spec.Gcm.blocksAt s.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀) = Spec.Gcm.ctr32 (VG.Proof.Gcm.X86_64.Stitch.ciph s₀) (VG.Proof.Gcm.X86_64.Stitch.cb s₀) (VG.Spec.Gcm.blocksAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
  ctr : VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.cp s₀) = Nat.repeat inc32 (VG.Proof.Gcm.X86_64.Stitch.nb s₀) (VG.Proof.Gcm.X86_64.Stitch.cb s₀)
  y : VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) (VG.Proof.Gcm.X86_64.Stitch.y₀ s₀) (VG.Spec.Gcm.blocksAt s.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
  frame : Frame [VG.Proof.Gcm.X86_64.Stitch.cR s₀, VG.Proof.Gcm.X86_64.Stitch.yR s₀, VG.Proof.Gcm.X86_64.Stitch.dR s₀, VG.Proof.Gcm.X86_64.Stitch.pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the decryption leaves: the data decrypted, the counter advanced, `Y`
continued over the blocks as they were, nothing else written but the working
space. -/
structure DPost (s₀ s : State) : Prop where
  data : VG.Spec.Gcm.blocksAt s.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀) = Spec.Gcm.ctr32 (VG.Proof.Gcm.X86_64.Stitch.ciph s₀) (VG.Proof.Gcm.X86_64.Stitch.cb s₀) (VG.Spec.Gcm.blocksAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
  ctr : VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.cp s₀) = Nat.repeat inc32 (VG.Proof.Gcm.X86_64.Stitch.nb s₀) (VG.Proof.Gcm.X86_64.Stitch.cb s₀)
  y : VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) (VG.Proof.Gcm.X86_64.Stitch.y₀ s₀) (VG.Spec.Gcm.blocksAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
  frame : Frame [VG.Proof.Gcm.X86_64.Stitch.cR s₀, VG.Proof.Gcm.X86_64.Stitch.yR s₀, VG.Proof.Gcm.X86_64.Stitch.dR s₀, VG.Proof.Gcm.X86_64.Stitch.pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Interleaved loops `enc` and `dec` meet these contracts. -/
def StitchOk (enc dec : Prog isa) : Prop :=
  (∀ s₀, VG.Proof.Gcm.X86_64.Stitch.SPre s₀ → WP isa enc s₀ (VG.Proof.Gcm.X86_64.Stitch.EPost s₀)) ∧ (∀ s₀, VG.Proof.Gcm.X86_64.Stitch.SPre s₀ → WP isa dec s₀ (VG.Proof.Gcm.X86_64.Stitch.DPost s₀))

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base`. -/
section

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
  have := VG.Proof.Gcm.X86_64.Stitch.ofNat_toNat_le off
  omega

theorem in_sub_int {rs : List Region} {b : Addr} {L off n : Nat} (h : InRegions rs b L)
    (ho : off + n ≤ L) : InRegions rs (b + BitVec.ofInt 64 (off : Int)) n := by
  rw [show BitVec.ofInt 64 (off : Int) = BitVec.ofNat 64 off from BitVec.ofInt_natCast ..]
  exact VG.Proof.Gcm.X86_64.Stitch.in_sub h ho

theorem in_rdwr {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs' a n) :
    InRegions (rs ++ rs') a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## What both loops' proofs share -/

open VG.Spec.Gcm (mul blocksAt)

theorem ghash_append16 (h y : VG.Spec.Gcm.Block) (f : Nat → VG.Spec.Gcm.Block) (g : Nat) :
    ghashFrom h y ((List.range (16 * (g + 1))).map f) =
      ghashFrom h (ghashFrom h y ((List.range (16 * g)).map f)) ((List.range 16).map fun i => f (16 * g + i)) := by
  rw [show 16 * (g + 1) = 16 * g + 16 by omega, List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

theorem ghash16 (h y : VG.Spec.Gcm.Block) (X : Nat → VG.Spec.Gcm.Block) :
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
    (hd : Region.Disjoint ⟨p, 16⟩ R) (hw : w / 8 = R.len) : VG.Spec.Gcm.blockAt (m.writeW R.base v) p = VG.Spec.Gcm.blockAt m p := by
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
theorem blocks_ctr32 {s₀ : State} {m : Mem} (hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt m (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k) = VG.Proof.Gcm.X86_64.Stitch.ctb s₀ k) :
    VG.Spec.Gcm.blocksAt m (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀) = Spec.Gcm.ctr32 (VG.Proof.Gcm.X86_64.Stitch.ciph s₀) (VG.Proof.Gcm.X86_64.Stitch.cb s₀) (VG.Spec.Gcm.blocksAt s₀.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀)) := by
  apply List.ext_getElem
  · simp [VG.Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < VG.Proof.Gcm.X86_64.Stitch.nb s₀ := by simpa [VG.Spec.Gcm.blocksAt] using h₁
    simp only [VG.Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map, List.getElem_range,
      List.getElem_zipWith, List.length_map, List.length_range]
    exact hb k hk

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes`. -/
section

/-!
# Interleaved counter mode and GHASH: a batch of eight blocks

`batch_ok`: `batch j g` encrypts the eight data blocks at `rdx + 32 j` (blocks
`c … c + 7`, `AInv`): the counter blocks into `ymm3`–`ymm6` (`Vaes.ctrs_ok`),
AES of both lanes of each (`Vaes.aesG_ok`), and the XOR into the data
(`Vaes.xorData_ok`). The blocks `g i` between the rounds do what `Q` says,
which neither the counter blocks, the rounds nor the XOR (which writes only
those eight blocks) undo.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (ctrsK aesK xorDataK)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch)
open VG.Proof.Aes.X86_64.Vaes (ctrs_ok aesG_ok xorData_ok two YFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame st)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the counter pair, the mask, the increment,
the key schedule and its last round key, and the data (blocks below `c`
encrypted, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀
  ctr : ∀ l < 2, s.lane .xmm14 l = Nat.repeat inc32 (c + l) (VG.Proof.Gcm.X86_64.Stitch.cb s₀)
  msk : ∀ l < 2, s.lane .xmm0 l = revMask
  inc : ∀ l < 2, s.lane .xmm15 l = two
  rdi : s.gpr .rdi = VG.Proof.Gcm.X86_64.Stitch.kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = VG.Proof.Gcm.X86_64.Stitch.kp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Gcm.X86_64.Stitch.nr s₀)
  frame : Frame [VG.Proof.Gcm.X86_64.Stitch.dR s₀, VG.Proof.Gcm.X86_64.Stitch.pR s₀] s₀.mem s.mem
  blocks : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k) = if k < c then VG.Proof.Gcm.X86_64.Stitch.ctb s₀ k else VG.Proof.Gcm.X86_64.Stitch.blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.yframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ c s)
    (f : YFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.lane _ h14 l hl]; exact h.ctr l hl, fun l hl => by rw [f.lane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.lane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi, by rw [f.gpr]; exact h.rsi,
    by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame, fun k hk => by rw [f.mem]; exact h.blocks k hk,
    by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

/-- The key schedule is not in the data or the working space. -/
theorem sch_frame {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {m : Mem} (hf : Frame [VG.Proof.Gcm.X86_64.Stitch.dR s₀, VG.Proof.Gcm.X86_64.Stitch.pR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (VG.Proof.Gcm.X86_64.Stitch.kp s₀) (16 * (VG.Proof.Gcm.X86_64.Stitch.nr s₀ + 1)) = VG.Proof.Gcm.X86_64.Stitch.sch s₀ := by
  have hn : 16 * (VG.Proof.Gcm.X86_64.Stitch.nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega
  simp only [VG.Proof.Gcm.X86_64.Stitch.sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨VG.Proof.Gcm.X86_64.Stitch.kp s₀, 16 * (VG.Proof.Gcm.X86_64.Stitch.nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (VG.Proof.Gcm.X86_64.Stitch.nr s₀ + 1) ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)

theorem AInv.keys {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {c : Nat} {s : State} (hI : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ c s) :
    Keys (VG.Proof.Gcm.X86_64.Stitch.nr s₀) (VG.Proof.Gcm.X86_64.Stitch.sch s₀) s :=
  ⟨by rw [hI.rdi, VG.Proof.Gcm.X86_64.Stitch.sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact VG.Proof.Gcm.X86_64.Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

/-- Addresses at offsets of two bases, equal as numbers. -/
theorem addr_eq {a b : Addr} {x y : Nat} (h : a.toNat + x = b.toNat + y) :
    a + BitVec.ofNat 64 x = b + BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_mod_mod,
    Nat.add_mod_mod, h]

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem batch_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (VG.Proof.Gcm.X86_64.Stitch.nr s₀) (VG.Proof.Gcm.X86_64.Stitch.sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, s'.lane r l = s.lane r l) →
      Frame [⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 8 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 32 * j = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => VG.Proof.Gcm.X86_64.Stitch.AInv s₀ (c + 8) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      Frame [⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := VG.Proof.Gcm.X86_64.Stitch.aregs_ok
  have hw := hp.wrap_d
  refine WP.seq (WP.mono (ctrs_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (VG.Proof.Gcm.X86_64.Stitch.cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (VG.Proof.Gcm.X86_64.Stitch.nr s₀) (VG.Proof.Gcm.X86_64.Stitch.sch s₀) s₁ := YFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesG_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 2, XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask =
      VG.Proof.Gcm.X86_64.Stitch.ciph s₀ (Nat.repeat inc32 (c + 2 * k + l) (VG.Proof.Gcm.X86_64.Stitch.cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (32 * j + 16 * i) = VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (c + i) := fun i =>
    VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega)
  refine WP.mono (xorData_ok .xmm13 .rdx aregs j s₂ hnd h13 (fun k hk => by
      rw [hrdx₂, f₂.wr, f₁.wr, hI.wr, show BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int) =
        BitVec.ofNat 64 (32 * j + 16 * (2 * k)) by rw [BitVec.ofInt_natCast]; congr 1; omega, addr]
      exact VG.Proof.Gcm.X86_64.Stitch.in_sub hp.d_in (by simp [aregs] at hk; omega))
      (by rw [hrdx₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hrdx₂] at b₃ fr₃
  rw [show 32 * j = 32 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 2,
      VG.Spec.Gcm.blockAt s₃.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (c + (2 * k + l))) =
        VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (c + (2 * k + l))) ^^^ XBinOp.eval .pshufb (s₂.lane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [show 16 * (2 * (j + k) + l) = 32 * j + 16 * (2 * k + l) by omega, addr] at this
  have fr' : Frame [⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 2, s₃.lane r l = s.lane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.lane r (by simp [h13', hr, hg']) l hl, f₁.lane r (by simp [h14, hr]) l hl]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr, hI.rdi],
    by rw [g₃, f₂.gpr, f₁.gpr, hI.rsi], by rw [g₃, f₂.gpr, f₁.gpr, hI.r10], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    by rw [g₃, f₂.gpr, f₁.gpr], kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.lane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨VG.Proof.Gcm.X86_64.Stitch.dR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 8) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 8) → VG.Spec.Gcm.blockAt s₃.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k) = VG.Spec.Gcm.blockAt s.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k) :=
      fun hn => blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + 8 by omega, ite_true]
    · by_cases hhi : k < c + 8
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (2 * (i / 2) + i % 2) := ⟨k - c, by omega⟩
        have hj : i / 2 < aregs.length := by simp [aregs]; omega
        rw [hb3 (i / 2) hj (i % 2) (by omega), hI.blocks _ hk, ks (i / 2) hj (i % 2) (by omega),
          show c + 2 * (i / 2) + i % 2 = c + (2 * (i / 2) + i % 2) by omega]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Gh`. -/
section

/-!
# Interleaved counter mode and GHASH: the GHASH loads

`ghLoad_ok`: `ghLoad k` loads the `k`-th pair of powers from the working
space into `ymm12`, and then does what `vg_ghash_vpclmul`'s `k`-th load does
(`Vpclmul.load_ok`). The products after the loads of a body, in the order of
an encryption body (`ordE`: the product with `Y` last) or of a decryption
body (`ordD`), are `accN`. That, reduced, the two lanes' add up to `GHASH`
over the sixteen blocks for the powers the setup stores (`FinOk`) needs the
field: `Stitch/Ok.lean` proves it (`finE`, `finD`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Proof.Gcm.X86_64.Vpclmul (restV ldacc load_ok load256_lo load256_hi)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (ghLoad)
open VG.Spec.Gcm (Block blockAt)

theorem lane_ld12 {k : Nat} (hk : k < 8) :
    laneSseBlock (restV k .xmm12) = some (ldacc (decide (k = 0)) .xmm12) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The `k`-th pair of powers into `ymm12`, and blocks `2k` and `2k + 1` at
`rdx + 32 k` added to the lanes' products with them. -/
theorem ghLoad_ok {k : Nat} (hk : k < 8) (t : State) (h0 : ∀ l < 2, t.lane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (ghLoad k)) t fun t' =>
      (∀ l < 2, prod (t'.proj l) = (prod (t.proj l)).acc
        ((if k = 0 then t.lane .xmm2 l else 0) ^^^
          VG.Spec.Gcm.blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let a := t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := t.mem.readW a 256
  let t₁ := t.setV .l256 .xmm12 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [ghLoad, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load256, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hpin, ite_true,
    Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → ∀ l < 2, t₁.lane r l = t.lane r l := fun r hr l _ => by
    simp [t₁, State.lane_setV256, hr]
  have l12 : ∀ l < 2, t₁.lane .xmm12 l = t.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [t₁, State.lane_setV256, v, load256_lo]
    · simp [t₁, State.lane_setV256, v, load256_hi]
  refine WP.mono (load_ok (VG.Proof.Gcm.X86_64.Stitch.lane_ld12 hk) (by decide) t₁ (fun l hl => by rw [keep _ (by decide) l hl]; exact h0 l hl)
    (by simpa [t₁] using hin)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [p' l hl, l12 l hl, keep _ (by decide) l hl]
    have hp : prod (t₁.proj l) = prod (t.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    rw [hp]; rfl
  · refine ⟨f'.gpr, f'.mem, f'.rd, f'.wr, fun r hr l hl => ?_⟩
    rw [f'.lane r (fun h => hr (List.mem_cons_of_mem _ h)) l hl, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

/-! ## The products of a body -/

/-- The input of the `k`-th load in lane `l`: block `2k + l`, with `Y` (`yl l`)
added to block 0. -/
def inp (X : Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (k l : Nat) : VG.Spec.Gcm.Block := (if k = 0 then yl l else 0) ^^^ X (2 * k + l)

/-- The products of lane `l` after the first `n` loads, in the order `ord`. -/
def accN (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (l n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (VG.Proof.Gcm.X86_64.Stitch.inp X yl (ord i) l) (P (ord i) l)) Prod.zero

theorem accN_zero (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (l : Nat) :
    VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl l 0 = Prod.zero := rfl

theorem accN_succ (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (l n : Nat) :
    VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl l (n + 1) = (VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl l n).acc (VG.Proof.Gcm.X86_64.Stitch.inp X yl (ord n) l) (P (ord n) l) := by
  simp only [VG.Proof.Gcm.X86_64.Stitch.accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem zero_xor_b (a : VG.Spec.Gcm.Block) : (0 : VG.Spec.Gcm.Block) ^^^ a = a := by simp

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Group`. -/
section

/-!
# Interleaved counter mode and GHASH: hashing a group between the rounds

`GEnv`: what the GHASH loads of a group need: its blocks at `rdx` (those from
`lo` on, which the loads to come read), the powers in the working space, and
the mask. `ghStep` is one load (`ghLoad_ok`), `ghFin` the reduction of both
lanes and their sum into `Y`.

The GHASH work between the rounds of a batch is `gq ord base fin`: loads
`base … base + 3` of the order `ord` after rounds 1–4, and, if `fin`, the
reduction after round 5. `QG` is what holds before the blocks after round
`j`, and `gq_ok` is the obligation of `batch_ok` for it.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (reduce_lanes combine_ok)
open VG.Impl.Gcm.X86_64.Stitch (ghLoad aregs gq ordE ordD)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Spec.Gcm (Block blockAt ghashFrom)

structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = VG.Proof.Gcm.X86_64.Stitch.pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → VG.Spec.Gcm.blockAt s.mem (a + BitVec.ofNat 64 (16 * i)) = X i
  pv : ∀ k < 8, ∀ l < 2, s.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  ina : ∀ k < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32
  inp : ∀ k < 8, InRegions (s.rd ++ s.wr) (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32
  m0 : ∀ l < 2, s.lane .xmm0 l = revMask

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {s : State} (h : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s) (hl : lo ≤ lo') : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.yframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s) (f : YFrame rs s s') (h0 : .xmm0 ∉ rs) :
    VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk l hl => by rw [f.mem]; exact h.pv k hk l hl, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk, fun l hl => by rw [f.lane _ h0 l hl]; exact h.m0 l hl⟩

theorem off2 (a : Addr) (k l : Nat) :
    a + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (16 * (2 * k + l)) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 32 * k + 16 * l = 16 * (2 * k + l) by omega]

theorem offp (a : Addr) (k l : Nat) :
    a + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (32 * k + 16 * l) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- One GHASH load, the `n`-th of the order `ord`. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {yl : Nat → VG.Spec.Gcm.Block} {ord : Nat → Nat} {n : Nat} (hk : ord n < 8) (hlo : lo ≤ 2 * ord n) {s : State}
    (hE : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s) (hp : ∀ l < 2, prod (s.proj l) = VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl l n)
    (hy : ∀ l < 2, s.lane .xmm2 l = yl l) :
    WP isa (.block (ghLoad (ord n))) s fun s' => VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s' ∧
      (∀ l < 2, prod (s'.proj l) = VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl l (n + 1)) ∧ (∀ l < 2, s'.lane .xmm2 l = yl l) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghLoad_ok hk s hE.m0 (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.yframe f' (by decide), fun l hl => ?_, fun l hl => ?_, f'⟩
  · rw [p' l hl, hp l hl, VG.Proof.Gcm.X86_64.Stitch.accN_succ, hE.rdx, hE.r11, VG.Proof.Gcm.X86_64.Stitch.off2, VG.Proof.Gcm.X86_64.Stitch.offp, hE.xs _ (by omega) (by omega),
      hE.pv _ hk l hl, hy l hl]
    rfl
  · rw [f'.lane _ (by decide) l hl, hy l hl]

/-- The reduction of both lanes, and their sum into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block} {s : State}
    (hE : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Vpclmul.reduce .xmm7 ++ Impl.Gcm.X86_64.Vpclmul.combine)) s fun s' =>
      VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ lo a X P s' ∧ s'.lane .xmm2 0 = reduce (prod (s.proj 0)) ^^^ reduce (prod (s.proj 1)) ∧
      s'.lane .xmm2 1 = 0 ∧ YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (reduce_lanes s h1) fun s₁ ⟨r₁, f₁⟩ => WP.mono (combine_ok s₁) fun s' ⟨c', y', f'⟩ =>
    ⟨(hE.yframe f₁ (by decide)).yframe f' (by decide), by rw [c', r₁ 0 (by decide), r₁ 1 (by decide)], y',
      f₁.comp f'⟩

theorem ite_t {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : ite c a b = a := by
  simp [h]

theorem ite_f {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : ite c a b = b := by
  simp [h]

/-! ## The GHASH work of a batch -/

/-- `Y` after the sixteen blocks of a body. -/
abbrev yNew (ord : Nat → Nat) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) : VG.Spec.Gcm.Block :=
  reduce (VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl 0 8) ^^^ reduce (VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl 1 8)

/-- What the products of a body, in the order `ord`, add up to, for the
powers `P` (`P k l` in lane `l` of the `k`-th load): `GHASH` over its sixteen
blocks, from `Y` in lane 0 (`Stitch/Ok.lean` proves it of the powers the
setup stores). -/
def FinOk (ord : Nat → Nat) (H : VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) : Prop :=
  ∀ X yl, yl 1 = 0 → VG.Proof.Gcm.X86_64.Stitch.yNew ord X P yl = ghashFrom H (yl 0) ((List.range 16).map X)

/-- What holds before the blocks after round `j` of a batch. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block)
    (yl : Nat → VG.Spec.Gcm.Block) (ord : Nat → Nat) (base : Nat) (fin : Bool) (j : Nat) (s : State) : Prop :=
  VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ (lo j) a X P s ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
  (if fin ∧ 5 < j then s.lane .xmm2 0 = VG.Proof.Gcm.X86_64.Stitch.yNew ord X P yl ∧ s.lane .xmm2 1 = 0
   else (∀ l < 2, prod (s.proj l) = VG.Proof.Gcm.X86_64.Stitch.accN ord X P yl l (base + min (j - 1) 4)) ∧
     ∀ l < 2, s.lane .xmm2 l = yl l)

/-- The registers the GHASH work of a batch writes. -/
abbrev gRegs : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

theorem gRegs_ok : ∀ r ∈ VG.Proof.Gcm.X86_64.Stitch.gRegs, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem QG.yframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {yl : Nat → VG.Spec.Gcm.Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j : Nat} {s s' : State} {rs : List XReg}
    (h : VG.Proof.Gcm.X86_64.Stitch.QG s₀ lo a X P yl ord base fin j s) (f : YFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    VG.Proof.Gcm.X86_64.Stitch.QG s₀ lo a X P yl ord base fin j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r hr l hl => f.lane r (fun h => hrs r h hr) l hl
  have kp : ∀ l < 2, prod (s'.proj l) = prod (s.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.yframe f (fun h => hrs _ h (by decide)), fun l hl => by rw [k .xmm1 (by decide) l hl]; exact h1 l hl,
    ?_⟩
  split
  · rw [VG.Proof.Gcm.X86_64.Stitch.ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1, by rw [k .xmm2 (by decide) 1 (by decide)]; exact h2.2⟩
  · rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by assumption)] at h2
    exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl, fun l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 l hl⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {yl : Nat → VG.Spec.Gcm.Block} {ord : Nat → Nat} {base : Nat} {fin : Bool}
    (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → ord (base + j - 1) < 8 ∧ lo j ≤ 2 * ord (base + j - 1))
    (hfin : fin = true → base = 4) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (VG.Proof.Gcm.X86_64.Stitch.nr s₀) (VG.Proof.Gcm.X86_64.Stitch.sch s₀) s → VG.Proof.Gcm.X86_64.Stitch.QG s₀ lo a X P yl ord base fin j s →
      WP isa (.block (gq ord base fin j)) s fun s' =>
        VG.Proof.Gcm.X86_64.Stitch.QG s₀ lo a X P yl ord base fin (j + 1) s' ∧ YFrame VG.Proof.Gcm.X86_64.Stitch.gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    obtain ⟨hk, hlo⟩ := hrd j hj1 hl4
    rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by omega)] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega] at h2
    have hn : base + (j - 1) = base + j - 1 := by omega
    rw [hn] at h2
    refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghStep hk hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
        f'.mono (by decide)⟩
    rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by omega), show min (j + 1 - 1) 4 = j by omega, show base + j = base + j - 1 + 1 by omega]
    exact ⟨p', y'⟩
  · by_cases h5 : fin = true ∧ j = 5
    · -- The reduction.
      obtain ⟨hf, rfl⟩ := h5
      rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by omega)] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega, ite_false, hf, and_self, ite_true]
      have hb := hfin hf
      subst hb
      refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghFin hE h1) fun s' ⟨hE', y0, y1, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), fun l hl => by rw [f'.lane _ (by decide) l hl]; exact h1 l hl, ?_⟩,
          f'.mono (by decide)⟩
      rw [VG.Proof.Gcm.X86_64.Stitch.ite_t ⟨rfl, by omega⟩]
      refine ⟨by rw [y0, h2.1 0 (by decide), h2.1 1 (by decide)]; rfl, y1⟩
    · -- Nothing.
      have hg : gq ord base fin j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega, ite_false]
        rw [VG.Proof.Gcm.X86_64.Stitch.ite_f h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, YFrame.refl _ _⟩
      by_cases hf : fin = true ∧ 5 < j
      · rw [VG.Proof.Gcm.X86_64.Stitch.ite_t hf] at h2; rw [VG.Proof.Gcm.X86_64.Stitch.ite_t ⟨hf.1, by omega⟩]; exact h2
      · rw [VG.Proof.Gcm.X86_64.Stitch.ite_f hf] at h2
        by_cases hf' : fin = true ∧ 5 < j + 1
        · -- `j = 5` with `fin` is the reduction.
          have : ¬ 5 < j := fun h => hf ⟨hf'.1, h⟩
          exact absurd ⟨hf'.1, by omega⟩ h5
        · rw [VG.Proof.Gcm.X86_64.Stitch.ite_f hf', show min (j + 1 - 1) 4 = min (j - 1) 4 by omega]; exact h2

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Loop`. -/
section

/-!
# Interleaved counter mode and GHASH: the encryption loop

`EInv s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInv`), the
first `e - 1` hashed into `Y` (in `xmm2`), the powers `P` in the working
space; `rdx` points to group `e - 1`, the next to hash. `body_ok`: a body
encrypts group `e` (two batches, `batch_ok`) while it hashes group `e - 1`
between their rounds (`gq_ok`), which they do not write (`QG.data`). It is
proven for any powers whose products add up to `GHASH` (`FinOk`), without
the field, which only `Stitch/Ok.lean` imports.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch gA gB body gq ordE)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep)
open VG.Spec.Gcm (Block blockAt ghashFrom inc32)

/-! ## The GHASH state, kept by the data written -/

theorem QG.data {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block}
    {P : Nat → Nat → VG.Spec.Gcm.Block} {yl : Nat → VG.Spec.Gcm.Block} {ord : Nat → Nat} {base : Nat} {fin : Bool} {j c g : Nat}
    (hc : c + 8 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (hg : 16 * g + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 8))
    {t t' : State} (h : VG.Proof.Gcm.X86_64.Stitch.QG s₀ lo a X P yl ord base fin j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 2, t'.lane r l = t.lane r l)
    (hf : Frame [⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩] t.mem t'.mem) : VG.Proof.Gcm.X86_64.Stitch.QG s₀ lo a X P yl ord base fin j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  have kp : ∀ l < 2, prod (t'.proj l) = prod (t.proj l) := fun l hl => by
    simp only [prod, State.proj_xmm, hlane .xmm8 (by decide) (by decide) l hl, hlane .xmm9 (by decide) (by decide) l hl,
      hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (16 * g + i) := VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [VG.Proof.Gcm.X86_64.Stitch.ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        by rw [hlane _ (by decide) (by decide) 1 (by decide)]; exact h2.2⟩
    · rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → VG.Spec.Gcm.Block) (e : Nat) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = VG.Proof.Gcm.X86_64.Stitch.cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) (VG.Proof.Gcm.X86_64.Stitch.y₀ s₀) ((List.range (16 * (e - 1))).map (VG.Proof.Gcm.X86_64.Stitch.ctb s₀))
  y1 : s.lane .xmm2 1 = 0

theorem body_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.Stitch.FinOk ordE (VG.Proof.Gcm.X86_64.Stitch.hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s) :
    WP isa body s fun s' => VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → VG.Spec.Gcm.Block := fun i => VG.Proof.Gcm.X86_64.Stitch.ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → VG.Spec.Gcm.Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = VG.Proof.Gcm.X86_64.Stitch.pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  have hE₁ : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (16 * (e - 1) + i) from VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega)]
        exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr (VG.Proof.Gcm.X86_64.Stitch.in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr (VG.Proof.Gcm.X86_64.Stitch.in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  have hrdx₁ : (s₁.gpr .rdx).toNat + 32 * 8 = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega
  have hsepA : ∀ c, 16 * e ≤ c → ∀ i, 0 ≤ i → i < 16 → ¬ (c ≤ 16 * (e - 1) + i ∧ 16 * (e - 1) + i < c + 8) :=
    fun c hc i _ hi => by omega
  -- The first batch, with loads 1–4 of the previous group.
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.batch_ok hp gA VG.Proof.Gcm.X86_64.Stitch.gRegs VG.Proof.Gcm.X86_64.Stitch.gRegs_ok (VG.Proof.Gcm.X86_64.Stitch.QG s₀ (fun _ => 0) a X P yl ordE 0 false)
    (VG.Proof.Gcm.X86_64.Stitch.gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (hsepA _ (Nat.le_refl _)) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 8) (by omega) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  have hrdx₂ : (s₂.gpr .rdx).toNat + 32 * 12 = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * (16 * e + 8) := by
    rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega
  have hQ₂' : VG.Proof.Gcm.X86_64.Stitch.QG s₀ (fun _ => 0) a X P yl ordE 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by decide)]; exact h2⟩
  -- The second batch, with loads 5–7 and 0 of the previous group, and the reduction.
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.batch_ok hp gB VG.Proof.Gcm.X86_64.Stitch.gRegs VG.Proof.Gcm.X86_64.Stitch.gRegs_ok (VG.Proof.Gcm.X86_64.Stitch.QG s₀ (fun _ => 0) a X P yl ordE 4 true)
    (VG.Proof.Gcm.X86_64.Stitch.gq_ok (fun _ => Nat.le_refl _) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, Nat.zero_le _⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (hsepA _ (by omega)) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 12) (by omega) hA₂ hrdx₂ hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.nextE_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [VG.Proof.Gcm.X86_64.Stitch.ite_t ⟨rfl, by decide⟩] at h2
  -- The memory of the powers is kept.
  have dP : ∀ c, c + 8 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ → ∀ r' ∈ [(⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩ : Region)], (VG.Proof.Gcm.X86_64.Stitch.pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))
  have keepP : ∀ k < 8, ∀ l < 2, s'.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 =
      s.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 :=
    fun k hk l hl => by
      rw [fm, hm₃.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide),
        hm₂.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide), f₁.mem]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ VG.Proof.Gcm.X86_64.Stitch.gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (by simp only [VG.Proof.Gcm.X86_64.Stitch.gRegs, List.mem_cons, not_or] at hg' ⊢; simp_all) l hl]
  have hA' : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fm]; exact hA₃.frame,
      fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd, by rw [fwr]; exact hA₃.wr⟩
  have hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega, VG.Proof.Gcm.X86_64.Stitch.ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup`. -/
section

/-!
# Interleaved counter mode and GHASH: the setup

`storesK_ok`: `storesK base rs j` stores the registers `rs` to
`base + 32 (j + i)`. `setupC_ok`: the end of the setup loads `Y`, and makes
the counter pair, the increment and the last round key's address. The
powers the setup computes before (`setupG_ok`) are in the field, in
`Stitch/Ok.lean`.
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (storesK setupC)
open VG.Proof.Gcm.X86_64.Vpclmul (getLsbD_one8)
open VG.Proof.Aes.X86_64.Vaes (extract_lo extract_hi)
open VG.Spec.Gcm (Block blockAt inc32)

theorem storesK_ok (base : Reg) : ∀ (rs : List XReg) (j : Nat) (s : State),
    (∀ k < rs.length, InRegions s.wr (s.gpr base + BitVec.ofInt 64 ((32 * (j + k) : Nat) : Int)) 32) →
    (s.gpr base).toNat + 32 * (j + rs.length) ≤ 2 ^ 64 →
    WP isa (.block (storesK base rs j)) s fun s' =>
      (∀ k (h : k < rs.length), ∀ l < 2,
        s'.mem.readW (s.gpr base + BitVec.ofNat 64 (32 * (j + k) + 16 * l)) 128 = s.lane rs[k] l) ∧
      Frame [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * rs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l)
  | [], _, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | r :: rs, j, s, hin, hw => by
    simp only [List.length_cons] at hin hw
    have ha : s.gpr base + BitVec.ofInt 64 ((32 * j : Nat) : Int) = s.gpr base + BitVec.ofNat 64 (32 * j) := by
      rw [BitVec.ofInt_natCast]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero, ha] at hin0
    let s₁ := s.setMem (s.mem.writeW (s.gpr base + BitVec.ofNat 64 (32 * j)) (s.ymm r))
    rw [storesK, WP.block_cons_iff]
    refine ⟨s₁, by
      simp only [isa, exec, State.store256_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, ha, hin0, ite_true]; rfl, ?_⟩
    have hg₁ : s₁.gpr = s.gpr := by simp [s₁]
    refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.storesK_ok base rs (j + 1) s₁ (fun k hk => by
        rw [hg₁, show s₁.wr = s.wr by simp [s₁], show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hg₁]; omega)) fun s' ⟨hv, hf, g, rd, wr, hl⟩ => ?_
    rw [hg₁] at hv hf
    refine ⟨fun k hk l hl => ?_, ?_, by rw [g, hg₁], by rw [rd]; simp [s₁], by rw [wr]; simp [s₁],
      fun r' l => by rw [hl]; simp [s₁, State.lane]⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hf.readW (r := ⟨s.gpr base + BitVec.ofNat 64 (32 * j + 16 * l), 16⟩) (Region.contains_self _ _)
          (fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
        show (s.mem.writeW (s.gpr base + BitVec.ofNat 64 (32 * j)) (s.ymm r)).readW _ 128 = _
        rw [show s.gpr base + BitVec.ofNat 64 (32 * j + 16 * l) =
          s.gpr base + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 (16 * l) by
            rw [BitVec.add_assoc, BitVec.ofNat_add], State.ymm_eq]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · have e := readW_writeW_inside s.mem (s.gpr base + BitVec.ofNat 64 (32 * j))
            (s.lane r 1 ++ s.lane r 0) (k := 0) (n := 16) (by decide) (by decide)
          rw [show 16 * 0 = 0 from rfl]
          exact e.trans (extract_lo _ _)
        · have e := readW_writeW_inside s.mem (s.gpr base + BitVec.ofNat 64 (32 * j))
            (s.lane r 1 ++ s.lane r 0) (k := 16) (n := 16) (by decide) (by decide)
          rw [show 16 * 1 = 16 from rfl, e, extract_hi]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega, hv k (by simpa using hk) l hl]
        simp [s₁, State.lane]
    · refine (Frame.writeW (Frame.refl [⟨s.gpr base + BitVec.ofNat 64 (32 * j), 32 * (rs.length + 1)⟩] s.mem)
        List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r' hr' => ⟨_, List.mem_cons_self, fun x hx => ?_⟩)
      simp only [List.mem_singleton] at hr'
      subst hr'
      exact (Offset.sub _ (by omega) (by omega)) x hx

/-! ## `Y`, the counter, the increment and the pointers -/

theorem setupC_ok (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hy : InRegions s.wr (s.gpr .rcx) 16) (hc : InRegions s.wr (s.gpr .rdx) 16) :
    WP isa (.block setupC) s fun s' =>
      s'.lane .xmm2 0 = VG.Spec.Gcm.blockAt s.mem (s.gpr .rcx) ∧ s'.lane .xmm2 1 = 0 ∧
      (∀ l < 2, s'.lane .xmm14 l = Nat.repeat inc32 l (VG.Spec.Gcm.blockAt s.mem (s.gpr .rdx))) ∧
      (∀ l < 2, s'.lane .xmm15 l = VG.Proof.Aes.X86_64.Vaes.two) ∧
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      s'.gpr .rax = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .xmm2 → r ≠ .xmm13 → r ≠ .xmm14 → r ≠ .xmm15 → ∀ l < 2, s'.lane r l = s.lane r l) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hy' : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr hy
  have hc' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr hc
  have m0 := h0 0 (by decide)
  simp only [State.lane, ite_true] at m0
  apply WP.of_runBlock
  simp only [setupC, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setV, State.setReg, State.load128, State.lane,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hy', hc', VBinOp.sse, getLsbD_one8, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', m0]
  refine ⟨?_, trivial, fun l hl => ?_, fun l hl => ?_, ?_, trivial, trivial, fun r h1 h2 h3 => ?_,
    fun r h2 h13 h14 h15 l hl => ?_, trivial, trivial, trivial⟩
  · rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [ite_true]
      rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact (VG.Proof.Gcm.X86_64.blockAt_eq _ _).symm
    · simp only [Nat.one_ne_zero, ite_false]
      rw [BitVec.ofInt_natCast, BitVec.add_zero, ← VG.Proof.Gcm.X86_64.blockAt_eq]
      exact VG.Proof.Aes.X86_64.AesNi.paddd_one _
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · bv_omega
  · simp [h1, h2, h3]
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [h2, h13, h14, h15]

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Enc`. -/
section

/-!
# Interleaved counter mode and GHASH: encryption

`Ready s₀ P s`: after the setup, nothing is encrypted (`AInv s₀ 0`), the
powers `P` are in the working space, `Y` in `xmm2`, `rdx` points to the data
(`setupT_ok`, after the powers are computed, which `Stitch/Ok.lean` proves in
the field). `first_ok`: the first group is encrypted (`EInv s₀ P 1`).
`encTail_ok`: the encryption after the setup, for any powers whose products
add up to `GHASH` (`FinOk`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (storesK pregs setupC first batch body ghLoad ordE storeCtr lastG storeY)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

structure Ready (s₀ : State) (P : Nat → Nat → VG.Spec.Gcm.Block) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ 0 s
  rdx : s.gpr .rdx = VG.Proof.Gcm.X86_64.Stitch.dp s₀
  rax : s.gpr .rax = VG.Proof.Gcm.X86_64.Stitch.cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = VG.Proof.Gcm.X86_64.Stitch.y₀ s₀
  y1 : s.lane .xmm2 1 = 0

theorem pregs_get : ∀ k (h : k < pregs.length), pregs[k] = preg16 k := by decide

/-- A block outside the working space is kept by writes to it. -/
theorem blockAt_outP {s₀ : State} {m m' : Mem} {p : Addr} (hf : Frame [VG.Proof.Gcm.X86_64.Stitch.pR s₀] m m')
    (hd : Region.Disjoint ⟨p, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.pR s₀)) : VG.Spec.Gcm.blockAt m' p = VG.Spec.Gcm.blockAt m p :=
  blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

/-- The setup after the powers (`setupG`): they are stored in the working
space, then `Y`, the counter, the increment and the pointers. -/
theorem setupT_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {s₁ : State} (l0 : ∀ l < 2, s₁.lane .xmm0 l = revMask)
    (l1 : ∀ l < 2, s₁.lane .xmm1 l = poly) (g₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) (m₁ : s₁.mem = s₀.mem)
    (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr) :
    WP isa (.block (storesK .r11 pregs 0 ++ setupC)) s₁ (VG.Proof.Gcm.X86_64.Stitch.Ready s₀ fun k l => s₁.lane (preg16 k) l) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have hr11 : s₁.gpr .r11 = VG.Proof.Gcm.X86_64.Stitch.pp s₀ := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.storesK_ok .r11 pregs 0 s₁ (fun k hk => by
      rw [wr₁, hr11]; exact VG.Proof.Gcm.X86_64.Stitch.in_sub_int hp.p_in (by simp [pregs] at hk; omega))
    (by rw [hr11]; simp [pregs]; omega)) fun s₂ ⟨sv, fr, g₂, rd₂, wr₂, l₂⟩ => ?_
  rw [hr11, Nat.mul_zero, BitVec.add_zero, show 32 * pregs.length = 256 from rfl, m₁] at fr
  have hp₂ : ∀ {p : Addr}, Region.Disjoint ⟨p, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.pR s₀) → VG.Spec.Gcm.blockAt s₂.mem p = VG.Spec.Gcm.blockAt s₀.mem p :=
    fun hd => by rw [VG.Proof.Gcm.X86_64.Stitch.blockAt_outP fr hd]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.setupC_ok s₂ (fun l hl => by rw [l₂]; exact l0 l hl)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.y_in)
    (by rw [wr₂, wr₁, g₂, g₁ _ (by decide)]; exact hp.c_in))
    fun s₃ ⟨y0, y1, c14, c15, r10, rax, rdx, gk, lk, m₃, rd₃, wr₃⟩ => ?_
  have gs : ∀ r, r ≠ .rax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, g₁ r hr]
  refine ⟨⟨Nat.zero_le _, fun l hl => ?_, fun l hl => ?_, c15, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩,
    by rw [rdx, gs _ (by decide)], by rw [rax, gs _ (by decide)],
    fun r h1 h2 h3 => by rw [gk r h1 h2 h3, gs r h1], fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l1 l hl,
    by rw [y0, gs _ (by decide), hp₂ (hp.p_y.symm)], y1⟩
  · rw [c14 l hl, gs _ (by decide), hp₂ hp.p_c.symm, Nat.zero_add]
  · rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl, l₂]; exact l0 l hl
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [gk _ (by decide) (by decide) (by decide), gs _ (by decide)]
  · rw [r10, gs _ (by decide), gs _ (by decide)]
  · rw [m₃]; exact fr.mono fun r hr => by simp at hr ⊢; exact Or.inr hr
  · rw [m₃, hp₂ (hp.d_p.sub_left (Offset.sub_base _ (by omega)))]
    simp only [Nat.not_lt_zero, ite_false]
  · rw [rd₃, rd₂, rd₁]
  · rw [wr₃, wr₂, wr₁]
  · rw [m₃, show VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l) = s₁.gpr .r11 + BitVec.ofNat 64 (32 * (0 + k) + 16 * l)
      by rw [hr11, Nat.zero_add], sv k (by simp [pregs]; omega) l hl, VG.Proof.Gcm.X86_64.Stitch.pregs_get]

/-- The first group: two batches, with nothing between their rounds. -/
theorem first_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} {s : State} (hR : VG.Proof.Gcm.X86_64.Stitch.Ready s₀ P s) :
    WP isa first s (VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P 1) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (VG.Proof.Gcm.X86_64.Stitch.nr s₀) (VG.Proof.Gcm.X86_64.Stitch.sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ YFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_)
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0 + 8) (j := 4) (by omega) hA₁
    (by rw [hg₁, hR.rdx]) trivial) fun s₂ ⟨hA₂, _, hg₂, hl₂, hm₂⟩ => ?_
  have dP : ∀ c, c + 8 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ → ∀ r' ∈ [(⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩ : Region)], (VG.Proof.Gcm.X86_64.Stitch.pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ VG.Impl.Gcm.X86_64.Stitch.aregs → ∀ l < 2,
      s₂.lane r l = s.lane r l := fun r h13 h14 hr l hl => by
    rw [hl₂ r h13 h14 hr (by simp) l hl, hl₁ r h13 h14 hr (by simp) l hl]
  have gk : s₂.gpr = s.gpr := by rw [hg₂, hg₁]
  refine ⟨by simpa using hA₂, Nat.le_refl _, by rw [gk, hR.rdx]; simp, ?_, by rw [gk]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [gk]; exact hR.gpr r h1 h2 h4, fun k hk l hl => ?_,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) l hl]; exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    by rw [lk _ (by decide) (by decide) (by decide) 1 (by decide)]; exact hR.y1⟩
  · rw [gk, hR.gpr _ (by decide) (by decide) (by decide)]; simp
  · rw [hm₂.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide),
      hm₁.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide)]
    exact hR.pw k hk l hl

/-! ## The loop -/

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → VG.Spec.Gcm.Block} {e : Nat} {s : State} (hI : VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega)]; rfl

theorem loopE_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.Stitch.FinOk ordE (VG.Proof.Gcm.X86_64.Stitch.hk s₀) P) {s : State}
    (hI : VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P 1 s) (hcf : s.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s' := by
  have hm := hp.nbm
  have fin : ∀ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1) < 32 → ∀ t, VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e t → ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ ∧ VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s
    have hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega, hI⟩

/-! ## The last group, and the stores -/

/-- The loads `0 … n − 1` of the order of an encryption body. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block} {yl : Nat → VG.Spec.Gcm.Block} :
    ∀ n, n ≤ 8 → ∀ s, VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ 0 a X P s → (∀ l < 2, prod (s.proj l) = Prod.zero) →
      (∀ l < 2, s.lane .xmm2 l = yl l) →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ordE i))) s fun s' => VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ 0 a X P s' ∧
        (∀ l < 2, prod (s'.proj l) = VG.Proof.Gcm.X86_64.Stitch.accN ordE X P yl l n) ∧ (∀ l < 2, s'.lane .xmm2 l = yl l) ∧
        YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s'
  | 0, _, s, hE, hz, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, fun l hl => by rw [hz l hl]; rfl, hy, YFrame.refl _ _⟩
  | n + 1, hn, s, hE, hz, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghRun_ok n (by omega) s hE hz hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hk : ordE n < 8 := by
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghStep hk (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

/-! ## The whole encryption -/

theorem final_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.Stitch.FinOk ordE (VG.Proof.Gcm.X86_64.Stitch.hk s₀) P) {e : Nat}
    (he : VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e) {s : State} (hI : VG.Proof.Gcm.X86_64.Stitch.EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (VG.Proof.Gcm.X86_64.Stitch.EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  -- The counter's memory is neither the data nor the working space.
  have cD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 8, ∀ l < 2, Region.Disjoint ⟨VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l), 16⟩ (VG.Proof.Gcm.X86_64.Stitch.cR s₀) := fun k hk l hl =>
    hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → VG.Spec.Gcm.Block := fun i => VG.Proof.Gcm.X86_64.Stitch.ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → VG.Spec.Gcm.Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = VG.Proof.Gcm.X86_64.Stitch.pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_lanes s₁) fun s₂ ⟨z₂, f₂, _⟩ => ?_
  have hE₂ : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (16 * (e - 1) + i) from VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega),
          VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 32 * k) from
            VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega)]
        exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr (VG.Proof.Gcm.X86_64.Stitch.in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr (VG.Proof.Gcm.X86_64.Stitch.in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghRun_ok (yl := yl) 8 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.ghFin hE₃ (fun l hl => by
      rw [f₃.lane _ (by decide) l hl, f₂.lane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide)] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [f₄.lane _ (by decide) 0 (by decide), f₃.lane _ (by decide) 0 (by decide),
      f₂.lane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hm0
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.store16_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have hrcx : s.gpr .rcx = VG.Proof.Gcm.X86_64.Stitch.yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  -- The final memory: the counter, then `Y`, written.
  have yD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k) = VG.Proof.Gcm.X86_64.Stitch.ctb s₀ k := fun k hk => by
    rw [m₅, VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' (yD k hk) rfl, VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  have hdata := VG.Proof.Gcm.X86_64.Stitch.blocks_ctr32 hb
  refine ⟨hdata, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show VG.Spec.Gcm.blockAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.cp s₀) = _
    rw [m₅, VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show VG.Spec.Gcm.blockAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) (VG.Proof.Gcm.X86_64.Stitch.y₀ s₀) (VG.Spec.Gcm.blocksAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
    rw [show VG.Spec.Gcm.blocksAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀) = (List.range (16 * e)).map (VG.Proof.Gcm.X86_64.Stitch.ctb s₀) from by
        rw [← he]; simp only [VG.Spec.Gcm.blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, y4]
    refine (hf X yl hI.y1).trans ?_
    rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, VG.Proof.Gcm.X86_64.Stitch.ghash_append16]
    exact congrArg (fun y => ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := VG.Proof.Gcm.X86_64.Stitch.cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := VG.Proof.Gcm.X86_64.Stitch.yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-- The encryption after the setup. -/
theorem encTail_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.Stitch.FinOk ordE (VG.Proof.Gcm.X86_64.Stitch.hk s₀) P) {s : State}
    (hR : VG.Proof.Gcm.X86_64.Stitch.Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (VG.Proof.Gcm.X86_64.Stitch.EPost s₀) := by
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.loopE_ok hp hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => VG.Proof.Gcm.X86_64.Stitch.final_ok hp hf he hI₄)

end VG.Proof.Gcm.X86_64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec`. -/
section

/-!
# Interleaved counter mode and GHASH: decryption

`DInv s₀ P e s`: `e` groups are decrypted (`AInv`) and hashed into `Y` (the
blocks as they were: the ciphertext), the powers `P` in the working space;
`rdx` points to group `e`. `dbody_ok`: a body hashes group `e` while it
decrypts it, reading blocks 0–7 during the rounds of the first batch, before
it overwrites them, and blocks 8–15 during those of the second.
`decTail_ok`: the decryption after the setup, for any powers whose products
add up to `GHASH` (`FinOk`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64.Vpclmul (zero_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs batch dA dB dbody gq ordD storeCtr storeY)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

structure DInv (s₀ : State) (P : Nat → Nat → VG.Spec.Gcm.Block) (e : Nat) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e)
  rax : s.gpr .rax = VG.Proof.Gcm.X86_64.Stitch.cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 8, ∀ l < 2, s.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.lane .xmm2 0 = ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) (VG.Proof.Gcm.X86_64.Stitch.y₀ s₀) ((List.range (16 * e)).map (VG.Proof.Gcm.X86_64.Stitch.blk s₀))
  y1 : s.lane .xmm2 1 = 0

/-- Which blocks of the group the GHASH loads to come still read: in the first
batch, all until its loads are done, then those the second batch reads. -/
abbrev loA (j : Nat) : Nat := if j < 5 then 0 else 8
abbrev loB (j : Nat) : Nat := if j < 5 then 8 else 16

theorem dbody_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.Stitch.FinOk ordD (VG.Proof.Gcm.X86_64.Stitch.hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.Stitch.DInv s₀ P e s) :
    WP isa dbody s fun s' => VG.Proof.Gcm.X86_64.Stitch.DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → VG.Spec.Gcm.Block := fun i => VG.Proof.Gcm.X86_64.Stitch.blk s₀ (16 * e + i)
  let yl : Nat → VG.Spec.Gcm.Block := fun l => s.lane .xmm2 l
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hr11 : s.gpr .r11 = VG.Proof.Gcm.X86_64.Stitch.pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (zero_lanes s) fun s₁ ⟨z₁, f₁, _⟩ => ?_)
  have hE₁ : VG.Proof.Gcm.X86_64.Stitch.GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ (16 * e + i) from VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (32 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * e + 32 * k) from VG.Proof.Gcm.X86_64.Stitch.addr_eq (by omega)]
        exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr (VG.Proof.Gcm.X86_64.Stitch.in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact VG.Proof.Gcm.X86_64.Stitch.in_rdwr (VG.Proof.Gcm.X86_64.Stitch.in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.yframe f₁ (by decide) (by decide) (by decide)
  -- The first batch decrypts blocks 0–7 of the group, hashing them (the product with `Y` last).
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.batch_ok hp dA VG.Proof.Gcm.X86_64.Stitch.gRegs VG.Proof.Gcm.X86_64.Stitch.gRegs_ok (VG.Proof.Gcm.X86_64.Stitch.QG s₀ VG.Proof.Gcm.X86_64.Stitch.loA a X P yl ordD 0 false)
    (VG.Proof.Gcm.X86_64.Stitch.gq_ok (fun j => by simp only [VG.Proof.Gcm.X86_64.Stitch.loA]; split <;> split <;> omega) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩) (fun h => absurd h (by decide)))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi _ => by have : 8 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega) hA₁ (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact hI.m1 l hl,
      by rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.lane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  have hQ₂' : VG.Proof.Gcm.X86_64.Stitch.QG s₀ VG.Proof.Gcm.X86_64.Stitch.loB a X P yl ordD 4 true 1 s₂ := by
    obtain ⟨hE, h1, h2⟩ := hQ₂
    rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by decide)] at h2
    exact ⟨hE, h1, by rw [VG.Proof.Gcm.X86_64.Stitch.ite_f (by decide)]; exact h2⟩
  -- The second batch decrypts blocks 8–15, hashing them, then reduces.
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.Stitch.batch_ok hp dB VG.Proof.Gcm.X86_64.Stitch.gRegs VG.Proof.Gcm.X86_64.Stitch.gRegs_ok (VG.Proof.Gcm.X86_64.Stitch.QG s₀ VG.Proof.Gcm.X86_64.Stitch.loB a X P yl ordD 4 true)
    (VG.Proof.Gcm.X86_64.Stitch.gq_ok (fun j => by simp only [VG.Proof.Gcm.X86_64.Stitch.loB]; split <;> split <;> omega) (fun j hj1 hj4 => by
      rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide⟩) (fun _ => rfl))
    (fun j t t' h f => h.yframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi hi' => by have : 16 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e + 8) (j := 4) (by omega) hA₂ (by rw [hg₂, f₁.gpr]; show a.toNat + _ = _; omega) hQ₂')
    fun s₃ ⟨hA₃, hQ₃, hg₃, hl₃, hm₃⟩ => ?_)
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.nextD_ok s₃) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, _, h2⟩ := hQ₃
  rw [VG.Proof.Gcm.X86_64.Stitch.ite_t ⟨rfl, by decide⟩] at h2
  have dP : ∀ c, c + 8 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ → ∀ r' ∈ [(⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ c, 128⟩ : Region)], (VG.Proof.Gcm.X86_64.Stitch.pR s₀).Disjoint r' := fun c hc r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))
  have keepP : ∀ k < 8, ∀ l < 2, s'.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 =
      s.mem.readW (VG.Proof.Gcm.X86_64.Stitch.pp s₀ + BitVec.ofNat 64 (32 * k + 16 * l)) 128 :=
    fun k hk l hl => by
      rw [fm, hm₃.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide),
        hm₂.readW (r := VG.Proof.Gcm.X86_64.Stitch.pR s₀) (Offset.contains_base _ (by omega) (by omega)) (dP _ (by omega)) (by decide), f₁.mem]
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₃, hg₂, f₁.gpr]
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ VG.Proof.Gcm.X86_64.Stitch.gRegs → ∀ l < 2, s'.lane r l = s.lane r l :=
    fun r h13 h14 ha' hg' l hl => by
      rw [fl r l, hl₃ r h13 h14 ha' hg' l hl, hl₂ r h13 h14 ha' hg' l hl,
        f₁.lane r (by simp only [VG.Proof.Gcm.X86_64.Stitch.gRegs, List.mem_cons, not_or] at hg' ⊢; simp_all) l hl]
  have hA' : VG.Proof.Gcm.X86_64.Stitch.AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 8 + 8 by omega]
    exact ⟨hA₃.le, fun l hl => by rw [fl]; exact hA₃.ctr l hl, fun l hl => by rw [fl]; exact hA₃.msk l hl,
      fun l hl => by rw [fl]; exact hA₃.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₃.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₃.r10, by rw [fm]; exact hA₃.frame,
      fun k hk => by rw [fm]; exact hA₃.blocks k hk, by rw [frd]; exact hA₃.rd, by rw [fwr]; exact hA₃.wr⟩
  have hr9 : s₃.gpr .r9 - 16 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1)) := by
    rw [hg₃, hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [keepP k hk l hl]; exact hI.pw k hk l hl,
    fun l hl => by rw [lk _ (by decide) (by decide) (by decide) (by decide) l hl]; exact hI.m1 l hl, ?_,
    by rw [fl]; exact h2.2⟩, ?_⟩
  · rw [frdx, hg₃, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [VG.Proof.Gcm.X86_64.Stitch.ghash_append16]
    exact congrArg (fun y => ghashFrom (VG.Proof.Gcm.X86_64.Stitch.hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega)]

theorem dfinal_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} {e : Nat} (he : VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e) {s : State}
    (hI : VG.Proof.Gcm.X86_64.Stitch.DInv s₀ P e s) :
    WP isa (.block (storeCtr ++ storeY)) s (VG.Proof.Gcm.X86_64.Stitch.DPost s₀) := by
  have hw := hp.wrap_d
  have hm0 : s.lane .xmm0 0 = revMask := hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.store16_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = VG.Proof.Gcm.X86_64.Stitch.yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.store16_ok .xmm2 .xmm2 .rcx s₁ (by rw [l₁ _ (by decide) 0 (by decide)]; exact hm0)
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  rw [g₁, hrcx, m₁, l₁ _ (by decide) 0 (by decide)] at m₂
  have cD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have yD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s₂.mem (VG.Proof.Gcm.X86_64.Stitch.bAddr s₀ k) = VG.Proof.Gcm.X86_64.Stitch.ctb s₀ k := fun k hk => by
    rw [m₂, VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' (yD k hk) rfl, VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨VG.Proof.Gcm.X86_64.Stitch.blocks_ctr32 hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show VG.Spec.Gcm.blockAt s₂.mem (VG.Proof.Gcm.X86_64.Stitch.cp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.Stitch.blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, hI.a.ctr 0 (by decide),
      Nat.add_zero, he]
  · show VG.Spec.Gcm.blockAt s₂.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := VG.Proof.Gcm.X86_64.Stitch.cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := VG.Proof.Gcm.X86_64.Stitch.yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4

/-- The decryption after the setup. -/
theorem decTail_ok {s₀ : State} (hp : VG.Proof.Gcm.X86_64.Stitch.SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.Stitch.FinOk ordD (VG.Proof.Gcm.X86_64.Stitch.hk s₀) P) {s₁ : State}
    (hR : VG.Proof.Gcm.X86_64.Stitch.Ready s₀ P s₁) : WP isa (.seq (.loop dbody .ae) (.block (storeCtr ++ storeY))) s₁ (VG.Proof.Gcm.X86_64.Stitch.DPost s₀) := by
  have hm := hp.nbm
  have h16 := hp.nb16
  have hI₁ : VG.Proof.Gcm.X86_64.Stitch.DInv s₀ P 0 s₁ :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  let I : Nat → State → Prop := fun m s => ∃ e, m = VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ ∧ VG.Proof.Gcm.X86_64.Stitch.DInv s₀ P e s
  have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.Stitch.DInv s₀ P e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (VG.Proof.Gcm.X86_64.Stitch.dbody_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI'⟩
  exact WP.seq (WP.mono (WP.loop (M := isa) I hstep (VG.Proof.Gcm.X86_64.Stitch.nb s₀) s₁ ⟨0, by simp, by omega, hI₁⟩)
    fun s₂ ⟨e, he, hI₂⟩ => VG.Proof.Gcm.X86_64.Stitch.dfinal_ok hp he hI₂)

end VG.Proof.Gcm.X86_64.Stitch

end
