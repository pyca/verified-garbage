module

public import VerifiedGarbage.Proof.Scrypt.X86_64.FusedVerified
public import VerifiedGarbage.Proof.Scrypt.RoMix
public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import all Init.Data.Nat.Power2.Basic
import VerifiedGarbage.Proof.Scrypt.Memory
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit
public meta import VerifiedGarbage.Proof.Scrypt.X86_64.FusedVerified
meta import VerifiedGarbage.Proof.Scrypt.RoMix
meta import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Scrypt.X86_64.Common
meta import Init.Data.Nat.Power2.Basic
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import Mathlib.Tactic.DefEqTransformations
meta import Mathlib.Tactic.Set
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Scrypt.X86_64.Lit
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Scrypt.X86_64.PackedHalf
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.MdStream.X86_64.Common
meta import VerifiedGarbage.Proof.Scrypt.X86_64.PackedHalf
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.Proof.Framework.InstancePriority
meta import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `Scrypt.X86_64.RoMixLoops`, which this module and modules that import it used -/

section

/-! ### `Scrypt.X86_64.SimdMem`, which only this module used -/

section

/-! Unaligned SSE2 copy and XOR, preserving every general-purpose register. -/

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.SimdMem
open VG VG.X86_64 VG.Impl.Scrypt.X86_64

private theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) :
    (s.setXmm r v).ea m = s.ea m := rfl

theorem copy {s : State} {x d : Addr}
    (hx : s.ea (at_ .rdi 0) = x) (hd : s.ea (at_ .rsi 0) = d)
    (hin : InRegions (s.rd ++ s.wr) x 16) (hout : InRegions s.wr d 16) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rdi 0), .movdquStore (at_ .rsi 0) .xmm0]) s
      fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = s.mem.writeW d (s.mem.readW x 128) := by
  refine WP.block_cons_iff.mpr ⟨s.setXmm .xmm0 (s.mem.readW x 128), ?_, ?_⟩
  · simp only [reduceExec, State.load128, hx, hin, ite_true, Option.map_some]
  refine WP.block_cons_iff.mpr
    ⟨{ s.setXmm .xmm0 (s.mem.readW x 128) with mem := s.mem.writeW d (s.mem.readW x 128) },
      ?_, WP.block_nil ⟨rfl, rfl, rfl, rfl⟩⟩
  simp only [reduceExec, State.store128, ea_setXmm, hd, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, hout, ite_true]

theorem xor {s : State} {x y d : Addr}
    (hx : s.ea (at_ .rdi 0) = x) (hy : s.ea (at_ .rsi 0) = y)
    (hd : s.ea (at_ .r8 0) = d)
    (hinx : InRegions (s.rd ++ s.wr) x 16) (hiny : InRegions (s.rd ++ s.wr) y 16)
    (hout : InRegions s.wr d 16) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r8 0) .xmm0]) s
      fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = s.mem.writeW d (s.mem.readW x 128 ^^^ s.mem.readW y 128) := by
  refine WP.block_cons_iff.mpr ⟨s.setXmm .xmm0 (s.mem.readW x 128), ?_, ?_⟩
  · simp only [reduceExec, State.load128, hx, hinx, ite_true, Option.map_some]
  let t := (s.setXmm .xmm0 (s.mem.readW x 128)).setXmm .xmm1 (s.mem.readW y 128)
  refine WP.block_cons_iff.mpr ⟨t, ?_, ?_⟩
  · simp only [t, reduceExec, State.load128, ea_setXmm, hy, RegUpd.rd_setXmm,
      RegUpd.wr_setXmm, RegUpd.mem_setXmm, hiny, ite_true, Option.map_some]
  let u := t.setXmm .xmm0 (s.mem.readW x 128 ^^^ s.mem.readW y 128)
  refine WP.block_cons_iff.mpr ⟨u, ?_, ?_⟩
  · simp only [u, t, reduceExec, XOp.exec, reduceXBinOpEval,
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : XReg.xmm0 ≠ XReg.xmm1),
      RegUpd.xmm_setXmm_self]
  refine WP.block_cons_iff.mpr
    ⟨{ u with mem := s.mem.writeW d (s.mem.readW x 128 ^^^ s.mem.readW y 128) },
      ?_, WP.block_nil ⟨rfl, rfl, rfl, rfl⟩⟩
  simp only [u, t, reduceExec, State.store128, ea_setXmm, hd, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, hout, ite_true]

end VG.Proof.Scrypt.X86_64.SimdMem

end

end

/-! ### `Scrypt.X86_64.Memory128`, which only this module used -/

section

/-! Byte-level correctness of 128-bit XOR stores used by the SSE2 loops. -/

@[expose] public section

namespace VG.Proof.Scrypt.Memory
open VG VG.Spec.Scrypt VG.Spec.Pbkdf2
open VG.Proof.Sha256.Stream
theorem writeW_xor128 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 128 ^^^ m'.readW b 128) =
      writeBytes m d (xorBytes (bytesAt m' a 16) (bytesAt m' b 16)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (128 : Nat) / 8 = 16 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁]

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem128 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 16 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 16 * n⟩ ⟨x, 16 * n⟩) (hdy : Region.Disjoint ⟨d, 16 * n⟩ ⟨y, 16 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).writeW
      (d + BitVec.ofNat 64 (16 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (x + BitVec.ofNat 64 (16 * k)) 128 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (y + BitVec.ofNat 64 (16 * k)) 128) =
      writeBytes m d (xorBytes (bytesAt m x (16 * (k + 1))) (bytesAt m y (16 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length = 16 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  -- The words of `x` and `y` are not in the part of `d` written so far.
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega_using [hk]) (by omega_using [hk, hlt]))).sub_right
      (Region.sub_prefix (by omega_using [hk]))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega_using [hk]) (by omega_using [hk, hlt]))).sub_right
      (Region.sub_prefix (by omega_using [hk]))
  rw [writeW_xor128, bytesAt_writeBytes_sep _ _ sx (by omega_using []), bytesAt_writeBytes_sep _ _ sy (by omega_using [])]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (16 * k)) 16)
    (bytesAt m (y + BitVec.ofNat 64 (16 * k)) 16))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_using [hk, hlt])
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]


end VG.Proof.Scrypt.Memory

end

end


/-!
# scryptROMix on x86-64: the small loops

The word copy (`copyLoop`), the word exclusive-or (`xorLoop`), the
direct address multiplication (`mulLoop`) and the computation of `2 N` by
doubling (`nLoop`).
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.MdStream.X86_64 (Upd wp_movm wp_store wp_add wp_addi wp_subi wp_cmp ofNat_pred
  ofNat_beq_zero sub_beq)
open VG.Proof.Scrypt.X86_64.BlockMix (ea_at wp_xorm)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat copy_mem xor_mem128 dbl_pow)

/-! ## Instructions and arithmetic -/


theorem ea_at0 (s : State) (b : Reg) : s.ea (at_ b 0) = s.gpr b := by
  rw [ea_at]; exact BitVec.add_zero _

theorem sx16 : (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 := by decide

theorem sx1 : (1 : BitVec 32).signExtend 64 = 1 := by decide

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (16 * k) + (16 : BitVec 32).signExtend 64 = p + BitVec.ofNat 64 (16 * (k + 1)) := by
  rw [sx16, add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [sx1, ofNat_pred (by omega_using [hk]), Nat.sub_sub]

theorem dec_zf {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, ofNat_beq_zero (by omega_using [hn])]
  exact decide_eq_decide.mpr (by omega_using [hk])

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 (16 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_using [], hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by simp [eval, hz, hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [eval, hz, hl], n - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → t.gpr r = s.gpr r
  rdi : t.gpr .rdi = src + BitVec.ofNat 64 (16 * k)
  rsi : t.gpr .rsi = dst + BitVec.ofNat 64 (16 * k)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (16 * k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 16 * n < 2 ^ 64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (16 * k)) 16)
    (hsep : Region.Disjoint ⟨src, 16 * n⟩ ⟨dst, 16 * n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : CopyInv s src dst n k t) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rdi 0), .movdquStore (at_ .rsi 0) .xmm0,
      .alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  change WP isa (.block ([.movdquLoad .xmm0 (at_ .rdi 0),
    .movdquStore (at_ .rsi 0) .xmm0] ++
    [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 1)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (SimdMem.copy (by rw [ea_at0, h.rdi]) (by rw [ea_at0, h.rsi])
    (by rw [h.rd, h.wr]; exact hin k hk) (by rw [h.wr]; exact hout k hk)) ?_
  intro t₂ ⟨g₂, rd₂, wr₂, m₂⟩
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₂.gpr r = t.gpr r := fun r hr => congrFun g₂ r
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, h.wr],
    fun r ha hdi hsi hcx => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other r hcx, u₄.other r hsi, u₃.other r hdi, g r ha, h.other r ha hdi hsi hcx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.rdi, next_ptr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.rsi, next_ptr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx, dec_count hk]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, h.mem, Nat.mul_succ]
    exact copy_mem s.mem src dst k 16
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hk])
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hk])) (by omega_using [hlt, hk])
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx,
      dec_zf hk (by omega_using [hlt])]

/-- `copyLoop` copies `16 n` bytes from `rdi` to `rsi` (`rcx = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 16 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = src) (hsi : s.gpr .rsi = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (16 * k)) 16)
    (hsep : Region.Disjoint ⟨src, 16 * n⟩ ⟨dst, 16 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (16 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt hin hout hsep hk h) ?_) fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add, hdi], by rw [ofNat_zero_add, hsi],
    by rw [hcx, Nat.sub_zero], by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rcx → t.gpr r = s.gpr r
  rdi : t.gpr .rdi = x + BitVec.ofNat 64 (16 * k)
  rsi : t.gpr .rsi = y + BitVec.ofNat 64 (16 * k)
  r8 : t.gpr .r8 = d + BitVec.ofNat 64 (16 * k)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - k)
  mem : t.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (16 * k)) (bytesAt s.mem y (16 * k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 16 * n < 2 ^ 64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (16 * k)) 16)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (16 * k)) 16)
    (hdx : Region.Disjoint ⟨d, 16 * n⟩ ⟨x, 16 * n⟩) (hdy : Region.Disjoint ⟨d, 16 * n⟩ ⟨y, 16 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r8 0) .xmm0, .alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16),
      .alu .add .r8 (.imm 16), .alu .sub .rcx (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  change WP isa (.block ([.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0),
    .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r8 0) .xmm0] ++
    [.alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16), .alu .add .r8 (.imm 16),
      .alu .sub .rcx (.imm 1)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (SimdMem.xor (by rw [ea_at0, h.rdi]) (by rw [ea_at0, h.rsi])
    (by rw [ea_at0, h.r8]) (by rw [h.rd, h.wr]; exact hinx k hk)
    (by rw [h.rd, h.wr]; exact hiny k hk) (by rw [h.wr]; exact hout k hk)) ?_
  intro t₃ ⟨g₃, rd₃, wr₃, m₃⟩
  refine wp_addi fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_addi fun t₆ u₆ =>
    wp_subi fun t₇ u₇ z₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₃.gpr r = t.gpr r := fun r hr => congrFun g₃ r
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, h.wr],
    fun r ha hdi hsi h8 hcx => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other r hcx, u₆.other r h8, u₅.other r hsi, u₄.other r hdi, g r ha,
      h.other r ha hdi hsi h8 hcx]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g _ (by decide), h.rdi, next_ptr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g _ (by decide), h.rsi, next_ptr]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.r8, next_ptr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, dec_count hk]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, h.mem]
    exact xor_mem128 s.mem hk hlt hdx hdy
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, dec_zf hk (by omega_using [hlt])]

/-- `xorLoop` writes `[rdi] xor [rsi]` to `r8`, `16 n` bytes. -/
theorem xorLoop_ok {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n) (hlt : 16 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = x) (hsi : s.gpr .rsi = y) (hr8 : s.gpr .r8 = d)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (16 * k)) 16)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (16 * k)) 16)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (16 * k)) 16)
    (hdx : Region.Disjoint ⟨d, 16 * n⟩ ⟨x, 16 * n⟩) (hdy : Region.Disjoint ⟨d, 16 * n⟩ ⟨y, 16 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (16 * n)) (bytesAt s.mem y (16 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add, hdi], by rw [ofNat_zero_add, hsi],
    by rw [ofNat_zero_add, hr8], by rw [hcx, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `mulLoop` -/

/-- The low half of `mul` is multiplication modulo 2^64. -/
theorem mul_low (s : State) :
    (execMul .rcx s).gpr .rax = s.gpr .rax * s.gpr .rcx := by
  simp only [execMul, RegUpd.gpr_setReg,
    show Reg.rax ≠ Reg.rdx by decide, ↓reduceIte]
  exact (BitVec.ofNat_mul _ _).trans (by simp)

/-- Add `rax * rcx` to `rdx`; `rdi` is a temporary and memory is unchanged. -/
theorem mulLoop_ok {s : State} {j c : Nat} {a : Addr} (_hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = a) (hcx : s.gpr .rcx = BitVec.ofNat 64 c) :
    WP isa mulLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rdi → s'.gpr r = s.gpr r) ∧
      s'.gpr .rdx = a + BitVec.ofNat 64 (j * c) := by
  unfold mulLoop
  refine Proof.MdStream.X86_64.wp_mov fun t u _ _ => ?_
  refine Proof.MdStream.X86_64.WP.cons (s' := execMul .rcx t) rfl ?_
  refine Proof.MdStream.X86_64.wp_mov fun v uv _ _ => wp_add fun w uw => WP.block_nil ?_
  refine ⟨by rw [uw.rd, uv.rd]; exact u.rd,
    by rw [uw.wr, uv.wr]; exact u.wr,
    by rw [uw.mem, uv.mem]; exact u.mem, ?_, ?_⟩
  · intro r ha hd _ hi
    rw [uw.other _ hd, uv.other _ hd, Taint.execMul_gpr _ _ ha hd, u.other _ hi]
  · rw [uw.gpr, uv.gpr, Taint.execMul_gpr _ _ (by decide) (by decide), u.gpr,
      uv.other _ (by decide), mul_low, u.other _ (by decide), u.other _ (by decide),
      hdx, hax, hcx, ← BitVec.ofNat_mul]

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .rax → r' ≠ .rdx → t.gpr r' = s.gpr r'
  rax : t.gpr .rax = BitVec.ofNat 64 (r * 2 ^ k)
  rdx : t.gpr .rdx = BitVec.ofNat 64 (2 ^ k)

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : NInv s r k t) :
    WP isa (.block [.alu .add .rax (.reg .rax), .alu .add .rdx (.reg .rdx),
      .alu .cmp .rax (.reg .rcx)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_cmp fun t₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .rax = BitVec.ofNat 64 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.rax, dbl_pow]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega_using [hk]))
  refine ⟨⟨by rw [rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₃, u₂.wr, u₁.wr, h.wr],
    by rw [m₃, u₂.mem, u₁.mem, h.mem], fun r' ha hd => ?_, by rw [g₃, ax], ?_⟩, ?_⟩
  · rw [g₃, u₂.other r' hd, u₁.other r' ha, h.other r' ha hd]
  · rw [g₃, u₂.gpr, u₁.other _ (by decide), h.rdx, ← Nat.one_mul (2 ^ k), dbl_pow, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide), h.other _ (by decide) (by decide),
      hcx, sub_beq (by omega_using [hlt, le]) hlt]
    refine congrArg some (decide_eq_decide.mpr ⟨fun hh => ?_, fun hh => by rw [hh]⟩)
    exact (Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr hh)

/-- `nLoop` doubles `rax` (from `r`) and `rdx` (from 1) until `rax = rcx = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 r) (hdx : s.gpr .rdx = 1)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .rax → r' ≠ .rdx → s'.gpr r' = s.gpr r') ∧
      s'.gpr .rdx = BitVec.ofNat 64 (2 ^ (e + 1)) := by
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt hcx hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.rdx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [hax, Nat.pow_zero, Nat.mul_one], by rw [hdx]; rfl⟩

end VG.Proof.Scrypt.X86_64.RoMix

end

end

/-! ### `Scrypt.X86_64.PackedVerified`, which this module and modules that import it used -/

section

/-! ### `Scrypt.X86_64.PackedCT`, which only this module used -/

section

/-! ### `Scrypt.X86_64.PackedBody`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_subi)
open VG.Proof.Scrypt.X86_64.Retained (memWords)

structure Tail (s t : State) : Prop where
 mem : t.mem=s.mem
 rd : t.rd=s.rd
 wr : t.wr=s.wr
 rbx : t.gpr .rbx=s.gpr .rbx+128
 rbp : t.gpr .rbp=s.gpr .rbp+64
 r12 : t.gpr .r12=s.gpr .r12+64
 r14 : t.gpr .r14=s.gpr .r14-1
 r15 : t.gpr .r15=s.gpr .r12
 keep : ∀ r, r≠.rbx → r≠.rbp → r≠.r12 → r≠.r14 → r≠.r15 → t.gpr r=s.gpr r
 zf : t.zf=some (s.gpr .r14-1==0)

theorem tail_ok (s : State) : WP isa (.block tail) s fun t => Tail s t ∧ t.xmm=s.xmm := by
 refine WP.mono (WP.vecKeep (by decide) ?_) fun _ h => ⟨h.1,h.2.1⟩
 unfold tail
 refine wp_mov fun a ua _ _ => wp_addi fun b ub => wp_addi fun c uc =>
  wp_addi fun d ud => wp_subi fun t ut hz => WP.block_nil ?_
 refine ⟨ut.mem.trans (ud.mem.trans (uc.mem.trans (ub.mem.trans ua.mem))),
  ut.rd.trans (ud.rd.trans (uc.rd.trans (ub.rd.trans ua.rd))),
  ut.wr.trans (ud.wr.trans (uc.wr.trans (ub.wr.trans ua.wr))),?_,?_,?_,?_,?_,?_,?_⟩
 · rw [ut.other _ (by decide),ud.other _ (by decide),uc.other _ (by decide),ub.gpr,ua.other _ (by decide)]; rfl
 · rw [ut.other _ (by decide),ud.other _ (by decide),uc.gpr,ub.other _ (by decide),ua.other _ (by decide)]; rfl
 · rw [ut.other _ (by decide),ud.gpr,uc.other _ (by decide),ub.other _ (by decide),ua.other _ (by decide)]; rfl
 · rw [ut.gpr,ud.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ua.other _ (by decide)]; rfl
 · rw [ut.other _ (by decide),ud.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ua.gpr]
 · intro r hb hp h12 h14 h15
   rw [ut.other r h14,ud.other r h12,uc.other r hp,ub.other r hb,ua.other r h15]
 · rw [hz,ud.other _ (by decide),uc.other _ (by decide),ub.other _ (by decide),ua.other _ (by decide)]; rfl

namespace BM
open VG.Proof.Scrypt.X86_64.BlockMix

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop extends BlockMix.Inv s₀ k s where
 words : Holds (memWords s.mem (xP s₀ k)) s

theorem Inv.frame_registers {s₀ s t : State} {k : Nat} (h : BlockMix.Inv s₀ k s) (f : F s t) :
 BlockMix.Inv s₀ k t := by
 rcases f with ⟨hg,hm,hr,hw⟩
 exact ⟨h.k_le,hr.trans h.rd,hw.trans h.wr,by rw [hg]; exact h.rsp,
  by rw [hg]; exact h.rbx,by rw [hg]; exact h.rbp,by rw [hg]; exact h.r12,
  by rw [hg]; exact h.r13,by rw [hg]; exact h.r14,by rw [hg]; exact h.r15,
  by rw [hm]; exact h.frame,by rw [hm]; exact h.saved,by rw [hm]; exact h.done,
  by rw [hm]; exact h.x⟩

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
 WP isa (.block (VG.Impl.Scrypt.X86_64.bmPrologue++load)) s₀ (Inv s₀ 0) := by
 rw [WP.block_append_iff]
 refine WP.mono (BlockMix.prologue_ok hp) fun s h => ?_
 have hi : InRegions (s.rd++s.wr) (s.gpr .r15) 64 := by
  rw [h.rd,h.wr,h.r15,xP,hp.rd,hp.wr]
  exact ⟨BlockMix.bR s₀,by simp,BlockMix.in_b hp (o:=128*rr s₀-64) (n:=64) (by have := hp.pos; omega_using [this])⟩
 exact WP.mono (load_ok hi) fun t ⟨f,ht⟩ =>
  ⟨Inv.frame_registers h f,by rw [f.mem]; rw [h.r15] at ht; exact ht⟩

end BM
end VG.Proof.Scrypt.X86_64.Packed

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed.BM
open VG VG.X86_64 VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.Scrypt.X86_64.BlockMix
open VG.Proof.Scrypt.X86_64.Retained (memWords core_bytes)
open VG.Proof.Scrypt.Memory (InRegions.of_mem)

attribute [local irreducible] memWords

theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k<rr s₀) {s : State} (h : Inv s₀ k s) :
 WP isa body s fun t => Inv s₀ (k+1) t ∧ t.zf=some (BitVec.ofNat 64 (rr s₀-k)-1==0) := by
 have ie : InRegions (s.rd++s.wr) (bB s₀ k) 64 := by
  rw [h.rd,h.wr,hp.rd,hp.wr]
  exact ⟨BlockMix.bR s₀,by simp,in_b hp (by omega_using [hk])⟩
 have we : InRegions s.wr (yE s₀ k) 64 := by
  rw [h.wr,hp.wr]
  exact ⟨yR s₀,by simp,in_y hp (by omega_using [hk])⟩
 refine WP.seq (WP.mono (Packed.half_ok h.words (by rw [h.rbx]; exact plus_zero _) ie h.rbp we) fun a ha => ?_)
 obtain ⟨wa,ma,fa,ga,ra,wra⟩ := ha
 have ba : Spec.Scrypt.bytesAt a.mem (yE s₀ k) 64 = Spec.Scrypt.salsa
   (Spec.Pbkdf2.xorBytes (Spec.Scrypt.bytesAt s.mem (xP s₀ k) 64) (Spec.Scrypt.bytesAt s.mem (bB s₀ k) 64)) :=
  core_bytes (fun j hj => by have := congrArg (fun v : Vector Spec.Scrypt.Word 16 => v[j]'hj) ma; simpa only [memWords,Vector.getElem_ofFn] using this)
 have baddr : plus (bB s₀ k) 64 = bP s₀ + BitVec.ofNat 64 (64*(2*k+1)) := by
  rw [plus,bB,Memory.add_ofNat]; congr 2; omega_using []
 let src := bP s₀+BitVec.ofNat 64 (64*(2*k+1))
 have io : InRegions (a.rd++a.wr) src 64 := by
  rw [ra,wra,h.rd,h.wr,hp.rd,hp.wr]
  exact ⟨BlockMix.bR s₀,by simp,in_b hp (by omega_using [hk])⟩
 have wo : InRegions a.wr (yO s₀ k) 64 := by
  rw [wra,h.wr,hp.wr]
  exact ⟨yR s₀,by simp,in_y hp (by omega_using [hk])⟩
 have wa' : Holds (memWords a.mem (yE s₀ k)) a := by rw [ma]; exact wa
 refine WP.seq (WP.mono (Packed.half_ok wa' (by rw [ga,h.rbx]; exact baddr) io
  (by rw [ga,h.r12]) wo) fun b hb => ?_)
 obtain ⟨wb,mb,fb,gb,rb,wrb⟩ := hb
 have bb : Spec.Scrypt.bytesAt b.mem (yO s₀ k) 64 = Spec.Scrypt.salsa
   (Spec.Pbkdf2.xorBytes (Spec.Scrypt.bytesAt a.mem (yE s₀ k) 64) (Spec.Scrypt.bytesAt a.mem src 64)) :=
  core_bytes (fun j hj => by have := congrArg (fun v : Vector Spec.Scrypt.Word 16 => v[j]'hj) mb; simpa only [memWords,Vector.getElem_ofFn] using this)
 have ffa : Frame [slot s₀ (64*k),⟨sc s₀,64⟩,stkR s₀] s.mem a.mem :=
  fa.mono (fun R hr => by simp only [List.mem_singleton] at hr; subst R; simp [slot,yE])
 have ffb : Frame [slot s₀ (64*(rr s₀+k)),⟨sc s₀,64⟩,stkR s₀] a.mem b.mem :=
  fb.mono (fun R hr => by simp only [List.mem_singleton] at hr; subst R; simp [slot,yO])
 obtain ⟨ff,saved,done⟩ := mem_ok hp hk h.toInv ffa ba ffb bb
 have wb' : Holds (memWords b.mem (yO s₀ k)) b := by rw [mb]; exact wb
 refine WP.mono (Packed.tail_ok b) fun t ⟨ht,hx⟩ => ?_
 have nextb : bB s₀ k+128=bB s₀ (k+1) := by
  change bP s₀+BitVec.ofNat 64 (128*k)+BitVec.ofNat 64 128=_
  rw [Memory.add_ofNat]; congr 2
 have nexte : yE s₀ k+64=yE s₀ (k+1) := by
  change yP s₀+BitVec.ofNat 64 (64*k)+BitVec.ofNat 64 64=_
  rw [Memory.add_ofNat]; congr 2
 have nexto : yO s₀ k+64=yO s₀ (k+1) := by
  change yP s₀+BitVec.ofNat 64 (64*(rr s₀+k))+BitVec.ofNat 64 64=_
  rw [Memory.add_ofNat]; congr 2
 have nextc : BitVec.ofNat 64 (rr s₀-k)-1=BitVec.ofNat 64 (rr s₀-(k+1)) := by
  have := r_lt hp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub,Memory.toNat_ofNat_lt (by omega_using [this]),Memory.toNat_ofNat_lt (by omega_using [this]),
    show (1 : BitVec 64).toNat=1 from rfl]
  omega_using [hk, this]
 have zf := ht.zf
 rw [gb,ga,h.r14] at zf
 refine ⟨⟨⟨by omega_using [hk],ht.rd.trans (rb.trans (ra.trans h.rd)),ht.wr.trans (wrb.trans (wra.trans h.wr)),
  ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩,zf⟩
 · rw [ht.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),gb,ga]; exact h.rsp
 · rw [ht.rbx,gb,ga,h.rbx,nextb]
 · rw [ht.rbp,gb,ga,h.rbp,nexte]
 · rw [ht.r12,gb,ga,h.r12,nexto]
 · rw [ht.keep _ (by decide) (by decide) (by decide) (by decide) (by decide),gb,ga]; exact h.r13
 · rw [ht.r14,gb,ga,h.r14,nextc]
 · rw [ht.r15,gb,ga,h.r12]; rfl
 · rw [ht.mem]; exact ff
 · rw [ht.mem]; exact saved
 · rw [ht.mem]; exact done
 · rw [ht.mem]; change Spec.Scrypt.bytesAt b.mem (yO s₀ k) 64=_
   rw [(done k (by omega_using [])).2]; rfl
 · rw [ht.mem]; exact wb'.keep (fun _ _ => congrFun hx _)

end VG.Proof.Scrypt.X86_64.Packed.BM

end
end

end

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed.BM
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.Scrypt.X86_64.BlockMix

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body_rel {k : Nat} (hk : k < rr s₀) :
 RelCT isa (fun s t => Inv s₀ k s ∧ Inv s₀' k t) body fun s t =>
  (Inv s₀ (k+1) s ∧ s.zf=some (BitVec.ofNat 64 (rr s₀-k)-1==0)) ∧
  (Inv s₀' (k+1) t ∧ t.zf=some (BitVec.ofNat 64 (rr s₀'-k)-1==0)) := by
 have ct : RelCT isa (fun s t => Inv s₀ k s ∧ Inv s₀' k t) body (fun _ _ => True) :=
  RelCT.taint (A:=taint) (Taint.ofRegs [.rbx,.rbp,.r12,.r14]) (fun s t h =>
   Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · rw [h.1.rbx,h.2.rbx,bB,bB,bP,bP,hq.rdi]
    · rw [h.1.rbp,h.2.rbp,yE,yE,yP,yP,hq.rdx]
    · rw [h.1.r12,h.2.r12,yO,yO,yP,yP,hq.rdx,hq.rr]
    · rw [h.1.r14,h.2.r14,hq.rr]) (by taint_decide)
 exact (ct.wp fun _ _ h => ⟨body_ok hp hk h.1,body_ok hp' (hq.rr ▸ hk) h.2⟩).mono
  (fun _ _ h => h) (fun _ _ h => h.2)

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop body .ne) fun s s' =>
      Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := body) (c := .ne)
    (Q := fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s')
    (fun n s s' => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s ∧ Inv s₀' k s') (fun n => by
      intro s s' t t' u u' ⟨k, hn, hk, h, h'⟩ e e'
      have hk' : k < rr s₀' := hq.rr ▸ hk
      obtain ⟨ht, ⟨i, z⟩, ⟨i', z'⟩⟩ := body_rel hp hp' hq hk _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_ne hp hk z, eval_ne hp' hk' z', ← hq.rr]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : k + 1 = rr s₀ := by simpa using hf
        exact ⟨hl ▸ i, hl ▸ i'⟩
      · have hl : k + 1 ≠ rr s₀ := by simpa using ht'
        exact ⟨rr s₀ - (k + 1), by omega_using [hn, hk], k + 1, rfl, by omega_using [hk, hl], i, i'⟩) (rr s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, hp.pos, h.1, h.2⟩) fun _ _ h => h

theorem blockMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Packed.blockMix fun _ _ => True := by
  unfold Packed.blockMix
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (bmPrologue ++ Packed.load))
      fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.r8
        · exact hq.rsp) (c := .block (bmPrologue ++ Packed.load)) (by taint_decide)).wp
      (F₁ := Inv s₀ 0) (F₂ := Inv s₀' 0) fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s') (.block bmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq ((loop_rel hp hp' hq).seq epi)

end
end VG.Proof.Scrypt.X86_64.Packed.BM

end

end

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Packed.BM
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.Scrypt.X86_64.BlockMix
open VG.Proof.Scrypt.Memory (InRegions.of_mem)
theorem loop_ok {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop body .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  rw [eval_ne hp hk hz]
  by_cases hl : k + 1 = rr s₀
  · exact .inl ⟨by simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [hl], rr s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hl], hi'⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  refine WP.mono (Spill.restore_ok .r13 bmSaved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r13]; exact h.saved)) fun s' ⟨h₁, h₂, hm, _⟩ =>
    ⟨hm, Spill.calleeSaved_ok h₁ h₂ (by decide) h.rsp⟩
  have := saved_bound p hp'
  rw [h.r13, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by omega_using [this]))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Packed.blockMix s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86_64.post s₀ s' := by
  unfold Packed.blockMix
  refine WP.seq (WP.mono (BM.prologue_ok hp) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_y
    · exact hp.ret_s
    · exact ret_stk s₀
  · show Spec.Scrypt.bytesAt s'.mem (yP s₀) (128 * rr s₀) = Spec.Scrypt.blockMix (rr s₀) (B s₀)
    rw [hm']
    exact post_of fun i hi => h₃.done i hi
end VG.Proof.Scrypt.X86_64.Packed.BM

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.Packed.BM
open VG VG.X86_64
open VG.Proof.Scrypt.X86_64.BlockMix
theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.Packed.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre
    Proof.Scrypt.blockMixX86_64.pub Impl.Scrypt.X86_64.Packed.blockMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (blockMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Scrypt.X86_64.Packed.BM

end
end

end

/-!
# scryptROMix on x86-64: the precondition and the calls

The regions the function works on, and `BlockMixSpec`: what a call of the
verified `vg_scrypt_blockmix` does, from its `Verified` proof by `WP.call`.
-/

@[expose] public section

namespace VG.Proof.Scrypt.X86_64.RoMix

namespace Stream
export VG.Proof.MdStream.X86_64 (Upd)
end Stream

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c`, emitted as `n`, writes scryptBlockMix of the `128 r` bytes
at `rdi` to `rdx`, with the 128 bytes at `r8` as working space. -/
def BlockMixSpec (n : String) (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : Addr) (r : Nat), s.gpr .rdi = src → s.gpr .rsi = BitVec.ofNat 64 r →
    s.gpr .rdx = dst → s.gpr .rcx = BitVec.ofNat 64 r → s.gpr .r8 = scr → 0 < r →
    128 * r < 2 ^ 64 →
    Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩ → Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩ →
    Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨src, 128 * r⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨dst, 128 * r⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨scr, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 64 → dst.toNat + 128 * r ≤ 2 ^ 64 → scr.toNat + 128 ≤ 2 ^ 64 →
    InRegions (s.rd ++ s.wr) src (128 * r) → InRegions s.wr dst (128 * r) →
    InRegions s.wr scr 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr →
        (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨dst, 128 * r⟩, ⟨scr, 128⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
        bytesAt s'.mem dst (128 * r) = blockMix r (bytesAt s.mem src (128 * r)) → Q s') →
    WP isa (.call n c) s Q

/-- An implementation of scryptBlockMix, emitted as `name`, with what ROMix's
proofs use of it: its contract (`Proof.Scrypt.blockMixX86_64`), and that it
calls nothing and keeps `rsp`. -/
structure BMImpl where
  name : String
  code : Prog isa
  correct : ∀ s, Proof.Scrypt.blockMixX86_64.pre s → ∃ t s', Exec isa code s t s' ∧
    abiPreserved s s' ∧ Proof.Scrypt.blockMixX86_64.post s s'
  ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre Proof.Scrypt.blockMixX86_64.pub code
  depth : code.depth = 0
  nosp : NoSp code

theorem packed_nosp : NoSp Impl.Scrypt.X86_64.Packed.blockMix := by
  have : ((instrs Impl.Scrypt.X86_64.Packed.blockMix).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem fused_nosp : NoSp Impl.Scrypt.X86_64.blockMixFused := by
  have : ((instrs Impl.Scrypt.X86_64.blockMixFused).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The SSE2 BlockMix (`Impl.Scrypt.X86_64.Packed`). -/
def BMImpl.packed : BMImpl where
  name := "vg_scrypt_blockmix_sse2"
  code := Impl.Scrypt.X86_64.Packed.blockMix
  correct := Packed.BM.blockMix_correct
  ct := Packed.BM.blockMix_ct
  depth := by lit_decide
  nosp := packed_nosp

/-- The scalar BlockMix (`Impl.Scrypt.X86_64.blockMixFused`). -/
def BMImpl.fused : BMImpl where
  name := "vg_scrypt_blockmix"
  code := Impl.Scrypt.X86_64.blockMixFused
  correct := BlockMix.Fused.blockMix_correct
  ct := BlockMix.Fused.blockMix_ct
  depth := by lit_decide
  nosp := fused_nosp

/-- The 8 bytes below the stack pointer after a call are within the 16 below it before. -/
theorem below8_sub (sp : Addr) : Region.Sub (below (sp - 8) 8) (below sp 16) :=
  below_callee sp 8

/-- The return address slot of a call from `sp`. -/
theorem ret8_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) := by
  intro a h
  simp only [Region.Contains] at h ⊢
  obtain e : a - (sp - BitVec.ofNat 64 16) = (a - (sp - 8)) + 8 := by bv_omega
  rw [e, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
  have := Nat.mod_le ((a - (sp - 8)).toNat + 8) (2 ^ 64)
  omega_using [h]

/-- What a call of `vg_scrypt_blockmix` needs: its contract's precondition,
once the return address is stored and its permissions are narrowed. -/
theorem bm_pre {s : State} {src dst scr : Addr} {r : Nat} (hdi : s.gpr .rdi = src)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 r) (hdx : s.gpr .rdx = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 r)
    (hr8 : s.gpr .r8 = scr) (hr : 0 < r) (_hlt : 128 * r < 2 ^ 64)
    (hds : Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩) (hsd : Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩)
    (bsrc : (below (s.gpr .rsp) 16).Disjoint ⟨src, 128 * r⟩)
    (bdst : (below (s.gpr .rsp) 16).Disjoint ⟨dst, 128 * r⟩)
    (bscr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 64) (ndst : dst.toNat + 128 * r ≤ 2 ^ 64)
    (nscr : scr.toNat + 128 ≤ 2 ^ 64)
    (isrc : InRegions (s.rd ++ s.wr) src (128 * r)) (idst : InRegions s.wr dst (128 * r))
    (iscr : InRegions s.wr scr 128) :
    Proof.Scrypt.blockMixX86_64.pre
      (s.callEntry.withRegions [⟨src, 128 * r⟩] [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) ∧
    Covers ([⟨src, 128 * r⟩] ++ [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨dst, 128 * r⟩, ⟨scr, 128⟩] s.wr := by
  obtain hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  obtain tr : (BitVec.ofNat 64 r).toNat = r := Memory.toNat_ofNat_lt (by omega_using [ndst])
  obtain c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  obtain cw := Covers.pair (Covers.one idst) (Covers.one iscr)
  refine ⟨?_, ?_, cw⟩
  · simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx,
      hr8, tr, c128]
    refine ⟨trivial, trivial, hds, hsd, hss, ?_, ?_, ?_, ?_, ?_, nsrc, ndst, nscr, trivial, hr⟩
    · exact bdst.sub_left (ret8_sub _)
    · exact bscr.sub_left (ret8_sub _)
    · exact bsrc.sub_left (below8_sub _)
    · exact bdst.sub_left (below8_sub _)
    · exact bscr.sub_left (below8_sub _)
  · have h1 := Covers.one isrc
    intro a n h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h1 a n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩

theorem blockMixSpec (bm : BMImpl) : BlockMixSpec bm.name bm.code := by
  intro s src dst scr r hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr Q hQ
  obtain hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  obtain tr : (BitVec.ofNat 64 r).toNat = r := Memory.toNat_ofNat_lt (by omega_using [ndst])
  obtain ⟨p, c₁, c₂⟩ := bm_pre hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr
  refine WP.call (k := Proof.Scrypt.blockMixX86_64) bm.correct bm.nosp
    (by rw [bm.depth]; decide) p c₁ c₂ ?_
  intro s₂ hrd hwr hcs hf _ ⟨s₃, hm₃, _, hpost⟩
  simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hdi, hsi, hdx, hm₃, tr] at hpost
  rw [bm.depth] at hf
  refine hQ s₂ hrd hwr hcs (by
    simpa using VG.X86_64.Frame.below_mono (b := 16) hf (by decide) (by decide)) ?_
  rw [hpost]
  congr 1
  exact Memory.bytesAt_congr fun i hi =>
    callEntry_byte s (R := ⟨src, 128 * r⟩) (bsrc.sub_left (below_sub (by omega_using []) (by omega_using [])))
      (by show 128 * r ≤ 2 ^ 64; omega_using [ndst]) hi

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .rdi
abbrev rr : Nat := (s₀.gpr .rsi).toNat
abbrev vP : Addr := s₀.gpr .rdx
abbrev vl : Nat := (s₀.gpr .rcx).toNat
abbrev sc : Addr := s₀.gpr .r8
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vP s₀, vl s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, (rr s₀ + 2) * 128⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)
/-- `(V[i]'(by omega))`. -/
abbrev vAt (i : Nat) : Addr := vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := sc s₀ + BitVec.ofNat 64 192

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (sc s₀) s₀.gpr rmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, vR s₀, scR s₀]
  b_v : (bR s₀).Disjoint (vR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  v_s : (vR s₀).Disjoint (scR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_v : (retR s₀).Disjoint (vR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_v : (stkR s₀).Disjoint (vR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + (rr s₀ + 2) * 128 ≤ 2 ^ 64
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo
  r9 : (s₀.gpr .r9).toNat = rr s₀ + 2

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  simp only [h18] at h2 h4 h5 h8 h11 h14
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_, h17, h18⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h16)).symm

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem NN_pos : 0 < NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * rr s₀ * NN s₀ < 2 ^ 64 := by
  obtain e : 128 * rr s₀ * NN s₀ = vl s₀ * 128 := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [e]
  by_contra hc
  refine hp.v_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
  simp only [Region.Contains]
  have := (sc s₀ - vP s₀).isLt
  omega

theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  have := v_lt hp
  have := NN_pos hp
  have : 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_right _ (by omega_using [this])
  omega_arith

/-- `(V[i]'(by omega))` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < NN s₀) : Region.Sub ⟨vAt s₀ i, 128 * rr s₀⟩ (vR s₀) := by
  have := v_lt hp
  obtain e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  show Region.Sub ⟨vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vP s₀, vl s₀ * 128⟩
  exact Memory.sub_off (by rw [e]; omega_using [this]) (by omega_arith)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  obtain hle : ∀ j, j < NN s₀ → 128 * rr s₀ * j + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := fun j hj => by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain h1 := hle i hi
  obtain h2 := hle k hk
  have hpos := hp.pos
  refine Memory.disj_off _ ?_ (by omega_using [this, h1]) (by omega_using [this, h2]) (by omega_using [this, h1]) (by omega_using [this, h2])
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left
    have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    exact this
  · right
    have : 128 * rr s₀ * k + 128 * rr s₀ ≤ 128 * rr s₀ * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    exact this

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨tP s₀, 128 * rr s₀⟩ (scR s₀) := by
  have := hp.s_nw
  exact Memory.sub_off (by omega_using []) (by omega_using [])

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨sc s₀, 128⟩ (scR s₀) := Region.sub_prefix (by omega_using [])

theorem t_w : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨sc s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := Memory.disj_off (sc s₀) (o₁ := 192) (n₁ := 128 * rr s₀) (o₂ := 0) (n₂ := 128) (by omega_using [])
    (by omega_using []) (by omega_using []) (by omega_arith) (by omega_using [])
  simpa using this

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega_using [h]) (by omega_using [h])

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  Memory.sub_off (by omega_using [h]) (by omega_using [h])

/-! ## What stays in `scratch`: the caller's registers and `N` -/

/-- Bytes `[128, 184)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨sc s₀ + BitVec.ofNat 64 128, 56⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  Saved s₀ m ∧ m.readW (sc s₀ + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 (NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 184) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega_using [h₁], ← Memory.add_ofNat]
  exact Memory.sub_off (by omega_using [h₂]) (by omega_using [h₂])

theorem saved_offs {p : Reg × Nat} (hp : p ∈ rmSaved) : 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 :=
  (show ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 by decide) p hp

theorem Kept.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Kept s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Kept s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have ho := saved_offs hp
    rw [← h.1 p hp]
    exact hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ ho.1 (by omega_using [ho]))) (by decide)
  · rw [← h.2]
    exact hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 176, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ (by omega_using []) (by omega_using []))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (scR s₀) := s_sub s₀ (by omega_using [])

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)
theorem keep_stk : (keepR s₀).Disjoint (stkR s₀) := hp.stk_s.symm.sub_left (keep_sub s₀)

omit hp in
theorem keep_w : (keepR s₀).Disjoint ⟨sc s₀, 128⟩ := by
  have := Memory.disj_off (sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 0) (n₂ := 128) (by omega_using [])
    (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [])
  simpa using this

theorem keep_t : (keepR s₀).Disjoint ⟨tP s₀, 128 * rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact Memory.disj_off (sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 192) (n₂ := 128 * rr s₀) (by omega_using [])
    (by omega_using []) (by omega_using []) (by omega_using []) (by omega_arith)

omit hp in
theorem b_sub' : Region.Sub ⟨bP s₀, 128 * rr s₀⟩ (bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Stream.Upd s s' d (s.gpr d >>> n) → s'.zf = some ((s.gpr d >>> n) == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine Proof.MdStream.X86_64.WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_ rfl)
  · simp [exec, execShift, h₁, h₂]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl,
      rfl⟩

theorem wp_and {d r : Reg}
    (k : ∀ s', Stream.Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.MdStream.X86_64.WP.cons rfl (k _ (VG.Proof.MdStream.X86_64.Upd.flags _ _ _ _ _ _))

end

theorem shr_ofNat {a : Nat} (n : Nat) (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Memory.toNat_ofNat_lt h, Memory.toNat_ofNat_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: correctness

The prologue saves our caller's registers in `scratch` and computes `N`; step
2 and step 3 are loops whose bodies call `vg_scrypt_blockmix` (through
`BlockMixSpec`); the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_mov32i)
open VG.Proof.Sha256.Stream (writeBytes)

theorem frame_bytesAt' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Memory.frame_bytesAt hf hd hn

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sc s₀) s₀.gpr rmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame _ _ _ _ fun _ hp => in_s s₀ (by have := saved_offs hp; omega_using [this])

theorem prologue_eq : rmPrologue =
    ([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp, .store (at_ .r8 144) .r12,
     .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15, .store (at_ .r8 168) .r13] : List Instr) ++
    ([.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8), .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp,
      .store (at_ .r8 144) .r12, .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15,
      .store (at_ .r8 168) .r13] : List Instr) ++ rest)) s₀ Q := by
  refine Spill.save_then .r8 rmSaved (fun p hp' => ?_) (k _ rfl rfl rfl rfl)
  have := saved_offs hp'
  rw [hp.wr]; exact Memory.InRegions.of_mem (by simp) (in_s s₀ (by omega_using [this]))

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  rax : s.gpr .rax = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = 1
  rcx : s.gpr .rcx = BitVec.ofNat 64 (2 * vl s₀)

set_option linter.unusedSimpArgs false in
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8),
     .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)]) s₁ (P1 s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_add fun e7 u7 => wp_mov fun f uf _ _ =>
    wp_mov32i fun h uh _ _ => wp_add fun i ui => WP.block_nil ?_
  have x0 : d.gpr .r14 = BitVec.ofNat 64 (rr s₀) := by
    rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (BlockMix.dbl x0)
  have x2 := u2.gpr.trans (BlockMix.dbl x1)
  have x3 := u3.gpr.trans (BlockMix.dbl x2)
  have x4 := u4.gpr.trans (BlockMix.dbl x3)
  have x5 := u5.gpr.trans (BlockMix.dbl x4)
  have x6 := u6.gpr.trans (BlockMix.dbl x5)
  have x7 : e7.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [u7.gpr.trans (BlockMix.dbl x6)]; exact congrArg (BitVec.ofNat _) (by omega_using [])
  have xc : h.gpr .rcx = BitVec.ofNat 64 (vl s₀) := by
    simp (disch := decide) only [uh.other, uf.other, u7.other, u6.other, u5.other, u4.other,
      u3.other, u2.other, u1.other, ud.other, uc.other, ub.other, ua.other, g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ui.rd, uh.rd, uf.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, uf.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.mem, uh.mem, uf.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  all_goals simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other,
    ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, u7.other, x7,
    uf.gpr, uf.other, uh.gpr, uh.other, ui.gpr, ui.other, g, xc, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  all_goals first | rfl | decide |
    exact BlockMix.dbl (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hm => setup_ok hp g hrd hwr hm

/-! ## Computing `N` -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = vAt s₀ i
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

theorem setupMem_kept (s₀ : State) :
    Kept s₀ ((saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (NN s₀))) :=
  ⟨Spill.Saved.writeW (saveMem_saved s₀) _ (fun _ hp => by have := saved_offs hp; omega_using [this])
    (fun _ hp => by have := saved_offs hp; omega_using [this]) (by decide), Mem.readW_writeW_self64 _ _ _⟩

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  obtain lt := v_lt hp
  have pos := hp.pos
  obtain e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_comm]
  obtain hNe : 2 * vl s₀ < 2 ^ 64 := by
    have : 128 * rr s₀ * NN s₀ = 128 * vl s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega_using [lt, this]
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega_using [e2, hNe]) h.rax h.rdx
    (by rw [h.rcx, e2])) fun t ⟨rd, wr, mem, oth, rdx⟩ => ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r := oth
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem, h.mem],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx],
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [rdx, he, Nat.pow_succ, Nat.mul_comm]⟩

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  obtain lt := v_lt hp
  obtain n1 := NN_pos hp
  have : 2 * NN s₀ < 2 ^ 64 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega_using [this]
      exact Nat.mul_le_mul_right _ this
    omega_using [lt, this]
  unfold rmSetup
  refine wp_shr (by decide) (by decide) fun t1 u1 _ => ?_
  obtain hd : t1.gpr .rdx = BitVec.ofNat 64 (NN s₀) := by
    rw [u1.gpr, h.rdx, shr_ofNat _ (by omega_using [this]), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 176)
    (by rw [BlockMix.ea_at, u1.other _ (by decide), h.r13])
    (by rw [u1.wr, h.wr, hp.wr]; exact Memory.InRegions.of_mem (by simp) (in_s s₀ (by omega_using [])))
    fun t2 g2 m2 rd2 wr2 => wp_mov fun t3 u3 _ _ => wp_mov fun t4 u4 _ _ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .rdx → r ≠ .r15 → r ≠ .rbp → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, g2, u1.other _ b]
  obtain hm : t4.mem = (saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (NN s₀)) := by
    rw [u4.mem, u3.mem, m2, hd, u1.mem, h.mem]
  obtain fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega_using []))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, rd2, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, wr2, u1.wr, h.wr], by rw [g _ (by decide) (by decide) (by decide), h.rsp],
    by rw [g _ (by decide) (by decide) (by decide), h.rbx], ?_,
    by rw [g _ (by decide) (by decide) (by decide), h.r12],
    by rw [g _ (by decide) (by decide) (by decide), h.r13],
    by rw [g _ (by decide) (by decide) (by decide), h.r14], ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega_using [])⟩
  · rw [u4.gpr, u3.other _ (by decide), g2, u1.other _ (by decide), h.r12]
    simp
  · rw [u4.other _ (by decide), u3.gpr, g2, hd]; rfl
  · refine frame_bytesAt' fr (fun r hr => ?_) (by have := r_lt hp; omega_using [this])
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

theorem start_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) {rest : Prog isa}
    {Q : State → Prop} (hk : ∀ s', Inv2 s₀ 0 s' → WP isa rest s' Q) :
    WP isa (.seq nLoop (.seq (.block rmSetup) rest)) s Q :=
  WP.seq (WP.mono (nloop_ok hp h) fun _ h' => WP.seq (WP.mono (setup2_ok hp h') hk))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `rdi` is set. -/
abbrev bmTail : List Instr :=
  [.mov .rsi (.reg .r14), .shift .shr .rsi 7, .mov .rcx (.reg .rsi), .mov .rdx (.reg .rbx),
    .mov .r8 (.reg .r13)]

theorem blockMixTo_eq (n : String) (c : Prog isa) (src : List Instr) :
    blockMixTo n c src = .seq (.block (src ++ bmTail)) (.call n c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bP s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine Memory.InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (sc s₀) 128 := by
  rw [hp.wr]
  refine Memory.InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []

theorem calleeSaved_tail {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Setting up and making the call, from `rdi = A`. -/
theorem bm_ok {n : String} {c : Prog isa} (hS : BlockMixSpec n c) {s₀ : State} (hp : Pre s₀) {s : State} {A : Addr}
    (hA : s.gpr .rdi = A) (hbx : s.gpr .rbx = bP s₀) (h13 : s.gpr .r13 = sc s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩)
    (hAs : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩) (hAn : A.toNat + 128 * rr s₀ ≤ 2 ^ 64)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (bP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s.mem A (128 * rr s₀)) →
      Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call n c) s' Q := by
  obtain lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ?_
  obtain k : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → f.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [uf.other _ h4, ue.other _ h3, ud.other _ h2, ub.other _ h1, ua.other _ h1]
  obtain hsi : b.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ub.gpr, ua.gpr, h14, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega_using [])
  obtain hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, ub.mem, ua.mem]
  obtain hsp' : f.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by decide) (by decide) (by decide) (by decide), hsp]
  refine hS f A (bP s₀) (sc s₀) (rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide) (by decide), hA])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi])
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), hbx])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi])
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h13])
    hp.pos lt ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hAb hAw
    (by rw [hsp']; exact hAs) (by rw [hsp']; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [hsp']; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hAn (by have := hp.b_nw; omega_using [this])
    (by have := hp.s_nw; omega_using [this])
    (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hrd, hwr]; exact hAi)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact b_in hp)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact w_in hp) _
    fun s' rd' wr' cs' f' b' => hQ s' (by rw [rd', uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [wr', uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      (fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := calleeSaved_tail hr
        rw [cs' r hr, k r h1 h2 h3 h4])
      (by rw [hm, hsp'] at f'; exact f') (by rw [b', hm])

/-! ## Step 2 -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := v_lt hp
  have := hp.pos
  have hv := hp.v_nw
  obtain e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [Memory.toNat_add_ofNat _ (by omega_arith)]
  omega_using [hv, e, this]

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  obtain e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  obtain lt := v_lt hp
  exact Memory.InRegions.of_mem (R := vR s₀) (by simp)
    (Memory.contains_off (by rw [e]; omega_using [this]) (by omega_using [this, lt]))

/-- `(V[i]'(by omega))` and the parts of `scratch` and the stack we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (stkR s₀) :=
  hp.stk_v.symm.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m') :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `(V[k]'(by omega))`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt' hf (fun r hr => ?_) (by have := r_lt hp; omega_using [this])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub
  · exact vAt_stk hp hk

theorem call_kept {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w
    · exact keep_stk hp

end

theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt s₀ i + BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * (i + 1))
  rw [Memory.add_ofNat, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bP s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact Memory.InRegions.of_mem (R := bR s₀) (by simp) (Memory.contains_off (by omega_using [hk]) (by omega_using [hk, this]))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 8 * rr s₀) :
    InRegions s₀.wr (vAt s₀ i + BitVec.ofNat 64 (16 * k)) 16 := by
  rw [hp.wr]
  obtain e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  obtain lt := v_lt hp
  show InRegions _ (vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (16 * k)) 16
  rw [Memory.add_ofNat]
  exact Memory.InRegions.of_mem (R := vR s₀) (by simp)
    (Memory.contains_off (by rw [e]; omega_using [hk, this]) (by omega_using [hk, this, lt]))

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = BitVec.ofNat 64 (NN s₀ - 1)
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  obtain n1 := NN_pos hp
  unfold rmMid
  refine wp_movm (a := sc s₀ + BitVec.ofNat 64 176) (by rw [BlockMix.ea_at, h.r13])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega_using [])))
    fun a ua => wp_mov fun b ub _ _ => wp_subi fun d ud _ => WP.block_nil ?_
  obtain ka : a.gpr .r15 = BitVec.ofNat 64 (NN s₀) := by rw [ua.gpr, h.kept.2]
  obtain k : ∀ r, r ≠ .r15 → r ≠ .rbp → d.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ud.other _ h2, ub.other _ h2, ua.other _ h1]
  obtain hm : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ud.rd, ub.rd, ua.rd, h.rd], by rw [ud.wr, ub.wr, ua.wr, h.wr],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx], ?_,
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [ud.other _ (by decide), ub.other _ (by decide), ka]; rfl,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk, ?_,
    ?_⟩
  · rw [ud.gpr, ub.gpr, ka]
    have := dec_count (n := NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem ea_j {s₀ : State} (hp : Pre s₀) (s : State) (hbx : s.gpr .rbx = bP s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)) :
    s.ea { base := .rbx, index := some .r14, disp := -64 } =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) := by
  have := hp.pos
  simp only [State.ea, hbx, h14]
  rw [ofNat_split (a := 64) (b := 128 * rr s₀) (by omega_using [this]),
    show BitVec.ofInt 64 (-64) = 0 - BitVec.ofNat 64 64 by decide]
  bv_omega

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bP s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 &&& BitVec.ofNat 64 (NN s₀ - 1) =
      BitVec.ofNat 64 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  obtain vlt := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega_using [this])
  obtain he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega_using [hc])
    omega_arith
  apply BitVec.eq_of_toNat_eq
  rw [Memory.toNat_ofNat_lt (by have := jOf_lt hp m; omega_arith), he, and_mask _ he', jOf, he,
    integerify_mod _ _ hp.pos he']

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8 * rr s₀) :
    InRegions s₀.wr (tP s₀ + BitVec.ofNat 64 (16 * k)) 16 := by
  have := hp.s_nw
  rw [hp.wr, Memory.add_ofNat]
  exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (Memory.contains_off (by omega_using [hk]) (by omega_using [hk, this]))

theorem t_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (Memory.contains_off (by omega_using []) (by omega_using []))

theorem t_b {s₀ : State} (hp : Pre s₀) :
    Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_nw {s₀ : State} (hp : Pre s₀) : (tP s₀).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := hp.s_nw
  rw [Memory.toNat_add_ofNat _ (by omega_using [this])]
  omega_using [this]

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  obtain lt := r_lt hp
  obtain hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  obtain hl : T.length = 128 * rr s₀ := by
    rw [hT, Memory.xorBytes_length _ _ (by simp [Memory.bytesAt_length]), Memory.bytesAt_length]
  obtain hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := Memory.bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  obtain f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  obtain f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  obtain hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, Memory.bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) lt]
      exact h.v k hk
  obtain e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega_using [hi]
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

theorem sx192 : (192 : BitVec 32).signExtend 64 = BitVec.ofNat 64 192 := by decide

/-- One iteration of step 3. -/
theorem step3_ok {n : String} {c : Prog isa} (hS : BlockMixSpec n c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 n c) s fun s' => Inv3 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  obtain lt := r_lt hp
  obtain vlt := v_lt hp
  have pos := hp.pos
  obtain hN : NN s₀ < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega_using [pos])
    omega_using [vlt, this]
  obtain hj := jOf_lt hp s.mem
  obtain e8 : 16 * (8 * rr s₀) = 128 * rr s₀ := by omega_using []
  have hrd : s.rd = s₀.rd := h.rd
  have hwr : s.wr = s₀.wr := h.wr
  unfold step3 jBlock
  refine WP.seq (wp_movm (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (ea_j hp s h.rbx h.r14)
    (by rw [hrd, hwr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := bR s₀) (by simp)
          (Memory.contains_off (by omega_using [pos]) (by omega_using [lt])))
    fun a ua => wp_and fun b ub => WP.block_nil ?_)
  obtain hax : b.gpr .rax = BitVec.ofNat 64 (jOf s₀ s.mem) := by
    rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp]; exact jOf_eq hp s.mem
  refine WP.seq (wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (mulLoop_ok (j := jOf s₀ s.mem) (c := 128 * rr s₀) (a := vP s₀)
    (by omega_using [hN, hj]) (by rw [ue.other _ (by decide), ud.other _ (by decide), hax])
    (by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r12])
    (by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14]))
    fun f ⟨rdf, wrf, mf, gf, dxf⟩ => ?_)
  obtain hdx : f.gpr .rdx = vAt s₀ (jOf s₀ s.mem) := by rw [dxf, Nat.mul_comm]
  refine WP.seq (wp_mov fun g1 u1 _ _ => wp_mov fun g2 u2 _ _ => wp_mov fun g3 u3 _ _ =>
    wp_addi fun g4 u4 => wp_mov fun g5 u5 _ _ => wp_shr (by decide) (by decide) fun g6 u6 _ =>
    WP.block_nil ?_)
  obtain rd6 : g6.rd = s₀.rd := by
    rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, rdf, ue.rd, ud.rd, ub.rd, ua.rd, hrd]
  obtain wr6 : g6.wr = s₀.wr := by
    rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, wrf, ue.wr, ud.wr, ub.wr, ua.wr, hwr]
  obtain m6 : g6.mem = s.mem := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, mf, ue.mem, ud.mem, ub.mem, ua.mem]
  obtain k6 : ∀ r ∈ calleeSaved, g6.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cs_ne hr
    rw [u6.other _ h4, u5.other _ h4, u4.other _ h6, u3.other _ h6, u2.other _ h3, u1.other _ h2,
      gf _ h1 h5 h4 h2, ue.other _ h4, ud.other _ h5, ub.other _ h1, ua.other _ h1]
  obtain x6 : g6.gpr .r8 = tP s₀ := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13, sx192]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ (jOf s₀ s.mem)) (d := tP s₀)
    (n := 8 * rr s₀) (by omega_using [pos]) (by omega_using [lt])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, gf _ (by decide) (by decide) (by decide) (by decide),
      ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide),
      h.rbx])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hdx])
    x6
    (by rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14,
      shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega_using []))
    (fun k hk => by rw [rd6, wr6]; exact b_word hp hk)
    (fun k hk => by rw [rd6, wr6]; exact Memory.InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wr6]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [m6, e8] at mt
  obtain kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := cs_ne hr
    rw [gt r h1 h2 h3 h6 h4, k6 r hr]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun q1 v1 _ _ => wp_addi fun q2 v2 => ?_))
  obtain kq : ∀ r ∈ calleeSaved, q2.gpr r = s.gpr r := fun r hr => by
    rw [v2.other _ (cs_ne hr).2.1, v1.other _ (cs_ne hr).2.1, kt r hr]
  refine bm_ok hS hp (A := tP s₀)
    (by rw [v2.gpr, v1.gpr, kt _ (by decide), h.r13, sx192])
    (by rw [kq _ (by decide), h.rbx]) (by rw [kq _ (by decide), h.r13])
    (by rw [kq _ (by decide), h.r14]) (by rw [kq _ (by decide), h.rsp])
    (by rw [v2.rd, v1.rd, rdt, rd6]) (by rw [v2.wr, v1.wr, wrt, wr6])
    (t_b hp) (t_w hp) (hp.stk_s.sub_right (t_sub hp)) (t_nw hp)
    (Memory.InRegions.right (t_in hp)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [v2.mem, v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  obtain k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kq r hr]
  refine wp_subi fun s5 u5 z5 => WP.block_nil ?_
  obtain k5 : ∀ r ∈ calleeSaved, r ≠ .r15 → s5.gpr r = s.gpr r := fun r hr h1 => by
    rw [u5.other _ h1, k4 r hr]
  obtain e15 : s4.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i) := by rw [k4 _ (by decide), h.r15]
  refine ⟨⟨by omega_using [hi], by rw [u5.rd, rd4, v2.rd, v1.rd, rdt, rd6],
    by rw [u5.wr, wr4, v2.wr, v1.wr, wrt, wr6],
    by rw [k5 _ (by decide) (by decide), h.rsp], by rw [k5 _ (by decide) (by decide), h.rbx],
    by rw [k5 _ (by decide) (by decide), h.rbp], by rw [k5 _ (by decide) (by decide), h.r12],
    by rw [k5 _ (by decide) (by decide), h.r13], by rw [k5 _ (by decide) (by decide), h.r14],
    by rw [u5.gpr, e15, dec_count hi],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [z5, e15, dec_zf hi hN]⟩

theorem loop3_ok {n : String} {c : Prog isa} (hS : BlockMixSpec n c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 n c) .ne) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  refine WP.mono (Spill.restore_ok .r13 rmSaved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r13]; exact h.kept.1)) fun s' ⟨h₁, h₂, hm, _⟩ =>
    ⟨hm, Spill.calleeSaved_ok h₁ h₂ (by decide) h.rsp⟩
  have := saved_offs hp'
  rw [h.r13, h.rd, h.wr, hp.rd, hp.wr]
  exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega_using [this]))

end VG.Proof.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: constant time, up to the indices `j`

As for scryptBlockMix (`BlockMixCT.lean`), we relate two runs (`RelCT`):
correctness determines our registers from the public arguments, so they
agree between the calls, where the taint analysis proves each block
constant time; the calls are constant time by scryptBlockMix's own proof.
In step 3, the address of `(V[j]'(by omega))` and the branches of the multiplication
depend on `j`, which the contract declares public: the two runs compute the
same `j`, since both compute their indices in order (`Inv3.js`) and agree on
the whole list.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_add wp_subi)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.rsi]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.rsi, hq.rcx]
theorem PubEq.vAt (i : Nat) : vAt s₀ i = vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.rsi, hq.rdx]
theorem PubEq.tP : tP s₀ = tP s₀' := by simp only [RoMix.tP, RoMix.sc, hq.r8]

end

/-- The registers the loops keep, with `rbp = bp` and `r15 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = bp
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = q

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hk _ (by decide)).trans h.rsp,
    (hk _ (by decide)).trans h.rbx, (hk _ (by decide)).trans h.rbp,
    (hk _ (by decide)).trans h.r12, (hk _ (by decide)).trans h.r13,
    (hk _ (by decide)).trans h.r14, (hk _ (by decide)).trans h.r15⟩

/-- `KR` survives instructions that write none of its registers. -/
theorem KR.upd {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) :
    KR s₀ bp q s' :=
  h.keep hrd hwr fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cs_ne hr
    exact hk r h1 h2 h3 h4 h5 h6

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- The registers `KR` fixes agree in two runs. -/
theorem KR.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, bP, bP, hq.rdi]
  · rw [h.rbp, h'.rbp, hbp]
  · rw [h.r12, h'.r12, vP, vP, hq.rdx]
  · rw [h.r13, h'.r13, sc, sc, hq.r8]
  · rw [h.r14, h'.r14, hq.rr]
  · rw [h.r15, h'.r15, hq']
  · rw [h.rsp, h'.rsp, hq.rsp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  rdi : s.gpr .rdi = A
  rsi : s.gpr .rsi = BitVec.ofNat 64 (rr s₀)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = bP s₀
  r8 : s.gpr .r8 = sc s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩
  stk : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 64
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)

theorem srcOK_t {s₀ : State} (hp : Pre s₀) : SrcOK s₀ (tP s₀) :=
  ⟨t_b hp, t_w hp, hp.stk_s.sub_right (t_sub hp), t_nw hp, Memory.InRegions.right (t_in hp)⟩

/-! ## The call -/

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixX86_64.pre (s.callEntry.withRegions [⟨A, 128 * rr s₀⟩]
      [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) ∧
    Covers ([⟨A, 128 * rr s₀⟩] ++ [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] s.wr := by
  obtain lt := r_lt hp
  exact bm_pre ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega_using [this])
    (by have := hp.s_nw; omega_using [this]) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

-- The BlockMix ROMix calls.
variable {bm : BMImpl}

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call bm.name bm.code) s (KR s₀ bp q) := by
  obtain lt := r_lt hp
  exact blockMixSpec bm s A (bP s₀) (sc s₀) (rr s₀) ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega_using [this])
    (by have := hp.s_nw; omega_using [this]) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp) _ fun _ rd wr cs _ _ => h.keep rd wr cs

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀') {A A' : Addr}
    (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A') {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call bm.name bm.code)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.rdi.symm
  have es : sc s₀' = sc s₀ := hq.r8.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  obtain call := RelCT.call (n := bm.name) (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    bm.correct bm.ct [⟨A, 128 * rr s₀⟩]
    [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [h.rsp, h'.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8,
        ha'.rdi, ha'.rsi, ha'.rdx, ha'.rcx, ha'.r8, eb, es, er, h.rsp, h'.rsp, hq.rsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## What each piece does to the registers -/

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    X86_64.Taint.Agree (Taint.ofRegs (extra ++ kRegs)) s s' :=
  Taint.agree_ofRegs fun r hr => (List.mem_append.mp hr).elim (hx r) (KR.agree hq h h' hbp hq' r)

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : Addr} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .rdi = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  obtain lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ _ h3 h4 h5 h6 => by
        rw [uf.other _ h6, ue.other _ h5, ud.other _ h4, ub.other _ h3, ua.other _ h3]
  obtain hsi : b.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ub.gpr, ua.gpr, h.r14, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega_using [])
  exact ⟨by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi],
    by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.rbx],
    by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13]⟩

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block (([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] : List Instr) ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP s₀) s' :=
  wp_mov fun a ua _ _ => wp_addi fun b ub => tail_wp hp
    (h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ h2 _ _ _ _ => by
      rw [ub.other r h2, ua.other r h2])
    (by rw [ub.gpr, ua.gpr, h.r13, sx192])

/-! ## Step 3: what each piece does to the registers -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : Addr} {s : State}
    (h : KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j := by
  obtain lt := r_lt hp
  have := hp.pos
  unfold jBlock
  refine Proof.MdStream.X86_64.wp_movm (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64))
    (ea_j hp s h.rbx h.r14)
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := bR s₀) (by simp)
          (Memory.contains_off (by omega_using [this]) (by omega_using [lt])))
    fun a ua => wp_and fun b ub => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r h1 _ _ _ _ _ => by
      rw [ub.other _ h1, ua.other _ h1]
  · rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp, jOf_eq hp, hj]

theorem m1_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) {j : Nat}
    (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) s fun s' =>
      KR s₀ bp q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀) :=
  wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => WP.block_nil
    ⟨h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ _ _ h4 h5 _ => by
      rw [ub.other _ h4, ua.other _ h5],
    by rw [ub.other _ (by decide), ua.other _ (by decide), hax],
    by rw [ub.other _ (by decide), ua.gpr, h.r12], by rw [ub.gpr, ua.other _ (by decide), h.r14]⟩

theorem mul_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) {j : Nat} (hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = vP s₀)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) :
    WP isa mulLoop s fun s' => KR s₀ bp q s' ∧ s'.gpr .rdx = vAt s₀ j :=
  WP.mono (mulLoop_ok hj hax hdx hcx) fun _ ⟨rd, wr, _, g, dx⟩ =>
    ⟨h.upd rd wr fun r h1 h2 _ h4 h5 _ => g r h1 h5 h4 h2, by rw [dx, Nat.mul_comm]⟩

theorem m2_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) (hp : Pre s₀) {j : Nat}
    (hdx : s.gpr .rdx = vAt s₀ j) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
      .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 4]) s fun s' =>
      KR s₀ bp q s' ∧ s'.gpr .rdi = bP s₀ ∧ s'.gpr .rsi = vAt s₀ j ∧ s'.gpr .r8 = tP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀) := by
  obtain lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ => wp_addi fun e ue =>
    wp_mov fun f uf _ _ => wp_shr (by decide) (by decide) fun g ug _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ug.rd, uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [ug.wr, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr]) fun r _ h2 h3 h4 _ h6 => by
        rw [ug.other _ h4, uf.other _ h4, ue.other _ h6, ud.other _ h6, ub.other _ h3, ua.other _ h2]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.gpr, ua.other _ (by decide), hdx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.gpr, ub.other _ (by decide),
      ua.other _ (by decide), h.r13, sx192]
  · rw [ug.gpr, uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega_using []

theorem xor_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) (hp : Pre s₀) {j : Nat}
    (hj : j < NN s₀) (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = vAt s₀ j)
    (hr8 : s.gpr .r8 = tP s₀) (hcx : s.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀)) :
    WP isa xorLoop s (KR s₀ bp q) := by
  obtain lt := r_lt hp
  obtain e8 : 16 * (8 * rr s₀) = 128 * rr s₀ := by omega_using []
  refine WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ j) (d := tP s₀) (n := 8 * rr s₀)
    (by have := hp.pos; omega_using [this]) (by omega_using [lt]) hdi hsi hr8 hcx
    (fun k hk => by rw [h.rd, h.wr]; exact b_word hp hk)
    (fun k hk => by rw [h.rd, h.wr]; exact Memory.InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [h.wr]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun _ ⟨rd, wr, g, _⟩ => h.upd rd wr fun r h1 h2 h3 h4 _ h6 => g r h1 h2 h3 h6 h4

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  obtain e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega_using [hi]
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Step 3, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) (hj : j < NN s₀) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 bm.name bm.code)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  obtain hi' : i < NN s₀' := hq.NN ▸ hi
  obtain hj' : j < NN s₀' := hq.NN ▸ hj
  obtain vlt := v_lt hp
  obtain hjl : j < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega_using [this])
    omega_using [hj, vlt, this]
  obtain e1 : BitVec.ofNat 64 (NN s₀ - 1) = BitVec.ofNat 64 (NN s₀' - 1) := by rw [hq.NN]
  obtain e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop := KR t₀ (BitVec.ofNat 64 (NN t₀ - 1)) (BitVec.ofNat 64 (NN t₀ - i)) t
  obtain jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  obtain m1 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j))
      (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide)).wp
      fun _ _ h => ⟨m1_wp h.1.1 h.1.2, m1_wp h.2.1 h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ml : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀')))
      mulLoop fun s s' => (K s₀ s ∧ s.gpr .rdx = vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = vAt s₀' j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax, .rdx, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ => agree_K hq h h' e1 e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ax, ax']
        · rw [dx, dx', vP, vP, hq.rdx]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ =>
        ⟨mul_wp h hjl ax dx cx, mul_wp h' hjl ax' dx' cx'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain m2 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rdx = vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = vAt s₀' j))
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
        .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 4]) fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = bP s₀ ∧ s.gpr .rsi = vAt s₀ j ∧ s.gpr .r8 = tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = bP s₀' ∧ s'.gpr .rsi = vAt s₀' j ∧ s'.gpr .r8 = tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdx] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hq.vAt])
      (by taint_decide)).wp
      fun _ _ h => ⟨m2_wp h.1.1 hp h.1.2, m2_wp h.2.1 hp' h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain xl : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = bP s₀ ∧ s.gpr .rsi = vAt s₀ j ∧ s.gpr .r8 = tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = bP s₀' ∧ s'.gpr .rsi = vAt s₀' j ∧ s'.gpr .r8 = tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (8 * rr s₀')))
      xorLoop fun s s' => K s₀ s ∧ K s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .r8, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ => agree_K hq h h' e1 e15
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [di, di', bP, bP, hq.rdi]
          · rw [si, si', hq.vAt]
          · rw [r8, r8', hq.tP]
          · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ =>
        ⟨xor_wp h hp hj di si r8 cx, xor_wp h' hp' hj' di' si' r8' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  obtain x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP s₀') s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain cl := call_rel (bm := bm) hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (NN s₀ - 1)) (q := BitVec.ofNat 64 (NN s₀ - i))
    (bp' := BitVec.ofNat 64 (NN s₀' - 1)) (q' := BitVec.ofNat 64 (NN s₀' - i))
  obtain e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.alu .sub .r15 (.imm 1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  obtain body := jb.seq (m1.seq (ml.seq (m2.seq (xl.seq ((x.seq cl).seq e)))))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok (blockMixSpec bm) hp hi h.1.1,
    step3_ok (blockMixSpec bm) hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 bm.name bm.code)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  obtain hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Fin (NN s₀)) => body3_rel_j hp hp' hq hi j.1 j.2).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  obtain e := (List.cons.inj hr').1
  exact ⟨⟨jOf s₀ s.mem, jOf_lt hp s.mem⟩, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s') (.loop (step3 bm.name bm.code) .ne)
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  obtain lp := RelCT.loop (M := isa) (body := step3 bm.name bm.code) (c := .ne)
    (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      obtain ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega_using [hn, hi], i + 1, rfl, by omega_using [hi, hl], j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

end VG.Proof.Scrypt.X86_64.RoMix
