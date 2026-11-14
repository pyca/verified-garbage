module

import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Scrypt.X86_64.Common
public import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit

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
