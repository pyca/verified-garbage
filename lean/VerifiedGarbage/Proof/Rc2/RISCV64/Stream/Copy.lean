module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Rc2.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops

/-!
# Streaming RC2-CBC on RISCV64: the byte copy

`copy src dst dd cnt` writes the `cnt` bytes at `src` to `dst + dd`
(`writeBytes`), advancing `src` and `dst` by the count (`copy_run`).
-/

@[expose] public section

namespace VG.Proof.Rc2.RISCV64.Stream

open VG VG.RISCV64 VG.Impl.Rc2.RISCV64.Stream
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

/-- The registers the copy uses: distinct, and none `a7`. -/
structure Regs (src dst cnt : Reg) : Prop where
  sd : src ≠ dst
  sc : src ≠ cnt
  dc : dst ≠ cnt
  s0 : src ≠ .a7
  d0 : dst ≠ .a7
  c0 : cnt ≠ .a7

/-- After `j` of the `k` bytes from `A` to `B`, from `s₀`. -/
structure CopyI (s₀ : State) (src dst cnt : Reg) (A B : Addr) (k j : Nat) (s : State) : Prop where
  psrc : s.gpr src = A + BitVec.ofNat 64 j
  pdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 j
  pcnt : s.gpr cnt = BitVec.ofNat 64 (k - j)
  keep : Keep [.a7, src, dst, cnt] s₀ s
  mem : s.mem = writeBytes s₀.mem B ((Spec.Rc2.bytesAt s₀.mem A k).take j)

/-- What the copy leaves. -/
structure CopyPost (s₀ : State) (src dst cnt : Reg) (A B : Addr) (k : Nat) (s : State) : Prop where
  psrc : s.gpr src = A + BitVec.ofNat 64 k
  pdst : s.gpr dst = s₀.gpr dst + BitVec.ofNat 64 k
  keep : Keep [.a7, src, dst, cnt] s₀ s
  mem : s.mem = writeBytes s₀.mem B (Spec.Rc2.bytesAt s₀.mem A k)

theorem CopyI.post {s₀ s : State} {src dst cnt : Reg} {A B : Addr} {k : Nat}
    (h : CopyI s₀ src dst cnt A B k k s) : CopyPost s₀ src dst cnt A B k s := by
  refine ⟨h.psrc, h.pdst, h.keep, ?_⟩
  rw [h.mem, List.take_of_length_le (by simp [Spec.Rc2.bytesAt])]

theorem lo8_ext' (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq b)

theorem body_run {src dst cnt : Reg} (hr : Regs src dst cnt) {dd : Nat} (hdd : dd < 2048) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr src) 1) (hout : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 dd) 1) :
    WP isa (.block (copyBody src dst dd cnt)) s fun t =>
      t.gpr src = s.gpr src + 1#64 ∧ t.gpr dst = s.gpr dst + 1#64 ∧ t.gpr cnt = s.gpr cnt - 1#64 ∧
      t.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 dd) (s.mem (s.gpr src)) ∧ Keep [.a7, src, dst, cnt] s t := by
  have := hr.sd; have := hr.sc; have := hr.dc; have := hr.s0; have := hr.d0; have := hr.c0
  refine WP.mono (WP.keep [.a7, src, dst, cnt] (c := .block (copyBody src dst dd cnt)) (Q := fun t =>
      t.gpr src = s.gpr src + 1#64 ∧ t.gpr dst = s.gpr dst + 1#64 ∧ t.gpr cnt = s.gpr cnt - 1#64 ∧
      t.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 dd) (s.mem (s.gpr src))) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, copyBody, dstOf]) rfl) fun t ⟨⟨a, b, c, d⟩, e⟩ => ⟨a, b, c, d, e⟩
  unfold copyBody
  rrun [hin, hout, hdd, Ne.symm hr.sd, Ne.symm hr.sc, Ne.symm hr.dc, Ne.symm hr.s0, Ne.symm hr.d0,
    Ne.symm hr.c0, hr.sd, hr.sc, hr.dc, hr.s0, hr.d0, hr.c0, lo8_ext']

/-- Copying `k` bytes from `A = src` to `B = dst + dd`, when they may be read
and written and do not overlap. -/
theorem copy_run {src dst cnt : Reg} (hr : Regs src dst cnt) {dd : Nat} (hdd : dd < 2048) {s₀ : State}
    {A B : Addr} {k : Nat} (hA : s₀.gpr src = A) (hB : s₀.gpr dst + BitVec.ofNat 64 dd = B)
    (hk : s₀.gpr cnt = BitVec.ofNat 64 k) (hk' : k < 2 ^ 64)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (B + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨A, k⟩ ⟨B, k⟩) :
    WP isa (copy src dst dd cnt) s₀ (CopyPost s₀ src dst cnt A B k) := by
  have hI₀ : CopyI s₀ src dst cnt A B k 0 s₀ :=
    ⟨by rw [hA]; simp, by simp, by rw [hk, Nat.sub_zero], Keep.refl _ _, by rw [List.take_zero, writeBytes_nil]⟩
  unfold copy
  refine WP.ite (decide (k = 0)) (by rw [Steps.eval_zero, hk, Steps.ofNat_beq_zero hk'])
    (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have e : k = 0 := of_decide_eq_true hb
    subst e
    exact hI₀.post
  have hk0 : k ≠ 0 := of_decide_eq_false hb
  refine WP.mono (countLoop _ cnt (CopyI s₀ src dst cnt A B k) k (fun j hj s h => ?_) 0 (by omega) s₀ hI₀)
    fun s h => h.post
  have hbyte : s.mem (A + BitVec.ofNat 64 j) = s₀.mem (A + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (R := ⟨B, k⟩)
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add,
        List.length_take, Spec.Rc2.bytesAt, List.length_map, List.length_range]; omega)).bytes
      (R := ⟨A, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  have hdst' : s.gpr dst + BitVec.ofNat 64 dd = B + BitVec.ofNat 64 j := by
    rw [h.pdst, ← hB, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)]
  refine WP.mono (body_run hr hdd s (by rw [h.psrc, h.keep.2.1, h.keep.2.2]; exact hsrc j hj)
    (by rw [hdst', h.keep.2.2]; exact hdst j hj)) fun t ⟨a, b, c, m, kk⟩ => ⟨⟨?_, ?_, ?_, (h.keep.trans kk).mono
      (by simp), ?_⟩, ?_⟩
  · rw [a, h.psrc, Offset.add_add]
  · rw [b, h.pdst, Offset.add_add]
  · rw [c, h.pcnt, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · have hj' : j < (Spec.Rc2.bytesAt s₀.mem A k).length := by simp [Spec.Rc2.bytesAt]; omega
    have hl : (List.take j (Spec.Rc2.bytesAt s₀.mem A k)).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [m, hdst', h.psrc, hbyte, h.mem, List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl]
    congr 1
    simp [Spec.Rc2.bytesAt]
  · rw [c, h.pcnt, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub, ofNat_bne_zero' (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.Rc2.RISCV64.Stream
