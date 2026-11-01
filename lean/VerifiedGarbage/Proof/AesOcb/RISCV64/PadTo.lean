module

public import VerifiedGarbage.Impl.AesOcb.RISCV64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-OCB on RISCV64: padding a string (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `s4` to `W + d`: zeros, the bytes
(AES-GCM's `copyLoop`), and `0x80` after them (`padTo_ok`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/PadTo.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.AesGcm.RISCV64 (copyLoop_ok LoopPre in_left in_off)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- The 16 bytes of a block that is zero. -/
theorem bytesAt_of_zero {m : Mem} {p : Addr} (h : blockAtMem m p = 0) : bytesAt m p 16 = Spec.Ocb.zeros 16 := by
  rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt m p 16), ← toBytes_zero, ← h]; rfl

/-- The byte of `0x80`. -/
theorem setWidth_0x80 : (BitVec.ofNat 64 0x80).setWidth 8 = (0x80 : Byte) := by decide

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.t0, .t1, .a0, .a1, .a2, .a3]

/-- What `padTo d` leaves: `pad(S)` at `W + d`. -/
structure PadOut (W : Addr) (d : Nat) (v : Block) (s t : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem
  val : blockAtMem t.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ padRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `s4`, `0 < n < 16`. -/
theorem padTo_ok {W : Addr} {s : State} (hs0 : s.gpr .s0 = W) (hW : W.toNat % 8 = 0)
    (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr}
    {n d : Nat} (hn : 0 < n) (hn' : n < 16) (hd : d % 8 = 0 ∧ d + 16 ≤ 2048) (hs4 : s.gpr .s4 = S)
    (hs5 : s.gpr .s5 = BitVec.ofNat 64 n) (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s (PadOut W d (pad (bytesAt s.mem S n)) s) := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  unfold padTo
  have hA : WP isa (.block (zero16 d ++ [.addi .a1 .s0 (d : Int), Impl.AesGcm.RISCV64.mov .a0 .s4,
      Impl.AesGcm.RISCV64.mov .a2 .s5])) s fun s₂ => ∃ s₁, BlkStep W d 0 [.t0] s s₁ ∧
      s₂.gpr .a1 = W + BitVec.ofNat 64 d ∧ s₂.gpr .a0 = S ∧
      s₂.gpr .a2 = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine WP.block_append (WP.mono (zero16_ok (s := s) (d := d) hW ⟨hd.1, by omega⟩ hs0 (wW (by omega))
      (wW (by omega))) fun s₁ B₁ => ?_)
    refine wp_addi (by omega) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_mv fun t₃ u₃ => WP.block_nil ?_
    refine ⟨s₁, B₁, ?_, ?_, ?_, fun r h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, B₁.gpr _ (by decide), hs0]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide), hs4]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), hs5]
    · rw [u₃.other _ h5, u₂.other _ h3, u₁.other _ h4]
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.sp, u₂.sp, u₁.sp]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
  refine WP.seq (WP.mono hA ?_)
  rintro s₂ ⟨s₁, B₁, a1₂, a0₂, a2₂, g₂, m₂, sp₂, rd₂, wr₂⟩
  have hS₂ : Covers [⟨S, n⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hS
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact Proof.AesGcm.RISCV64.covers_off hw (by omega) (by decide)
  have hSD' : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ := hSD.sub_right (Region.sub_prefix (by omega))
  have eS : bytesAt s₂.mem S n = bytesAt s.mem S n := by
    rw [m₂]
    exact Proof.Cmac.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact bytesAt_of_zero B₁.val
  refine WP.seq (WP.mono (copyLoop_ok s₂ ⟨a0₂, a1₂, a2₂, hn, by omega, hS₂, hD₂, hSD'⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, o₃⟩ := h₃
  obtain ⟨rd₃, wr₃, sp₃⟩ := o₃.keeps
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact wW (by omega)
  refine wp_li (imm := 0x80) (by decide) fun t₁ u₁ => wp_sb (a := W + BitVec.ofNat 64 d + BitVec.ofNat 64 n)
    (by decide) (by rw [u₁.other _ (by decide), o₃.a1, BitVec.add_zero]) (by rw [u₁.wr]; exact w₃)
    fun t₂ u₂ => WP.block_nil ?_
  have hlen : (bytesAt s.mem S n).length = n := length_bytesAt _ _ _
  have mt : t₂.mem = writeBytes s₂.mem (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [(0x80 : Byte)]) := by
    rw [u₂.mem, u₁.gpr, u₁.mem, m₃, setWidth_0x80, eS, writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, by rw [u₂.sp, u₁.sp, sp₃, sp₂, B₁.sp],
    by rw [u₂.rd, u₁.rd, rd₃, rd₂, B₁.rd], by rw [u₂.wr, u₁.wr, wr₃, wr₂, B₁.wr]⟩
  · rw [mt]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega)) x hx, m₂]
    exact B₁.frame x hx
  · rw [mt, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₂]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
  · simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.gpr, u₁.other _ hr.2.1, o₃.other r hr.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2,
      g₂ r hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1, B₁.gpr r (by simp [hr.1])]

end VG.Proof.AesOcb.RISCV64
