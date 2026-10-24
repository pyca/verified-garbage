module

public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-OCB on PPC64LE: padding a string (`padTo`)

Untrusted: everything here is checked by Lean. `padTo d` writes `pad(S)`
(§4.1) of the `n < 16` bytes `S` at `r24` to `W + d`: zeros, the bytes
(AES-GCM's `copyLoop`), and `0x80` after them (`padTo_ok`). As on AArch64
(`Proof/AesOcb/AArch64/PadTo.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem pad)
open VG.Proof.AesGcm.PPC64LE (copyLoop_ok LoopPre in_left in_off)
open VG.Proof.Ocb (length_bytesAt bytesAt_writeBytes_base)
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li wp_stb)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or

theorem contains_pre (p : Addr) {j n : Nat} (h : j ≤ n) : (⟨p, n⟩ : Region).Contains p j := by
  simpa using Offset.contains_base p (d := 0) (n := j) (k := n) (by omega) (by decide)

theorem toBytes_zero : Spec.Ocb.toBytes 0 = Spec.Ocb.zeros 16 := by decide

/-- The 16 bytes of a block that is zero. -/
theorem bytesAt_of_zero {m : Mem} {p : Addr} (h : blockAtMem m p = 0) : bytesAt m p 16 = Spec.Ocb.zeros 16 := by
  rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt m p 16), ← toBytes_zero, ← h]; rfl

/-- The byte of `0x80`. -/
theorem setWidth_0x80 : (BitVec.ofNat 64 0x80).setWidth 8 = (0x80 : Byte) := by decide

/-- The registers `padTo` writes. -/
abbrev padRegs : List Reg := [.r0, .r3, .r4, .r5, .r6]

/-- What `padTo d` leaves: `pad(S)` at `W + d`. -/
structure PadOut (W : Addr) (d : Nat) (v : Block) (s t : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem t.mem
  val : blockAtMem t.mem (W + BitVec.ofNat 64 d) = v
  gpr : ∀ r, r ∉ padRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  lr : t.lr = s.lr
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- `padTo d`: `W + d ← pad(S)`, for the `n` bytes `S` at `r24`, `0 < n < 16`. -/
theorem padTo_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {S : Addr}
    {n d : Nat} (hn : 0 < n) (hn' : n < 16) (hd : d % 4 = 0 ∧ d + 16 ≤ 2560) (h24 : s.gpr .r24 = S)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 n) (hS : Covers [⟨S, n⟩] (s.rd ++ s.wr))
    (hSD : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩) :
    WP isa (padTo d) s (PadOut W d (pad (bytesAt s.mem S n)) s) := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  unfold padTo
  have hA : WP isa (.block (zero16 d ++ [.addi .r4 .r31 d, Impl.AesGcm.PPC64LE.mov .r3 .r24,
      Impl.AesGcm.PPC64LE.mov .r5 .r25])) s fun s₂ => ∃ s₁, BlkStep W d 0 [.r0] s s₁ ∧
      s₂.gpr .r4 = W + BitVec.ofNat 64 d ∧ s₂.gpr .r3 = S ∧
      s₂.gpr .r5 = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.lr = s₁.lr ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine WP.block_append (WP.mono (zero16_ok (s := s) (d := d) ⟨hd.1, by omega⟩ h31 (wW (by omega))
      (wW (by omega))) fun s₁ B₁ => ?_)
    refine wp_addi (by decide) (by omega) fun t₁ u₁ => cwp_or fun t₂ u₂ => cwp_or fun t₃ u₃ => WP.block_nil ?_
    refine ⟨s₁, B₁, ?_, ?_, ?_, fun r h3 h4 h5 => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, B₁.gpr _ (by decide), h31]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), BitVec.or_self, B₁.gpr _ (by decide), h24]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), BitVec.or_self, B₁.gpr _ (by decide), h25]
    · rw [u₃.other _ h5, u₂.other _ h3, u₁.other _ h4]
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.sp, u₂.sp, u₁.sp]
    · rw [u₃.lr, u₂.lr, u₁.lr]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
  refine WP.seq (WP.mono hA ?_)
  rintro s₂ ⟨s₁, B₁, r4₂, r3₂, r5₂, g₂, m₂, sp₂, lr₂, rd₂, wr₂⟩
  have hS₂ : Covers [⟨S, n⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂, B₁.rd, B₁.wr]; exact hS
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s₂.wr := by
    rw [wr₂, B₁.wr]; exact Proof.AesGcm.PPC64LE.covers_off hw (by omega) (by decide)
  have hSD' : (⟨S, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ := hSD.sub_right (Region.sub_prefix (by omega))
  have eS : bytesAt s₂.mem S n = bytesAt s.mem S n := by
    rw [m₂]
    exact Proof.Cmac.bytesAt_frame B₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hSD) (by omega)
  have z₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 d) 16 = Spec.Ocb.zeros 16 := by
    rw [m₂]; exact bytesAt_of_zero B₁.val
  refine WP.seq (WP.mono (copyLoop_ok s₂ ⟨r3₂, r4₂, r5₂, hn, by omega, hS₂, hD₂, hSD'⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, o₃⟩ := h₃
  obtain ⟨rd₃, wr₃, sp₃, lr₃⟩ := o₃.keeps
  have w₃ : InRegions s₃.wr (W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) 1 := by
    rw [wr₃, wr₂, B₁.wr, Offset.add_add]; exact wW (by omega)
  refine wp_li (by decide) fun t₁ u₁ => wp_stb (a := W + BitVec.ofNat 64 d + BitVec.ofNat 64 n) (by decide)
    (by decide) (by rw [u₁.other _ (by decide), o₃.r4, BitVec.add_zero]) (by rw [u₁.wr]; exact w₃)
    fun t₂ u₂ => WP.block_nil ?_
  have hlen : (bytesAt s.mem S n).length = n := length_bytesAt _ _ _
  have mt : t₂.mem = writeBytes s₂.mem (W + BitVec.ofNat 64 d) (bytesAt s.mem S n ++ [(0x80 : Byte)]) := by
    rw [u₂.mem, u₁.gpr, u₁.mem, m₃, setWidth_0x80, eS, writeBytes_snoc _ _ _ _ (by omega), hlen]
  refine ⟨?_, ?_, fun r hr => ?_, by rw [u₂.sp, u₁.sp, sp₃, sp₂, B₁.sp], by rw [u₂.lr, u₁.lr, lr₃, lr₂, B₁.lr],
    by rw [u₂.rd, u₁.rd, rd₃, rd₂, B₁.rd], by rw [u₂.wr, u₁.wr, wr₃, wr₂, B₁.wr]⟩
  · rw [mt]
    intro x hx
    rw [writeBytes_frame _ _ _ (by simp [hlen]; exact contains_pre _ (by omega)) x hx, m₂]
    exact B₁.frame x hx
  · rw [mt, blockAtMem, bytesAt_writeBytes_base _ _ _ (by simp [hlen]; omega) (by decide), z₂]
    simp only [pad, hlen, List.length_append, List.length_singleton, Spec.Ocb.zeros, List.drop_replicate,
      List.append_assoc, List.singleton_append, show 16 - (n + 1) = 15 - n by omega]
  · simp only [padRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.gpr, u₁.other _ hr.1, o₃.other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2,
      g₂ r hr.2.1 hr.2.2.1 hr.2.2.2.1, B₁.gpr r (by simp [hr.1])]

end VG.Proof.AesOcb.PPC64LE
