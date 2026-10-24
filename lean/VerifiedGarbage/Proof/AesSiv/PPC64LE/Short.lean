module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.S2v
import VerifiedGarbage.Proof.CmacAes.PPC64LE.FinSteps
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT

/-!
# AES-SIV on PPC64LE: finishing S2V with a string shorter than a block

Untrusted: everything here is checked by Lean. For a last string `P` of
`L < 16` bytes, `shortTail` zeroes the tail at `W + 32`, copies `P` into it
and puts `0x80` after it, so the tail is `pad(P)`, doubles `D` into
`W + 256` and XORs it into the tail (`shortTail_wp`); `shortMac` computes
the CMAC of the tail, one complete block, into `W + out` (`shortMac_wp`),
which is S2V's end (`Siv.s2vFinish_short`, `short_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE VG.WriteBytes
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.Gather.PPC64LE (copyBytes)
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_add wp_stb)
open VG.Proof.CmacAes.Stream.PPC64LE (FArgs)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.Gather.PPC64LE (BytesPre copyBytes_wp Keeps)
open VG.Spec.Aes (bytesAt)

/-- What S2V's end writes: `wR` and its result at `W + out`. -/
abbrev oR (c : Cx) (out : Nat) : List Region := ⟨c.W + BitVec.ofNat 64 out, 16⟩ :: wR c

theorem frame_oR {c : Cx} {m m' : Mem} (out : Nat) (h : Frame (wR c) m m') : Frame (oR c out) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem copyRegs_keep : ∀ r ∈ keepRegs, r ∉ VG.Proof.Gather.PPC64LE.copyRegs := by decide

theorem PK.ofKeeps {s t : State} (h : Keeps s t) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (copyRegs_keep r hr)⟩

/-- The tail after the copy: `P` on zeros. -/
abbrev copiedMem (m : Mem) (W : Addr) (xs : List Byte) : Mem :=
  writeBytes (Proof.Cmac.zero2 m (W + BitVec.ofNat 64 tailO)) (W + BitVec.ofNat 64 tailO) xs

/-- `P` copied onto the zeroed tail, if it is not empty. -/
theorem shortCopy_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n : Nat} (hP : Buf c s P n)
    (hn : n < 16) (h19 : s.gpr .r19 = P) (h20 : s.gpr .r20 = BitVec.ofNat 64 n) :
    WP isa (.seq (.block (Impl.AesCcm.PPC64LE.zero16 tailO))
      (.ite (.zero .d .r20) (.block []) (.seq (.block [mov .r3 .r19, .addi .r9 .r14 tailO, mov .r4 .r20])
        copyBytes))) s fun s' => PK s s' ∧ s'.gpr .r20 = s.gpr .r20 ∧
      s'.mem = copiedMem s.mem c.W (bytesAt s.mem P n) := by
  have ww := L.ww
  refine WP.seq (zero16_wp E (d := tailO) (is := []) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ =>
    WP.block_nil ?_)
  show WP isa _ s₁ _
  have h20₁ : s₁.gpr .r20 = BitVec.ofNat 64 n := by rw [g₁ _ (by decide), h20]
  have pmem : bytesAt s₁.mem P n = bytesAt s.mem P n := by
    rw [m₁]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega)
  refine WP.ite (decide (n = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h20₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨pk₁, by rw [h20₁, h20], ?_⟩
    rw [m₁]; simp [bytesAt, writeBytes_nil]
  · have h0 : n ≠ 0 := by simpa using hf
    have E₁ := E.of_pk pk₁
    have A : WP isa (.block [mov .r3 .r19, .addi .r9 .r14 tailO, mov .r4 .r20]) s₁ fun s₄ => PK s₁ s₄ ∧
        s₄.mem = s₁.mem ∧ s₄.gpr .r20 = s₁.gpr .r20 ∧ BytesPre s₄ P (c.W + BitVec.ofNat 64 tailO) n := by
      refine wp_mv fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ =>
        WP.block_nil ⟨(PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)),
          by rw [u₄.mem, u₃.mem, u₂.mem], by rw [u₄.other _ (by decide), u₃.other _ (by decide),
            u₂.other _ (by decide)], ?_⟩
      exact ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide), h19],
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), E₁.r14],
        by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h20₁], by omega, by omega,
        by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact (hP.of_eq pk₁.rd pk₁.wr).rd,
        by rw [u₄.wr, u₃.wr, u₂.wr]; exact Proof.Gather.PPC64LE.covers_prefix (E₁.perm.wC (d := tailO) (n := 16)
          (by decide)) (by omega),
        (hP.wd (d := tailO) (k := 16) (by decide)).sub_right (Region.sub_prefix (by omega))⟩
    refine WP.seq (WP.mono A fun s₄ ⟨pk₄, m₄, r20₄, hb⟩ => WP.mono (copyBytes_wp s₄ hb) fun s₅ ⟨m₅, _, k₅⟩ =>
      ⟨pk₁.trans (pk₄.trans (PK.ofKeeps k₅)), by rw [k₅.gpr .r20 (by decide), r20₄, h20₁, h20], ?_⟩)
    rw [m₅, m₄, pmem, m₁]

end VG.Proof.AesSiv.PPC64LE
