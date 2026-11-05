module

public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-!
# EMSA-PSS's encoding and its check on AArch64: their frames

`encode` and `checkEncoding` push their frame (21 units of 16 bytes); the
functions they call through the table of `MdHash` push at most one frame
(`FnsD`), and MGF1 its own frame (17 units) around the calls of the
functions of the table of `Hash`, which push at most one: their depth is at
most 39 (`encode_depth`, `chk_depth`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- The functions the calls through the tables may reach push at most one
frame. -/
structure FnsD (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) : Prop where
  init : ∀ q ∈ f.init, q.2.aarch64Depth ≤ 1
  comp : ∀ q ∈ f.comp, q.2.aarch64Depth ≤ 1
  dig : ∀ q ∈ f.dig, q.2.aarch64Depth ≤ 1
  gi : ∀ q ∈ g.init, q.2.aarch64Depth ≤ 1
  gu : ∀ q ∈ g.upd, q.2.aarch64Depth ≤ 1
  gf : ∀ q ∈ g.fin, q.2.aarch64Depth ≤ 1

theorem icalls_depth {i : Instr} {ts : List (String × Prog isa)} {n : Nat} (h : ∀ q ∈ ts, q.2.aarch64Depth ≤ n) :
    (Code.icalls i ts).aarch64Depth ≤ n := by
  induction ts with
  | nil => simp [Code.icalls, Code.aarch64Depth]
  | cons q ts ih =>
    simp only [Code.icalls, Code.aarch64Depth, Nat.max_le]
    exact ⟨h q List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

variable {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} (hd : FnsD f g) (H : Hash)
include hd

theorem encode_depth : (encode f H g).aarch64Depth ≤ 39 := by
  have hi := icalls_depth (i := .blr .x16) hd.init
  have hc := icalls_depth (i := .blr .x16) hd.comp
  have hdg := icalls_depth (i := .blr .x16) hd.dig
  have gi := icalls_depth (i := .blr .x16) hd.gi
  have gu := icalls_depth (i := .blr .x16) hd.gu
  have gf := icalls_depth (i := .blr .x16) hd.gf
  simp only [encode, encBody, encMain, ret0, copyOut, signEnc, Code.aarch64Depth, seqs, clearY, copyDigest, copySaltY,
    ctHash, ctHashWith, clearEm, putSalt, putH, mgfXor, Impl.RsaPkcs1Sig.AArch64.copyLoop, Instr.frameUnits,
    frameBytes, ctInit, compLoop, compT, scall, pad80, lenLoop, digestOut, select, Impl.RsaPkcs1Sig.AArch64.psLoop,
    Impl.RsaOaep.AArch64.Mgf1.Table.mgfXor, Impl.RsaOaep.AArch64.Mgf1.Table.round, Impl.RsaOaep.AArch64.Mgf1.seqs,
    Impl.RsaOaep.AArch64.Mgf1.Table.tcall, Impl.RsaOaep.AArch64.Mgf1.Table.xorOut, mgfFrame,
    Impl.RsaOaep.AArch64.frameBytes]
  omega

theorem chk_depth : (checkEncoding f H g).aarch64Depth ≤ 39 := by
  have hi := icalls_depth (i := .blr .x16) hd.init
  have hc := icalls_depth (i := .blr .x16) hd.comp
  have hdg := icalls_depth (i := .blr .x16) hd.dig
  have gi := icalls_depth (i := .blr .x16) hd.gi
  have gu := icalls_depth (i := .blr .x16) hd.gu
  have gf := icalls_depth (i := .blr .x16) hd.gf
  simp only [checkEncoding, chkBody, chkMain, ret0, copyIn, expLen, Code.aarch64Depth, seqs, mgfXor,
    Impl.RsaPkcs1Sig.AArch64.copyLoop, Instr.frameUnits, frameBytes, ctInit, pad80, lenLoop, digestOut,
    compT, scall, select, compLoop, ctHash, ctHashWith, posScan, posCheck, FixedSalt.select,
    FixedSalt.finish, FixedSalt.copySalt, clearY, copyDigest, copyDb, shift, shiftPass, cmpH,
    Impl.RsaOaep.AArch64.Mgf1.Table.mgfXor, Impl.RsaOaep.AArch64.Mgf1.Table.round, Impl.RsaOaep.AArch64.Mgf1.seqs,
    Impl.RsaOaep.AArch64.Mgf1.Table.tcall, Impl.RsaOaep.AArch64.Mgf1.Table.xorOut, mgfFrame,
    Impl.RsaOaep.AArch64.frameBytes]
  omega

end VG.Proof.RsaPss.AArch64
