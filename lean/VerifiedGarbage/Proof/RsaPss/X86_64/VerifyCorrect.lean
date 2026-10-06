import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyPadding

/-! # RSASSA-PSS verification: the public operation and padding check -/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem vmain_done (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {pubN : String} {pubC : Prog isa}
    (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s')
    (hspC : SpSafe pubC) (hdC : pubC.x86_64Depth = 0)
    {s u : State} (hp : VPre lk.G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 3)) (R : Rep u.mem (fb s) (stackArg s 3) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r) (hM : Frame (vwrR s) s.mem u.mem)
    {lo z : Nat} {fixed : Bool}
    (h17 : W 17 = s.gpr .rsi) (h18 : W 18 = s.gpr .rdi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h25 : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z))
    (h26 : W 26 = BitVec.ofNat 64 lo) (h35 : W 35 = if fixed then 0 else 1) (h36 : W 36 = stackArg s 1)
    (h37 : W 37 = s.gpr .r8) (h38 : W 38 = s.gpr .r9) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12)
    (hlo : lo ≤ 1) (hfit : H.D + 2 ≤ (s.gpr .rsi).toNat - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - lo - (H.D + 2)))
    (hspec : verifyOut lk.G s = true ↔ (lo = 1 → (vx s).getD 0 0 = 0) ∧
      EncOk lk.G (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len) ((vx s).drop lo) ((s.gpr .rsi).toNat - lo) z
        (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32)))
    (hsl : Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32) =
      if fixed then some (stackArg s 1).toNat else none) :
    WP isa (verifyMain H pubN pubC) u (VDone lk.G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hG := validG hH lk.hash lk.len
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  rw [verifyMain, show [Code.block dbSlots, .block pubArgs, .call pubN pubC, .block acc0, mgfXor H, .block clearTop,
      posScan, posCheck H, clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H] =
    [Code.block dbSlots, .block pubArgs, .call pubN pubC] ++ [.block acc0, mgfXor H, .block clearTop, posScan,
      posCheck H, clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H] from rfl]
  -- The public-key operation.
  refine WP.seqs_append (by simp) (by simp) (WP.mono (vfront_ok hv hspC hdC hp L R hw hrd hM h17 h18 h19 h20 h22
    h26 h38 hax) fun u3 ⟨L3, wr3, rd3, cs3, hM3, V1, W1, R1, hW1, h23, h24, hV1, hO1⟩ => ?_)
  have hxl : (vx s).length = (s.gpr .rsi).toNat := by
    unfold vx
    cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat) with
    | none => simp only [Option.getD_none, RsaPss.zeros_length]
    | some y => rw [Option.getD_some, publicOpChecked_length' hpo, bytesAt_length]
  have g1 : ∀ j, j < nW → 4 ≤ j → j ≠ 23 → j ≠ 24 → W1 j = W j := fun j a b c d => hW1 j a b c d
  refine WP.mono (vpadding_done hH K lk hp L3 R1 (wr3.trans hw) (rd3.trans hrd)
    (fun r hr => (cs3 r hr).trans (hcs r hr)) hM3 (vx s) hxl hV1
    (by rw [g1 17 (by decide) (by decide) (by decide) (by decide), h17]) h23
    (by rw [h24]; congr 1; omega)
    (by rw [g1 25 (by decide) (by decide) (by decide) (by decide), h25])
    (by rw [g1 26 (by decide) (by decide) (by decide) (by decide), h26])
    (by rw [g1 35 (by decide) (by decide) (by decide) (by decide), h35])
    (by rw [g1 36 (by decide) (by decide) (by decide) (by decide), h36])
    (by rw [g1 37 (by decide) (by decide) (by decide) (by decide), h37])
    (by rw [g1 41 (by decide) (by decide) (by decide) (by decide), h41])
    (by rw [g1 42 (by decide) (by decide) (by decide) (by decide), h42])
    (by rw [g1 43 (by decide) (by decide) (by decide) (by decide), h43]) hlo hfit hspec hsl)
    fun _ h => ⟨h.L, h.wr, h.cs, h.rbx, h.rbp, h.r12, h.out⟩

end VG.Proof.RsaPss.X86_64
