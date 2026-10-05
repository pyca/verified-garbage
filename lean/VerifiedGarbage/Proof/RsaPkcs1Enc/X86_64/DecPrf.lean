import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecKdk

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: IRPRF

The message of block `i` (`msgCL_run`, `msgAM_run`), one block (`prf_step`),
and the loops (`clLoop_step`, `amLoop_step`): `CL = IRPRF(KDK, "length", 256)`
at `scratch + sCL` and `AM = IRPRF(KDK, "message", k)` at `scratch + sAM`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

/-- The message of block `i` of `CL`. -/
def msgCL (i : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2

theorem msgCL_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hi : i < 256) (hdi : t.gpr .rdi = sc s) (hax : t.gpr .rax = BitVec.ofNat 64 i) :
    WP isa (.block (msgBytes lengthLabel clLen)) t fun t' => Outside (sc s) sMsg 16 t.mem t'.mem ∧
      Spec.Rsa.bytesAt t'.mem (scA s sMsg) 10 = msgCL i ∧ Keep [.rdx] t t' := by
  have hs := hc.scr hp
  refine (WP.keep [.rdx] (c := .block (msgBytes lengthLabel clLen)) (Q := fun t' =>
    Outside (sc s) sMsg 16 t.mem t'.mem ∧ Spec.Rsa.bytesAt t'.mem (scA s sMsg) 10 = msgCL i) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hst : ∀ d, d + 1 ≤ scrBytes → InRegions t.wr (off (sc s) d) 1 := fun d h => hs.st8 h
  simp only [msgBytes, lengthLabel, clLen, putByte, List.zipIdx, List.flatMap, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil, Nat.reduceAdd, sMsg]
  xrun [ea_atd (p := sc s), hdi, hax, hst 1024 (by decide), hst 1025 (by decide), hst 1026 (by decide), hst 1027 (by decide), hst 1028 (by decide), hst 1029 (by decide), hst 1030 (by decide), hst 1031 (by decide), hst 1032 (by decide), hst 1033 (by decide)]
  refine ⟨?_, ?_⟩
  · repeat (first | exact Outside.refl _ _ _ _ | refine Outside.wb ?_ _ (by decide) (by decide) (by decide))
  · simp only [Spec.Rsa.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, scA, off_add,
      Nat.reduceAdd]
    simp (disch := decide) only [byte_wb, byte_wb_self]
    simp only [msgCL, i2osp_two, Spec.RsaPkcs1Enc.ascii, Nat.div_eq_of_lt hi]
    rw [show BitVec.setWidth 8 (BitVec.ofNat 64 i) = BitVec.ofNat 8 i from
      BitVec.eq_of_toNat_eq (by simp)]
    rfl


/-- The message of block `i` of `AM`, for a modulus of `k` bytes. -/
def msgAM (k i : Nat) : List Byte :=
  Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * k) 2

theorem msgAM_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i : Nat} (hi : i < 256) (hdi : t.gpr .rdi = sc s) (hax : t.gpr .rax = BitVec.ofNat 64 i)
    (h9 : t.gpr .r9 = s.gpr .r8) :
    WP isa (.block (msgBytes messageLabel amLen)) t fun t' => Outside (sc s) sMsg 16 t.mem t'.mem ∧
      Spec.Rsa.bytesAt t'.mem (scA s sMsg) 11 = msgAM (kOf s) i ∧ Keep [.rdx] t t' := by
  have hs := hc.scr hp
  have hf := hc.frm hp
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  refine (WP.keep [.rdx] (c := .block (msgBytes messageLabel amLen)) (Q := fun t' =>
    Outside (sc s) sMsg 16 t.mem t'.mem ∧ Spec.Rsa.bytesAt t'.mem (scA s sMsg) 11 = msgAM (kOf s) i) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hst : ∀ d, d + 1 ≤ scrBytes → InRegions t.wr (off (sc s) d) 1 := fun d h => hs.st8 h
  simp only [msgBytes, messageLabel, amLen, putByte, List.zipIdx, List.flatMap, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil, Nat.reduceAdd, sMsg]
  xrun [ea_atd (p := sc s), hdi, hax, h9, hst 1024 (by decide), hst 1025 (by decide), hst 1026 (by decide), hst 1027 (by decide), hst 1028 (by decide), hst 1029 (by decide), hst 1030 (by decide), hst 1031 (by decide), hst 1032 (by decide), hst 1033 (by decide), hst 1034 (by decide)]
  refine ⟨?_, ?_⟩
  · repeat (first | exact Outside.refl _ _ _ _ | refine Outside.wb ?_ _ (by decide) (by decide) (by decide))
  · simp only [Spec.Rsa.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, scA, off_add,
      Nat.reduceAdd]
    simp (disch := decide) only [byte_wb, byte_wb_self]
    simp only [msgAM, i2osp_two, Spec.RsaPkcs1Enc.ascii, Nat.div_eq_of_lt hi]
    have hx : (s.gpr .r8).toNat = kOf s := rfl
    rw [show BitVec.setWidth 8 (BitVec.ofNat 64 i) = BitVec.ofNat 8 i from BitVec.eq_of_toNat_eq (by simp),
      show BitVec.setWidth 8 ((s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8) +
          (s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8))) >>> 8) = BitVec.ofNat 8 (8 * kOf s / 256) from
        BitVec.eq_of_toNat_eq (by
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.shiftRight_eq_div_pow, hx]; omega),
      show BitVec.setWidth 8 (s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8) +
          (s.gpr .r8 + s.gpr .r8 + (s.gpr .r8 + s.gpr .r8))) = BitVec.ofNat 8 (8 * kOf s) from
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, hx]; omega)]
    rfl

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
