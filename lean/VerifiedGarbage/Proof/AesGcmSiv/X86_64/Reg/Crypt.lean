module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Polyval
public import VerifiedGarbage.Proof.GcmSiv.Ctr
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Chunk
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV in registers on x86-64: the tag and counter mode

Untrusted: everything here is checked by Lean. `tag_ok`: the tag input from
POLYVAL's result in `xmm2`, encrypted and stored. `crypt_ok`: the data XORed
with the keystream of the counter blocks from the tag, the counter in `xmm9`.
-/

-- separate module: the tag and counter mode, apart from POLYVAL's algebra

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO bO skO roundsO nonceO tagO dataO lenO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Impl.Aes.X86_64.AesNi (aes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc punpck_movq writeW128_app readW128_app le16 le16_readW le16_xor
  bytesAt_writeW128 ctrX paddd_one counterBlock_store)
open VG.Proof.AesGcm.X86_64 (in_off ofNat_add_ofNat bytesAt_frame)
open VG.Proof.Aes.X86_64.AesNi (st getD_st getD_ofFn st_ext st_toList aes_ok Keys XFrame)
open VG.Proof.Cmac (le8 le4)

/-! ## Registers as bytes -/

theorem le16_st (v : BitVec 128) : (st v).toList = le16 v := by
  rw [st_toList]; rfl

theorem st_le16 (v : BitVec 128) : (Vector.ofFn fun i : Fin 16 => (le16 v).getD i 0) = st v := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_ofFn hi]
  simp [le16, hi, byte]

/-- `CIPH_K` of the bytes of `x`, from the register `r` that AES of `x` left. -/
theorem aesWith_le16 (nr : Nat) (w : List Byte) (x r : BitVec 128) (h : st r = Spec.Aes.cipher nr w (st x)) :
    Spec.GcmSiv.aesWith nr w (le16 x) = le16 r := by
  rw [Spec.GcmSiv.aesWith, st_le16, ← h, le16_st]

/-- The bytes of two quadwords. -/
theorem le16_app (hi lo : BitVec 64) : le16 (hi ++ lo) = le8 lo ++ le8 hi := by
  rw [← bytesAt_writeW128 (fun _ => 0) 0 (hi ++ lo), writeW128_app, Proof.Cmac.bytesAt_store2]

/-- The high quadword, shifted down and moved out. -/
theorem hi64 (v : BitVec 128) : (XShiftOp.eval .psrldq v 8).extractLsb' 0 64 = qword v 1 := by
  rw [show XShiftOp.eval .psrldq v 8 = v >>> 64 from rfl]
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight, qword, Nat.zero_add]

/-! ## The tag -/

/-- `aes`'s keys for the schedule at `W + 248`. -/
theorem keysW {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    (hdi : t.gpr .rdi = W + BitVec.ofNat 64 248) :
    Keys R (bytesAt t.mem (W + BitVec.ofNat 64 248) (16 * (R + 1))) t := by
  refine ⟨by rw [hdi], by omega_arith, fun j hj => ?_⟩
  rw [hdi, Proof.Aes.X86_64.AesNi.ofInt_natCast, add_ofNat_assoc]
  exact E.perm.wR (by omega_arith)

/-- What `tag o` leaves: the tag at `W + o`. -/
structure TagPost (K W SP : Addr) (R o : Nat) (N : Addr) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨W + BitVec.ofNat 64 o, 16⟩] t.mem t'.mem
  out : bytesAt t'.mem (W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R
      (GcmSiv.tagOf (Spec.GcmSiv.toBytes (t.xmm .xmm2)) (bytesAt t.mem N 12))

theorem tagIn_run {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hN : Buf K W SP t N 12) :
    ∃ t₁ : State, runBlock isa (tagIn ++ aesArgs (ptr .rdi .r15 skO)) t = some t₁ ∧
      le16 (t₁.xmm .xmm0) = GcmSiv.tagOf (Spec.GcmSiv.toBytes (t.xmm .xmm2)) (bytesAt t.mem N 12) ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .r10 = W + BitVec.ofNat 64 248 + BitVec.ofNat 64 (16 * R) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r := by
  have h15 := E.r15
  have rR := S.rounds
  have rN := S.nonce
  have rr := E.perm.wR (show 200 + 8 ≤ 488 by decide)
  have rn := E.perm.wR (show 208 + 8 ≤ 488 by decide)
  obtain n₀ : InRegions (t.rd ++ t.wr) N 8 := by
    simpa using in_off (d := 0) (n := 8) hN.rd (by decide) (by decide)
  obtain n₈ := in_off (d := 8) (n := 4) hN.rd (by decide) (by decide)
  refine ⟨_, by xrun [tagIn, aesArgs, lastKey, skO, roundsO, nonceO, h15, rR, rN, rr, rn, n₀, n₈], ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      mem_setReg, mem_arithFlags, mem_setXmm, mem_setFlags, punpck_movq, h15, rN, nonceO, ne_eq, not_false_eq_true]
    rw [le16_app, hi64, show (t.xmm .xmm2).extractLsb' 0 64 = qword (t.xmm .xmm2) 0 from rfl]
    conv_rhs => rw [Proof.Gcm.X86_64.Pclmul.qwords (t.xmm .xmm2)]
    rw [GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le8_readW,
      ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words]
    rfl
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15, skO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, rR, roundsO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, rR, roundsO, skO, execShift]
    rw [BitVec.add_comm]; congr 1; rcases hR with rfl | rfl <;> decide
  · rfl
  · rfl
  · rfl
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]

theorem tag_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hN : Buf K W SP t N 12) {o : Nat}
    (ho : o = 0 ∨ o = 128) : WP isa (tag o) t (TagPost K W SP R o N t) := by
  have hw := L.ww
  obtain ⟨t₁, run₁, x0, rdi, rsi, r10, m₁, rd₁, wr₁, g₁⟩ := tagIn_run hR E S hN
  have E₁ : Env K W SP t₁ := E.keep g₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have K₁ := keysW hR E₁ rdi
  refine WP.mono (aes_ok [.xmm0] (by decide) (by decide) (by omega_arith) t₁ K₁ rsi (by rw [r10, rdi]))
    fun t₂ ⟨hc, hf⟩ => ?_
  have h15 : t₂.gpr .r15 = W := by rw [hf.gpr]; exact E₁.r15
  have ww : InRegions t₂.wr (W + BitVec.ofNat 64 o) 16 := by
    rw [hf.wr]; exact E₁.perm.wW (by omega_arith)
  refine WP.of_runBlock ⟨_, by xrun [h15, ww], ?_⟩
  have hx := hc .xmm0 (List.mem_singleton_self _)
  refine ⟨E₁.keep (fun r _ => by show t₂.gpr r = _; rw [hf.gpr]) hf.rd hf.wr, hf.rd.trans rd₁, hf.wr.trans wr₁, ?_, ?_⟩
  · show Frame _ t.mem (t₂.mem.writeW _ _)
    rw [hf.mem, m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · show bytesAt (t₂.mem.writeW _ _) _ 16 = _
    rw [bytesAt_writeW128, ← aesWith_le16 _ _ _ _ hx, x0, m₁]
    rfl

end VG.Proof.AesGcmSivReg.X86_64
