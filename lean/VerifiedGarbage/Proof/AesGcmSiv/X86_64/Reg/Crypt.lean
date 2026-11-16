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
import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
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

/-- A register as its two quadwords. -/
theorem qwords (v : BitVec 128) : v = qword v 1 ++ qword v 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 64
  · simp only [h, ↓reduceIte, decide_true, Nat.mul_zero, Nat.zero_add, Bool.true_and]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega_arith), Bool.true_and]
    exact congrArg _ (by omega_arith)

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
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      mem_setReg, mem_arithFlags, mem_setXmm, mem_setFlags, punpck_movq, h15, rN, nonceO, ne_eq, not_false_eq_true]
    rw [le16_app, hi64, show (t.xmm .xmm2).extractLsb' 0 64 = qword (t.xmm .xmm2) 0 from rfl]
    rw [show Spec.GcmSiv.toBytes (t.xmm .xmm2) =
      Spec.GcmSiv.toBytes (qword (t.xmm .xmm2) 1 ++ qword (t.xmm .xmm2) 0) from congrArg _ (qwords _)]
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

/-! ## Counter mode: the counter -/

open VG.Proof.AesGcmSiv.X86_64 (frame_outside bytesAt_rest12)

/-- A counter block's bytes. -/
theorem le16_ctrX {icb : List Byte} {d : BitVec 128}
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4)
    (i : Nat) : le16 (ctrX icb d i) = Spec.GcmSiv.counterBlock icb i := by
  rw [← bytesAt_writeW128 (fun _ => 0) 0 (ctrX icb d i)]
  exact counterBlock_store _ _ hrest

/-- A register whose bytes are `icb`: the counter before block 0, and its
other words. -/
theorem ctr_of_le16 {v : BitVec 128} {icb : List Byte} (h : le16 v = icb) :
    le4 (dword v 1) ++ le4 (dword v 2) ++ le4 (dword v 3) = icb.drop 4 ∧ ctrX icb v 0 = v := by
  let m : Mem := Mem.writeW (fun _ => 0) (0 : Addr) v
  have hr : m.readW 0 128 = v := Mem.readW_writeW_self _ 0 16 v (by decide)
  have hb : bytesAt m 0 16 = icb := by rw [← le16_readW, hr, h]
  have h4 := Proof.Cmac.bytesAt_add m 0 4 12
  rw [show 4 + 12 = 16 from rfl, hb] at h4
  refine ⟨?_, ?_⟩
  · rw [← hr, VG.X86_64.dword_readW _ _ (by decide), VG.X86_64.dword_readW _ _ (by decide),
      VG.X86_64.dword_readW _ _ (by decide), ← bytesAt_rest12, h4,
      List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  · have hw0 : dword v 0 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4)) := by
      rw [← hr, VG.X86_64.dword_readW _ _ (by decide), show (0 : Addr) + BitVec.ofNat 64 (4 * 0) = 0 from rfl,
        GcmSiv.readW32_leNat, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    rw [ctrX, Nat.add_zero, ← hw0]
    exact VG.X86_64.ofDwords_dword _

/-- The counter, one on. -/
theorem ctrX_succ (icb : List Byte) (d : BitVec 128) (i : Nat) :
    XBinOp.eval .paddd (ctrX icb d i) ((0 : BitVec 64) ++ BitVec.ofNat 64 1) = ctrX icb d (i + 1) := by
  rw [ctrX, paddd_one, ← BitVec.ofNat_add, Nat.add_assoc]

/-- The next counter block into `b`. -/
theorem ctrs1_run (b : XReg) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (t : State) :
    ∃ t' : State, runBlock isa (ctrs [b]) t = some t' ∧ t'.xmm b = t.xmm .xmm9 ∧
      t'.xmm .xmm9 = XBinOp.eval .paddd (t.xmm .xmm9) (t.xmm .xmm10) ∧
      (∀ r, r ≠ b → r ≠ .xmm9 → t'.xmm r = t.xmm r) ∧ t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  refine ⟨(t.setXmm b (t.xmm .xmm9)).setXmm .xmm9 (XBinOp.eval .paddd (t.xmm .xmm9) (t.xmm .xmm10)), ?_, ?_, ?_,
    fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [ctrs, List.append_nil, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, isa, exec, XOp.exec, XBinOp.eval, xmm_setXmm_self,
      xmm_setXmm_of_ne _ _ (Ne.symm hb9), xmm_setXmm_of_ne _ _ (Ne.symm hb10)]
  · rw [xmm_setXmm_of_ne _ _ hb9, xmm_setXmm_self]
  · rw [xmm_setXmm_self]
  · rw [xmm_setXmm_of_ne _ _ h₂, xmm_setXmm_of_ne _ _ h₁]

/-! ## Counter mode: a block -/

/-- Counter mode before block `j` of the data: `aes`'s arguments for the
schedule at `W + 248`, the counter and its increment, and the data. -/
structure CInv (K W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte)
    (d : BitVec 128) (σ : State) (j : Nat) (t : State) : Prop where
  env : Env K W SP t
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 248
  rsi : t.gpr .rsi = BitVec.ofNat 64 R
  r10 : t.gpr .r10 = W + BitVec.ofNat 64 248 + BitVec.ofNat 64 (16 * R)
  key : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph
  x9 : t.xmm .xmm9 = ctrX icb d j
  x10 : t.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - j)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (n % 16)
  data : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * j)
  frame : Frame [⟨D, n⟩] σ.mem t.mem

/-- The keystream block in `b` XORed into block `j + l` of the data. -/
theorem xorData_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {D : Addr} {n : Nat}
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) (b : XReg) (hb8 : b ≠ .xmm8) {j l : Nat}
    {i i' : Nat} (hi : i = j + l) (hi' : i' = i + 1)
    {t : State} (hD : Buf K W SP t D n) (hDw : Covers [⟨D, n⟩] t.wr) (hlen : 16 * (j + l) + 16 ≤ n)
    (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * j))
    (hdata : bytesAt t.mem D n = GcmSiv.ctrPart ciph icb x (16 * i))
    (hks : le16 (t.xmm b) = GcmSiv.ksBlock ciph icb i)
    (hkey : Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R = ciph) :
    ∃ t' : State, runBlock isa (xorData b l) t = some t' ∧
      bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x (16 * i') ∧
      Frame [⟨D, n⟩] t.mem t'.mem ∧ Spec.GcmSiv.ctxCiph t'.mem (W + BitVec.ofNat 64 248) R = ciph ∧
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r, r ≠ b → r ≠ .xmm8 → t'.xmm r = t.xmm r) := by
  subst hi hi'
  have hn := hD.lt
  have ea : D + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (16 * l) = D + BitVec.ofNat 64 (16 * (j + l)) := by
    rw [add_ofNat_assoc, Nat.mul_add]
  have hr : InRegions (t.rd ++ t.wr) (D + BitVec.ofNat 64 (16 * (j + l))) 16 := in_off hD.rd (by omega_arith) hn
  have hw : InRegions t.wr (D + BitVec.ofNat 64 (16 * (j + l))) 16 := in_off hDw (by omega_arith) hn
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h <;> subst h <;> decide
  obtain ⟨t', run, hm, hg, hrd, hwr, hx⟩ : ∃ t' : State, runBlock isa (xorData b l) t = some t' ∧
      t'.mem = t.mem.writeW (D + BitVec.ofNat 64 (16 * (j + l)))
        (t.xmm b ^^^ t.mem.readW (D + BitVec.ofNat 64 (16 * (j + l))) 128) ∧
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ (∀ r, r ≠ b → r ≠ .xmm8 → t'.xmm r = t.xmm r) := by
    refine ⟨{ (t.setXmm .xmm8 (t.mem.readW (D + BitVec.ofNat 64 (16 * (j + l))) 128)).setXmm b
        (t.xmm b ^^^ t.mem.readW (D + BitVec.ofNat 64 (16 * (j + l))) 128) with
        mem := t.mem.writeW (D + BitVec.ofNat 64 (16 * (j + l)))
          (t.xmm b ^^^ t.mem.readW (D + BitVec.ofNat 64 (16 * (j + l))) 128) },
      by xrun [xorData, h12, ea, hr, hw, xmm_setXmm_of_ne _ _ hb8] <;> rfl, rfl, rfl, rfl, rfl, fun r h₁ h₂ => ?_⟩
    show ((t.setXmm .xmm8 _).setXmm b _).xmm r = _
    rw [xmm_setXmm_of_ne _ _ h₁, xmm_setXmm_of_ne _ _ h₂]
  have fw : Frame [⟨D + BitVec.ofNat 64 (16 * (j + l)), 16⟩] t.mem t'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fD : Frame [⟨D, n⟩] t.mem t'.mem := fw.sub fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base D hlen⟩
  refine ⟨t', run, ?_, fD, ?_, hg, hrd, hwr, hx⟩
  · have hk : (GcmSiv.ksBlock ciph icb (j + l)).length = 16 := by rw [← hkey]; exact GcmSiv.ctxCiph_length _ _ _ _
    have := GcmSiv.ctrPart_step ciph icb x D (m' := t'.mem) (i := j + l) (n := 16) (Nat.le_refl _) hk
      (by rw [hxl]; exact hdata)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; exact hn) (by rw [hxl]; exact hlen))
      (by rw [hm, bytesAt_writeW128, BitVec.xor_comm, le16_xor, le16_readW, hks,
        List.take_of_length_le (Nat.le_of_eq hk)])
    rw [hxl, show 16 * (j + l) + 16 = 16 * (j + l + 1) by omega_arith] at this
    exact this
  · rw [← hkey]
    exact ctxCiph_frame fD (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hD.w.sub_right (Lay.wSub (by decide))).symm) hRb

/-- The keystream block of the counter that `aes` enciphered into `b`. -/
theorem ks_of {K W SP : Addr} {R : Nat} {D : Addr} {n : Nat} {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte}
    {d : BitVec 128} {σ : State} {j : Nat} {t : State} (I : CInv K W SP R D n ciph icb x d σ j t)
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4) {t₁ t₂ : State}
    (m₁ : t₁.mem = t.mem) {b : XReg} {i : Nat} (xb : t₁.xmm b = ctrX icb d i)
    (hc : st (t₂.xmm b) = Spec.Aes.cipher R (bytesAt t₁.mem (W + BitVec.ofNat 64 248) (16 * (R + 1))) (st (t₁.xmm b))) :
    le16 (t₂.xmm b) = GcmSiv.ksBlock ciph icb i := by
  rw [← aesWith_le16 _ _ _ _ hc, xb, le16_ctrX hrest, m₁, ← I.key]
  rfl

/-- One block enciphered. -/
theorem crypt1_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {D : Addr} {n : Nat}
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {d : BitVec 128} {σ : State}
    (hD : Buf K W SP σ D n) (hDw : Covers [⟨D, n⟩] σ.wr)
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4) {j : Nat} (hj : j < n / 16)
    {t : State} (I : CInv K W SP R D n ciph icb x d σ j t) :
    WP isa crypt1 t fun t' => CInv K W SP R D n ciph icb x d σ (j + 1) t' ∧
      t'.zf = some (decide (n / 16 - j = 1)) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, xb, x9₁, xo₁, g₁, m₁, rd₁, wr₁⟩ := ctrs1_run .xmm0 (by decide) (by decide) t
  have E₁ : Env K W SP t₁ := I.env.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have K₁ := keysW hR E₁ (by rw [g₁]; exact I.rdi)
  refine WP.mono (aes_ok [.xmm0] (by decide) (by decide) (by omega_arith) t₁ K₁ (by rw [g₁]; exact I.rsi)
    (by rw [g₁, I.r10, I.rdi])) fun t₂ ⟨hc, hf⟩ => ?_
  have hks := ks_of I hrest m₁ (xb.trans I.x9) (hc .xmm0 (List.mem_singleton_self _))
  have rd₂ : t₂.rd = σ.rd := by rw [hf.rd, rd₁, I.rd]
  have wr₂ : t₂.wr = σ.wr := by rw [hf.wr, wr₁, I.wr]
  obtain ⟨t₃, run₃, d₃, f₃, k₃, g₃, rd₃, wr₃, x₃⟩ := xorData_ok (K := K) (W := W) (SP := SP) hR hxl .xmm0 (by decide)
    (j := j) (l := 0) (i := j) (i' := j + 1) rfl rfl (hD.of_eq rd₂ wr₂) (by rw [wr₂]; exact hDw) (by omega_arith)
    (by rw [hf.gpr, g₁]; exact I.r12) (by rw [hf.mem, m₁]; exact I.data) hks (by rw [hf.mem, m₁]; exact I.key)
  have h12 : t₃.gpr .r12 = D + BitVec.ofNat 64 (16 * j) := by rw [g₃, hf.gpr, g₁]; exact I.r12
  have hbx : t₃.gpr .rbx = BitVec.ofNat 64 (n / 16 - j) := by rw [g₃, hf.gpr, g₁]; exact I.rbx
  obtain ⟨t₄, run₄, r12₄, rbx₄, zf₄, g₄, x₄, m₄, rd₄, wr₄⟩ : ∃ t₄ : State, runBlock isa
      [.alu .add .r12 (imm 16), .alu .sub .rbx (imm 1)] t₃ = some t₄ ∧
      t₄.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 1)) ∧ t₄.gpr .rbx = BitVec.ofNat 64 (n / 16 - (j + 1)) ∧
      t₄.zf = some (decide (n / 16 - j = 1)) ∧ (∀ r, r ≠ .r12 → r ≠ .rbx → t₄.gpr r = t₃.gpr r) ∧
      t₄.xmm = t₃.xmm ∧ t₄.mem = t₃.mem ∧ t₄.rd = t₃.rd ∧ t₄.wr = t₃.wr := by
    refine ⟨_, by srun [h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12, add_ofNat_assoc]
      rw [show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
    · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx,
        Proof.AesGcm.X86_64.sub_beq (show n / 16 - j < 2 ^ 64 by omega_arith) (show 1 < 2 ^ 64 by decide)]
    · intro r h₁ h₂
      simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
    all_goals rfl
  have gk : ∀ r, r ≠ .r12 → r ≠ .rbx → t₄.gpr r = t.gpr r := fun r h₁ h₂ => by
    rw [g₄ r h₁ h₂, g₃, hf.gpr, g₁]
  have xk : ∀ r, r ≠ .xmm0 → r ≠ .xmm8 → r ≠ .xmm9 → t₄.xmm r = t.xmm r := fun r h₁ h₂ h₃ => by
    rw [x₄, x₃ r h₁ h₂, hf.xmm r (by simp [h₁, h₂]), xo₁ r h₁ h₃]
  refine WP.of_runBlock ⟨t₄, by rw [VG.Interleave.runBlock_append, run₃]; exact run₄, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r12₄, rbx₄,
    ?_, ?_, ?_⟩, zf₄⟩
  · exact I.env.keep (fun r hr => gk r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [rd₄, rd₃, rd₂, I.rd]) (by rw [wr₄, wr₃, wr₂, I.wr])
  · rw [rd₄, rd₃, rd₂]
  · rw [wr₄, wr₃, wr₂]
  · rw [gk _ (by decide) (by decide), I.rdi]
  · rw [gk _ (by decide) (by decide), I.rsi]
  · rw [gk _ (by decide) (by decide), I.r10]
  · rw [m₄]; exact k₃
  · rw [x₄, x₃ _ (by decide) (by decide), hf.xmm _ (by decide), x9₁, I.x9, I.x10, ctrX_succ]
  · rw [xk _ (by decide) (by decide) (by decide), I.x10]
  · rw [gk _ (by decide) (by decide), I.rbp]
  · rw [m₄]; exact d₃
  · rw [m₄]
    exact I.frame.trans (by rw [← m₁, ← hf.mem]; exact f₃)

/-- The next four counter blocks. -/
theorem ctrs4_run {icb : List Byte} {d : BitVec 128} {j : Nat} {t : State} (x9 : t.xmm .xmm9 = ctrX icb d j)
    (x10 : t.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1) :
    ∃ t' : State, runBlock isa (ctrs [.xmm0, .xmm1, .xmm2, .xmm3]) t = some t' ∧
      t'.xmm .xmm0 = ctrX icb d j ∧ t'.xmm .xmm1 = ctrX icb d (j + 1) ∧ t'.xmm .xmm2 = ctrX icb d (j + 2) ∧
      t'.xmm .xmm3 = ctrX icb d (j + 3) ∧ t'.xmm .xmm9 = ctrX icb d (j + 4) ∧
      t'.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 ∧
      t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨t₁, r₁, a₁, n₁, o₁, g₁, m₁, rd₁, wr₁⟩ := ctrs1_run .xmm0 (by decide) (by decide) t
  obtain ⟨t₂, r₂, a₂, n₂, o₂, g₂, m₂, rd₂, wr₂⟩ := ctrs1_run .xmm1 (by decide) (by decide) t₁
  obtain ⟨t₃, r₃, a₃, n₃, o₃, g₃, m₃, rd₃, wr₃⟩ := ctrs1_run .xmm2 (by decide) (by decide) t₂
  obtain ⟨t₄, r₄, a₄, n₄, o₄, g₄, m₄, rd₄, wr₄⟩ := ctrs1_run .xmm3 (by decide) (by decide) t₃
  have e₁ : t₁.xmm .xmm9 = ctrX icb d (j + 1) := by rw [n₁, x9, x10, ctrX_succ]
  have t₁₀ : t₁.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 := by rw [o₁ _ (by decide) (by decide), x10]
  have e₂ : t₂.xmm .xmm9 = ctrX icb d (j + 2) := by rw [n₂, e₁, t₁₀, ctrX_succ]
  have t₂₀ : t₂.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 := by rw [o₂ _ (by decide) (by decide), t₁₀]
  have e₃ : t₃.xmm .xmm9 = ctrX icb d (j + 3) := by rw [n₃, e₂, t₂₀, ctrX_succ]
  have t₃₀ : t₃.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 := by rw [o₃ _ (by decide) (by decide), t₂₀]
  refine ⟨t₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show runBlock isa (ctrs [.xmm0] ++ (ctrs [.xmm1] ++ (ctrs [.xmm2] ++ ctrs [.xmm3]))) t = _
    rw [VG.Interleave.runBlock_append, r₁]
    show runBlock isa (ctrs [.xmm1] ++ (ctrs [.xmm2] ++ ctrs [.xmm3])) t₁ = _
    rw [VG.Interleave.runBlock_append, r₂]
    show runBlock isa (ctrs [.xmm2] ++ ctrs [.xmm3]) t₂ = _
    rw [VG.Interleave.runBlock_append, r₃]
    exact r₄
  · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), a₁, x9]
  · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), a₂, e₁]
  · rw [o₄ _ (by decide) (by decide), a₃, e₂]
  · rw [a₄, e₃]
  · rw [n₄, e₃, t₃₀, ctrX_succ]
  · rw [o₄ _ (by decide) (by decide), t₃₀]
  · rw [g₄, g₃, g₂, g₁]
  · rw [m₄, m₃, m₂, m₁]
  · rw [rd₄, rd₃, rd₂, rd₁]
  · rw [wr₄, wr₃, wr₂, wr₁]

/-- Four blocks enciphered. -/
theorem crypt4_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {D : Addr} {n : Nat}
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {d : BitVec 128} {σ : State}
    (hD : Buf K W SP σ D n) (hDw : Covers [⟨D, n⟩] σ.wr)
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4) {j : Nat} (hj : j + 4 ≤ n / 16)
    {t : State} (I : CInv K W SP R D n ciph icb x d σ j t) :
    WP isa crypt4 t fun t' => CInv K W SP R D n ciph icb x d σ (j + 4) t' ∧
      t'.cf = some (decide (n / 16 - (j + 4) < 4)) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, c0, c1, c2, c3, c9, c10, g₁, m₁, rd₁, wr₁⟩ := ctrs4_run I.x9 I.x10
  have E₁ : Env K W SP t₁ := I.env.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have K₁ := keysW hR E₁ (by rw [g₁]; exact I.rdi)
  refine WP.mono (aes_ok [.xmm0, .xmm1, .xmm2, .xmm3] (by decide) (by decide) (by omega_arith) t₁ K₁
    (by rw [g₁]; exact I.rsi) (by rw [g₁, I.r10, I.rdi])) fun t₂ ⟨hc, hf⟩ => ?_
  have k0 := ks_of I hrest m₁ c0 (hc .xmm0 (by simp))
  have k1 := ks_of I hrest m₁ c1 (hc .xmm1 (by simp))
  have k2 := ks_of I hrest m₁ c2 (hc .xmm2 (by simp))
  have k3 := ks_of I hrest m₁ c3 (hc .xmm3 (by simp))
  have rd₂ : t₂.rd = σ.rd := by rw [hf.rd, rd₁, I.rd]
  have wr₂ : t₂.wr = σ.wr := by rw [hf.wr, wr₁, I.wr]
  have h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * j) := by rw [hf.gpr, g₁]; exact I.r12
  obtain ⟨u₀, ru₀, d₀, f₀, y₀, g₀, rd₀, wr₀, x₀⟩ := xorData_ok (K := K) (W := W) (SP := SP) hR hxl .xmm0 (by decide)
    (j := j) (l := 0) (i := j) (i' := j + 1) rfl rfl (hD.of_eq rd₂ wr₂) (by rw [wr₂]; exact hDw) (by omega_arith) h12₂
    (by rw [hf.mem, m₁]; exact I.data) k0 (by rw [hf.mem, m₁]; exact I.key)
  obtain ⟨u₁, ru₁, d₁, f₁, y₁, g₁', rd₁', wr₁', x₁⟩ := xorData_ok (K := K) (W := W) (SP := SP) hR hxl .xmm1
    (by decide) (j := j) (l := 1) (i := j + 1) (i' := j + 2) rfl rfl (hD.of_eq (rd₀.trans rd₂) (wr₀.trans wr₂)) (by rw [wr₀, wr₂]; exact hDw)
    (by omega_arith) (by rw [g₀]; exact h12₂) d₀ (by rw [x₀ _ (by decide) (by decide)]; exact k1) y₀
  obtain ⟨u₂, ru₂, d₂, f₂, y₂, g₂, rd₂', wr₂', x₂⟩ := xorData_ok (K := K) (W := W) (SP := SP) hR hxl .xmm2
    (by decide) (j := j) (l := 2) (i := j + 2) (i' := j + 3) rfl rfl (hD.of_eq (rd₁'.trans (rd₀.trans rd₂)) (wr₁'.trans (wr₀.trans wr₂)))
    (by rw [wr₁', wr₀, wr₂]; exact hDw) (by omega_arith) (by rw [g₁', g₀]; exact h12₂) d₁
    (by rw [x₁ _ (by decide) (by decide), x₀ _ (by decide) (by decide)]; exact k2) y₁
  obtain ⟨u₃, ru₃, d₃, f₃, y₃, g₃, rd₃, wr₃, x₃⟩ := xorData_ok (K := K) (W := W) (SP := SP) hR hxl .xmm3
    (by decide) (j := j) (l := 3) (i := j + 3) (i' := j + 4) rfl rfl (hD.of_eq (rd₂'.trans (rd₁'.trans (rd₀.trans rd₂)))
      (wr₂'.trans (wr₁'.trans (wr₀.trans wr₂))))
    (by rw [wr₂', wr₁', wr₀, wr₂]; exact hDw) (by omega_arith) (by rw [g₂, g₁', g₀]; exact h12₂) d₂
    (by rw [x₂ _ (by decide) (by decide), x₁ _ (by decide) (by decide), x₀ _ (by decide) (by decide)]; exact k3) y₂
  have gu : u₃.gpr = t.gpr := by rw [g₃, g₂, g₁', g₀, hf.gpr, g₁]
  have h12 : u₃.gpr .r12 = D + BitVec.ofNat 64 (16 * j) := by rw [gu]; exact I.r12
  have hbx : u₃.gpr .rbx = BitVec.ofNat 64 (n / 16 - j) := by rw [gu]; exact I.rbx
  obtain ⟨t₇, run₇, r12₇, rbx₇, cf₇, g₇, x₇, m₇, rd₇, wr₇⟩ : ∃ t₇ : State, runBlock isa
      [.alu .add .r12 (imm 64), .alu .sub .rbx (imm 4), .alu .cmp .rbx (imm 4)] u₃ = some t₇ ∧
      t₇.gpr .r12 = D + BitVec.ofNat 64 (16 * (j + 4)) ∧ t₇.gpr .rbx = BitVec.ofNat 64 (n / 16 - (j + 4)) ∧
      t₇.cf = some (decide (n / 16 - (j + 4) < 4)) ∧ (∀ r, r ≠ .r12 → r ≠ .rbx → t₇.gpr r = u₃.gpr r) ∧
      t₇.xmm = u₃.xmm ∧ t₇.mem = u₃.mem ∧ t₇.rd = u₃.rd ∧ t₇.wr = u₃.wr := by
    refine ⟨_, by srun [h12, hbx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h12, add_ofNat_assoc]
      rw [show 16 * j + 64 = 16 * (j + 4) by omega_arith]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hbx]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
    · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
      simp only [Proof.AesGcm.X86_64.toNat_ofNat_of_lt (show n / 16 - (j + 4) < 2 ^ 64 by omega_arith)]
      rfl
    · intro r h₁ h₂
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, ite_false]
    all_goals rfl
  have gk : ∀ r, r ≠ .r12 → r ≠ .rbx → t₇.gpr r = t.gpr r := fun r h₁ h₂ => by rw [g₇ r h₁ h₂, gu]
  have xk : ∀ r, r ∉ [XReg.xmm8, .xmm0, .xmm1, .xmm2, .xmm3] → t₇.xmm r = t₁.xmm r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [x₇, x₃ r hr.2.2.2.2 hr.1, x₂ r hr.2.2.2.1 hr.1, x₁ r hr.2.2.1 hr.1, x₀ r hr.2.1 hr.1,
      hf.xmm r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  have rdk : t₇.rd = σ.rd := by rw [rd₇, rd₃, rd₂', rd₁', rd₀, rd₂]
  have wrk : t₇.wr = σ.wr := by rw [wr₇, wr₃, wr₂', wr₁', wr₀, wr₂]
  have runAll : runBlock isa (xorData .xmm0 0 ++ (xorData .xmm1 1 ++ (xorData .xmm2 2 ++ (xorData .xmm3 3 ++
      [.alu .add .r12 (imm 64), .alu .sub .rbx (imm 4), .alu .cmp .rbx (imm 4)])))) t₂ = some t₇ := by
    rw [VG.Interleave.runBlock_append, ru₀, Option.bind_some, VG.Interleave.runBlock_append, ru₁, Option.bind_some,
      VG.Interleave.runBlock_append, ru₂, Option.bind_some, VG.Interleave.runBlock_append, ru₃, Option.bind_some]
    exact run₇
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.of_runBlock ⟨t₇, runAll, ⟨?_, rdk, wrk, ?_, ?_, ?_, ?_, ?_, ?_, r12₇, rbx₇, ?_, ?_, ?_⟩, cf₇⟩
  · exact I.env.keep (fun r hr => gk r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [rdk, I.rd]) (by rw [wrk, I.wr])
  · rw [gk _ (by decide) (by decide), I.rdi]
  · rw [gk _ (by decide) (by decide), I.rsi]
  · rw [gk _ (by decide) (by decide), I.r10]
  · rw [m₇]; exact y₃
  · rw [xk _ (by decide), c9]
  · rw [xk _ (by decide), c10]
  · rw [gk _ (by decide) (by decide), I.rbp]
  · rw [m₇]; exact d₃
  · rw [m₇]
    exact I.frame.trans (by rw [← m₁, ← hf.mem]; exact ((f₀.trans f₁).trans f₂).trans f₃)

/-! ## Counter mode: the whole data -/

theorem CInv.flags {K W SP : Addr} {R : Nat} {D : Addr} {n : Nat} {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte}
    {d : BitVec 128} {σ : State} {j : Nat} {t : State} (I : CInv K W SP R D n ciph icb x d σ j t) (v : BitVec 64)
    (c o : Bool) : CInv K W SP R D n ciph icb x d σ j (arithFlags t v c o) :=
  ⟨I.env.keep (fun _ _ => rfl) rfl rfl, I.rd, I.wr, I.rdi, I.rsi, I.r10, I.key, I.x9, I.x10, I.r12, I.rbx, I.rbp,
    I.data, I.frame⟩

/-- The start of `crypt`: the counter block from the tag, `aes`'s arguments,
and the data's whole blocks and last bytes. -/
theorem ctrInit_run {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {t : State} (E : Env K W SP t)
    {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hn : n < 2 ^ 64) :
    ∃ t₁ : State, runBlock isa ctrInit t = some t₁ ∧
      le16 (t₁.xmm .xmm9) = Spec.GcmSiv.initialCounter (bytesAt t.mem W 16) ∧
      t₁.xmm .xmm10 = (0 : BitVec 64) ++ BitVec.ofNat 64 1 ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 248 ∧ t₁.gpr .rsi = BitVec.ofNat 64 R ∧
      t₁.gpr .r10 = W + BitVec.ofNat 64 248 + BitVec.ofNat 64 (16 * R) ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧
      t₁.zf = some (decide (n / 16 = 0)) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧ ∀ r ∈ [Reg.r13, .r15, .rsp], t₁.gpr r = t.gpr r := by
  have h15 := E.r15
  have rR := S.rounds
  have sD := S.data
  have sL := S.len
  have rr := E.perm.wR (show 200 + 8 ≤ 488 by decide)
  have rD := E.perm.wR (show 232 + 8 ≤ 488 by decide)
  have rL := E.perm.wR (show 240 + 8 ≤ 488 by decide)
  have rT := E.perm.wR (show 0 + 16 ≤ 488 by decide)
  obtain rT' : InRegions (t.rd ++ t.wr) W 16 := by simpa using rT
  obtain hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 n)
  rw [Proof.AesGcm.X86_64.toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine ⟨_, by xrun [ctrInit, aesArgs, lastKey, skO, roundsO, tagO, dataO, lenO, h15, rR, sD, sL, rr, rD, rL, rT,
    rT'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
      mem_setReg, mem_arithFlags, mem_setXmm, mem_setFlags, h15, tagO, BitVec.add_zero, ne_eq, not_false_eq_true]
    have e : XShiftOp.eval .pslldq ((0 : BitVec 64) ++ (9223372036854775808 : BitVec 64)) 8 =
        (9223372036854775808 : BitVec 64) ++ (0 : BitVec 64) := by decide
    rw [e]
    show le16 (((9223372036854775808 : BitVec 64) ++ (0 : BitVec 64)) ||| t.mem.readW W 128) = _
    rw [readW128_app, BitVec.or_append, le16_app, show (0 : BitVec 64) ||| t.mem.readW W 64 = t.mem.readW W 64 from
      BitVec.zero_or, BitVec.or_comm, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
      GcmSiv.initialCounter_words]
    rfl
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags,
      xmm_setFlags, gpr_setXmm, gpr_setReg, ite_true, ite_false, reduceCtorEq, ne_eq, not_false_eq_true]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h15, skO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, rR, roundsO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, rR, roundsO, skO, execShift]
    rw [BitVec.add_comm]; congr 1; rcases hR with rfl | rfl <;> decide
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, sD, dataO]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, sL, lenO, hand]
  · simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setXmm, mem_setReg, mem_arithFlags,
      mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, sL, lenO, Proof.AesGcm.X86_64.shr4 _ hn]
  · simp only [zf_setReg, zf_setXmm, zf_arithFlags, gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags,
      mem_setXmm, mem_setReg, mem_arithFlags, mem_setFlags, ite_true, ite_false, reduceCtorEq, h15, sL, lenO,
      Proof.AesGcm.X86_64.shr4 _ hn]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]
  · rfl
  · rfl
  · rfl
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]

/-- The loop of single blocks, from any block before the last. -/
theorem cones_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {D : Addr} {n : Nat}
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {d : BitVec 128} {σ : State}
    (hD : Buf K W SP σ D n) (hDw : Covers [⟨D, n⟩] σ.wr)
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4) {j₀ : Nat} (hj₀ : j₀ < n / 16)
    {t : State} (I₀ : CInv K W SP R D n ciph icb x d σ j₀ t) :
    WP isa (.loop crypt1 .ne) t (CInv K W SP R D n ciph icb x d σ (n / 16)) := by
  refine WP.loop (M := isa) (body := crypt1) (c := .ne)
    (fun (m : Nat) (t : State) => ∃ j, m = n / 16 - j ∧ j < n / 16 ∧ CInv K W SP R D n ciph icb x d σ j t) ?_
    (n / 16 - j₀) t ⟨j₀, rfl, hj₀, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  refine WP.mono (crypt1_ok hR hxl hD hDw hrest hj I) fun t' ⟨I', hz⟩ => ?_
  have ev : isa.eval .ne t' = some !(decide (n / 16 - j = 1)) := by
    show t'.zf.map (!·) = _; rw [hz]; rfl
  by_cases h1 : n / 16 - j = 1
  · left
    refine ⟨by rw [ev, decide_eq_true h1]; rfl, ?_⟩
    rw [show n / 16 = j + 1 by omega_arith]; exact I'
  · right
    exact ⟨by rw [ev, decide_eq_false h1]; rfl, n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

/-- The whole blocks enciphered. -/
theorem cblocks_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {D : Addr} {n : Nat}
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {d : BitVec 128} {σ : State}
    (hD : Buf K W SP σ D n) (hDw : Covers [⟨D, n⟩] σ.wr)
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4)
    {t : State} (I : CInv K W SP R D n ciph icb x d σ 0 t) (hz : t.zf = some (decide (n / 16 = 0))) :
    WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rbx (imm 4)])
          (.seq (.ite .b (.block []) (.loop crypt4 .ae))
            (.seq (.block [.alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop crypt1 .ne)))))) t
      (CInv K W SP R D n ciph icb x d σ (n / 16)) := by
  have hlt := hD.lt
  refine WP.ite (decide (n / 16 = 0)) hz (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have : n / 16 = 0 := by simpa using h0
    rw [this]; exact I
  obtain ⟨v, o, run₁⟩ := cmpbx_run t (k := n / 16) (by omega_arith) (by rw [I.rbx, Nat.sub_zero])
  refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
  have I₁ := I.flags v (decide (n / 16 < 4)) o
  have mid : WP isa (.ite .b (.block []) (.loop crypt4 .ae)) (arithFlags t v (decide (n / 16 < 4)) o)
      fun u => ∃ k, k ≤ n / 16 ∧ CInv K W SP R D n ciph icb x d σ k u := by
    refine WP.ite (decide (n / 16 < 4)) rfl (fun _ => WP.block_nil ⟨0, Nat.zero_le _, I₁⟩) (fun h4 => ?_)
    have h4' : ¬ n / 16 < 4 := by simpa using h4
    refine WP.loop (M := isa) (body := crypt4) (c := .ae)
      (fun (m : Nat) (u : State) => ∃ k, m = n / 16 - k ∧ k + 4 ≤ n / 16 ∧ CInv K W SP R D n ciph icb x d σ k u) ?_
      (n / 16 - 0) _ ⟨0, rfl, by omega_arith, I₁⟩
    rintro m u ⟨k, rfl, hk, Iu⟩
    refine WP.mono (crypt4_ok hR hxl hD hDw hrest hk Iu) fun u' ⟨Iu', hcf'⟩ => ?_
    have ev : isa.eval .ae u' = some !(decide (n / 16 - (k + 4) < 4)) := by
      show u'.cf.map (!·) = _; rw [hcf']; rfl
    by_cases hlt4 : n / 16 - (k + 4) < 4
    · left
      exact ⟨by rw [ev, decide_eq_true hlt4]; rfl, k + 4, hk, Iu'⟩
    · right
      exact ⟨by rw [ev, decide_eq_false hlt4]; rfl, n / 16 - (k + 4), by omega_arith, k + 4, rfl, by omega_arith,
        Iu'⟩
  refine WP.seq (WP.mono mid fun u ⟨k, hk, Iu⟩ => ?_)
  obtain ⟨run₂, hy⟩ := test_run .rbx u (k := n / 16 - k) (by omega_arith) Iu.rbx
  refine WP.seq (WP.of_runBlock ⟨_, run₂, ?_⟩)
  have I₃ := Iu.flags (BitVec.ofNat 64 (n / 16 - k)) false false
  refine WP.ite (decide (n / 16 - k = 0)) (by rw [← hy]; rfl) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have e : k = n / 16 := by simp at h0; omega_arith
    have cast : ∀ s, CInv K W SP R D n ciph icb x d σ k s → CInv K W SP R D n ciph icb x d σ (n / 16) s :=
      fun s h => by rw [← e]; exact h
    exact cast _ I₃
  · exact cones_ok hR hxl hD hDw hrest (by simp at h0; omega_arith) I₃

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega_using [h, h₁]), h₁, ite_true,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

/-- The last bytes enciphered, with a keystream block at `W + 128`. -/
theorem cryptTail_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {D : Addr} {n : Nat}
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = n) {d : BitVec 128} {σ : State}
    (hD : Buf K W SP σ D n) (hDw : Covers [⟨D, n⟩] σ.wr)
    (hrest : le4 (dword d 1) ++ le4 (dword d 2) ++ le4 (dword d 3) = icb.drop 4) (hr1 : 1 ≤ n % 16)
    {t : State} (I : CInv K W SP R D n ciph icb x d σ (n / 16) t) :
    WP isa cryptTail t fun t' => Env K W SP t' ∧ t'.rd = σ.rd ∧ t'.wr = σ.wr ∧
      bytesAt t'.mem D n = GcmSiv.ctrPart ciph icb x n ∧
      Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨D, n⟩] σ.mem t'.mem := by
  have hn := hD.lt
  have hw := L.ww
  obtain ⟨t₁, run₁, xb, x9₁, xo₁, g₁, m₁, rd₁, wr₁⟩ := ctrs1_run .xmm0 (by decide) (by decide) t
  have E₁ : Env K W SP t₁ := I.env.keep (fun r _ => by rw [g₁]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  have K₁ := keysW hR E₁ (by rw [g₁]; exact I.rdi)
  refine WP.mono (aes_ok [.xmm0] (by decide) (by decide) (by omega_arith) t₁ K₁ (by rw [g₁]; exact I.rsi)
    (by rw [g₁, I.r10, I.rdi])) fun t₂ ⟨hc, hf⟩ => ?_
  have hks := ks_of I hrest m₁ (xb.trans I.x9) (hc .xmm0 (List.mem_singleton_self _))
  have rd₂ : t₂.rd = σ.rd := by rw [hf.rd, rd₁, I.rd]
  have wr₂ : t₂.wr = σ.wr := by rw [hf.wr, wr₁, I.wr]
  have E₂ : Env K W SP t₂ := E₁.keep (fun r _ => by rw [hf.gpr]) hf.rd hf.wr
  have h15 := E₂.r15
  have h12 : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) := by rw [hf.gpr, g₁]; exact I.r12
  have hbp : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by rw [hf.gpr, g₁]; exact I.rbp
  have ww := E₂.perm.wW (show 128 + 16 ≤ 488 by decide)
  obtain ⟨t₃, run₃, hm₃, rsi₃, rdi₃, rcx₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃ : State, runBlock isa
      (ptr .rsi .r15 bO ++ ([.movdquStore (at_ .rsi 0) .xmm0, .mov .rdi (.reg .r12),
        .mov .rcx (.reg .rbp)] : List Instr)) t₂ = some t₃ ∧
      t₃.mem = t₂.mem.writeW (W + BitVec.ofNat 64 128) (t₂.xmm .xmm0) ∧
      t₃.gpr .rsi = W + BitVec.ofNat 64 128 ∧ t₃.gpr .rdi = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
      t₃.gpr .rcx = BitVec.ofNat 64 (n % 16) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by xrun [bO, h15, ww], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setXmm, gpr_setReg, gpr_arithFlags, xmm_setReg, xmm_arithFlags,
        ite_true, ite_false, reduceCtorEq, h15, bO, BitVec.add_zero]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, bO]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  have fB : Frame [⟨W + BitVec.ofNat 64 128, 16⟩] t₂.mem t₃.mem := by
    rw [hm₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hblk : 16 * (n / 16) + n % 16 = n := by omega_arith
  have dD : (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 128, 16⟩ := hD.w.sub_right (Lay.wSub (by decide))
  obtain lp : Proof.AesGcm.X86_64.LoopPre t₃ (W + BitVec.ofNat 64 128) (D + BitVec.ofNat 64 (16 * (n / 16)))
      (n % 16) :=
    ⟨rsi₃, rdi₃, rcx₃, hr1, by omega_arith, by rw [hrd₃, hwr₃]; exact E₂.perm.wCR (by omega_arith),
      by rw [hwr₃, wr₂]; exact Proof.AesGcm.X86_64.covers_off hDw (by omega_arith) hn,
      ((dD.sub_left (Offset.sub_base D (show 16 * (n / 16) + n % 16 ≤ n by omega_arith))).sub_right
        (Region.sub_prefix (by omega_arith))).symm⟩
  refine WP.mono (Proof.AesGcm.X86_64.xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  obtain hl : (Proof.AesGcm.X86_64.xorBytes t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16)))
      (W + BitVec.ofNat 64 128) (n % 16)).length = n % 16 := by
    simp [Proof.AesGcm.X86_64.xorBytes, Proof.Cmac.bytesAt_length]
  obtain fw : Frame [⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have hk : (GcmSiv.ksBlock ciph icb (n / 16)).length = 16 := by rw [← I.key]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hd₃ : bytesAt t₃.mem D n = GcmSiv.ctrPart ciph icb x (16 * (n / 16)) := by
    rw [bytesAt_frame fB (fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact dD)
      (Nat.le_of_lt hn), hf.mem, m₁]
    exact I.data
  have hks₃ : bytesAt t₃.mem (W + BitVec.ofNat 64 128) 16 = GcmSiv.ksBlock ciph icb (n / 16) := by
    rw [hm₃, bytesAt_writeW128, hks]
  refine ⟨E₂.keep (fun q hq => ?_) (by rw [hrd₄, hrd₃]) (by rw [hwr₄, hwr₃]), by rw [hrd₄, hrd₃, rd₂],
    by rw [hwr₄, hwr₃, wr₂], ?_, ?_⟩
  · rw [hg₄ q (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl <;> decide),
      hg₃ q hq]
  · have hb' : bytesAt t₄.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) = Spec.Cmac.xor
        (bytesAt t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
        ((GcmSiv.ksBlock ciph icb (n / 16)).take (n % 16)) := by
      obtain e := bytesAt_writeBytes_self t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16)))
        (Proof.AesGcm.X86_64.xorBytes t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (W + BitVec.ofNat 64 128) (n % 16))
        (by omega_arith)
      rw [hl] at e
      obtain hs := Proof.Cmac.bytesAt_add t₃.mem (W + BitVec.ofNat 64 128) (n % 16) (16 - n % 16)
      rw [show n % 16 + (16 - n % 16) = 16 by omega_arith, hks₃] at hs
      rw [hm₄, e, Proof.AesGcm.X86_64.xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x D (m' := t₄.mem) (i := n / 16) (n := n % 16) (by omega_arith) hk
      (by rw [hxl]; exact hd₃)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; exact hn) (by rw [hxl]; omega_arith)) hb'
    rw [hxl, hblk] at this
    exact this
  · refine I.frame.sub (fun q hq => ⟨q, List.mem_cons_of_mem _ hq, fun _ h => h⟩) |>.trans ?_
    rw [← m₁, ← hf.mem]
    exact (fB.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self ..,
      fun _ h => h⟩).trans (fw.sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_arith)⟩)

/-- What `crypt` leaves: the data in counter mode from the tag at `W`. -/
structure CryptPost (K W SP : Addr) (R : Nat) (D : Addr) (n : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨D, n⟩] t.mem t'.mem
  data : bytesAt t'.mem D n = Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
    (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n)

theorem crypt_ok {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {t : State}
    (E : Env K W SP t) {N A D : Addr} {al n : Nat} (S : Slots W R N A D al n t.mem) (hD : Buf K W SP t D n)
    (hDw : Covers [⟨D, n⟩] t.wr) : WP isa crypt t (CryptPost K W SP R D n t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, h9, h10, rdi, rsi, r10, r12, rbp, rbx, zf, m₁, rd₁, wr₁, g₁⟩ := ctrInit_run hR E S hn
  obtain ⟨hrest, hc0⟩ := ctr_of_le16 h9
  have hxl : (bytesAt t.mem D n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R y).length = 16 :=
    fun y => GcmSiv.ctxCiph_length _ _ _ _
  have I₁ : CInv K W SP R D n (Spec.GcmSiv.ctxCiph t.mem (W + BitVec.ofNat 64 248) R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem W 16)) (bytesAt t.mem D n) (t₁.xmm .xmm9) t 0 t₁ :=
    ⟨E.keep g₁ rd₁ wr₁, rd₁, wr₁, rdi, rsi, r10, by rw [m₁], hc0.symm, h10,
      by rw [r12, Nat.mul_zero, BitVec.add_zero], by rw [rbx, Nat.sub_zero], rbp,
      by rw [m₁, Nat.mul_zero, GcmSiv.ctrPart_zero], by rw [m₁]; exact Frame.refl _ _⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (cblocks_ok hR hxl hD hDw hrest I₁ zf) fun t₂ I₂ => ?_)
  obtain ⟨run₂, hy⟩ := test_run .rbp t₂ (k := n % 16) (by omega_arith) I₂.rbp
  refine WP.seq (WP.of_runBlock ⟨_, run₂, ?_⟩)
  have I₃ := I₂.flags (BitVec.ofNat 64 (n % 16)) false false
  refine WP.ite (decide (n % 16 = 0)) (by rw [← hy]; rfl) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have h0' : n % 16 = 0 := by simpa using h0
    refine ⟨I₃.env, I₃.rd, I₃.wr, I₃.frame.sub fun q hq => ⟨q, List.mem_cons_of_mem _ hq, fun _ h => h⟩, ?_⟩
    rw [I₃.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl]; omega_arith)]
  · have h0' : n % 16 ≠ 0 := by simpa using h0
    refine WP.mono (cryptTail_ok L hR hxl hD hDw hrest (by omega_arith) I₃) fun t₄ ⟨E₄, rd₄, wr₄, d₄, f₄⟩ => ?_
    refine ⟨E₄, rd₄, wr₄, f₄, ?_⟩
    rw [d₄, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSivReg.X86_64
