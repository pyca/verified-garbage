import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# AES-GCM-SIV on x86-64: the encryption key's schedule and GHASH's key

Untrusted: everything here is checked by Lean. `expand` writes the schedule
of the encryption key at `W + 248` (`expand_ok`), and `hkey` GHASH's key,
`H · x` for the authentication key `H` (POLYVAL's field element), in
GHASH's order at `W + 64`, and zeroes its accumulator (`hkey_ok`): the
shift of `hi ++ lo` by one bit to the right, and `R` added when the bit
shifted out is set (`mulXG_words`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Polyval (mulXG)
open VG.Proof.AesGcm.X86_64 (GcmImpl key_call ofNat_add_ofNat)

theorem and1 (x : BitVec 64) : x &&& 1#64 = if x.getLsbD 0 then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  cases h : x.getLsbD 0
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_zero]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all
  · simp only [↓reduceIte, show (1#64).toNat = 1 from rfl]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all

theorem appLo (a b : BitVec 64) {j : Nat} (h : j < 64) : (a ++ b).getLsbD j = b.getLsbD j := by
  rw [BitVec.getLsbD_append]; simp [h]

theorem appHi (a b : BitVec 64) {j : Nat} (h : 64 ≤ j) : (a ++ b).getLsbD j = a.getLsbD (j - 64) := by
  rw [BitVec.getLsbD_append]; simp [show ¬ j < 64 by omega]

/-- `mulXG` on the halves of a block, for any words `M` and `C` with the bits
of the carry into the low half and of `R` in the high half. -/
theorem mulXG_core (hi lo : BitVec 64) (M C : BitVec 64)
    (hM : ∀ i < 64, M.getLsbD i = (decide (i = 63) && hi.getLsbD 0))
    (hC : ∀ i < 64, C.getLsbD i = (Spec.Gcm.R.getLsbD (i + 64) && lo.getLsbD 0))
    (hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false) :
    ((hi >>> 1) ^^^ C) ++ ((lo >>> 1) ||| M) = mulXG (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi128
  unfold mulXG; rw [appLo hi lo (by decide)]
  by_cases h64 : i < 64
  · rw [appLo _ _ h64, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, hM i h64]
    by_cases h63 : i = 63
    · subst h63
      have e : lo.getLsbD (1 + 63) = false := BitVec.getLsbD_of_ge lo _ (by decide)
      rw [e]
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, appHi hi lo (show 64 ≤ 1 + 63 by decide), hR 63 (by decide)] <;> simp
    · have e : (hi ++ lo).getLsbD (1 + i) = lo.getLsbD (1 + i) := appLo hi lo (by omega)
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, e, hR i h64, decide_eq_false h63] <;> simp
  · rw [appHi _ _ (by omega), BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, hC (i - 64) (by omega),
      show i - 64 + 64 = i by omega]
    have e : (hi ++ lo).getLsbD (1 + i) = hi.getLsbD (1 + (i - 64)) := by
      rw [appHi hi lo (by omega)]; congr 1; omega
    cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
      BitVec.getLsbD_ushiftRight, e] <;> simp

/-- GHASH's product with `x`, as `hkey` computes it on the halves of a block. -/
theorem mulXG_words (hi lo : BitVec 64) :
    ((hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))) ++
      ((lo >>> 1) ||| (hi &&& 1#64).rotateRight 1) = mulXG (hi ++ lo) := by
  have hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false := by decide +kernel
  have hR' : ∀ i < 64, (0xE100000000000000#64 : BitVec 64).getLsbD i = Spec.Gcm.R.getLsbD (i + 64) := by
    decide +kernel
  have h1 : ∀ i < 64, (0x8000000000000000#64 : BitVec 64).getLsbD i = decide (i = 63) := by decide +kernel
  refine mulXG_core hi lo _ _ (fun i hi64 => ?_) (fun i hi64 => ?_) hR
  · rw [and1 hi]; cases h : hi.getLsbD 0 <;> simp [h1 i hi64]
  · rw [and1 lo]; cases h : lo.getLsbD 0 <;> simp [hR' i hi64]

/-- Two words stored at `p` and `p + 8`, read as a block in GHASH's order. -/
theorem blockAt_two (m : Mem) (p : Addr) (x y : BitVec 64) :
    Spec.Gcm.blockAt ((m.writeW p (bswap64 x)).writeW (p + BitVec.ofNat 64 8) (bswap64 y)) p = x ++ y := by
  have hs : Mem.Sep p (64 / 8) (p + BitVec.ofNat 64 8) (64 / 8) := by
    simpa using Offset.sep p (d := 0) (n := 8) (e := 8) (k := 8) (.inl (by decide)) (by decide) (by decide)
  rw [← Proof.Gcm.X86_64.blockAt_bswap, Mem.readW_writeW_self64, BitVec.add_zero, Mem.readW_writeW_sep hs (by decide),
    Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64, Proof.Gcm.X86_64.bswap64_bswap64]

/-- The block at `W + 64`, after the accumulator at `W + 80` is zeroed. -/
theorem blockAt_zero_after (W : Addr) (m : Mem) :
    Spec.Gcm.blockAt ((m.writeW (W + BitVec.ofNat 64 80) (0#64)).writeW (W + BitVec.ofNat 64 88) (0#64))
      (W + BitVec.ofNat 64 64) = Spec.Gcm.blockAt m (W + BitVec.ofNat 64 64) := by
  have c₁ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 80) (64 / 8) :=
    Offset.contains W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide)
  have c₂ : (⟨W + BitVec.ofNat 64 80, 16⟩ : Region).Contains (W + BitVec.ofNat 64 88) (64 / 8) :=
    Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide)
  exact Proof.AesGcm.X86_64.blockAt_frame
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁).writeW (List.mem_singleton_self _) _ c₂)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))

/-- Four words written at `W + 64`, …, `W + 88`. -/
theorem frame4 (W : Addr) (m : Mem) (a b c d : BitVec 64) :
    Frame [⟨W + BitVec.ofNat 64 64, 32⟩] m ((((m.writeW (W + BitVec.ofNat 64 64) a).writeW (W + BitVec.ofNat 64 72) b).writeW
      (W + BitVec.ofNat 64 80) c).writeW (W + BitVec.ofNat 64 88) d) := by
  have ct : ∀ e, 64 ≤ e → e + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 e) (64 / 8) :=
    fun e h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 64 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (ct 72 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (ct 80 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (ct 88 (by decide) (by decide))

/-- `hkey`: GHASH's key at `W + 64` and its accumulator zeroed at `W + 80`. -/
theorem hkey_ok {K W SP : Addr} {t : State} (E : Env K W SP t) :
    ∃ t' : State, runBlock isa hkey t = some t' ∧
      Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 64) =
        mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt t'.mem (W + BitVec.ofNat 64 80) = 0 ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 16 + 8 ≤ 3816 by decide)
  have r₂ := E.perm.wR (show 24 + 8 ≤ 3816 by decide)
  have w₁ := E.perm.wW (show 64 + 8 ≤ 3816 by decide)
  have w₂ := E.perm.wW (show 72 + 8 ≤ 3816 by decide)
  have w₃ := E.perm.wW (show 80 + 8 ≤ 3816 by decide)
  have w₄ := E.perm.wW (show 88 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [hkey, zero16, h15, r₁, r₂, w₁, w₂, w₃, w₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      ite_false, reduceCtorEq]
    rw [blockAt_zero_after W, show W + BitVec.ofNat 64 72 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
      rw [add_ofNat_assoc], blockAt_two, GcmSiv.ofBytes_bytesAt, add_ofNat_assoc, ← mulXG_words]
    rfl
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    rw [show W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 by rw [add_ofNat_assoc],
      Spec.Gcm.blockAt, Proof.Cmac.bytesAt_store2]
    decide
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    exact frame4 W _ _ _ _ _
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- What `expand` leaves: the schedule of the encryption key at `W + 248`. -/
structure ExpPost (K W SP : Addr) (R : Nat) (t t' : State) : Prop where
  env : Env K W SP t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  saved : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r
  frame : Frame [⟨W + BitVec.ofNat 64 248, 240⟩, ⟨W + BitVec.ofNat 64 1768, 512⟩, below SP 8] t.mem t'.mem
  ciph : Spec.GcmSiv.ctxCiph t'.mem (W + BitVec.ofNat 64 248) R =
    Spec.GcmSiv.aes (bytesAt t.mem (W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen R))

/-- The arguments of `expand`'s call. -/
theorem expArgs_ok {K W SP : Addr} {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat} {t : State}
    (E : Env K W SP t) (S : Slots W R N A D al n t.mem) :
    ∃ t₁ : State, runBlock isa
      (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
        .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO) t = some t₁ ∧
      t₁.mem = t.mem ∧ t₁.gpr .rdi = W + BitVec.ofNat 64 32 ∧
      t₁.gpr .rsi = BitVec.ofNat 64 (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rdx = W + BitVec.ofNat 64 248 ∧
      t₁.gpr .rcx = W + BitVec.ofNat 64 1768 ∧ (∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r) ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  refine ⟨_, by srun [h15, rR, rr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    rw [Proof.AesGcm.X86_64.ofNat_sub (by omega) (by omega), ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; unfold Spec.GcmSiv.keyLen; omega
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
  · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

theorem expand_ok (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {t : State} (E : Env K W SP t) (S : Slots W R N A D al n t.mem) :
    WP isa (expand v.callees) t (ExpPost K W SP R t) := by
  have h15 := E.r15
  have rR := S.rounds
  have rr := E.perm.wR (show 200 + 8 ≤ 3816 by decide)
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega
  obtain ⟨t₁, run₁, hm₁, rdi, rsi, rdx, rcx, hg₁, hrd₁, hwr₁⟩ := expArgs_ok hR E S
  have E₁ : Env K W SP t₁ := E.of_saved hg₁ hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (key_call v.key (kargs L E₁ hl rdi rsi rdx rcx)) fun t₂ P => ?_
  have fc := P.frame
  rw [E₁.rsp] at fc
  refine ⟨E₁.of_saved P.saved P.rd P.wr, by rw [P.rd, hrd₁], by rw [P.wr, hwr₁],
    fun r hr => by rw [P.saved r hr, hg₁ r hr], by rw [← hm₁]; exact fc, ?_⟩
  have hr : Spec.Aes.rounds (Spec.GcmSiv.keyLen R / 4) = R := by
    unfold Spec.Aes.rounds Spec.GcmSiv.keyLen; omega
  have out := P.out
  rw [hr] at out
  rw [Spec.GcmSiv.ctxCiph, out, Spec.GcmSiv.aes, Proof.Cmac.bytesAt_length, hr, hm₁]

end VG.Proof.AesGcmSiv.X86_64
