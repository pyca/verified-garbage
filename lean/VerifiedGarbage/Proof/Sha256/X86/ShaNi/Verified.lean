import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Impl.Sha256.X86.ShaNi
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Spec`. -/
section

/-!
# SHA-256 with the SHA extensions: the values in the SSE registers

How the working variables, the message schedule and the constants are laid out
in SSE registers, and that `sha256rnds2` and `sha256msg1`/`sha256msg2` compute
rounds and schedule words of `Spec/Sha256.lean`.
-/

namespace VG.Proof.Sha256.X86.ShaNi

open VG VG.X86
open VG.Spec.Sha256 (HashValue Word Block K W ch maj bsig0 bsig1 ssig0 ssig1)

/-- The working variables `A, B, E, F`, as `sha256rnds2` takes and returns them
(`A` in bits 127:96). -/
def abef (v : HashValue) : BitVec 128 := ofDwords v[5] v[4] v[1] v[0]

/-- The working variables `C, D, G, H` (`C` in bits 127:96). -/
def cdgh (v : HashValue) : BitVec 128 := ofDwords v[7] v[6] v[3] v[2]

/-- After two rounds, `C, D, G, H` are the old `A, B, E, F`. -/
theorem cdgh_two (v : HashValue) (k0 w0 k1 w1 : Word) :
    VG.Proof.Sha256.X86.ShaNi.cdgh (roundKW (roundKW v k0 w0) k1 w1) = VG.Proof.Sha256.X86.ShaNi.abef v := rfl

/-- `sha256rnds2` does two rounds, given `Wₜ + Kₜ` for them in the low doublewords of `x`. -/
theorem rnds2_eq (v : HashValue) (x : BitVec 128) {k0 w0 k1 w1 : Word}
    (h0 : dword x 0 = k0 + w0) (h1 : dword x 1 = k1 + w1) :
    sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.cdgh v) (VG.Proof.Sha256.X86.ShaNi.abef v) x = VG.Proof.Sha256.X86.ShaNi.abef (roundKW (roundKW v k0 w0) k1 w1) := by
  have ech : sha256Ch = ch := rfl
  have emaj : sha256Maj = maj := rfl
  have es0 : sha256BigSigma0 = bsig0 := rfl
  have es1 : sha256BigSigma1 = bsig1 := rfl
  simp only [sha256Rnds2, VG.Proof.Sha256.X86.ShaNi.abef, VG.Proof.Sha256.X86.ShaNi.cdgh, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, h0, h1, ech, emaj, es0, es1, roundKW_0, roundKW_1, roundKW_2, roundKW_3,
    roundKW_4, roundKW_5, roundKW_6, roundKW_7]
  generalize v[0]'(by decide) = a
  generalize v[1]'(by decide) = b
  generalize v[2]'(by decide) = c
  generalize v[3]'(by decide) = d
  generalize v[4]'(by decide) = e
  generalize v[5]'(by decide) = f
  generalize v[6]'(by decide) = g
  generalize v[7]'(by decide) = h
  have e1 : ch e f g + bsig1 e + (k0 + w0) + h + d = d + (h + bsig1 e + ch e f g + k0 + w0) := by ac_rfl
  have a1 : ch e f g + bsig1 e + (k0 + w0) + h + maj a b c + bsig0 a =
      h + bsig1 e + ch e f g + k0 + w0 + (bsig0 a + maj a b c) := by ac_rfl
  rw [e1, a1]
  generalize d + (h + bsig1 e + ch e f g + k0 + w0) = e₁
  generalize h + bsig1 e + ch e f g + k0 + w0 + (bsig0 a + maj a b c) = a₁
  have e2 : ch e₁ e f + bsig1 e₁ + (k1 + w1) + g + c = c + (g + bsig1 e₁ + ch e₁ e f + k1 + w1) := by ac_rfl
  have a2 : ch e₁ e f + bsig1 e₁ + (k1 + w1) + g + maj a₁ a b + bsig0 a₁ =
      g + bsig1 e₁ + ch e₁ e f + k1 + w1 + (bsig0 a₁ + maj a₁ a b) := by ac_rfl
  rw [e2, a2]

/-- The message schedule words `W₄ᵢ … W₄ᵢ₊₃` (`W₄ᵢ` in bits 31:0). -/
def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofDwords (W M (4 * i)) (W M (4 * i + 1)) (W M (4 * i + 2)) (W M (4 * i + 3))

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = ssig1 (W M (t + 14)) + W M (t + 9) + ssig0 (W M (t + 1)) + W M t := by
  rw [W_ge M (by omega)]; rfl

/-- `W_ge'`, summed in the order of `sha256msg1` and `sha256msg2`. -/
theorem W_ge_rev (M : Block) (t : Nat) :
    W M (t + 16) = W M t + ssig0 (W M (t + 1)) + W M (t + 9) + ssig1 (W M (t + 14)) := by
  rw [VG.Proof.Sha256.X86.ShaNi.W_ge' M t]; ac_rfl

/-- `sha256msg1`, `palignr` and `sha256msg2` compute the next four schedule words
from the previous sixteen. -/
theorem schedule_eq (M : Block) (i : Nat) :
    sha256Msg2 (XBinOp.eval .paddd (XBinOp.eval .sha256msg1 (VG.Proof.Sha256.X86.ShaNi.quad M i) (VG.Proof.Sha256.X86.ShaNi.quad M (i + 1)))
        (alignRight (VG.Proof.Sha256.X86.ShaNi.quad M (i + 3)) (VG.Proof.Sha256.X86.ShaNi.quad M (i + 2)) 4)) (VG.Proof.Sha256.X86.ShaNi.quad M (i + 3)) = VG.Proof.Sha256.X86.ShaNi.quad M (i + 4) := by
  have ess0 : sha256Sigma0 = ssig0 := rfl
  have ess1 : sha256Sigma1 = ssig1 := rfl
  simp only [sha256Msg2, XBinOp.eval, alignRight_4, VG.Proof.Sha256.X86.ShaNi.quad, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, ess0, ess1]
  have w0 := VG.Proof.Sha256.X86.ShaNi.W_ge_rev M (4 * i)
  have w1 := VG.Proof.Sha256.X86.ShaNi.W_ge_rev M (4 * i + 1)
  have w2 := VG.Proof.Sha256.X86.ShaNi.W_ge_rev M (4 * i + 2)
  have w3 := VG.Proof.Sha256.X86.ShaNi.W_ge_rev M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega, show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega,
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega, show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega,
    show 4 * i + 14 = 4 * (i + 3) + 2 by omega, show 4 * i + 1 + 14 = 4 * (i + 3) + 3 by omega,
    show 4 * i + 9 = 4 * (i + 2) + 1 by omega, show 4 * i + 1 + 9 = 4 * (i + 2) + 2 by omega,
    show 4 * i + 2 + 9 = 4 * (i + 2) + 3 by omega, show 4 * i + 3 + 9 = 4 * (i + 3) by omega,
    show 4 * i + 1 + 1 = 4 * i + 2 by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
    show 4 * i + 3 + 1 = 4 * (i + 1) by omega] at w0 w1 w2 w3 ⊢
  rw [w2, w3, w0, w1]

/-- Adding the working variables into the hash value, two registers at a time. -/
theorem paddd_abef (v H : HashValue) :
    XBinOp.eval .paddd (VG.Proof.Sha256.X86.ShaNi.abef v) (VG.Proof.Sha256.X86.ShaNi.abef H) = VG.Proof.Sha256.X86.ShaNi.abef (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, VG.Proof.Sha256.X86.ShaNi.abef, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith]

theorem paddd_cdgh (v H : HashValue) :
    XBinOp.eval .paddd (VG.Proof.Sha256.X86.ShaNi.cdgh v) (VG.Proof.Sha256.X86.ShaNi.cdgh H) = VG.Proof.Sha256.X86.ShaNi.cdgh (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, VG.Proof.Sha256.X86.ShaNi.cdgh, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith]

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Memory`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86
open VG.Spec.Sha256 (stateAt)

theorem stateAt_lo (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW p 128) j = (stateAt m p)[j] := by
  rw [dword_readW _ _ hj]; simp only [stateAt, Vector.getElem_ofFn]

theorem stateAt_hi (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW (p + BitVec.ofNat 64 16) 128) j = (stateAt m p)[4 + j] := by
  rw [dword_readW _ _ hj]
  simp only [stateAt, Vector.getElem_ofFn]
  refine congrArg (fun a => m.readW a 32) ?_
  exact Offset.add_add_eq _ (by omega)

theorem stateAt_store (m : Mem) (p : Addr) (x y : BitVec 128) :
    stateAt ((m.writeW p x).writeW (p + BitVec.ofNat 64 16) y) p =
      #v[dword x 0, dword x 1, dword x 2, dword x 3, dword y 0, dword y 1, dword y 2, dword y 3] := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  by_cases hlo : j < 4
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      readW_writeW128 _ _ _ hlo]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [show p + BitVec.ofNat 64 (4 * j) = p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (4 * (j - 4)) from
        (Offset.add_add_eq _ (by omega)).symm, readW_writeW128 _ _ _ (by omega)]
    rcases (by omega : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Const`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG.X86

theorem movd_value (a : BitVec 32) :
    (0 : BitVec 96) ++ a = ofDwords a 0 0 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, getLsbD_ofDwords, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
  by_cases h : i < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, ite_self]

theorem shift_last_value (a : BitVec 32) :
    XShiftOp.eval .pslldq (ofDwords a 0 0 0) 12 = ofDwords 0 0 0 a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XShiftOp.eval, BitVec.ofNat_eq_ofNat, show min (12#8).toNat 16 * 8 = 96 from rfl,
    BitVec.getLsbD_shiftLeft, getLsbD_ofDwords, BitVec.getLsbD_zero]
  by_cases h : i < 96
  · simp (disch := omega) only [ite_eq_left, ite_self, decide_eq_true, Bool.not_true, Bool.and_false, Bool.false_and]
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, decide_eq_false, Bool.not_false, Bool.true_and]
    exact congrArg _ (by omega)

theorem or_last_value (a b c d : BitVec 32) :
    XBinOp.eval .por (ofDwords a b c 0) (ofDwords 0 0 0 d) = ofDwords a b c d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, BitVec.getLsbD_or, getLsbD_ofDwords, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero]
  by_cases h0 : i < 32
  · simp only [h0, ite_true, Bool.or_false]
  by_cases h1 : i < 64
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.or_false]
  by_cases h2 : i < 96
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.or_false]
  · simp (disch := omega) only [ite_eq_right, Bool.false_or]

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Compress`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem const_ok (c : BitVec 128) (s : State) :
    WP isa (.block (const c)) s fun s' =>
      s'.xmm .xmm0 = c ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  have ldq : ∀ a b, XBinOp.eval .punpckldq a b =
      ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1) := fun _ _ => rfl
  apply WP.of_runBlock
  simp only [Nat.reduceAdd, and_self, const, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, XOp.exec, isa, VG.Proof.Sha256.X86.ShaNi.movd_value, ldq,
    dword_ofDwords_0, dword_ofDwords_1, punpcklqdq_eq,
    VG.Proof.Sha256.X86.ShaNi.shift_last_value,
    RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.zf_setXmm, RegUpd.zf_setReg,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h0 h7 => ?_, fun r hr => ?_, trivial⟩
  · exact (VG.Proof.Sha256.X86.ShaNi.or_last_value _ _ _ _).trans (ofDwords_dword c)
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setXmm_of_ne, h0, h7, not_false_eq_true]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
  have key : ∀ c < 4, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem roundOps_ok (n : Nat) (s : State) (v : HashValue) (q k : BitVec 128)
    (h0 : s.xmm .xmm0 = k) (h1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef v)
    (h2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh v) (hq : s.xmm (msg n) = q) :
    WP isa (.block (roundOps n)) s fun s' =>
      s'.xmm .xmm1 = sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.abef v) (sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.cdgh v) (VG.Proof.Sha256.X86.ShaNi.abef v)
        (XBinOp.eval .paddd k q)) (shufDwords (XBinOp.eval .paddd k q) 0x0e) ∧
      s'.xmm .xmm2 = sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.cdgh v) (VG.Proof.Sha256.X86.ShaNi.abef v) (XBinOp.eval .paddd k q) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := VG.Proof.Sha256.X86.ShaNi.msg_nodup n
  apply WP.of_runBlock
  simp only [roundOps]
  generalize msg n = x at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, reduceCtorEq, hd, h0, h1, h2, hq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h1 h2 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, not_false_eq_true]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 2)) = c)
    (hd' : s.xmm (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = sha256Msg2 (XBinOp.eval .paddd (XBinOp.eval .sha256msg1 a b) (alignRight d c 4)) d ∧
      (∀ r, r ≠ msg n → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := VG.Proof.Sha256.X86.ShaNi.msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, show ¬ n < 4 by omega, ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp only [and_self, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, hd, hd'', ha, hb, hc, hd',
    eval_movdqa, eval_sha256msg2,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 h7 => by
    simp only [RegUpd.xmm_setXmm_of_ne, h0, h7, not_false_eq_true], trivial⟩


theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (16 * n)) 16)
    (hmask : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) 16) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        (s.mem.readW (addr (s.gpr .edi) (16 * n)) 128)
        (s.mem.readW (addr (s.gpr .esi) 16) 128) ∧
      (∀ r, r ≠ msg n → r ≠ .xmm0 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := VG.Proof.Sha256.X86.ShaNi.msg_nodup n
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  generalize msg n = x₀ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp only [↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, State.load128, VG.Proof.Sha256.X86.ShaNi.ea_at, hin,
    hmask, hd, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 hx => by simp only [RegUpd.xmm_setXmm_of_ne, h0, hx, not_false_eq_true], trivial⟩

theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := VG.Proof.Sha256.X86.ShaNi.msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1


theorem rounds_four (H : HashValue) (M : Block) (n : Nat) :
    Spec.Sha256.rounds H M (4 * (n + 1)) =
      roundKW (roundKW (roundKW (roundKW (Spec.Sha256.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n)))
        (K (4 * n + 1)) (W M (4 * n + 1))) (K (4 * n + 2)) (W M (4 * n + 2)))
        (K (4 * n + 3)) (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ]
  rfl

theorem kq_quad (n : Nat) (M : Block) :
    dword (XBinOp.eval .paddd (kQuad (4 * n)) (VG.Proof.Sha256.X86.ShaNi.quad M n)) 0 = K (4 * n) + W M (4 * n) ∧
    dword (XBinOp.eval .paddd (kQuad (4 * n)) (VG.Proof.Sha256.X86.ShaNi.quad M n)) 1 = K (4 * n + 1) + W M (4 * n + 1) ∧
    dword (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) (VG.Proof.Sha256.X86.ShaNi.quad M n)) 0x0e) 0 =
      K (4 * n + 2) + W M (4 * n + 2) ∧
    dword (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) (VG.Proof.Sha256.X86.ShaNi.quad M n)) 0x0e) 1 =
      K (4 * n + 3) + W M (4 * n + 3) := by
  simp only [shufDwords_0e, XBinOp.eval, kQuad, VG.Proof.Sha256.X86.ShaNi.quad, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]
  exact ⟨trivial, trivial, trivial, trivial⟩


theorem msg_other (n : Nat) (r : XReg)
    (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm7], msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

theorem rounds4_ok (n : Nat) (s : State) (v : HashValue) (q : BitVec 128)
    (h1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef v) (h2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh v)
    (hq : s.xmm (msg n) = q)
:
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.abef v) (sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.cdgh v) (VG.Proof.Sha256.X86.ShaNi.abef v)
        (XBinOp.eval .paddd (kQuad (4 * n)) q))
        (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) q) 0x0e) ∧
      s'.xmm .xmm2 = sha256Rnds2 (VG.Proof.Sha256.X86.ShaNi.cdgh v) (VG.Proof.Sha256.X86.ShaNi.abef v) (XBinOp.eval .paddd (kQuad (4 * n)) q) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [rounds4, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.const_ok (kQuad (4 * n)) s)
    fun s₁ ⟨h0, hx, hg, hm, hrd, hwr, _⟩ => ?_
  have hq₁ : s₁.xmm (msg n) = q := (hx _ (VG.Proof.Sha256.X86.ShaNi.msg_other n _ (.inl rfl)) (VG.Proof.Sha256.X86.ShaNi.msg_other n _ (.inr (.inr (.inr rfl))))).trans hq
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.roundOps_ok n s₁ v q (kQuad (4 * n)) h0
    ((hx _ (by decide) (by decide)).trans h1) ((hx _ (by decide) (by decide)).trans h2) hq₁)
    fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
  exact ⟨e1, e2, fun r h0 h1 h2 h7 => (hx₂ r h0 h1 h2).trans (hx r h0 h7),
    fun r hr => (congrFun hg₂ r).trans (hg r hr), hm₂.trans hm,
    hrd₂.trans hrd, hwr₂.trans hwr⟩

theorem rounds4_step (H : HashValue) (M : Block) (n : Nat) (s : State)
    (h1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (Spec.Sha256.rounds H M (4 * n)))
    (h2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (Spec.Sha256.rounds H M (4 * n)))
    (hq : s.xmm (msg n) = VG.Proof.Sha256.X86.ShaNi.quad M n)
:
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      s'.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.rounds4_ok n s _ _ h1 h2 hq)
    fun s' ⟨e1, e2, hx, hg, hm, hrd, hwr⟩ => ?_
  obtain ⟨k0, k1, k2, k3⟩ := VG.Proof.Sha256.X86.ShaNi.kq_quad n M
  rw [VG.Proof.Sha256.X86.ShaNi.rnds2_eq _ _ k0 k1] at e1 e2
  rw [← VG.Proof.Sha256.X86.ShaNi.cdgh_two (Spec.Sha256.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n))
    (K (4 * n + 1)) (W M (4 * n + 1)), VG.Proof.Sha256.X86.ShaNi.rnds2_eq _ _ k2 k3] at e1
  exact ⟨by rw [e1, VG.Proof.Sha256.X86.ShaNi.rounds_four], by rw [e2, VG.Proof.Sha256.X86.ShaNi.rounds_four, VG.Proof.Sha256.X86.ShaNi.cdgh_two], hx, hg, hm, hrd, hwr⟩

structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (Spec.Sha256.rounds H M (4 * n))
  x2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (Spec.Sha256.rounds H M (4 * n))
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = VG.Proof.Sha256.X86.ShaNi.quad M k
  gpr : ∀ r, r ≠ .eax → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 →
      bswap (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (bp + BitVec.ofNat 64 (16 * n)) 128) bswapMask = VG.Proof.Sha256.X86.ShaNi.quad M n := by
  rw [show bswapMask = 0x0c0d0e0f08090a0b0405060700010203#128 from rfl, pshufb_bswap]
  have e : ∀ j, j < 4 → bswap (dword (m.readW (bp + BitVec.ofNat 64 (16 * n)) 128) j) =
      W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega)]
    refine congrArg (fun a => bswap (m.readW a 32)) ?_
    exact Offset.add_add_eq _ (by omega)
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rfl

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hrdi : sB.gpr .edi = bp) (hrsi : sB.gpr .esi = scr)
    (hbpFit : bp.toNat + 64 ≤ 2 ^ 32) (hscFit : scr.toNat + 32 ≤ 2 ^ 32)
    (hin : ∀ n < 4, InRegions (sB.rd ++ sB.wr)
      (bp.setWidth 64 + BitVec.ofNat 64 (16 * n)) 16)
    (hinMask : InRegions (sB.rd ++ sB.wr) (scr.setWidth 64 + BitVec.ofNat 64 16) 16)
    (hmask : sB.mem.readW (scr.setWidth 64 + BitVec.ofNat 64 16) 128 = bswapMask)
    (hblk : ∀ t < 16, bswap (sB.mem.readW
      (bp.setWidth 64 + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h1 : sB.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef H) (h2 : sB.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh H) :
    ∀ n ≤ 16, WP isa (rounds n) sB (VG.Proof.Sha256.X86.ShaNi.RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h1, h2, fun _ h => absurd h (by omega),
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hdi : s.gpr .edi = bp := (hs.gpr .edi (by decide)).trans hrdi
    have hsi : s.gpr .esi = scr := (hs.gpr .esi (by decide)).trans hrsi
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = VG.Proof.Sha256.X86.ShaNi.quad M n ∧
        (∀ r, r ≠ msg n → r ≠ .xmm0 → r ≠ .xmm7 → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · have eaB : addr (s.gpr .edi) (16 * n) = bp.setWidth 64 + BitVec.ofNat 64 (16 * n) := by
          rw [hdi]; exact addr_eq (by omega)
        have eaS : addr (s.gpr .esi) 16 = scr.setWidth 64 + BitVec.ofNat 64 16 := by
          rw [hsi]; exact addr_eq (by omega)
        refine WP.mono (VG.Proof.Sha256.X86.ShaNi.schedule_lo n hlo s (by rw [eaB, hs.rd, hs.wr]; exact hin n hlo)
          (by rw [eaS, hs.rd, hs.wr]; exact hinMask))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r hr h0 _ => hx r hr h0, hg, hm, hrd, hwr⟩
        rw [e, eaB, eaS, hs.mem, hmask]
        exact VG.Proof.Sha256.X86.ShaNi.load_quad M sB.mem (bp.setWidth 64) hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
        refine WP.mono (VG.Proof.Sha256.X86.ShaNi.schedule_hi (i + 4) (by omega) s (VG.Proof.Sha256.X86.ShaNi.quad M i) (VG.Proof.Sha256.X86.ShaNi.quad M (i + 1))
          (VG.Proof.Sha256.X86.ShaNi.quad M (i + 2)) (VG.Proof.Sha256.X86.ShaNi.quad M (i + 3)) ?_ ?_ ?_ ?_)
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r hr _ h7 => hx r hr h7, hg, hm, hrd, hwr⟩
        · rw [VG.Proof.Sha256.X86.ShaNi.msg_add4]; exact hs.msgs i (by omega) (by omega)
        · rw [show i + 4 + 1 = i + 1 + 4 by omega, VG.Proof.Sha256.X86.ShaNi.msg_add4]; exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [show i + 4 + 2 = i + 2 + 4 by omega, VG.Proof.Sha256.X86.ShaNi.msg_add4]; exact hs.msgs (i + 2) (by omega) (by omega)
        · rw [show i + 4 + 3 = i + 3 + 4 by omega, VG.Proof.Sha256.X86.ShaNi.msg_add4]; exact hs.msgs (i + 3) (by omega) (by omega)
        · rw [e]; exact VG.Proof.Sha256.X86.ShaNi.schedule_eq M i
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have o1 := VG.Proof.Sha256.X86.ShaNi.msg_other n .xmm1 (.inr (.inl rfl))
    have o2 := VG.Proof.Sha256.X86.ShaNi.msg_other n .xmm2 (.inr (.inr (.inl rfl)))
    refine WP.mono (VG.Proof.Sha256.X86.ShaNi.rounds4_step H M n s₁
      (by rw [hx₁ _ (Ne.symm o1) (by decide) (by decide)]; exact hs.x1)
      (by rw [hx₁ _ (Ne.symm o2) (by decide) (by decide)]; exact hs.x2) hq)
      fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e1, e2, fun k hk hk' => ?_, fun r hr => ?_, ?_,
      hrd₂.trans (hrd₁.trans hs.rd), hwr₂.trans (hwr₁.trans hs.wr)⟩
    · rw [hx₂ _ (VG.Proof.Sha256.X86.ShaNi.msg_other k _ (.inl rfl)) (VG.Proof.Sha256.X86.ShaNi.msg_other k _ (.inr (.inl rfl)))
        (VG.Proof.Sha256.X86.ShaNi.msg_other k _ (.inr (.inr (.inl rfl)))) (VG.Proof.Sha256.X86.ShaNi.msg_other k _ (.inr (.inr (.inr rfl))))]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (VG.Proof.Sha256.X86.ShaNi.msg_ne n k (by omega) (by omega)) (VG.Proof.Sha256.X86.ShaNi.msg_other k _ (.inl rfl))
          (VG.Proof.Sha256.X86.ShaNi.msg_other k _ (.inr (.inr (.inr rfl))))]
        exact hs.msgs k (by omega) (by omega)
    · exact (hg₂ r hr).trans ((congrFun hg₁ r).trans (hs.gpr r hr))
    · exact hm₂.trans (hm₁.trans hs.mem)

theorem loadState_ok (s : State)
    (hfit : (s.gpr .ebx).toNat + 32 ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) 16)
    (hhi : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16) 16) :
    WP isa (.block loadState) s fun s' =>
      s'.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (stateAt s.mem ((s.gpr .ebx).setWidth 64)) ∧
      s'.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (stateAt s.mem ((s.gpr .ebx).setWidth 64)) ∧
      s'.zf = s.zf ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea0 : addr (s.gpr .ebx) 0 = (s.gpr .ebx).setWidth 64 := by
    rw [addr_eq (by omega)]; exact BitVec.add_zero _
  have ea16 : addr (s.gpr .ebx) 16 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16 :=
    addr_eq (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadState, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, isa, State.load128, VG.Proof.Sha256.X86.ShaNi.ea_at, ea0, ea16, hlo, hhi, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.zf_setXmm,
    reduceCtorEq, not_false_eq_true, eval_movdqa,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial⟩ <;>
  simp only [punpcklqdq_eq, punpckhqdq_eq, shufDwords_b1, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, VG.Proof.Sha256.X86.ShaNi.abef, VG.Proof.Sha256.X86.ShaNi.cdgh, VG.Proof.Sha256.X86.ShaNi.stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 0 < 4 by decide),
    VG.Proof.Sha256.X86.ShaNi.stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 1 < 4 by decide), VG.Proof.Sha256.X86.ShaNi.stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 2 < 4 by decide),
    VG.Proof.Sha256.X86.ShaNi.stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 3 < 4 by decide), VG.Proof.Sha256.X86.ShaNi.stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 0 < 4 by decide),
    VG.Proof.Sha256.X86.ShaNi.stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 1 < 4 by decide), VG.Proof.Sha256.X86.ShaNi.stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 2 < 4 by decide),
    VG.Proof.Sha256.X86.ShaNi.stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 3 < 4 by decide)]

theorem store_ok (s : State) (v : HashValue)
    (h1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef v) (h2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh v)
    (hfit : (s.gpr .ebx).toNat + 32 ≤ 2 ^ 32)
    (hlo : InRegions s.wr ((s.gpr .ebx).setWidth 64) 16)
    (hhi : InRegions s.wr ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16) 16) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 128, s'.mem = (s.mem.writeW ((s.gpr .ebx).setWidth 64) x).writeW
        ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16) y) ∧
      stateAt s'.mem ((s.gpr .ebx).setWidth 64) = v ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea0 : addr (s.gpr .ebx) 0 = (s.gpr .ebx).setWidth 64 := by
    rw [addr_eq (by omega)]; exact BitVec.add_zero _
  have ea16 : addr (s.gpr .ebx) 16 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16 :=
    addr_eq (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [store, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, isa, State.store128, VG.Proof.Sha256.X86.ShaNi.ea_at, ea0, ea16, hlo, hhi, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    reduceCtorEq, not_false_eq_true, h1, h2, eval_movdqa,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, trivial⟩
  rw [VG.Proof.Sha256.X86.ShaNi.stateAt_store]
  simp only [punpcklqdq_eq, punpckhqdq_eq, shufDwords_b1, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, VG.Proof.Sha256.X86.ShaNi.abef, VG.Proof.Sha256.X86.ShaNi.cdgh]
  apply Vector.ext
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem saveHash_ok (s : State)
    (h32 : InRegions s.wr (addr (s.gpr .esi) 32) 16)
    (h48 : InRegions s.wr (addr (s.gpr .esi) 48) 16) :
    WP isa (.block saveHash) s fun s' =>
      s'.mem = (s.mem.writeW (addr (s.gpr .esi) 32) (s.xmm .xmm1)).writeW
        (addr (s.gpr .esi) 48) (s.xmm .xmm2) ∧
      s'.xmm = s.xmm ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [saveHash, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128,
    VG.Proof.Sha256.X86.ShaNi.ea_at, h32, h48, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem finishBlock_ok (s : State) (H : HashValue) (M : Block)
    (h1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (Spec.Sha256.rounds H M 64))
    (h2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (Spec.Sha256.rounds H M 64))
    (h32 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) 32) 16)
    (h48 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) 48) 16)
    (v32 : s.mem.readW (addr (s.gpr .esi) 32) 128 = VG.Proof.Sha256.X86.ShaNi.abef H)
    (v48 : s.mem.readW (addr (s.gpr .esi) 48) 128 = VG.Proof.Sha256.X86.ShaNi.cdgh H) :
    WP isa (.block finishBlock) s fun s' =>
      s'.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (compress H M) ∧ s'.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (compress H M) ∧
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
      (∀ r, r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.zf = some (s.gpr .ebp - 1 == 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finishBlock, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, execAlu, readSrc, isa, State.load128, VG.Proof.Sha256.X86.ShaNi.ea_at, h32, h48, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    reduceCtorEq, not_false_eq_true, h1, h2, v32, v48, VG.Proof.Sha256.X86.ShaNi.paddd_abef, VG.Proof.Sha256.X86.ShaNi.paddd_cdgh,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, trivial, fun r hdi hbp => ?_, trivial⟩
  · rfl
  · rfl
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne, hdi, hbp, not_false_eq_true,
      RegUpd.gpr_setXmm]

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Block`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (workRegion)
open VG.Proof.Sha256.X86 (Pre st bp nb scr esp₀ stR blR scrR H₀ blkAddr blk Saved
  contains_sub work_sub saved_frame blk_word compressBlocks_succ)
open VG.Spec.Sha256 (HashValue Block stateAt compressBlocks)

theorem Pre.scr_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 112) :
    InRegions s₀.wr (addr (scr s₀) d) 16 :=
  ⟨scrR s₀, by simp [hp.wr],
    contains_sub hd (by omega) (hp.scr_eq (by omega))⟩

theorem Pre.blk_fit {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have hb := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 64 * i < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show (bp s₀).toNat + 64 * i < 2 ^ 32 by omega)]
  omega

theorem Pre.blk_vec {s₀ : State} (hp : Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) ((blkAddr s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * n)) 16 := by
  have he : (blkAddr s₀ i).setWidth 64 =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    simpa only [blkAddr, addr] using addr_eq (x := bp s₀) (k := 64 * i)
      (by have := hp.blk_fits; omega)
  refine ⟨blR s₀, by simp only [hp.rd, List.mem_append, List.mem_cons, true_or], ?_⟩
  rw [he, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by have := hp.blk_fits; omega)

theorem work_write128 (p : BitVec 32) (hfit : p.toNat + 112 ≤ 2 ^ 32)
    (m : Mem) (v : BitVec 128) {d : Nat} (hd : d + 16 ≤ 96) :
    Frame [workRegion p] m (m.writeW (addr p d) v) := by
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) v ?_
  rw [addr_eq (by omega)]
  exact Offset.contains_base _ hd (by omega)

theorem saveHash_frame (s : State) (hfit : (s.gpr .esi).toNat + 112 ≤ 2 ^ 32) :
    Frame [workRegion (s.gpr .esi)] s.mem
      ((s.mem.writeW (addr (s.gpr .esi) 32) (s.xmm .xmm1)).writeW
        (addr (s.gpr .esi) 48) (s.xmm .xmm2)) :=
  (VG.Proof.Sha256.X86.ShaNi.work_write128 _ hfit _ _ (d := 32) (by decide)).trans
    (VG.Proof.Sha256.X86.ShaNi.work_write128 _ hfit _ _ (d := 48) (by decide))

structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = VG.Proof.Sha256.X86.ShaNi.abef (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  x2 : s.xmm .xmm2 = VG.Proof.Sha256.X86.ShaNi.cdgh (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = st s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  mask : s.mem.readW (addr (scr s₀) 16) 128 = bswapMask

structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha256.X86.ShaNi.Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (nb s₀ - i)

theorem saveHash_reads (p : BitVec 32) (hfit : p.toNat + 112 ≤ 2 ^ 32)
    (m : Mem) (x y : BitVec 128) :
    let m' := (m.writeW (addr p 32) x).writeW (addr p 48) y
    m'.readW (addr p 32) 128 = x ∧ m'.readW (addr p 48) 128 = y ∧
      m'.readW (addr p 16) 128 = m.readW (addr p 16) 128 := by
  have sep : ∀ d e : Nat, d + 16 ≤ 112 → e + 16 ≤ 112 →
      d + 16 ≤ e ∨ e + 16 ≤ d → Mem.Sep (addr p d) 16 (addr p e) 16 := by
    intro d e hd he hde
    rw [addr_eq (by omega), addr_eq (by omega)]
    exact Offset.sep _ hde (by omega) (by omega)
  dsimp only
  rw [Mem.readW_writeW_sep (sep 32 48 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self m _ 16 x (by decide), Mem.readW_writeW_self _ _ 16 y (by decide),
    Mem.readW_writeW_sep (sep 16 48 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 16 32 (by decide) (by decide) (by decide)) (by decide)]
  exact ⟨rfl, rfl, rfl⟩

theorem in_read_of_write {rd wr : List Region} {p : Addr} {n : Nat}
    (h : InRegions wr p n) : InRegions (rd ++ wr) p n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append.mpr (.inr hr), hc⟩

theorem body_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : VG.Proof.Sha256.X86.ShaNi.LInv s₀ i s) :
    WP isa body s fun s' =>
      VG.Proof.Sha256.X86.ShaNi.Common s₀ (i + 1) s' ∧ s'.gpr .edi = blkAddr s₀ (i + 1) ∧
      s'.gpr .ebp = BitVec.ofNat 32 (nb s₀ - (i + 1)) ∧
      s'.zf = some (BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0) := by
  have vecwr : ∀ d : Nat, d + 16 ≤ 112 → InRegions s.wr (addr (s.gpr .esi) d) 16 := by
    intro d hd; rw [hL.wr, hL.esi]; exact Pre.scr_vec hp hd
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.ShaNi.saveHash_ok s (vecwr 32 (by decide)) (vecwr 48 (by decide)))
    fun s₁ ⟨hm₁, hx₁, hg₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [workRegion (scr s₀)] s.mem s₁.mem := by
    rw [hm₁]
    have hf := VG.Proof.Sha256.X86.ShaNi.saveHash_frame s (by rw [hL.esi]; exact hp.scr_fits)
    simpa only [hL.esi] using hf
  have hf₁full : Frame [stR s₀, scrR s₀] s.mem s₁.mem := hf₁.sub
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨scrR s₀, by simp, work_sub _⟩)
  have hf : Frame [stR s₀, scrR s₀] s₀.mem s₁.mem := hL.frame.trans hf₁full
  have hdi₁ : s₁.gpr .edi = blkAddr s₀ i := (congrFun hg₁ _).trans hL.edi
  have hsi₁ : s₁.gpr .esi = scr s₀ := (congrFun hg₁ _).trans hL.esi
  have savedValues := VG.Proof.Sha256.X86.ShaNi.saveHash_reads (scr s₀) hp.scr_fits s.mem (s.xmm .xmm1) (s.xmm .xmm2)
  have vals : s₁.mem.readW (addr (scr s₀) 32) 128 = s.xmm .xmm1 ∧
      s₁.mem.readW (addr (scr s₀) 48) 128 = s.xmm .xmm2 ∧
      s₁.mem.readW (addr (scr s₀) 16) 128 = bswapMask := by
    rw [hm₁, hL.esi]
    exact ⟨savedValues.1, savedValues.2.1, savedValues.2.2.trans hL.mask⟩
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.ShaNi.rounds_ok _ (blk s₀ i) (blkAddr s₀ i) (scr s₀) s₁ hdi₁ hsi₁
    (Pre.blk_fit hp hi) (by have := hp.scr_fits; omega)
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.blk_vec hp hi hn)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr, ← hp.scr_eq (by decide)];
        exact VG.Proof.Sha256.X86.ShaNi.in_read_of_write (Pre.scr_vec hp (d := 16) (by decide)))
    (by rw [← hp.scr_eq (by decide)]; exact vals.2.2)
    (fun t ht => by
      have ea : addr (blkAddr s₀ i) (4 * t) =
          (blkAddr s₀ i).setWidth 64 + BitVec.ofNat 64 (4 * t) :=
        addr_eq (by have := Pre.blk_fit hp hi; omega)
      rw [← ea, hf.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
      exact blk_word hp hi ht)
    (by rw [hx₁]; exact hL.x1) (by rw [hx₁]; exact hL.x2) 16 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hsi₂ : s₂.gpr .esi = scr s₀ := (hR.gpr _ (by decide)).trans hsi₁
  have hg₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr =>
    (hR.gpr r hr).trans (congrFun hg₁ r)
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.finishBlock_ok s₂ _ _ hR.x1 hR.x2
    (by rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hsi₂];
        exact VG.Proof.Sha256.X86.ShaNi.in_read_of_write (Pre.scr_vec hp (d := 32) (by decide)))
    (by rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hsi₂];
        exact VG.Proof.Sha256.X86.ShaNi.in_read_of_write (Pre.scr_vec hp (d := 48) (by decide)))
    (by rw [hsi₂, hR.mem, vals.1]; exact hL.x1)
    (by rw [hsi₂, hR.mem, vals.2.1]; exact hL.x2))
    fun s₃ ⟨f1, f2, fdi, fbp, fg, fzf, fm, frd, fwr⟩ => ?_
  have mem : s₃.mem = s₁.mem := fm.trans hR.mem
  have ebp : s₂.gpr .ebp - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [hg₂ _ (by decide), hL.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fbp.trans ebp, ?_⟩
  · rw [f1, compressBlocks_succ]
  · rw [f2, compressBlocks_succ]
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.esi
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.esp
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.ebx
  · exact frd.trans (hR.rd.trans (hrd₁.trans hL.rd))
  · exact fwr.trans (hR.wr.trans (hwr₁.trans hL.wr))
  · rw [mem]; exact hf
  · rw [mem]; exact saved_frame hp hL.saved (.inl hf₁)
  · rw [mem]; exact vals.2.2
  · rw [fdi, hg₂ _ (by decide), hL.edi, blkAddr, blkAddr, BitVec.add_assoc]
    rw [show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => bp s₀ + BitVec.ofNat 32 n) (by omega)
  · rw [fzf, ebp]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : VG.Proof.Sha256.X86.ShaNi.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Sha256.X86.ShaNi.Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ VG.Proof.Sha256.X86.ShaNi.LInv s₀ (i + 1) s') := by
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.body_step hp hi hL) fun s' ⟨hc, hdi, hbp, hz⟩ => ?_
  have hev : eval .ne s' = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · exact .inl ⟨by rw [hev, hlast]; simp, hlast ▸ hc⟩
  · have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      have hn : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)] at h'
      exact hne h'
    exact .inr ⟨by rw [hev]; simpa using h0, by omega, { hc with edi := hdi, ebp := hbp }⟩

theorem loop_ok {s₀ : State} (hp : Pre s₀) (hpos : 0 < nb s₀) {s : State}
    (hL : VG.Proof.Sha256.X86.ShaNi.LInv s₀ 0 s) :
    WP isa (.loop body .ne) s (VG.Proof.Sha256.X86.ShaNi.Common s₀ (nb s₀)) := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VG.Proof.Sha256.X86.ShaNi.LInv s₀ i s
  have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Sha256.X86.ShaNi.Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hL⟩
    refine WP.mono (VG.Proof.Sha256.X86.ShaNi.body_ok hp hi hL) fun s' h => ?_
    rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
  exact WP.loop (M := isa) Inv hstep (nb s₀) s ⟨0, rfl, hpos, hL⟩

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit`. -/
section

namespace VG
materialize_code Impl.Sha256.X86.ShaNi.compress
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Load`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (Pre st scr esp₀ stR scrR H₀ stAddr workRegion work_sub saved_frame
  contains_sub stateAt_eq stateAt_get)
open VG.Spec.Sha256 (stateAt compressBlocks)

theorem loadPointer_ok (s : State) (p : BitVec 32)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p) :
    WP isa (.block [.mov .ebx (.mem (at_ .esp 4))]) s fun s' =>
      s'.gpr .ebx = p ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.load32,
    VG.Proof.Sha256.X86.ShaNi.ea_at, hin, ite_true, hv, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg]
  exact ⟨trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial, trivial, trivial, trivial⟩

theorem storeMask_ok (s : State)
    (hout : InRegions s.wr (addr (s.gpr .esi) 16) 16) :
    WP isa (.block [.movdquStore (at_ .esi 16) .xmm0]) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .esi) 16) (s.xmm .xmm0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, VG.Proof.Sha256.X86.ShaNi.ea_at,
    hout, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State}
    (hc : VG.Proof.Sha256.X86.Common s₀ 0 s) :
    WP isa (.block load) s fun s' =>
      VG.Proof.Sha256.X86.ShaNi.Common s₀ 0 s' ∧ (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.zf = s.zf := by
  have shape : load = [.mov .ebx (.mem (at_ .esp 4))] ++
      (const bswapMask ++ (([.movdquStore (at_ .esi 16) .xmm0] : List Instr) ++ loadState)) := by
    simp only [load, List.append_assoc]
  rw [shape, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.loadPointer_ok s (st s₀)
    (by rw [hc.esp, hc.rd, hc.wr]; exact hp.in_arg (by decide) (by decide))
    (by rw [hc.esp]; exact hp.arg_frame hc.frame (i := 0) (by decide)))
    fun s₁ ⟨hb₁, hg₁, hm₁, hrd₁, hwr₁, hz₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.const_ok bswapMask s₁)
    fun s₂ ⟨h0, hx₂, hg₂, hm₂, hrd₂, hwr₂, hz₂⟩ => ?_
  have hsi₂ : s₂.gpr .esi = scr s₀ := (hg₂ _ (by decide)).trans ((hg₁ _ (by decide)).trans hc.esi)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.storeMask_ok s₂
    (by rw [hsi₂, hwr₂, hwr₁, hc.wr]; exact Pre.scr_vec hp (by decide)))
    fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃, hz₃⟩ => ?_
  have hmem : s₃.mem = s.mem.writeW (addr (scr s₀) 16) bswapMask := by
    rw [hm₃, hm₂, hm₁, hsi₂, h0]
  have hframe : Frame [workRegion (scr s₀)] s.mem s₃.mem := by
    rw [hmem]; exact VG.Proof.Sha256.X86.ShaNi.work_write128 _ hp.scr_fits _ _ (by decide)
  have hframeFull : Frame [stR s₀, scrR s₀] s.mem s₃.mem := hframe.sub
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨scrR s₀, by simp, work_sub _⟩)
  have state : stateAt s₃.mem ((st s₀).setWidth 64) =
      compressBlocks (H₀ s₀) s₀.mem ((VG.Proof.Sha256.X86.bp s₀).setWidth 64) 0 := by
    apply stateAt_eq hp
    intro k hk
    rw [hframe.readW (contains_sub (len := 32) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk)) (by simpa using hp.st_scr.sub_right (work_sub _)) (by decide),
      ← stateAt_get hp s.mem hk, hc.state]
  have hb₃ : s₃.gpr .ebx = st s₀ := by rw [hg₃, hg₂ _ (by decide), hb₁]
  have rd₃ : s₃.rd = s₀.rd := hrd₃.trans (hrd₂.trans (hrd₁.trans hc.rd))
  have wr₃ : s₃.wr = s₀.wr := hwr₃.trans (hwr₂.trans (hwr₁.trans hc.wr))
  have out0 : InRegions s₀.wr ((st s₀).setWidth 64) 16 :=
    ⟨stR s₀, by simp [hp.wr], by simpa only [BitVec.add_zero] using
      (Offset.contains_base ((st s₀).setWidth 64) (d := 0) (n := 16) (k := 32) (by decide) (by decide))⟩
  have out16 : InRegions s₀.wr ((st s₀).setWidth 64 + BitVec.ofNat 64 16) 16 :=
    ⟨stR s₀, by simp [hp.wr], Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (VG.Proof.Sha256.X86.ShaNi.loadState_ok s₃ (by rw [hb₃]; exact hp.st_fits)
    (by rw [hb₃, rd₃, wr₃]; exact VG.Proof.Sha256.X86.ShaNi.in_read_of_write out0)
    (by rw [hb₃, rd₃, wr₃]; exact VG.Proof.Sha256.X86.ShaNi.in_read_of_write out16))
    fun s₄ ⟨x1, x2, hz₄, hg₄, hm₄, hrd₄, hwr₄⟩ => ?_
  have regs : ∀ r, r ≠ .eax → r ≠ .ebx → s₄.gpr r = s.gpr r :=
    fun r ha hb => (congrFun hg₄ r).trans ((congrFun hg₃ r).trans ((hg₂ r ha).trans (hg₁ r hb)))
  refine ⟨⟨?_, ?_, (regs _ (by decide) (by decide)).trans hc.esi,
    (regs _ (by decide) (by decide)).trans hc.esp, ?_, hrd₄.trans rd₃, hwr₄.trans wr₃,
    ?_, ?_, ?_⟩, regs, hz₄.trans (hz₃.trans (hz₂.trans hz₁))⟩
  · rw [x1, hb₃, state]
  · rw [x2, hb₃, state]
  · rw [hg₄]; exact hb₃
  · rw [hm₄]; exact hc.frame.trans hframeFull
  · rw [hm₄]; exact saved_frame hp hc.saved (.inl hframe)
  · rw [hm₄, hmem]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Whole`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (Pre pre_of st scr bp nb esp₀ stR scrR retR H₀
  save_ok common_zero restore_ok saved_frame)
open VG.Spec.Sha256 (stateAt compressBlocks)

theorem state_write_frame (p : Addr) (m : Mem) (x y : BitVec 128) :
    Frame [⟨p, 32⟩] m ((m.writeW p x).writeW (p + BitVec.ofNat 64 16) y) := by
  have c0 : (⟨p, 32⟩ : Region).Contains p 16 := by
    simpa only [BitVec.add_zero] using
      (Offset.contains_base p (d := 0) (n := 16) (k := 32) (by decide) (by decide))
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) x c0).writeW
    (List.mem_singleton_self _) y (Offset.contains_base _ (by decide) (by decide))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha256.X86.ShaNi.compress s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha256.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp)
    fun s₁ ⟨hesi, hedi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86.ShaNi.load_ok hp (common_zero hp hesi hesp hrd hwr hm))
    fun s₂ ⟨hc₀, hg, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha256.X86.ShaNi.Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_)
  · refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0)
      (by simp only [eval, hzf, hz]) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      refine VG.Proof.Sha256.X86.ShaNi.loop_ok hp hpos { hc₀ with
                                        edi := ?_, ebp := ?_ }
      · rw [hg _ (by decide) (by decide), hedi]; simp [VG.Proof.Sha256.X86.blkAddr]
      · rw [hg _ (by decide) (by decide), hebp]; simp [nb]
  · rw [WP.block_append_iff]
    have out0 : InRegions s₃.wr ((st s₀).setWidth 64) 16 :=
      ⟨stR s₀, by simp [hc.wr, hp.wr], by simpa only [BitVec.add_zero] using
        (Offset.contains_base ((st s₀).setWidth 64) (d := 0) (n := 16) (k := 32) (by decide) (by decide))⟩
    have out16 : InRegions s₃.wr ((st s₀).setWidth 64 + BitVec.ofNat 64 16) 16 :=
      ⟨stR s₀, by simp [hc.wr, hp.wr], Offset.contains_base _ (by decide) (by decide)⟩
    refine WP.mono (VG.Proof.Sha256.X86.ShaNi.store_ok s₃ _ hc.x1 hc.x2 (by rw [hc.ebx]; exact hp.st_fits)
      (by rw [hc.ebx]; exact out0) (by rw [hc.ebx]; exact out16))
      fun s₄ ⟨⟨x, y, hm₄⟩, hstate, hg₄, hrd₄, hwr₄⟩ => ?_
    have hf : Frame [stR s₀] s₃.mem s₄.mem := by
      rw [hm₄, hc.ebx]; exact VG.Proof.Sha256.X86.ShaNi.state_write_frame _ _ _ _
    have hfFull : Frame [stR s₀, scrR s₀] s₃.mem s₄.mem := hf.sub
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact ⟨stR s₀, by simp, fun _ h => h⟩)
    have hs : VG.Proof.Sha256.X86.Common s₀ (nb s₀) s₄ :=
      ⟨(congrFun hg₄ _).trans hc.esi, (congrFun hg₄ _).trans hc.esp,
        hrd₄.trans hc.rd, hwr₄.trans hc.wr, hc.frame.trans hfFull,
        by rw [hc.ebx] at hstate; exact hstate,
        saved_frame hp hc.saved (.inr hf)⟩
    refine WP.mono (restore_ok hp hs) fun s₅ ⟨hr, hm₅⟩ => ⟨⟨hr, ?_⟩, ?_⟩
    · rw [hm₅]
      exact hs.frame.readW (Region.contains_self _ _)
        (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
    · show stateAt s₅.mem _ = _
      rw [hm₅]; exact hs.state

end VG.Proof.Sha256.X86.ShaNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.ShaNi.Verified`. -/
section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86

theorem compress_verified :
    Verified X86.target Impl.Sha256.X86.ShaNi.compress Proof.Sha256.compressX86 :=
  ⟨fun s hs => VG.Proof.Sha256.X86.ShaNi.correct (VG.Proof.Sha256.X86.pre_of s hs),
    VG.Taint.constantTime (A := sseTaint) VG.Proof.Sha256.X86.τ₀
      (fun _ _ h₁ h₂ hpub => VG.Proof.Sha256.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Sha256.X86.satState, VG.Proof.Sha256.X86.sat_pre⟩⟩

theorem compress_nosp : NoSp Impl.Sha256.X86.ShaNi.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Sha256.X86.ShaNi.compress = 0 := by lit_decide

end VG.Proof.Sha256.X86.ShaNi

end
