import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedArgs

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)

variable {G : Spec.Mgf1.Hash}

theorem front_ok (v : PublicImpl)
    {s u : State} (hp : Pre G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 3)) (R : Rep u.mem (fb s) (stackArg s 3) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hM : Frame (vwrR s) s.mem u.mem) {lo a : Nat}
    (h17 : W 17 = s.gpr .rsi) (h18 : W 18 = s.gpr .rdi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h26 : W 26 = BitVec.ofNat 64 lo) (h38 : W 38 = s.gpr .r9)
    (hax : u.gpr .rax = BitVec.ofNat 64 a) :
    WP isa (seqs [.block dbSlots, .block Impl.RsaPss.X86_64.Precomputed.pubArgs, .call v.name v.code]) u fun u3 =>
      Lay u3 (fb s) (stackArg s 3) ∧ u3.wr = u.wr ∧ u3.rd = u.rd ∧
      (∀ r ∈ [Reg.r13, .r14, .r15], u3.gpr r = u.gpr r) ∧ Frame (vwrR s) s.mem u3.mem ∧
      ∃ V1 W1 x, Rep u3.mem (fb s) (stackArg s 3) V1 W1 ∧ (∀ j < nW, 4 ≤ j → j ≠ 23 → j ≠ 24 → W1 j = W j) ∧
        W1 23 = off (stackArg s 3) (oEm + lo) ∧ W1 24 = BitVec.ofNat 64 (a + 1) ∧
        x.length = (s.gpr .rsi).toNat ∧ (validCache s → x = vx s) ∧
        (∀ i < (s.gpr .rsi).toNat, V1 (oEm + i) = x.getD i 0) ∧
        (∀ o, ¬ (oEm ≤ o ∧ o < oEm + (s.gpr .rsi).toNat) → V1 o = V o) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  simp only [seqs]
  -- `DB`'s slots.
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R h26 hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hM1 := vframe_keep hp.toVPre hw L.rsp hM f1
  have g1 : ∀ j, j ≠ 23 → j ≠ 24 → upd (upd W 24 (BitVec.ofNat 64 (a + 1))) 23 (off (stackArg s 3) (oEm + lo)) j =
      W j := fun j h23 h24 => by simp [upd, h23, h24]
  -- The arguments.
  refine WP.seq (WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (args_ok hp L1 R1 (k1.2.2.trans hw) (k1.2.1.trans hrd) hM1 (by rw [g1 17 (by decide) (by decide), h17]) (by rw [g1 18 (by decide) (by decide), h18])
      (by rw [g1 19 (by decide) (by decide), h19]) (by rw [g1 20 (by decide) (by decide), h20])
      (by rw [g1 22 (by decide) (by decide), h22]) (by rw [g1 38 (by decide) (by decide), h38])))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ => ?_)
  have hw1 : u1.wr = frR s :: s.wr := k1.2.2.trans hw
  have hw2 : u2.wr = frR s :: s.wr := k2.2.2.trans hw1
  have hM2 := vframe_keep hp.toVPre hw1 L1.rsp hM1 f2
  -- The call.
  refine WP.mono (call_ok v hp L2.rsp ((k2.2.1.trans k1.2.1).trans hrd) hw2 hM2
    (fun i hi => (R2.fr i (by unfold nW frameBytes; omega)).trans (hW2a i hi)) h2di h2si h2dx h2cx h2r8 h2r9)
    fun u3 ⟨rd3, wr3, cs3, _, hM3, hk3, hout3⟩ => ?_
  have hEm : oEm + (s.gpr .rsi).toNat ≤ oRsa := by unfold oEm oRsa; omega
  have R3 := R2.of_em L2.geo hEm hk3
  have L3 : Lay u3 (fb s) (stackArg s 3) := L2.of_rep' R2 R3 rfl (cs3 .rsp (by decide)) wr3
  refine ⟨L3, wr3.trans (k2.2.2.trans k1.2.2), rd3.trans (k2.2.1.trans k1.2.1), fun r hr => ?_, hM3, _, _, Spec.Rsa.bytesAt u3.mem (off (stackArg s 3) oEm) (s.gpr .rsi).toNat, R3,
    fun j hj h4 h23 h24 => by rw [hW2b j hj h4, g1 j h23 h24], by rw [hW2b 23 (by decide) (by decide)]; simp [upd],
    by rw [hW2b 24 (by decide) (by decide)]; simp [upd], bytesAt_length .., ?_, fun i hi => ?_, fun o ho => ?_⟩
  · have hr3 : r = .r13 ∨ r = .r14 ∨ r = .r15 := by simpa using hr
    have h1 : r ∈ calleeSaved := by rcases hr3 with rfl | rfl | rfl <;> decide
    have h2 : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by rcases hr3 with rfl | rfl | rfl <;> decide
    rw [cs3 r h1, k2.gpr h2, k1.gpr (by rcases hr3 with rfl | rfl | rfl <;> decide)]
  · intro hc
    have hout := hout3 hc
    unfold vx
    cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat) with
    | none => rw [hpo] at hout; exact hout.2
    | some y => rw [hpo] at hout; exact hout.2
  · rw [bytesAt_off]
    simp only [ifp (show oEm ≤ oEm + i ∧ oEm + i < oEm + (s.gpr .rsi).toNat by omega)]
    rw [getD_map_range, ifp hi]
  · simp only [ifn ho]


end VG.Proof.RsaPss.X86_64.Pc
