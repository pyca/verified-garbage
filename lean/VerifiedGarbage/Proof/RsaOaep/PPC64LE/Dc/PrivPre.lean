module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivArgs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP decryption on PPC64LE: the private operation's precondition

Untrusted: everything here is checked by Lean. The regions the call of
`vg_rsa_private_checked` is narrowed to (`callRd`, `callWr`): `n`, `e`, the
ciphertext, the private key and its stack arguments; `EM`'s place and the
rest of `scratch`. Its precondition at the call (`preP_at`), from the
caller's (`PreD`) and the state at the call (`AtPriv`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec

/-- `EM`'s place and the rest of `scratch`, which the call writes. -/
abbrev emR (s : State) : Region := ⟨Sd s, kk s⟩
abbrev rsR (s : State) : Region := ⟨Sd s + BitVec.ofNat 64 oRsa, ((stackArg s 14).toNat - 1024) * 8⟩
/-- The call's stack arguments. -/
abbrev psaR (s : State) : Region := ⟨pb s + BitVec.ofNat 64 96, 96⟩

/-- The regions the call reads and writes. -/
abbrev callRd (s : State) : List Region :=
  [nR s, eR s, ⟨stackArg s 11, kk s⟩, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev callWr (s : State) : List Region := [emR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (s t : State) : State := t.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_sp (s t : State) : (callE s t).sp = t.sp := rfl
theorem callE_mem (s t : State) : (callE s t).mem = t.mem := rfl

theorem callE_stackArg {s t : State} (A : AtPriv s t) {i : Nat} (hi : i < 12) :
    stackArg (callE s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE s t) i) 64 = _
  rw [stackArgAddr, callE_sp, A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega]
  exact A.psa i hi

theorem callE_addr {s t : State} (A : AtPriv s t) : stackArgAddr (callE s t) 0 = pb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, callE_sp, A.sp]

/-- The private operation's frame, below ours. -/
theorem privK (s : State) :
    Rsa.PPC64LE.Priv.kR { s with sp := pb s } = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
  simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, pb_base, BitVec.add_sub_cancel]

section
variable {s : State} (P : PreD s)
include P

theorem kk_le : kk s ≤ 1024 := P.k2

theorem em_sub : Region.Sub (emR s) (scR s) :=
  Region.sub_prefix (by show kk s ≤ _; have := scLen P; have := P.k2; unfold kk oRsa at *; omega)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this
  exact Offset.sub_base _ (by unfold oRsa; omega)

omit P in
theorem psa_subD : Region.Sub (psaR s) (kD s) := pb_sub s (by decide)

theorem em_rs : (emR s).Disjoint (rsR s) := by
  have h := Offset.disjoint_base (Sd s) (d := oRsa) (n := ((stackArg s 14).toNat - 1024) * 8) (k := kk s)
    (by have := P.k2; unfold kk oRsa; omega) (by have := P.wsc; have := scLen P; unfold oRsa at *; omega)
  exact h.symm

theorem preP_at {t : State} (A : AtPriv s t) : Rsa.PPC64LE.Priv.PreP (callE s t) := by
  have hk := P.k2
  have hk1 := P.k1
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have hsp : (callE s t).sp = pb s := A.sp
  have sp1 := P.sp1
  have hpbt : (pb s).toNat = s.sp.toNat - 448 := by
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes) (by decide)]
    unfold stackBytes at sp1; unfold frameBytes privBytes at *; omega
  have g3 : (callE s t).gpr .r3 = Sd s := (callE_gpr s t).trans A.r3
  have g4 : (callE s t).gpr .r4 = s.gpr .r7 := (callE_gpr s t).trans A.r4
  have g5 : (callE s t).gpr .r5 = s.gpr .r6 := (callE_gpr s t).trans A.r5
  have g6 : (callE s t).gpr .r6 = s.gpr .r7 := (callE_gpr s t).trans A.r6
  have g7 : (callE s t).gpr .r7 = s.gpr .r8 := (callE_gpr s t).trans A.r7
  have g8 : (callE s t).gpr .r8 = s.gpr .r9 := (callE_gpr s t).trans A.r8
  have g9 : (callE s t).gpr .r9 = stackArg s 11 := (callE_gpr s t).trans A.r9
  have g10 : (callE s t).gpr .r10 = s.gpr .r7 := (callE_gpr s t).trans A.r10
  have hO : Rsa.PPC64LE.Priv.oR (callE s t) = emR s := by simp only [Rsa.PPC64LE.Priv.oR, g3, g4, emR, kk]
  have hN : Rsa.PPC64LE.Priv.nR (callE s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  have hE : Rsa.PPC64LE.Priv.eR (callE s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  have hI : Rsa.PPC64LE.Priv.iR (callE s t) = ctR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, ctR, P.oc]
  have hI' : (⟨stackArg s 11, kk s⟩ : Region) = ctR s := by simp only [ctR, kk, P.oc]
  have hP : Rsa.PPC64LE.Priv.pR (callE s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]; rfl
  have hQ : Rsa.PPC64LE.Priv.qR (callE s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]; rfl
  have hDP : Rsa.PPC64LE.Priv.dpR (callE s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]; rfl
  have hDQ : Rsa.PPC64LE.Priv.dqR (callE s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]; rfl
  have hQI : Rsa.PPC64LE.Priv.qiR (callE s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]; rfl
  have hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega
  have w11 : (BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega)]
  have hS : Rsa.PPC64LE.Priv.sR (callE s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hA : Rsa.PPC64LE.Priv.aR (callE s t) = psaR s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  have hK : Rsa.PPC64LE.Priv.kR (callE s t) = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  have kD' : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kD s) := by
    have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
      (k := stackBytes) (by decide)
    rwa [BitVec.add_zero] at this
  have ka : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR s) := by
    show Region.Disjoint _ ⟨pb s + BitVec.ofNat 64 96, 96⟩
    rw [pb_base, Offset.add_add]
    exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  have es := em_sub P
  have rss := rs_sub P
  have ps : Region.Sub (psaR s) (kD s) := psa_subD
  have s1 := sa 1 (by decide)
  have s3 := sa 3 (by decide)
  have s5 := sa 5 (by decide)
  have s7 := sa 7 (by decide)
  have s9 := sa 9 (by decide)
  have s11 := sa 11 (by decide)
  simp only [psa] at s1 s3 s5 s7 s9 s11
  have wS : (Sd s + BitVec.ofNat 64 oRsa).toNat = (stackArg s 13).toNat + oRsa := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oRsa) (by decide),
      Nat.mod_eq_of_lt (by
        have e : (Sd s).toNat = (stackArg s 13).toNat := rfl
        have := P.wsc; have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords oRsa at *; omega)]
  have q1 : Impl.Rsa.PPC64LE.Priv.frameBytes ≤ (callE s t).sp.toNat := by
    rw [hsp, hpbt]; rw [stackBytes_eq] at sp1; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega
  have q2 : (callE s t).sp.toNat + 192 ≤ 2 ^ 64 := by rw [hsp, hpbt]; have := P.sp2; omega
  have hkk : kk s = (s.gpr .r7).toNat := rfl
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA, ← hI']; rfl
  · rw [hO, hS]; rfl
  · rw [hO, hN]; exact (P.ns.sub_right es).symm
  · rw [hO, hE]; exact (P.es.sub_right es).symm
  · rw [hO, hI]; exact (P.cts.sub_right es).symm
  · rw [hO, hP]; exact (P.ps.sub_right es).symm
  · rw [hO, hQ]; exact (P.qs.sub_right es).symm
  · rw [hO, hDP]; exact (P.dps.sub_right es).symm
  · rw [hO, hDQ]; exact (P.dqs.sub_right es).symm
  · rw [hO, hQI]; exact (P.qis.sub_right es).symm
  · rw [hO, hS]; exact em_rs P
  · rw [hO, hA]; exact ((P.ks.sub_left ps).sub_right es).symm
  · rw [hN, hS]; exact P.ns.sub_right rss
  · rw [hE, hS]; exact P.es.sub_right rss
  · rw [hI, hS]; exact P.cts.sub_right rss
  · rw [hP, hS]; exact P.ps.sub_right rss
  · rw [hQ, hS]; exact P.qs.sub_right rss
  · rw [hDP, hS]; exact P.dps.sub_right rss
  · rw [hDQ, hS]; exact P.dqs.sub_right rss
  · rw [hQI, hS]; exact P.qis.sub_right rss
  · rw [hS, hA]; exact ((P.ks.sub_left ps).sub_right rss).symm
  · rw [hK, hO]; exact (P.ks.sub_left kD').sub_right es
  · rw [hK, hN]; exact P.kn.sub_left kD'
  · rw [hK, hE]; exact P.ke.sub_left kD'
  · rw [hK, hI]; exact P.kct.sub_left kD'
  · rw [hK, hP]; exact P.kp.sub_left kD'
  · rw [hK, hQ]; exact P.kq.sub_left kD'
  · rw [hK, hDP]; exact P.kdp.sub_left kD'
  · rw [hK, hDQ]; exact P.kdq.sub_left kD'
  · rw [hK, hQI]; exact P.kqi.sub_left kD'
  · rw [hK, hS]; exact (P.ks.sub_left kD').sub_right rss
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; show (stackArg s 13).toNat + _ ≤ _; have := P.wsc; have := scLen P; unfold oRsa at *; omega
  · rw [g5, g6]; exact P.wn
  · rw [g7, g8]; exact P.we
  · rw [g9, g10, ← P.oc]; exact P.wct
  · rw [sa 0 (by decide), s1]; exact P.wp
  · rw [sa 2 (by decide), s3]; exact P.wq
  · rw [sa 4 (by decide), s5]; exact P.wdp
  · rw [sa 6 (by decide), s7]; exact P.wdq
  · rw [sa 8 (by decide), s9]; exact P.wqi
  · rw [sa 10 (by decide), s11, w11]; simp only [psa]; rw [wS]; have := P.wsc; unfold oRsa; omega
  · rw [g6]; exact hk1
  · rw [g6]; exact hk
  · rw [g4, g6]
  · rw [g10, g6]
  · rw [g8]; exact P.e1
  · rw [g8, g6]; exact P.e2
  · rw [s1]; exact P.p1
  · rw [s1, g6]; exact P.p2
  · rw [s3]; exact P.q1
  · rw [s3, g6]; exact P.q2
  · rw [s5, s1]; exact P.h4
  · rw [s9, s1]; exact P.h8
  · rw [s7, s3]; exact P.h6
  · rw [g6, s11, w11]; have := P.hs; unfold Spec.RsaPss.scratchWords at this; omega

end

end VG.Proof.RsaOaep.PPC64LE.Dec
