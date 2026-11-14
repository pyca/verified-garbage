module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivArgs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPreCopy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaOaep.PPC64LE.Dc.PrivPre`, which only this module used -/

section

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
variable {pc : Bool}

/-- The call's stack arguments: twelve, or with `pc` fourteen. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨pb s + BitVec.ofNat 64 96, if pc then 112 else 96⟩

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, ⟨stackArg s 11, kk s⟩, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++
    [psaR pc s]

abbrev callWr (s : State) : List Region := [emR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_sp (s t : State) : (callE pc s t).sp = t.sp := rfl
theorem callE_stackArg {s t : State} (A : AtPriv pc s t) {i : Nat} (hi : i < nCallArgs pc) :
    stackArg (callE pc s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, callE_sp, A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]
  exact A.psa i hi

theorem callE_addr {s t : State} (A : AtPriv pc s t) : stackArgAddr (callE pc s t) 0 = pb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, callE_sp, A.sp]

theorem lt_nCall {i : Nat} (hi : i < 12) : i < nCallArgs pc := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hi]

theorem psa_subD (s : State) : Region.Sub (psaR pc s) (kD s) := by
  cases pc
  · exact pb_sub s (by decide)
  · exact pb_sub s (by decide)

/-- The callee's frame and the call's stack arguments. -/
theorem callee_psa (s : State) :
    Region.Disjoint ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR pc s) := by
  show Region.Disjoint _ ⟨pb s + BitVec.ofNat 64 96, _⟩
  rw [pb_base, Offset.add_add]
  cases pc
  · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  · exact (Offset.disjoint_base _ (by decide) (by decide)).symm

section
variable {s : State} (P : PreD pc s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) :=
  Region.sub_prefix (by show kk s ≤ _; have := scLen P; have := P.k2; unfold kk oRsa at *; omega_arith)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this
  exact Offset.sub_base _ (by unfold oRsa; omega_using [this])


theorem em_rs : (emR s).Disjoint (rsR s) := by
  have h := Offset.disjoint_base (Sd s) (d := oRsa) (n := ((stackArg s 14).toNat - 1024) * 8) (k := kk s)
    (by have := P.k2; unfold kk oRsa; omega_using [this]) (by have := P.wsc; have := scLen P; unfold oRsa at *; omega_arith)
  exact h.symm

theorem pb_toNat : (pb s).toNat = s.sp.toNat - 464 := by
  have sp1 := P.sp1
  rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes) (by decide)]
  unfold stackBytes at sp1; unfold frameBytes privBytes at *; omega_using [sp1]

theorem preP_at {t : State} (A : AtPriv pc s t) : Rsa.PPC64LE.Priv.PreP pc (callE pc s t) := by
  have hk := P.k2
  have hk1 := P.k1
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  have hsp : (callE pc s t).sp = pb s := A.sp
  have sp1 := P.sp1
  have hpbt : (pb s).toNat = s.sp.toNat - 464 := by
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes) (by decide)]
    unfold stackBytes at sp1; unfold frameBytes privBytes at *; omega_using [sp1]
  have g3 : (callE pc s t).gpr .r3 = Sd s := (callE_gpr (pc := pc) s t).trans A.r3
  have g4 : (callE pc s t).gpr .r4 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r4
  have g5 : (callE pc s t).gpr .r5 = s.gpr .r6 := (callE_gpr (pc := pc) s t).trans A.r5
  have g6 : (callE pc s t).gpr .r6 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r6
  have g7 : (callE pc s t).gpr .r7 = s.gpr .r8 := (callE_gpr (pc := pc) s t).trans A.r7
  have g8 : (callE pc s t).gpr .r8 = s.gpr .r9 := (callE_gpr (pc := pc) s t).trans A.r8
  have g9 : (callE pc s t).gpr .r9 = stackArg s 11 := (callE_gpr (pc := pc) s t).trans A.r9
  have g10 : (callE pc s t).gpr .r10 = s.gpr .r7 := (callE_gpr (pc := pc) s t).trans A.r10
  have hO : Rsa.PPC64LE.Priv.oR (callE pc s t) = emR s := by simp only [Rsa.PPC64LE.Priv.oR, g3, g4, emR, kk]
  have hN : Rsa.PPC64LE.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  have hE : Rsa.PPC64LE.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  have hI : Rsa.PPC64LE.Priv.iR (callE pc s t) = ctR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, ctR, P.oc]
  have hI' : (⟨stackArg s 11, kk s⟩ : Region) = ctR s := by simp only [ctR, kk, P.oc]
  have hP : Rsa.PPC64LE.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]; rfl
  have hQ : Rsa.PPC64LE.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]; rfl
  have hDP : Rsa.PPC64LE.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]; rfl
  have hDQ : Rsa.PPC64LE.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]; rfl
  have hQI : Rsa.PPC64LE.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]; rfl
  have hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have w11 : (BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega_using [])]
  have hS : Rsa.PPC64LE.Priv.sR (callE pc s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hA : Rsa.PPC64LE.Priv.aR pc (callE pc s t) = psaR pc s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  have hK : Rsa.PPC64LE.Priv.kR (callE pc s t) = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  have kD' : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kD s) := by
    have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
      (k := stackBytes) (by decide)
    rwa [BitVec.add_zero] at this
  have ka := callee_psa (pc := pc) s
  have es := em_sub P
  have rss := rs_sub P
  have ps : Region.Sub (psaR pc s) (kD s) := psa_subD s
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
        have := P.wsc; have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords oRsa at *; omega_arith)]
  have q1 : Impl.Rsa.PPC64LE.Priv.frameBytes ≤ (callE pc s t).sp.toNat := by
    rw [hsp, hpbt]; rw [stackBytes_eq] at sp1; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [sp1]
  have q2 : (callE pc s t).sp.toNat + 192 ≤ 2 ^ 64 := by rw [hsp, hpbt]; have := P.sp2; split at this <;> omega_using []
  have hkk : kk s = (s.gpr .r7).toNat := rfl
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rsa.PPC64LE.Priv.rdL]
    rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA, ← hI']
    cases pc
    · rfl
    · simp only [↓reduceIte, Rsa.PPC64LE.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide), psa]
      rfl
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
  · rw [g3, g4]; show (stackArg s 13).toNat + _ ≤ _; have := P.wsc; have := scLen P; unfold oRsa at *; omega_using [hk, wS]
  · rw [g5, g6]; exact P.wn
  · rw [g7, g8]; exact P.we
  · rw [g9, g10, ← P.oc]; exact P.wct
  · rw [sa 0 (by decide), s1]; exact P.wp
  · rw [sa 2 (by decide), s3]; exact P.wq
  · rw [sa 4 (by decide), s5]; exact P.wdp
  · rw [sa 6 (by decide), s7]; exact P.wdq
  · rw [sa 8 (by decide), s9]; exact P.wqi
  · rw [sa 10 (by decide), s11, w11]; simp only [psa]; rw [wS]; have := P.wsc; unfold oRsa; omega_using [hl, this]
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
  · rw [g6, s11, w11]; have := P.hs; unfold Spec.RsaPss.scratchWords at this; omega_using [this]

end

end VG.Proof.RsaOaep.PPC64LE.Dec

end

end


/-!
# RSAES-OAEP decryption on PPC64LE: the private operation

Untrusted: everything here is checked by Lean. `priv_ok`: the private
operation's frame, its arguments, the call of `vg_rsa_private_checked` and
its result zero-extended into `r20` leave `EM` (or zeros) at `scratch` and
the outcome's code (`rcOf`) in `r20`, and the state `Base` needs for the
decoding (`AfterPriv`), with memory from after the call as the entry's.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_lsrw wp_nil)

/-- RSADP checked against `e`, of the entry's buffers. -/
def privO (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 11) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 0).toNat)

/-- The result's code: 1, 0 or 2. -/
def rcOf : Spec.Rsa.Outcome → Nat
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

/-- What it writes to `EM`'s place. -/
def emOf (k : Nat) : Spec.Rsa.Outcome → List Byte
  | .ok y => y
  | _ => List.replicate k 0

/-- The entry state with memory `m`, as `Base` takes it for the decoding. -/
abbrev withMem (s : State) (m : Mem) : State := { s with mem := m }

/-- After the private operation. -/
structure AfterPriv (s v : State) : Prop where
  base : Base (SD s) (VD s (rcOf (privO s))) (withMem s v.mem) v
  mem : Frame [kD s, scR s] s.mem v.mem
  em : Spec.Rsa.bytesAt v.mem (Sd s) (kk s) = emOf (kk s) (privO s)

theorem rcOf_le (o : Spec.Rsa.Outcome) : rcOf o ≤ 2 := by cases o <;> simp [rcOf]

/-- The outcome, from `writtenOutcome`. -/
theorem of_written {m : Mem} {p : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Spec.Rsa.writtenOutcome m p k r o) : r = BitVec.ofNat 32 (rcOf o) ∧ Spec.Rsa.bytesAt m p k = emOf k o := by
  cases o with
  | ok y => exact ⟨h.1, h.2⟩
  | invalid => exact ⟨h.1, h.2⟩
  | fault => exact ⟨h.1, h.2⟩

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel
theorem privP_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.codeP = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

section
variable {pc : Bool} {s : State} (P : PreD pc s)
include P

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 14).toNat * 8) :
    Covers [⟨Sd s + BitVec.ofNat 64 d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} (A : AtPriv pc s t) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · have := cov_sc P (d := 0) (n := kk s) (by have := scLen P; have := P.k2; unfold kk oRsa at *; omega_using [hl, this])
      rw [BitVec.add_zero] at this
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
    · have := cov_sc P (d := oRsa) (n := ((stackArg s 14).toNat - 1024) * 8) (by unfold oRsa; omega_using [hl])
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  have hct : (⟨stackArg s 11, kk s⟩ : Region) = ctR s := by simp only [ctR, kk, P.oc]
  have hpsa : Covers [psaR pc s] (rdL pc s ++ ⟨pb s + BitVec.ofNat 64 32, 176⟩ :: fr s :: s.wr) :=
    Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine ⟨⟨pb s + BitVec.ofNat 64 32, 176⟩, List.mem_cons_self .., 64, ?_, ?_⟩
      · show pb s + BitVec.ofNat 64 96 = pb s + BitVec.ofNat 64 32 + BitVec.ofNat 64 64
        rw [Offset.add_add]
      · show 64 + (if pc then 112 else 96) ≤ 176
        cases pc <;> decide)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hr) | rfl
  rotate_left 8
  · cases pc
    · simp at hr
    · simp only [↓reduceIte, List.mem_singleton] at hr
      subst hr
      exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact hpsa
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hct]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} (A : AtPriv pc s t) {R : Region} (hd : (kD s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => A.mem.bytes (R := R) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd.symm) hl (List.mem_range.mp hi)

omit P in
theorem fb_base (s : State) : fb s = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 (stackBytes - frameBytes) := by
  rw [← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by decide)]; rfl

/-- The slots of our frame and what the call writes. -/
theorem slot_dis {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ callWr s ++ [below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  have hk : Region.Sub ⟨fb s + BitVec.ofNat 64 d, 8⟩ (kD s) := by
    rw [fb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes frameBytes at *; omega_using [hd])
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (P.ks.sub_left hk).sub_right (em_sub P)
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · have e : below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes =
        ⟨(s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 0, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
      simp only [below, pb_base, BitVec.add_sub_cancel, BitVec.add_zero]
    rw [e, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using []))
      (by unfold stackBytes frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega_using [hd]) (by decide)

/-- With `pc`, the precondition `vg_rsa_private_checked_precomputed` adds. -/
theorem preX_at (X : PreXD s) {t : State} (A : AtPriv true s t) : Rsa.PPC64LE.Priv.PreX (callE true s t) := by
  have sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = pb s := A.sp
  have hpbt := pb_toNat P
  have sp2 := P.sp2
  have hPre : Rsa.PPC64LE.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.PPC64LE.Priv.preR, sa 12 (by decide), sa 13 (by decide), psa]
  have hO : Rsa.PPC64LE.Priv.oR (callE true s t) = emR s := by
    simp only [Rsa.PPC64LE.Priv.oR, callE_gpr (pc := true) s t (r := .r3), callE_gpr (pc := true) s t (r := .r4),
      A.r3, A.r4, emR, kk]
  have hl : 1024 ≤ (stackArg s 14).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega_using [this]
  have w11 : (BitVec.ofNat 64 ((stackArg s 14).toNat - 1024)).toNat = (stackArg s 14).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 14).isLt; omega_using [])]
  have hS : Rsa.PPC64LE.Priv.sR (callE true s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hK : Rsa.PPC64LE.Priv.kR (callE true s t) = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  have kD' : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kD s) := by
    have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
      (k := stackBytes) (by decide)
    rwa [BitVec.add_zero] at this
  refine ⟨by rw [hO, hPre]; exact X.sP.sub_left (em_sub P), by rw [hS, hPre]; exact X.sP.sub_left (rs_sub P),
    by rw [hK, hPre]; exact X.kP.sub_left kD', ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr (pc := true) s t (r := .r6), A.r6]
    exact X.pl
  · rw [hsp, hpbt]; omega_using []
  · have hb := fun {p : Addr} {len : Nat} (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
      bytes_at A (R := ⟨p, len⟩) hd hl
    have hw := VG.Proof.Rsa.PPC64LE.Priv.words_of_frame A.mem (p := stackArg s 17) (n := (stackArg s 18).toNat)
      (fun r hr => by rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.PPC64LE.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem,
      callE_gpr (pc := true) s t (r := .r5), callE_gpr (pc := true) s t (r := .r6), A.r5, A.r6, sa 0 (by decide),
      sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), psa, hw]
    rw [hb P.kn (by have := P.wn; omega_using []), hb P.kp (by have := P.wp; omega_using []), hb P.kq (by have := P.wq; omega_using [])]
    exact X.hyp

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv (X : pc = true → PreXD s) {u : State} (A : AtPriv pc s u) :
    WP isa (privCall pc) u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧
      Frame (callWr s ++ [below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes]) u.mem v.mem ∧
      (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
      Rsa.PPC64LE.Priv.fnPost (callE pc s u) (v.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers P A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
      (Rsa.PPC64LE.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContractP) Rsa.PPC64LE.Priv.codeP_correct
      (Rsa.PPC64LE.Priv.pre_of_prePX (preP_at P A) (preX_at P (X rfl) A)) hc hw
      (fun v hrd hwr hsp hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth, A.sp] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩

/-- The private operation's frame, with the stack pointer after it. -/
theorem privF_ok (X : pc = true → PreXD s) {t : State} (E : Entered s t) :
    WP isa (.frame (.alloc privBytes) (.seq (.block (privArgs ++ preArgs pc)) (privCall pc)) (.free privBytes)) t
      fun w => w.sp = fb s ∧ WP isa (.block [.lsr .w .r20 .r3 0]) w (AfterPriv s) := by
  have hsp : t.sp = fb s := E.sv.sp
  have hk := P.k2
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by
    rw [hsp]; have := P.sp1
    rw [fb, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes) (by decide)]
    rw [stackBytes_eq] at this; unfold frameBytes privBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono (privArgsG_ok P E) fun u A => ?_)
  refine WP.mono (call_priv P X A) fun v ⟨hrd, hwr, hsp', hf, hpres, hpost⟩ => ?_
  have fsp : (freed privBytes v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 privBytes = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  refine ⟨fsp, wp_lsrw fun w ow ew => wp_nil ?_⟩
  -- The outcome.
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  simp only [Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr (pc := pc) s u (r := .r3), callE_gpr (pc := pc) s u (r := .r5),
    callE_gpr (pc := pc) s u (r := .r6), callE_gpr (pc := pc) s u (r := .r7), callE_gpr (pc := pc) s u (r := .r8),
    callE_gpr (pc := pc) s u (r := .r9), A.r3, A.r5, A.r6, A.r7, A.r8,
    A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide),
    sa 6 (by decide), sa 8 (by decide), psa] at hpost
  have hb := fun {p : Addr} {len : Nat} (hd : (kD s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) =>
    bytes_at A (R := ⟨p, len⟩) hd hl
  rw [hb P.kn (by have := P.wn; omega_using []), hb P.ke (by have := P.we; omega_using []),
    hb (by have := P.kct; simp only [ctR, P.oc] at this; exact this) (by omega_using []),
    hb P.kp (by have := P.wp; omega_using []), hb P.kq (by have := P.wq; omega_using []),
    hb (by have := P.kdp; simp only [dpR, P.h4] at this; exact this) (by have := P.wdp; omega_using []),
    hb (by have := P.kdq; simp only [dqR, P.h6] at this; exact this) (by have := P.wdq; omega_using []),
    hb (by have := P.kqi; simp only [qiR, P.h8] at this; exact this) (by have := P.wqi; omega_using [])] at hpost
  change Spec.Rsa.writtenOutcome _ _ _ _ (privO s) at hpost
  obtain ⟨hr, hem⟩ := of_written hpost
  -- The state after the frame's release.
  have fwr : (freed privBytes v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  have wsp : w.sp = fb s := by rw [ow.sp]; exact fsp
  have wg : ∀ r, r ≠ .r20 → w.gpr r = v.gpr r := fun r hr' => ow.gpr r (by simpa using hr')
  have wm : w.mem = v.mem := ow.mem
  have pv : ∀ r ∈ preserved, r ≠ .r20 → w.gpr r = u.gpr r := fun r hr' h20 => (wg r h20).trans (hpres r hr')
  have r20 : w.gpr .r20 = BitVec.ofNat 64 (rcOf (privO s)) := by
    rw [ew]; show ((v.gpr .r3).setWidth 32 >>> 0).setWidth 64 = _
    rw [hr, BitVec.ushiftRight_zero]
    apply BitVec.eq_of_toNat_eq
    have := rcOf_le (privO s)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := rcOf _) (by omega_using [this]), Nat.mod_eq_of_lt (a := rcOf _) (by omega_using [this])]
  have fm : Frame [kD s, scR s] s.mem w.mem := by
    rw [wm]
    refine (A.mem.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans (hf.sub fun r hr => ?_)
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s, by simp, em_sub P⟩
    · exact ⟨scR s, by simp, rs_sub P⟩
    · refine ⟨kD s, by simp, ?_⟩
      have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
        (k := stackBytes) (by decide)
      rw [BitVec.add_zero] at this
      simpa only [below, pb_base, BitVec.add_sub_cancel] using this
  have svs : Spill.Saved (fb s) s.gpr saved w.mem := by
    rw [wm]; exact A.sv.frame hf fun p hp r hr =>
      slot_dis P (by have := saved_offs p hp; unfold oLr frameBytes at *; omega_using [this]) r hr
  have lss : w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [wm, hf.readW (Region.contains_self _ _) (slot_dis P (by decide)) (by decide)]; exact A.ls
  refine ⟨⟨⟨wsp, by rw [ow.wr]; exact fwr, fun r hr => ?_, svs, lss⟩, by rw [ow.rd]; exact hrd.trans A.rd, ?_, ?_,
    Frame.refl _ _⟩, fm, by rw [wm, hem]⟩
  · rw [pv r (by revert r; decide) (by revert r; decide)]; exact A.hi r hr
  · rw [pv .r14 (by decide) (by decide)]; exact A.r14
  · intro r hr
    simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [pv _ (by decide) (by decide)]; exact A.r15
    · rw [pv _ (by decide) (by decide)]; exact A.r16
    · rw [pv _ (by decide) (by decide)]; exact A.r17
    · rw [pv _ (by decide) (by decide)]; exact A.r18
    · rw [pv _ (by decide) (by decide)]; exact A.r19
    · exact r20
    · rw [pv _ (by decide) (by decide)]; exact A.keep _ (by decide)
    · rw [pv _ (by decide) (by decide)]; exact A.keep _ (by decide)
    · rw [pv _ (by decide) (by decide)]; exact A.keep _ (by decide)

theorem priv_ok (X : pc = true → PreXD s) {t : State} (E : Entered s t) : WP isa (priv pc) t (AfterPriv s) :=
  WP.seq (WP.mono (privF_ok P X E) fun _ h => h.2)

end

end VG.Proof.RsaOaep.PPC64LE.Dec
