module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.PrivArgs
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Spec
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

/-!
# RSASSA-PSS signing on PPC64LE: the private operation

Untrusted: everything here is checked by Lean. The call's narrowed entry
state (`callE`: it reads `n`, `e`, `EM`, the private key and its stack
arguments, and writes `out` and the rest of `scratch`), its precondition
(`preP_at`) and regions (`call_covers`); `priv_ok`: the private operation's
frame, its arguments and the call of `vg_rsa_private_checked` write RSASP1
of `EM`, checked against `e`, to `out` and return its code (`privOut`), and
leave what the restores need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr oEm oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx hiRegs kR fb fr Saves saved_offs)

/-- `out`, `EM` and the rest of `scratch`. -/
abbrev outR (s : State) : Region := ⟨s.gpr .r3, kk s⟩
abbrev emR (s : State) : Region := ⟨off (Ss s) oEm, kk s⟩
abbrev rsR (s : State) : Region := ⟨Ss s + BitVec.ofNat 64 oRsa, ((stackArg s 12).toNat - 1024) * 8⟩
/-- The call's stack arguments. -/
abbrev psaR (s : State) : Region := ⟨pb s + BitVec.ofNat 64 96, 96⟩

/-- The regions the call reads and writes. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s, psaR s]
abbrev callWr (s : State) : List Region := [outR s, rsR s]

/-- The call's narrowed entry state. -/
abbrev callE (s t : State) : State := t.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_sp (s t : State) : (callE s t).sp = t.sp := rfl

theorem callE_stackArg {s t : State} {em : List Byte} (A : AtPriv s em t) {i : Nat} (hi : i < 12) :
    stackArg (callE s t) i = psa s i := by
  show t.mem.readW (stackArgAddr (callE s t) i) 64 = _
  rw [stackArgAddr, callE_sp, A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega]
  exact A.psa i hi

theorem callE_addr {s t : State} {em : List Byte} (A : AtPriv s em t) :
    stackArgAddr (callE s t) 0 = pb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, callE_sp, A.sp]

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem em_sub : Region.Sub (emR s) (scR s) := fun a ha =>
  sc_sub P a (VG.Proof.RsaOaep.PPC64LE.sc_in (S := Ss) (s := s) (by have := P.k2; unfold kk oEm oRsa at *; omega) a ha)

theorem rs_sub : Region.Sub (rsR s) (scR s) := by
  have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this
  exact Offset.sub_base _ (by unfold oRsa; omega)

omit P in
theorem psa_subS : Region.Sub (psaR s) (kS s) := pb_sub s (by decide)

theorem em_rs : (emR s).Disjoint (rsR s) := by
  have h := Offset.disjoint_base (Ss s) (d := oRsa) (n := ((stackArg s 12).toNat - 1024) * 8) (k := kk s)
    (by have := P.k2; unfold kk oRsa; omega) (by have := P.wsc; have := scLen P; unfold oRsa at *; omega)
  have e : emR s = ⟨Ss s, kk s⟩ := by simp only [emR, off, show oEm = 0 from rfl, BitVec.add_zero]
  rw [e]; exact h.symm

theorem out_eq : outR s = oR s := by simp only [outR, oR, kk, P.ok]

theorem preP_at {t : State} {em : List Byte} (A : AtPriv s em t) : Rsa.PPC64LE.Priv.PreP (callE s t) := by
  have hk := P.k2
  have hk1 := P.k1
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have hsp : (callE s t).sp = pb s := A.sp
  have sp1 := P.sp1
  have hpbt : (pb s).toNat = s.sp.toNat - 448 := by
    rw [pb_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes + privBytes) (by decide)]
    unfold stackBytes at sp1; unfold frameBytes privBytes at *; omega
  have g3 : (callE s t).gpr .r3 = s.gpr .r3 := (callE_gpr s t).trans A.r3
  have g4 : (callE s t).gpr .r4 = s.gpr .r6 := (callE_gpr s t).trans A.r4
  have g5 : (callE s t).gpr .r5 = s.gpr .r5 := (callE_gpr s t).trans A.r5
  have g6 : (callE s t).gpr .r6 = s.gpr .r6 := (callE_gpr s t).trans A.r6
  have g7 : (callE s t).gpr .r7 = s.gpr .r7 := (callE_gpr s t).trans A.r7
  have g8 : (callE s t).gpr .r8 = s.gpr .r8 := (callE_gpr s t).trans A.r8
  have g9 : (callE s t).gpr .r9 = off (Ss s) oEm := (callE_gpr s t).trans A.r9
  have g10 : (callE s t).gpr .r10 = s.gpr .r6 := (callE_gpr s t).trans A.r10
  have hO : Rsa.PPC64LE.Priv.oR (callE s t) = oR s := by
    simp only [Rsa.PPC64LE.Priv.oR, g3, g4, oR, P.ok]
  have hN : Rsa.PPC64LE.Priv.nR (callE s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  have hE : Rsa.PPC64LE.Priv.eR (callE s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  have hI : Rsa.PPC64LE.Priv.iR (callE s t) = emR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10, emR, kk]
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
  have hl : 1024 ≤ (stackArg s 12).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega
  have w11 : (BitVec.ofNat 64 ((stackArg s 12).toNat - 1024)).toNat = (stackArg s 12).toNat - 1024 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackArg s 12).isLt; omega)]
  have hS : Rsa.PPC64LE.Priv.sR (callE s t) = rsR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide), psa, w11]
  have hA : Rsa.PPC64LE.Priv.aR (callE s t) = psaR s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  have hK : Rsa.PPC64LE.Priv.kR (callE s t) = ⟨s.sp - BitVec.ofNat 64 stackBytes,
      Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, pb_base, BitVec.add_sub_cancel]
  have kD' : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kS s) := by
    have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := Impl.Rsa.PPC64LE.Priv.frameBytes)
      (k := stackBytes) (by decide)
    rwa [BitVec.add_zero] at this
  have ka : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 stackBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR s) := by
    show Region.Disjoint _ ⟨pb s + BitVec.ofNat 64 96, 96⟩
    rw [pb_base, Offset.add_add]
    exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  have es := em_sub P
  have rss := rs_sub P
  have ps : Region.Sub (psaR s) (kS s) := psa_subS
  have s1 := sa 1 (by decide)
  have s3 := sa 3 (by decide)
  have s5 := sa 5 (by decide)
  have s7 := sa 7 (by decide)
  have s9 := sa 9 (by decide)
  have s11 := sa 11 (by decide)
  simp only [psa] at s1 s3 s5 s7 s9 s11
  have wS : (Ss s + BitVec.ofNat 64 oRsa).toNat = (stackArg s 11).toNat + oRsa := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oRsa) (by decide),
      Nat.mod_eq_of_lt (by
        have e : (Ss s).toNat = (stackArg s 11).toNat := rfl
        have := P.wsc; have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords oRsa at *; omega)]
  have q1 : Impl.Rsa.PPC64LE.Priv.frameBytes ≤ (callE s t).sp.toNat := by
    rw [hsp, hpbt]; rw [stackBytes_eq] at sp1; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega
  have q2 : (callE s t).sp.toNat + 192 ≤ 2 ^ 64 := by rw [hsp, hpbt]; have := P.sp2; omega
  have hkk : kk s = (s.gpr .r6).toNat := rfl
  refine ⟨q1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]; rfl
  · rw [hO, hS, ← out_eq P]; rfl
  · rw [hO, hN]; exact P.on
  · rw [hO, hE]; exact P.oe
  · rw [hO, hI]; exact P.os.sub_right es
  · rw [hO, hP]; exact P.op
  · rw [hO, hQ]; exact P.oq
  · rw [hO, hDP]; exact P.odp
  · rw [hO, hDQ]; exact P.odq
  · rw [hO, hQI]; exact P.oqi
  · rw [hO, hS]; exact P.os.sub_right rss
  · rw [hO, hA]; exact (P.ko.sub_left ps).symm
  · rw [hN, hS]; exact P.ns.sub_right rss
  · rw [hE, hS]; exact P.es.sub_right rss
  · rw [hI, hS]; exact em_rs P
  · rw [hP, hS]; exact P.ps.sub_right rss
  · rw [hQ, hS]; exact P.qs.sub_right rss
  · rw [hDP, hS]; exact P.dps.sub_right rss
  · rw [hDQ, hS]; exact P.dqs.sub_right rss
  · rw [hQI, hS]; exact P.qis.sub_right rss
  · rw [hS, hA]; exact ((P.ks.sub_left ps).sub_right rss).symm
  · rw [hK, hO]; exact P.ko.sub_left kD'
  · rw [hK, hN]; exact P.kn.sub_left kD'
  · rw [hK, hE]; exact P.ke.sub_left kD'
  · rw [hK, hI]; exact (P.ks.sub_left kD').sub_right es
  · rw [hK, hP]; exact P.kp.sub_left kD'
  · rw [hK, hQ]; exact P.kq.sub_left kD'
  · rw [hK, hDP]; exact P.kdp.sub_left kD'
  · rw [hK, hDQ]; exact P.kdq.sub_left kD'
  · rw [hK, hQI]; exact P.kqi.sub_left kD'
  · rw [hK, hS]; exact (P.ks.sub_left kD').sub_right rss
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; have := P.wo; rw [P.ok] at this; exact this
  · rw [g5, g6]; exact P.wn
  · rw [g7, g8]; exact P.we
  · rw [g9, g10]
    show (Ss s + BitVec.ofNat 64 oEm).toNat + _ ≤ _
    rw [show oEm = 0 from rfl, BitVec.add_zero]
    show (stackArg s 11).toNat + _ ≤ _; have := P.wsc; have := scLen P; unfold oRsa at *; omega
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
  · rw [s5, s1]; exact P.h3
  · rw [s9, s1]; exact P.h7
  · rw [s7, s3]; exact P.h5
  · rw [g6, s11, w11]; have := P.hs; unfold Spec.RsaPss.scratchWords at this; omega

theorem cov_sc {d n : Nat} (h : d + n ≤ (stackArg s 12).toNat * 8) :
    Covers [⟨Ss s + BitVec.ofNat 64 d, n⟩] s.wr :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr, P.hwr]
    exact ⟨scR s, by simp, d, rfl, h⟩

theorem call_covers {t : State} {em : List Byte} (A : AtPriv s em t) :
    Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hl : 1024 ≤ (stackArg s 12).toNat := by
    have := P.hs; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr]
    refine Covers.pair ?_ ?_
    · rw [out_eq P]
      exact Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by rw [P.hwr]; simp))
    · have := cov_sc P (d := oRsa) (n := ((stackArg s 12).toNat - 1024) * 8) (by unfold oRsa; omega)
      exact fun a n hi => let ⟨r, hr, hc⟩ := this a n hi; ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, P.hrd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · have := cov_sc P (d := oEm) (n := kk s) (by have := scLen P; have := P.k2; unfold kk oEm oRsa at *; omega)
    exact Covers.right fun a n hi => let ⟨r, hr, hc⟩ := this a n hi;
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨pb s + BitVec.ofNat 64 32, 160⟩, List.mem_cons_self .., 64, by
        show pb s + BitVec.ofNat 64 96 = pb s + BitVec.ofNat 64 32 + BitVec.ofNat 64 64
        rw [Offset.add_add], show 64 + 96 ≤ 160 by decide⟩)

omit P in
/-- The caller's buffers at the call are as on entry. -/
theorem bytes_at {t : State} {em : List Byte} (A : AtPriv s em t) {R : Region} (hd : (kS s).Disjoint R)
    (hs : (SC Ss s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.RsaOaep.PPC64LE.bytes_entry A.mem hd hs hl

omit P in
theorem fb_base (s : State) : fb s = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 (stackBytes - frameBytes) := by
  rw [← Offset.sub_sub_eq, Offset.ofNat_sub_ofNat (by decide)]; rfl

/-- The slots of our frame and what the call writes. -/
theorem slot_dis {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ callWr s ++ [below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  have hk : Region.Sub ⟨fb s + BitVec.ofNat 64 d, 8⟩ (kS s) := by
    rw [fb_base, Offset.add_add]; exact Offset.sub_base _ (by unfold stackBytes frameBytes at *; omega)
  intro r hr
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [out_eq P]; exact P.ko.sub_left hk
  · exact (P.ks.sub_left hk).sub_right (rs_sub P)
  · have e : below (pb s) Impl.Rsa.PPC64LE.Priv.frameBytes =
        ⟨(s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 0, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
      simp only [below, pb_base, BitVec.add_sub_cancel, BitVec.add_zero]
    rw [e, fb_base, Offset.add_add]
    exact Offset.disjoint _ (.inr (by unfold stackBytes frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes; omega))
      (by unfold stackBytes frameBytes privBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega) (by decide)

/-- After the private operation. -/
def AfterS (s : State) (em : List Byte) (w : State) : Prop :=
  Saves s w ∧ w.rd = s.rd ∧
    Spec.Rsa.writtenOutcome w.mem (s.gpr .r3) (kk s) ((w.gpr .r3).setWidth 32) (privOut s em)

theorem priv_ok {t : State} (h : Base Ss vS s t) {em : List Byte}
    (hem : Spec.Rsa.bytesAt t.mem (off (Ss s) oEm) (kk s) = em) : WP isa priv t (AfterS s em) := by
  have hsp : t.sp = fb s := h.sv.sp
  have hk := P.k2
  unfold priv
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by
    rw [hsp]; have := P.sp1
    rw [fb, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := frameBytes) (by decide)]
    rw [stackBytes_eq] at this; unfold frameBytes privBytes; omega) ?_
  refine WP.seq (WP.mono (privArgs_ok P h hem) fun u A => ?_)
  obtain ⟨hc, hw⟩ := call_covers P A
  unfold privCall
  refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
    (Rsa.PPC64LE.Priv.pre_of_preP (preP_at P A)) hc hw (fun v hrd hwr hsp' hf hpres hpost => ?_)
    (by rw [priv_sdepth]; decide)
  rw [priv_sdepth, A.sp] at hf
  -- The outcome.
  have sa := fun i hi => callE_stackArg A (i := i) hi
  simp only [Rsa.PPC64LE.Priv.fnContract, Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, callE_gpr s u (r := .r3), callE_gpr s u (r := .r5), callE_gpr s u (r := .r6),
    callE_gpr s u (r := .r7), callE_gpr s u (r := .r8), callE_gpr s u (r := .r9), A.r3, A.r5, A.r6, A.r7, A.r8,
    A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide),
    sa 6 (by decide), sa 8 (by decide), psa] at hpost
  have hb := fun {p : Addr} {len : Nat} (hd : (kS s).Disjoint ⟨p, len⟩) (hs : (scR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) => bytes_at A (R := ⟨p, len⟩) hd (hs.sub_left (sc_sub P)) hl
  rw [A.em, hb P.kn P.ns.symm (by have := P.wn; omega), hb P.ke P.es.symm (by have := P.we; omega),
    hb P.kp P.ps.symm (by have := P.wp; omega), hb P.kq P.qs.symm (by have := P.wq; omega),
    hb (by have := P.kdp; simp only [dpR, P.h3] at this; exact this)
      (by have := P.dps; simp only [dpR, P.h3] at this; exact this.symm) (by have := P.wdp; rw [P.h3] at this; omega),
    hb (by have := P.kdq; simp only [dqR, P.h5] at this; exact this)
      (by have := P.dqs; simp only [dqR, P.h5] at this; exact this.symm) (by have := P.wdq; rw [P.h5] at this; omega),
    hb (by have := P.kqi; simp only [qiR, P.h7] at this; exact this)
      (by have := P.qis; simp only [qiR, P.h7] at this; exact this.symm) (by have := P.wqi; rw [P.h7] at this; omega)]
    at hpost
  -- The state after the frame's release.
  have fsp : (freed privBytes v).sp = fb s := by
    show v.sp + BitVec.ofNat 64 privBytes = fb s
    rw [hsp', A.sp, BitVec.sub_add_cancel]
  have fwr : (freed privBytes v).wr = fr s :: s.wr := by
    show v.wr.tail = _; rw [hwr, A.wr]; rfl
  have svs : Spill.Saved (fb s) s.gpr saved v.mem :=
    A.sv.frame hf fun p hp r hr => slot_dis P (by have := saved_offs p hp; unfold oLr frameBytes at *; omega) r hr
  have lss : v.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [hf.readW (Region.contains_self _ _) (slot_dis P (by decide)) (by decide)]; exact A.ls
  refine ⟨⟨fsp, fwr, fun r hr => ?_, svs, lss⟩, by show v.rd = _; exact hrd.trans A.rd, ?_⟩
  · show v.gpr r = _; rw [hpres r (by revert r; decide)]; exact A.hi r hr
  · exact hpost

end

end VG.Proof.RsaPss.PPC64LE.Sg
