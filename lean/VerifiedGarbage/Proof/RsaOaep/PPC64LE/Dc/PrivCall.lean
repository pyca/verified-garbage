module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivPre
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPCT
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

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
