module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignArgs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPre
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the call of `vg_rsa_private_checked`

The regions the call is narrowed to (`callRd`, `callWr`), its precondition
(`preP_entry`, `Priv.pre_of_preP`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign

/-- The regions the call reads and writes. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev callWr (s : State) : List Region := [⟨s.gpr .r3, (s.gpr .r6).toNat⟩, sR s]

/-- The call's narrowed entry state. -/
abbrev callE (s t : State) : State := t.callEntry.withRegions (callRd s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} {em : List Byte} (A : AtCall s t em) {i : Nat} (hi : i < 12) :
    stackArg (callE s t) i = stackArg s (1 + i) := by
  show t.mem.readW (stackArgAddr (callE s t) i) 64 = _
  rw [stackArgAddr, show (callE s t).sp = fb s from A.sp, show 32 + 8 * (8 + i) = 96 + 8 * i by omega]
  exact A.psa i hi

theorem callE_addr {s t : State} {em : List Byte} (A : AtCall s t em) :
    stackArgAddr (callE s t) 0 = fb s + BitVec.ofNat 64 96 := by
  rw [stackArgAddr, show (callE s t).sp = fb s from A.sp]

theorem preP_entry {s t : State} {em : List Byte} (h : SPre s) (A : AtCall s t em) :
    Rsa.PPC64LE.Priv.PreP (callE s t) := by
  have hk := h.k2
  have fbt := fb_toNat h
  have kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  have sa := fun i hi => callE_stackArg A (i := i) hi
  have hsp : (callE s t).sp = fb s := A.sp
  have hOo : (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
  have cs := callee_sub s
  have es := em_sub h
  have ps : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  have hK : Rsa.PPC64LE.Priv.kR (callE s t) = ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    simp only [Rsa.PPC64LE.Priv.kR, Rsa.PPC64LE.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  have ki : Region.Disjoint ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (emR s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 oEM, _⟩
    rw [fb_eq, Offset.add_add]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega)
      (by unfold oEM Impl.Rsa.PPC64LE.Priv.frameBytes; omega)).symm
  have ka : Region.Disjoint ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (psaR s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 96, _⟩
    rw [fb_eq, Offset.add_add]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega)
      (by unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega)).symm
  have cs' : Region.Sub ⟨kb s, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ (kR s) := by
    have := cs; rwa [fb_eq, BitVec.add_sub_cancel] at this
  have g3 : (callE s t).gpr .r3 = s.gpr .r3 := (callE_gpr s t).trans A.r3
  have g4 : (callE s t).gpr .r4 = s.gpr .r6 := (callE_gpr s t).trans A.r4
  have g5 : (callE s t).gpr .r5 = s.gpr .r5 := (callE_gpr s t).trans A.r5
  have g6 : (callE s t).gpr .r6 = s.gpr .r6 := (callE_gpr s t).trans A.r6
  have g7 : (callE s t).gpr .r7 = s.gpr .r7 := (callE_gpr s t).trans A.r7
  have g8 : (callE s t).gpr .r8 = s.gpr .r8 := (callE_gpr s t).trans A.r8
  have g9 : (callE s t).gpr .r9 = fb s + BitVec.ofNat 64 oEM := (callE_gpr s t).trans A.r9
  have g10 : (callE s t).gpr .r10 = s.gpr .r6 := (callE_gpr s t).trans A.r10
  have hO : Rsa.PPC64LE.Priv.oR (callE s t) = oR s := by simp only [Rsa.PPC64LE.Priv.oR, g3, g4, oR, h.h4]
  have hN : Rsa.PPC64LE.Priv.nR (callE s t) = nR s := by simp only [Rsa.PPC64LE.Priv.nR, g5, g6]
  have hE : Rsa.PPC64LE.Priv.eR (callE s t) = eR s := by simp only [Rsa.PPC64LE.Priv.eR, g7, g8]
  have hI : Rsa.PPC64LE.Priv.iR (callE s t) = emR s := by simp only [Rsa.PPC64LE.Priv.iR, g9, g10]
  have hP : Rsa.PPC64LE.Priv.pR (callE s t) = pR s := by
    simp only [Rsa.PPC64LE.Priv.pR, sa 0 (by decide), sa 1 (by decide)]
  have hQ : Rsa.PPC64LE.Priv.qR (callE s t) = qR s := by
    simp only [Rsa.PPC64LE.Priv.qR, sa 2 (by decide), sa 3 (by decide)]
  have hDP : Rsa.PPC64LE.Priv.dpR (callE s t) = dpR s := by
    simp only [Rsa.PPC64LE.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]
  have hDQ : Rsa.PPC64LE.Priv.dqR (callE s t) = dqR s := by
    simp only [Rsa.PPC64LE.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]
  have hQI : Rsa.PPC64LE.Priv.qiR (callE s t) = qiR s := by
    simp only [Rsa.PPC64LE.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]
  have hS : Rsa.PPC64LE.Priv.sR (callE s t) = sR s := by
    simp only [Rsa.PPC64LE.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  have hA : Rsa.PPC64LE.Priv.aR (callE s t) = psaR s := by simp only [Rsa.PPC64LE.Priv.aR, callE_addr A]
  have s1 := sa 1 (by decide)
  have s3 := sa 3 (by decide)
  have s5 := sa 5 (by decide)
  have s7 := sa 7 (by decide)
  have s9 := sa 9 (by decide)
  have s11 := sa 11 (by decide)
  have wo' : (s.gpr .r3).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 := h.h4 ▸ h.wo
  refine ⟨by rw [hsp]; unfold Impl.Rsa.PPC64LE.Priv.frameBytes; omega, by rw [hsp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]; rfl
  · rw [hO, hS, ← hOo]; rfl
  · rw [hO, hN]; exact h.on
  · rw [hO, hE]; exact h.oe
  · rw [hO, hI]; exact (h.ko.sub_left es).symm
  · rw [hO, hP]; exact h.op
  · rw [hO, hQ]; exact h.oq
  · rw [hO, hDP]; exact h.odp
  · rw [hO, hDQ]; exact h.odq
  · rw [hO, hQI]; exact h.oqi
  · rw [hO, hS]; exact h.os
  · rw [hO, hA]; exact (h.ko.sub_left ps).symm
  · rw [hN, hS]; exact h.ns
  · rw [hE, hS]; exact h.es
  · rw [hI, hS]; exact h.ks.sub_left es
  · rw [hP, hS]; exact h.ps
  · rw [hQ, hS]; exact h.qs
  · rw [hDP, hS]; exact h.dps
  · rw [hDQ, hS]; exact h.dqs
  · rw [hQI, hS]; exact h.qis
  · rw [hS, hA]; exact (h.ks.sub_left ps).symm
  · rw [hK, hO]; exact h.ko.sub_left cs'
  · rw [hK, hN]; exact h.kn.sub_left cs'
  · rw [hK, hE]; exact h.ke.sub_left cs'
  · rw [hK, hI]; exact ki
  · rw [hK, hP]; exact h.kp.sub_left cs'
  · rw [hK, hQ]; exact h.kq.sub_left cs'
  · rw [hK, hDP]; exact h.kdp.sub_left cs'
  · rw [hK, hDQ]; exact h.kdq.sub_left cs'
  · rw [hK, hQI]; exact h.kqi.sub_left cs'
  · rw [hK, hS]; exact h.ks.sub_left cs'
  · rw [hK, hA]; exact ka
  · rw [g3, g4]; exact wo'
  · rw [g5, g6]; exact h.wn
  · rw [g7, g8]; exact h.we
  · rw [g9, g10, Offset.toNat_add_ofNat]; unfold oEM; omega
  · rw [sa 0 (by decide), s1]; exact h.wp
  · rw [sa 2 (by decide), s3]; exact h.wq
  · rw [sa 4 (by decide), s5]; exact h.wdp
  · rw [sa 6 (by decide), s7]; exact h.wdq
  · rw [sa 8 (by decide), s9]; exact h.wqi
  · rw [sa 10 (by decide), s11]; exact h.ws
  · rw [g6]; exact h.k1
  · rw [g6]; exact h.k2
  · rw [g4, g6]
  · rw [g10, g6]
  · rw [g8]; exact h.e1
  · rw [g8, g6]; exact h.e2
  · rw [s1]; exact h.p1
  · rw [s1, g6]; exact h.p2
  · rw [s3]; exact h.q1
  · rw [s3, g6]; exact h.q2
  · rw [s5, s1]; exact h.h6
  · rw [s9, s1]; exact h.h10
  · rw [s7, s3]; exact h.h8
  · rw [g6, s11]; exact h.hs

/-- From the call on: `Fr`, with `out` and the working space written too. -/
structure Fr2 (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem
  ls : u.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- The outcome of `vg_rsa_private_checked` of `em`, from the caller's
buffers. -/
abbrev privOut (s : State) (em : List Byte) (u : State) : Prop :=
  Spec.Rsa.writtenOutcome u.mem (s.gpr .r3) (s.gpr .r6).toNat ((u.gpr .r3).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) em
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat))

/-- After the call. -/
structure AtRet (s u : State) (em : List Byte) : Prop extends Fr2 s u where
  r28 : u.gpr .r28 = s.gpr .r6
  out : privOut s em u

theorem call_covers {s t : State} {em : List Byte} (h : SPre s) (A : AtCall s t em) :
    Covers (callRd s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hk := h.k2
  have hOo : (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr, ← hOo]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oEM frameBytes; omega)))
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))

theorem priv_sdepth : sdepth Impl.Rsa.PPC64LE.Priv.code = Impl.Rsa.PPC64LE.Priv.frameBytes := by decide +kernel

theorem call_ok {s t : State} {em : List Byte} (h : SPre s) (A : AtCall s t em) {Q : State → Prop}
    (hQ : ∀ u, AtRet s u em → Q u) : WP isa privCall t Q := by
  have hk := h.k2
  obtain ⟨hc, hw⟩ := call_covers h A
  have hOo : (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s := by simp only [oR, h.h4]
  have cs := callee_sub s
  unfold privCall
  refine WP.callAny (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct
    (Rsa.PPC64LE.Priv.pre_of_preP (preP_entry h A)) hc hw
    (fun u hrd hwr hsp hf hpres hpost => hQ u ?_) (by rw [priv_sdepth]; decide)
  have hb : below t.sp (sdepth Impl.Rsa.PPC64LE.Priv.code) =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ := by
    rw [priv_sdepth, A.sp]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append, hOo] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ap : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64
      Impl.Rsa.PPC64LE.Priv.frameBytes, Impl.Rsa.PPC64LE.Priv.frameBytes⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s hd)
    · exact h.ks.sub_left (frame_sub s hd)
    · rw [fb_eq, BitVec.add_sub_cancel, Offset.add_add]
      exact Offset.disjoint_base _ (by omega) (by unfold frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes at *; omega)
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, fun r hr => (hp r (by revert r; decide)).trans
    (A.hi r hr), ?_, A.sv.frame hf fun p hp' r hr =>
      ap (by have := saved_offs p hp'; unfold oSave frameBytes at *; omega) r hr, ?_⟩,
    (hp _ (by decide)).trans A.r28, ?_⟩
  · refine A.mem.sub (fun r hr => ?_) |>.trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., cs⟩
  · rw [hf.readW (Region.contains_self _ _) (ap (by decide)) (by decide)]; exact A.ls
  · have sa := fun i hi => callE_stackArg A (i := i) hi
    simp only [Rsa.PPC64LE.Priv.fnContract, Rsa.PPC64LE.Priv.fnPost, State.withRegions_mem,
      State.withRegions_gpr, State.callEntry_mem, callE_gpr s t (r := .r3), callE_gpr s t (r := .r5),
      callE_gpr s t (r := .r6), callE_gpr s t (r := .r7), callE_gpr s t (r := .r8), callE_gpr s t (r := .r9),
      A.r3, A.r5, A.r6, A.r7, A.r8, A.r9, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide),
      sa 4 (by decide), sa 6 (by decide), sa 8 (by decide), Nat.reduceAdd, A.em] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega), hb h.ke.symm (by have := h.we; omega),
      hb h.kp.symm (by have := h.wp; omega), hb h.kq.symm (by have := h.wq; omega),
      hb (h.h6 ▸ h.kdp.symm) (by have := h.wdp; omega), hb (h.h8 ▸ h.kdq.symm) (by have := h.wdq; omega),
      hb (h.h10 ▸ h.kqi.symm) (by have := h.wqi; omega)] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
