module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivSetup
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFn
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_private_crt`

By the callee's contract on its registers and stack (`Crt.fnContract`,
`Crt.fn_correct`): the regions it is narrowed to (`crtRd`, `crtWr`), its
precondition at the call (`crt_pre`), and the call (`crtCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- `m`, in the frame. -/
abbrev mR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oM, (s.gpr .r6).toNat⟩

/-- The regions the call reads and writes. -/
abbrev crtRd (s : State) : List Region :=
  [nR s, ⟨s.gpr .r9, (s.gpr .r6).toNat⟩, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev crtWr (s : State) : List Region := [mR s, sR s]

/-- The call's narrowed entry state. -/
abbrev crtEntry (s t : State) : State := t.callEntry.withRegions (crtRd s) (crtWr s)

theorem crtEntry_stackArg {s t : State} (A : AtCrt s t) {i : Nat} (hi : i < 10) :
    stackArg (crtEntry s t) i = stackArg s (2 + i) := by
  show t.mem.readW (stackArgAddr (crtEntry s t) i) 64 = _
  rw [stackArgAddr_in, show (crtEntry s t).sp = fb s from A.sp]
  exact A.psa i hi

theorem crt_pre {s t : State} (h : PreP s) (A : AtCrt s t) :
    Proof.Bignum.PPC64LE.Crt.fnContract.pre (crtEntry s t) := by
  have g : ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
  have sa := fun i hi => crtEntry_stackArg A (i := i) hi
  have hsp : (crtEntry s t).sp = fb s := A.sp
  have ha : stackArgAddr (crtEntry s t) 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, hsp]
  simp only [Proof.Bignum.PPC64LE.Crt.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
    g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), g .r10 (by decide),
    A.r3, A.r4, A.r5, A.r6, A.r7, A.r8, A.r9, A.r10, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide),
    sa 3 (by decide), sa 4 (by decide), sa 5 (by decide), sa 6 (by decide), sa 7 (by decide), sa 8 (by decide),
    sa 9 (by decide), hsp, ha, State.withRegions_rd, State.withRegions_wr, Nat.reduceAdd]
  have hk := h.k2
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  have pk : Region.Sub (psaR s) (kR s) := frame_sub s (by decide)
  have mp : (mR s).Disjoint (psaR s) := Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega_arith) (by decide)
  rw [ei]
  refine ⟨by omega_arith, trivial, trivial, h.kn.sub_left mk, h.ki.sub_left mk, h.kp.sub_left mk, h.kq.sub_left mk,
    h.kdp.sub_left mk, h.kdq.sub_left mk, h.kqi.sub_left mk, h.ks.sub_left mk, mp, h.ns, h.is, h.ps, h.qs,
    h.dps, h.dqs, h.qis, (h.ks.sub_left pk).symm, ?_, h.wn, by rw [← h.h10]; exact h.wi, h.wp, h.wq, h.wdp, h.wdq, h.wqi, h.ws,
    ⟨h.k1, h.k2⟩, trivial, trivial, h.p1, h.p2, h.q1, h.q2, h.h5, h.h9, h.h7, h.hs⟩
  · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega_arith

/-- The bytes of `m` after the call: `vg_rsa_private_crt`'s result for the
caller's buffers, and its status. -/
abbrev crtOut (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat ((u.gpr .r3).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- The frame below `m` is apart from what the call writes. -/
theorem below_apart {s : State} (h : PreP s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ crtWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega_arith) (by have := h.k2; unfold oM; omega_arith)
  · exact h.ks.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_arith))

theorem crt_noFrames : Impl.Bignum.PPC64LE.Crt.crt.noFrames = true := by decide +kernel

theorem crt_covers {s t : State} (h : PreP s) (A : AtCrt s t) :
    Covers (crtRd s ++ crtWr s) (t.rd ++ t.wr) ∧ Covers (crtWr s) t.wr := by
  have hk := h.k2
  have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
  have hw : Covers (crtWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oM; omega_arith) (by unfold oM frameBytes; omega_arith))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [crtRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 7
  · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))
  all_goals exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [ei])

theorem crtCall_ok {s t : State} (h : PreP s) (A : AtCrt s t) {Q : State → Prop}
    (hQ : ∀ u, Mid s u → crtOut s u → Q u) : WP isa crtCall t Q := by
  have hk := h.k2
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
  obtain ⟨hc, hw⟩ := crt_covers h A
  unfold crtCall
  refine WP.call (k := Proof.Bignum.PPC64LE.Crt.fnContract) Proof.Bignum.PPC64LE.Crt.fn_correct (crt_pre h A) hc hw
    (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_ ?_) crt_noFrames
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    refine ⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.r24,
      (hp _ (by decide)).trans A.r25, (hp _ (by decide)).trans A.r26, (hp _ (by decide)).trans A.r27,
      (hp _ (by decide)).trans A.r28, (hp _ (by decide)).trans A.r29,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ?_, A.sv.frame hf fun p hp' r hr => below_apart h (by
        have := saved_offs p hp'; unfold oSave oM at *; omega_arith) hr, ?_⟩
    · refine (A.mem.mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
      · simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., mk⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · rw [hf.readW (Region.contains_self _ _) (fun r hr => below_apart h (by decide) hr) (by decide)]; exact A.ls
  · have g : ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
    have sa := fun i hi => crtEntry_stackArg A (i := i) hi
    simp only [Proof.Bignum.PPC64LE.Crt.fnContract, g .r3 (by decide), g .r5 (by decide), g .r6 (by decide),
      g .r7 (by decide), g .r9 (by decide), g .r10 (by decide), A.r3, A.r5, A.r6, A.r7, A.r9, A.r10,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_arith), hb (ei ▸ h.ki.symm) (by have := h.k2; omega_arith),
      hb h.kp.symm (by have := h.wp; omega_arith), hb h.kq.symm (by have := h.wq; omega_arith),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega_arith), hb (h.h7 ▸ h.kdq.symm) (by have := h.wdq; omega_arith),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega_arith)] at hpost
    exact hpost

end VG.Proof.Rsa.PPC64LE.Priv
