module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivSetup
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_private_checked` on RISC-V: the call of `vg_rsa_private_crt`

By the callee's contract on its registers and stack (`Crt.fnContract`,
`Crt.fn_correct`): the regions it is narrowed to (`crtRd`, `crtWr`), its
precondition at the call (`crt_pre`), and the call (`crtCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv

/-- `m`, in the frame. -/
abbrev mR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oM, (s.gpr .a3).toNat⟩

/-- The regions the call reads and writes. -/
abbrev crtRd (s : State) : List Region :=
  [nR s, ⟨s.gpr .a6, (s.gpr .a3).toNat⟩, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev crtWr (s : State) : List Region := [mR s, sR s]

/-- The call's narrowed entry state. -/
abbrev crtEntry (s t : State) : State := t.callEntry.withRegions (crtRd s) (crtWr s)

theorem crtEntry_stackArg {s t : State} (A : AtCrt s t) {i : Nat} (hi : i < 10) :
    stackArg (crtEntry s t) i = stackArg s (2 + i) := by
  show t.mem.readW ((crtEntry s t).sp + BitVec.ofNat 64 (8 * i)) 64 = _
  rw [show (crtEntry s t).sp = fb s from A.sp]
  exact A.psa i hi

theorem psa_sub (s : State) : Region.Sub (psaR s) (kR s) := by
  have := frame_sub s (d := 0) (n := 80) (by decide); rwa [BitVec.add_zero] at this

theorem mR_sub {s : State} (h : PreP s) : Region.Sub (mR s) (kR s) :=
  frame_sub s (by have := h.k2; unfold oM frameBytes; omega)

theorem iR_eq {s : State} (h : PreP s) : (⟨s.gpr .a6, (s.gpr .a3).toNat⟩ : Region) = iR s := by
  simp only [iR, h.h7]

theorem crt_pre {s t : State} (h : PreP s) (A : AtCrt s t) :
    Proof.Bignum.RISCV64.Crt.fnContract.pre (crtEntry s t) := by
  have g : ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
  have sa := fun i hi => crtEntry_stackArg A (i := i) hi
  have hsp : (crtEntry s t).sp = fb s := A.sp
  have ha : stackArgAddr (crtEntry s t) 0 = fb s := by
    simp only [stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]
  simp only [Proof.Bignum.RISCV64.Crt.fnContract, Proof.Bignum.RISCV64.Crt.stackArgs, g .a0 (by decide),
    g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide), g .a5 (by decide),
    g .a6 (by decide), g .a7 (by decide), A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, A.a6, A.a7, sa 0 (by decide),
    sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide), sa 5 (by decide), sa 6 (by decide),
    sa 7 (by decide), sa 8 (by decide), sa 9 (by decide), hsp, ha, State.withRegions_rd, State.withRegions_wr,
    Nat.reduceAdd]
  have hk := h.k2
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have mk := mR_sub h
  have pk := psa_sub s
  have mp : (mR s).Disjoint (psaR s) := Offset.disjoint_base _ (by decide) (by unfold oM; omega)
  rw [iR_eq h]
  refine ⟨trivial, trivial, h.kn.sub_left mk, h.ki.sub_left mk, h.kp.sub_left mk, h.kq.sub_left mk,
    h.kdp.sub_left mk, h.kdq.sub_left mk, h.kqi.sub_left mk, h.ks.sub_left mk, mp, h.ns, h.is, h.ps, h.qs,
    h.dps, h.dqs, h.qis, (h.ks.sub_left pk).symm, ?_, h.wn, by rw [← h.h7]; exact h.wi, h.wp, h.wq, h.wdp,
    h.wdq, h.wqi, h.ws, ⟨h.k1, h.k2⟩, trivial, trivial, h.p1, h.p2, h.q1, h.q2, h.h5, h.h9, h.h7', h.hs, h.al,
    fb_al h⟩
  · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega

/-- The bytes of `m` after the call: `vg_rsa_private_crt`'s result for the
caller's buffers, and its status. -/
abbrev crtOut (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat ((u.gpr .a0).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
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
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega) (by have := h.k2; unfold oM; omega)
  · exact h.ks.sub_left (frame_sub s (by unfold oM frameBytes at *; omega))

theorem crt_noFrames : Impl.Bignum.RISCV64.Crt.crt.noFrames = true := by decide +kernel

theorem crt_covers {s t : State} (h : PreP s) (A : AtCrt s t) :
    Covers (crtRd s ++ crtWr s) (t.rd ++ t.wr) ∧ Covers (crtWr s) t.wr := by
  have hk := h.k2
  have hw : Covers (crtWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oM frameBytes; omega))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [crtRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 7
  · exact Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, show 0 + 80 ≤ frameBytes by unfold frameBytes; omega⟩)
  all_goals exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [iR_eq h])

theorem crtCall_ok {s t : State} (h : PreP s) (A : AtCrt s t) {Q : State → Prop}
    (hQ : ∀ u, Mid s u → crtOut s u → Q u) : WP isa crtCall t Q := by
  have mk := mR_sub h
  obtain ⟨hc, hw⟩ := crt_covers h A
  unfold crtCall
  refine WP.call (k := Proof.Bignum.RISCV64.Crt.fnContract) Proof.Bignum.RISCV64.Crt.fn_correct (crt_pre h A) hc
    hw (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_ ?_) crt_noFrames
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    refine ⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.s1,
      (hp _ (by decide)).trans A.s2, (hp _ (by decide)).trans A.s3, (hp _ (by decide)).trans A.s4,
      (hp _ (by decide)).trans A.s5, (hp _ (by decide)).trans A.s6,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ?_, A.sv.frame hf fun p hp' r hr => below_apart h (by
        have := saved_offs p hp'; unfold oSave oM at *; omega) hr⟩
    refine (A.mem.mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    · simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., mk⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · have g : ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
    have sa := fun i hi => crtEntry_stackArg A (i := i) hi
    simp only [Proof.Bignum.RISCV64.Crt.fnContract, g .a0 (by decide), g .a2 (by decide), g .a3 (by decide),
      g .a4 (by decide), g .a6 (by decide), g .a7 (by decide), A.a0, A.a2, A.a3, A.a4, A.a6, A.a7,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega), hb (iR_eq h ▸ h.ki.symm) (by have := h.k2; omega),
      hb h.kp.symm (by have := h.wp; omega), hb h.kq.symm (by have := h.wq; omega),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega), hb (h.h7' ▸ h.kdq.symm) (by have := h.wdq; omega),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega)] at hpost
    exact hpost

end VG.Proof.Rsa.RISCV64.Priv
