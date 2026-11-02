module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivSetup
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked` on RISC-V: the calls of `vg_rsa_private_crt` and `vg_rsa_public_precompute`

By the first callee's contract on its registers and stack (`Crt.fnContract`,
`Crt.fn_correct`): the regions it is narrowed to (`crtRd`, `crtWr`), its
precondition at the call (`crt_pre`), and the call (`crtCall_ok`). Then the
CRT's status kept in the frame (`preArgs_ok`, into `AtPre`), and the call
by the second callee's contract on its registers (`Pre.fnContract`,
`Pre.fn_correct`): `n`'s values into the frame (`preCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

/-! ## The call of `vg_rsa_private_crt` -/

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

/-! ## The call of `vg_rsa_public_precompute` -/

theorem written_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.written m out k r o) :
    Spec.Rsa.written m' out k r o := by
  cases o <;> simp only [Spec.Rsa.written, hb] at h ⊢ <;> exact h

/-- `m` and the CRT's status kept in the frame. -/
abbrev crtOutM (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat
    ((u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- `Mid` is kept by a write of a word of the frame apart from the slots. -/
theorem Mid.store {s t : State} (M : Mid s t) {d : Nat} (hd : oRa + 8 ≤ d ∨ d + 8 ≤ oSave)
    (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Mid s u := by
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.s1,
    (hg _ (by decide)).trans M.s2, (hg _ (by decide)).trans M.s3, (hg _ (by decide)).trans M.s4,
    (hg _ (by decide)).trans M.s5, (hg _ (by decide)).trans M.s6,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      simp only [oSave, oRa] at this hd
      exact Offset.disjoint _ (by omega) (by unfold frameBytes at hd'; omega)
        (by unfold frameBytes at hd'; omega)⟩
  rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')

/-- At the call of `vg_rsa_public_precompute`. -/
structure AtPre (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  a0 : u.gpr .a0 = fb s + BitVec.ofNat 64 oPre
  a1 : u.gpr .a1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)
  a2 : u.gpr .a2 = s.gpr .a2
  a3 : u.gpr .a3 = s.gpr .a3
  a4 : u.gpr .a4 = stackArg s 10
  a5 : u.gpr .a5 = stackArg s 11

theorem preLen_val {x : BitVec 64} (hk : x.toNat ≤ 1024) :
    (x + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
  omega

/-- `preArgs` up to `argBase`. -/
abbrev pre1 : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 oSt, .addi .a0 .t0 oPre] ++ preLen .a1 ++ [mov .a2 .s2, mov .a3 .s3]

theorem preArgs_eq : preArgs = pre1 ++ (argBase ++ ([.load .d .a4 .t6 80, .load .d .a5 .t6 88] : List Instr)) := by
  simp only [preArgs, List.append_assoc]

theorem pre1_ok {s t : State} (h : PreP s) (M : Mid s t) :
    WP isa (.block pre1) t fun w =>
      (w.gpr .a0 = fb s + BitVec.ofNat 64 oPre ∧
        w.gpr .a1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧
        w.gpr .a2 = s.gpr .a2 ∧ w.gpr .a3 = s.gpr .a3 ∧
        w.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0)) ∧
      Keep [.t0, .a0, .a1, .a2, .a3] t w := by
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 152) 8 := by
    rw [M.wr]; exact in_fr s _ (by decide)
  have hal : (fb s + BitVec.ofNat 64 152).toNat % 8 = 0 := fb_al8 h (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [pre1, exec_addSp, M.sp, BitVec.add_zero, ho, hal, oSt, oPre, preLen, mov, M.s2, M.s3, preLen_val h.k2]

theorem pre2_ok {s x : State} (h : PreP s) (hrd : x.rd = s.rd) (hm : Frame [kR s, sR s] s.mem x.mem)
    (h6 : x.gpr .t6 = s.sp) :
    WP isa (.block [.load .d .a4 .t6 80, .load .d .a5 .t6 88]) x fun u =>
      (u.gpr .a4 = stackArg s 10 ∧ u.gpr .a5 = stackArg s 11 ∧ u.mem = x.mem) ∧ Keep [.a4, .a5] x u := by
  have i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 80) 8 := arg_in h hrd (j := 10) (by decide)
  have i1 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 88) 8 := arg_in h hrd (j := 11) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 80).toNat % 8 = 0 := stackArgAddr_al h 10
  have l1 : (s.sp + BitVec.ofNat 64 88).toNat % 8 = 0 := stackArgAddr_al h 11
  have r0 : x.mem.readW (s.sp + BitVec.ofNat 64 80) 64 = stackArg s 10 := arg_read2 h hm (j := 10) (by decide)
  have r1 : x.mem.readW (s.sp + BitVec.ofNat 64 88) 64 = stackArg s 11 := arg_read2 h hm (j := 11) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h6, i0, i1, l0, l1, r0, r1]

theorem preArgs_ok {s t : State} (h : PreP s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgs) t (AtPre s) := by
  have hk := h.k2
  rw [preArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (pre1_ok h M)) fun w ⟨⟨⟨w0, w1, w2, w3, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans M.sp) fun x x6 kx xm xsp => ?_
  have hmw : Frame [kR s, sR s] s.mem x.mem := by
    rw [xm, wm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s (by decide))
  refine WP.mono (WP.rdwr (pre2_ok h (kx.2.1.trans (wrd.trans M.rd)) hmw x6))
    fun u ⟨⟨⟨u4, u5, um⟩, ku⟩, urd, uwr, usp⟩ => ?_
  have hum : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0) := by rw [um, xm, wm]
  refine ⟨M.store (d := oSt) (.inl (by decide)) (by decide) _ (fun r hr => ?_) (usp.trans (xsp.trans wsp))
    (urd.trans (kx.2.1.trans wrd)) (uwr.trans (kx.2.2.trans wwr)) hum, ?_, ?_, ?_, ?_, ?_, u4, u5⟩
  · rw [ku.gpr (by revert r; decide), kx.gpr (by revert r; decide), kw.gpr (by revert r; decide)]
  · have hb : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [hum]
      exact Frame.bytes (R := mR s) (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
        (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega) (by decide))
        (show (s.gpr .a3).toNat ≤ 2 ^ 64 by omega) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [hum, Mem.readW_writeW_self64, ← hum]
    exact written_congr hb C
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w0
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w1
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w2
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w3

/-- `n`'s values, in the frame. -/
abbrev pwR (s : State) : Region :=
  ⟨fb s + BitVec.ofNat 64 oPre, Spec.Rsa.precomputedWords (s.gpr .a3).toNat * 8⟩

/-- The regions the call writes. -/
abbrev preWr (s : State) : List Region := [pwR s, sR s]

theorem pw_le {k : Nat} (hk : k ≤ 1024) : Spec.Rsa.precomputedWords k ≤ 256 := by
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega

theorem pwR_sub {s : State} (h : PreP s) : Region.Sub (pwR s) (kR s) :=
  frame_sub s (by have := pw_le h.k2; unfold oPre frameBytes; omega)

/-- The frame below `n`'s values is apart from what the call writes. -/
theorem below_pre {s : State} (h : PreP s) {d n : Nat} (hd : d + n ≤ oPre) {r : Region} (hr : r ∈ preWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl hd) (by unfold oPre at hd; omega)
      (by have := pw_le h.k2; unfold oPre; omega)
  · exact h.ks.sub_left (frame_sub s (by unfold oPre frameBytes at *; omega))

/-- After the call of `vg_rsa_public_precompute`. -/
structure AtPub (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  pre : Proof.Bignum.RISCV64.Pre.preOut (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) (u.gpr .a0) u.mem

theorem pre_noFrames : Impl.Bignum.RISCV64.Precompute.precompute.noFrames = true := by decide +kernel

theorem pre_covers {s t : State} (h : PreP s) (A : AtPre s t) :
    Covers ([nR s] ++ preWr s) (t.rd ++ t.wr) ∧ Covers (preWr s) t.wr := by
  have hk := h.k2
  have pwl := pw_le hk
  have hw : Covers (preWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oPre frameBytes; omega))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.right hw), hw⟩
  rw [List.mem_singleton.mp hr, A.rd, h.hrd]; simp

theorem pre_toNat {s : State} (h : PreP s) :
    (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
  have := pw_le h.k2
  rw [BitVec.toNat_ofNat]; omega

theorem pre_pre {s t : State} (h : PreP s) (A : AtPre s t) :
    Proof.Bignum.RISCV64.Pre.fnContract.pre (t.callEntry.withRegions [nR s] (preWr s)) := by
  have hk := h.k2
  have pk := pwR_sub h
  have pwl := pw_le hk
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  simp only [Proof.Bignum.RISCV64.Pre.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
    g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, pre_toNat h,
    State.withRegions_rd, State.withRegions_wr, Proof.Bignum.RISCV64.Pre.nR, Proof.Bignum.RISCV64.Pre.preR,
    Proof.Bignum.RISCV64.Pre.scrR]
  refine ⟨trivial, trivial, h.kn.sub_left pk, h.ks.sub_left pk, h.ns, ?_, h.wn, h.ws, ⟨h.k1, h.k2⟩, trivial, ?_,
    fb_al8 h (by decide), h.al⟩
  · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega
  · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
    unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega

theorem preCall_ok {s t : State} (h : PreP s) (A : AtPre s t) {Q : State → Prop}
    (hQ : ∀ u, AtPub s u → Q u) : WP isa preCall t Q := by
  have hk := h.k2
  have pk := pwR_sub h
  obtain ⟨hc, hw⟩ := pre_covers h A
  have g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  have e4 := pre_toNat h
  have hn : Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat :=
    bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega)
  unfold preCall
  refine WP.call (k := Proof.Bignum.RISCV64.Pre.fnContract) (rd := [nR s]) (wr := preWr s)
    Proof.Bignum.RISCV64.Pre.fn_correct (pre_pre h A) hc hw
    (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_) pre_noFrames
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ft : Frame [kR s, sR s] s.mem u.mem := by
    refine (A.mem.trans (hf.sub fun r hr => ?_))
    simp only [preWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., pk⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat :=
    bytes_of_frame (s := t) hf (fun r hr => below_pre h (by unfold oM oPre; omega) hr) (by omega)
  have hst : u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 :=
    hf.readW (Region.contains_self _ _) (fun r hr => below_pre h (by decide) hr) (by decide)
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.s1,
    (hp _ (by decide)).trans A.s2, (hp _ (by decide)).trans A.s3, (hp _ (by decide)).trans A.s4,
    (hp _ (by decide)).trans A.s5, (hp _ (by decide)).trans A.s6,
    fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => below_pre h (by
      have := saved_offs p hp'; unfold oSave oPre at *; omega) hr⟩, ?_, ?_⟩
  · show Spec.Rsa.written _ _ _ _ _
    rw [hst]; exact written_congr hm A.crt
  · simp only [Proof.Bignum.RISCV64.Pre.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
      g .a3 (by decide), A.a0, A.a1, A.a2, A.a3, e4, State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_mem, hn] at hpost
    exact hpost

end VG.Proof.Rsa.RISCV64.Priv
