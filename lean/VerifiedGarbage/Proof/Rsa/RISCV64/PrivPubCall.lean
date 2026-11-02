module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPreCall
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked` on RISC-V: the call of `vg_rsa_public_precomputed_checked`

Its arguments (`pubArgs_ok`, into `AtPubC`), then the call by the callee's
contract on its registers and stack (`Pub.fnContract`, `Pub.fn_correct`):
`m^e mod n` into `out` (`pubCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

/-- Words of a region apart from what changed. -/
theorem words_of_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 8 * n⟩ r) (hl : 8 * n ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (Offset.contains_base p (by omega) (by omega)) hd (by decide)

/-- `n`'s values, or zeros if they are invalid. -/
abbrev preW (s : State) (m : Mem) : Prop :=
  Spec.Rsa.wordsAt m (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) =
    (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)).getD
      (List.replicate (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) 0)

theorem preW_of {s : State} {r : BitVec 64} {m : Mem}
    (h : Proof.Bignum.RISCV64.Pre.preOut (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) r m) : preW s m := by
  unfold preW
  cases hw : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) <;>
    simp only [Proof.Bignum.RISCV64.Pre.preOut, hw] at h <;> exact h.2

/-- At the call of `vg_rsa_public_precomputed_checked`. -/
structure AtPubC (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  pre : preW s u.mem
  a0 : u.gpr .a0 = s.gpr .a0
  a1 : u.gpr .a1 = s.gpr .a3
  a2 : u.gpr .a2 = fb s + BitVec.ofNat 64 oPre
  a3 : u.gpr .a3 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)
  a4 : u.gpr .a4 = s.gpr .a4
  a5 : u.gpr .a5 = s.gpr .a5
  a6 : u.gpr .a6 = fb s + BitVec.ofNat 64 oM
  a7 : u.gpr .a7 = s.gpr .a3
  psa0 : u.mem.readW (fb s + BitVec.ofNat 64 0) 64 = stackArg s 10
  psa1 : u.mem.readW (fb s + BitVec.ofNat 64 8) 64 = stackArg s 11

/-- `pubArgs` up to `argBase`. -/
abbrev pub1 : List Instr :=
  [.addSp .t0 0, mov .a0 .s1, mov .a1 .s3, .addi .a2 .t0 oPre] ++ preLen .a3 ++
    [mov .a4 .s4, mov .a5 .s5, .addi .a6 .t0 oM, mov .a7 .s3]

abbrev pub2 : List Instr :=
  [.load .d .t1 .t6 80, .store .d .t1 .t0 0, .load .d .t1 .t6 88, .store .d .t1 .t0 8]

theorem pubArgs_eq : pubArgs = pub1 ++ (argBase ++ pub2) := by
  simp only [pubArgs, List.append_assoc]

theorem pub1_ok {s t : State} (h : PreP s) (A : AtPub s t) :
    WP isa (.block pub1) t fun w =>
      (w.gpr .t0 = fb s ∧ w.gpr .a0 = s.gpr .a0 ∧ w.gpr .a1 = s.gpr .a3 ∧
        w.gpr .a2 = fb s + BitVec.ofNat 64 oPre ∧
        w.gpr .a3 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧
        w.gpr .a4 = s.gpr .a4 ∧ w.gpr .a5 = s.gpr .a5 ∧ w.gpr .a6 = fb s + BitVec.ofNat 64 oM ∧
        w.gpr .a7 = s.gpr .a3 ∧ w.mem = t.mem) ∧
      Keep [.t0, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] t w := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [pub1, exec_addSp, A.sp, BitVec.add_zero, oPre, oM, preLen, mov, A.s1, A.s3, A.s4, A.s5, preLen_val h.k2]

theorem pub2_ok {s x : State} (h : PreP s) (hrd : x.rd = s.rd) (hwr : x.wr = kR s :: s.wr)
    (hm : Frame [kR s, sR s] s.mem x.mem) (h0 : x.gpr .t0 = fb s) (h6 : x.gpr .t6 = s.sp) :
    WP isa (.block pub2) x fun u =>
      u.mem = (x.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 10)).writeW (fb s + BitVec.ofNat 64 8)
        (stackArg s 11) ∧ Keep [.t1] x u := by
  have i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 80) 8 := arg_in h hrd (j := 10) (by decide)
  have i1 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 88) 8 := arg_in h hrd (j := 11) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 80).toNat % 8 = 0 := stackArgAddr_al h 10
  have l1 : (s.sp + BitVec.ofNat 64 88).toNat % 8 = 0 := stackArgAddr_al h 11
  have r0 : x.mem.readW (s.sp + BitVec.ofNat 64 80) 64 = stackArg s 10 := arg_read2 h hm (j := 10) (by decide)
  have r1 : (x.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 10)).readW (s.sp + BitVec.ofNat 64 88) 64 =
      stackArg s 11 := by
    have fw : Frame [⟨fb s + BitVec.ofNat 64 0, 8⟩] x.mem (x.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 10)) :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have e : s.sp + BitVec.ofNat 64 88 = stackArgAddr s 11 := rfl
    rw [e, fw.readW (in_aR (j := 11) (by decide)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (h.ka.sub_left (frame_sub s (by decide))).symm) (by decide)]
    exact arg_read2 h hm (j := 11) (by decide)
  have w0 : InRegions x.wr (fb s + BitVec.ofNat 64 0) 8 := by rw [hwr]; exact in_fr s _ (by decide)
  have w1 : InRegions x.wr (fb s + BitVec.ofNat 64 8) 8 := by rw [hwr]; exact in_fr s _ (by decide)
  have a0 : (fb s + BitVec.ofNat 64 0).toNat % 8 = 0 := fb_al8 h (by decide)
  have a1 : (fb s + BitVec.ofNat 64 8).toNat % 8 = 0 := fb_al8 h (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [pub2, h0, h6, i0, i1, l0, l1, r0, r1, w0, w1, a0, a1]

theorem pubArgs_ok {s t : State} (h : PreP s) (A : AtPub s t) :
    WP isa (.block pubArgs) t (AtPubC s) := by
  have hk := h.k2
  rw [pubArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (pub1_ok h A))
    fun w ⟨⟨⟨w0, wa0, wa1, wa2, wa3, wa4, wa5, wa6, wa7, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans A.sp) fun x x6 kx xm xsp => ?_
  have xrd : x.rd = s.rd := kx.2.1.trans (wrd.trans A.rd)
  have xwr : x.wr = kR s :: s.wr := kx.2.2.trans (wwr.trans A.wr)
  have hmx : Frame [kR s, sR s] s.mem x.mem := by rw [xm, wm]; exact A.mem
  refine WP.mono (WP.rdwr (pub2_ok h xrd xwr hmx ((kx.gpr (by decide)).trans w0) x6))
    fun u ⟨⟨um, ku⟩, urd, uwr, usp⟩ => ?_
  have um' : u.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 10)).writeW
      (fb s + BitVec.ofNat 64 8) (stackArg s 11) := by rw [um, xm, wm]
  have hg : ∀ r ∈ preserved, u.gpr r = t.gpr r := fun r hr => by
    rw [ku.gpr (by revert r; decide), kx.gpr (by revert r; decide), kw.gpr (by revert r; decide)]
  have M1 : Mid s { u with mem := t.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 10) } :=
    A.store (.inr (by decide)) (by decide) _ hg (usp.trans (xsp.trans wsp)) (urd.trans (kx.2.1.trans wrd))
      (uwr.trans (kx.2.2.trans wwr)) rfl
  have M2 : Mid s u := M1.store (d := 8) (.inr (by decide)) (by decide) _ (fun _ _ => rfl) rfl rfl rfl um'
  have fw : Frame [⟨fb s + BitVec.ofNat 64 0, 8⟩, ⟨fb s + BitVec.ofNat 64 8, 8⟩] t.mem u.mem := by
    rw [um']
    exact Frame.writeW (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 0, 64 / 8⟩,
      ⟨fb s + BitVec.ofNat 64 8, 64 / 8⟩] t.mem) (List.mem_cons_self ..) _ (Region.contains_self _ _))
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have ap : ∀ {d n : Nat}, 16 ≤ d → d + n ≤ 2 ^ 64 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 8⟩ : Region),
      ⟨fb s + BitVec.ofNat 64 8, 8⟩], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
    intro d n hd hn r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega)) hn (by decide)
    · exact Offset.disjoint _ (.inr (by omega)) hn (by decide)
  have pwl := pw_le hk
  have gu : ∀ r ∈ ([.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] : List Reg), u.gpr r = w.gpr r := fun r hr => by
    rw [ku.gpr (by revert r; decide), kx.gpr (by revert r; decide)]
  refine ⟨M2, ?_, ?_, (gu _ (by simp)).trans wa0, (gu _ (by simp)).trans wa1, (gu _ (by simp)).trans wa2,
    (gu _ (by simp)).trans wa3, (gu _ (by simp)).trans wa4, (gu _ (by simp)).trans wa5,
    (gu _ (by simp)).trans wa6, (gu _ (by simp)).trans wa7, ?_, ?_⟩
  · show Spec.Rsa.written _ _ _ _ _
    rw [fw.readW (Region.contains_self _ _) (ap (by decide) (by decide)) (by decide)]
    exact written_congr (bytes_of_frame (s := t) fw (ap (by decide) (by unfold oM; omega)) (by omega)) A.crt
  · show Spec.Rsa.wordsAt _ _ _ = _
    rw [words_of_frame fw (ap (by decide) (by unfold oPre; omega)) (by omega)]
    exact preW_of A.pre
  · rw [um', Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]
  · rw [um', Mem.readW_writeW_self64]

/-- `out`, of `k` bytes. -/
abbrev outR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a3).toNat⟩

theorem outR_eq {s : State} (h : PreP s) : outR s = oR s := by simp only [outR, oR, h.h1]

/-- The stack arguments of the call. -/
abbrev psR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 0, 16⟩

/-- The regions the call reads and writes. -/
abbrev pubRd (s : State) : List Region := [pwR s, eR s, mR s, psR s]

abbrev pubWr (s : State) : List Region := [outR s, sR s]

/-- The frame is apart from what the call writes. -/
theorem frame_pub {s : State} (h : PreP s) {d n : Nat} (hd : d + n ≤ frameBytes) {r : Region}
    (hr : r ∈ pubWr s) : Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [outR_eq h]; exact h.ko.sub_left (frame_sub s hd)
  · exact h.ks.sub_left (frame_sub s hd)

/-- `m^e mod n` in `out`, if `n`'s values are valid. -/
abbrev pubOut (s u : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = some ws →
    Spec.Rsa.written u.mem (s.gpr .a0) (s.gpr .a3).toNat ((u.gpr .a0).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
        (Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat))

/-- From the call of `vg_rsa_public_precomputed_checked` on: `Mid`, with
`out` written too. -/
structure Late (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = kR s :: s.wr
  s1 : u.gpr .s1 = s.gpr .a0
  s2 : u.gpr .s2 = s.gpr .a2
  s3 : u.gpr .s3 = s.gpr .a3
  s4 : u.gpr .s4 = s.gpr .a4
  s5 : u.gpr .s5 = s.gpr .a5
  s6 : u.gpr .s6 = s.gpr .a6
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem

/-- After the call of `vg_rsa_public_precomputed_checked`. -/
structure AtCmp (s u : State) : Prop extends Late s u where
  crt : crtOutM s u
  pub : pubOut s u

theorem pub_noFrames : Impl.Bignum.RISCV64.PublicChecked.publicChecked.noFrames = true := by decide +kernel

/-- The call's narrowed entry state. -/
abbrev pubEntry (s t : State) : State := t.callEntry.withRegions (pubRd s) (pubWr s)

theorem pub_pre {s t : State} (h : PreP s) (A : AtPubC s t) :
    Proof.Bignum.RISCV64.Pub.fnContract.pre (pubEntry s t) ∧ Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧
      Covers (pubWr s) t.wr := by
  have hk := h.k2
  have pk := pwR_sub h
  have pwl := pw_le hk
  have mk := mR_sub h
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have hw : Covers (pubWr s) t.wr := by
    rw [A.wr, h.hwr, ← outR_eq h]
    exact Covers.of_mem fun r hr => by
      simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  have hc : Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) := by
    refine Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw)
    rw [A.rd, A.wr, h.hrd]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Covers.right (Covers.one (in_fr s _ (by unfold oPre frameBytes; omega)))
    · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
    · exact Covers.right (Covers.one (in_fr s _ (by unfold oM frameBytes; omega)))
    · exact Covers.right (Covers.one (in_fr s _ (by decide)))
  have g : ∀ r, r ∉ linkRegs → (pubEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
  have hsp : (pubEntry s t).sp = fb s := A.sp
  have sa0 : stackArg (pubEntry s t) 0 = stackArg s 10 := by
    show t.mem.readW ((pubEntry s t).sp + _) 64 = _; rw [hsp]; exact A.psa0
  have sa1 : stackArg (pubEntry s t) 1 = stackArg s 11 := by
    show t.mem.readW ((pubEntry s t).sp + _) 64 = _; rw [hsp]; exact A.psa1
  have e6 : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
    rw [BitVec.toNat_ofNat]; omega
  have psk : Region.Sub (psR s) (kR s) := frame_sub s (by decide)
  refine ⟨?_, hc, hw⟩
  simp only [Proof.Bignum.RISCV64.Pub.fnContract, Proof.Bignum.RISCV64.Pub.stackArgs, stackArgAddr,
    g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, A.a6, A.a7, e6,
    sa0, sa1, hsp, Nat.mul_zero, State.withRegions_rd, State.withRegions_wr]
  rw [show (⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region) = oR s from outR_eq h]
  refine ⟨trivial, trivial, (h.ko.sub_left pk).symm, h.oe, (h.ko.sub_left mk).symm, h.os,
    (h.ko.sub_left psk).symm, h.ks.sub_left pk, h.es, h.ks.sub_left mk, (h.ks.sub_left psk).symm,
    h.h1 ▸ h.wo, ?_, h.we, ?_, h.ws, ⟨h.k1, h.k2⟩, trivial, trivial, h.e1, h.e2, ?_, fb_al8 h (by decide), h.al,
    fb_al h⟩
  · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega
  · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega
  · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
    unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega

theorem pubCall_ok {s t : State} (h : PreP s) (A : AtPubC s t) {Q : State → Prop}
    (hQ : ∀ u, AtCmp s u → Q u) : WP isa pubCall t Q := by
  have hk := h.k2
  have pwl := pw_le hk
  obtain ⟨hpre, hc, hw⟩ := pub_pre h A
  have g : ∀ r, r ∉ linkRegs → (pubEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
  have e6 : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
    rw [BitVec.toNat_ofNat]; omega
  unfold pubCall
  refine WP.call (k := Proof.Bignum.RISCV64.Pub.fnContract) (rd := pubRd s) (wr := pubWr s)
    Proof.Bignum.RISCV64.Pub.fn_correct hpre hc hw
    (fun u hrd hwr hsp' hf hpres _ hpost => hQ u ?_) pub_noFrames
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ft : Frame [kR s, oR s, sR s] s.mem u.mem := by
    refine ((A.mem.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [outR_eq h]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
  have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat :=
    bytes_of_frame (s := t) hf (fun r hr => frame_pub h (by unfold oM frameBytes; omega) hr) (by omega)
  refine ⟨⟨hsp'.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.s1,
    (hp _ (by decide)).trans A.s2, (hp _ (by decide)).trans A.s3, (hp _ (by decide)).trans A.s4,
    (hp _ (by decide)).trans A.s5, (hp _ (by decide)).trans A.s6,
    fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => frame_pub h (by
      have := saved_offs p hp'; unfold oSave frameBytes at *; omega) hr⟩, ?_, ?_⟩
  · show Spec.Rsa.written _ _ _ _ _
    rw [hf.readW (Region.contains_self _ _) (fun r hr => frame_pub h (by decide) hr) (by decide)]
    exact written_congr hm A.crt
  · intro ws hw
    have he : Spec.Rsa.bytesAt t.mem (s.gpr .a4) (s.gpr .a5).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat :=
      bytes_of_frame A.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.ke.symm
        · exact h.es) (by have := h.we; omega)
    simp only [Proof.Bignum.RISCV64.Pub.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
      g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), g .a6 (by decide), A.a0, A.a1, A.a2, A.a3,
      A.a4, A.a5, A.a6, e6, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, he] at hpost
    rw [hm]
    exact hpost _ (by simp [Spec.Rsa.bytesAt]) (by rw [A.pre, hw]; rfl)

end VG.Proof.Rsa.RISCV64.Priv
