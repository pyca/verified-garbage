module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPreCall
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_public_precomputed_checked`

Its arguments (`pubArgs_ok`, into `AtPubC`), then the call by the callee's
contract on its registers and stack (`Pub.fnContract`, `Pub.fn_correct`):
`m^e mod n` into `out` (`pubCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- Words of a region apart from what changed. -/
theorem words_of_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 8 * n⟩ r) (hl : 8 * n ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf.readW (Offset.contains_base p (by omega) (by omega)) hd (by decide)

/-- `n`'s values, if they are valid. -/
abbrev preW (s : State) (m : Mem) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws →
    Spec.Rsa.wordsAt m (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) = ws

theorem preW_of {s : State} {r : BitVec 64} {m : Mem}
    (h : Proof.Bignum.PPC64LE.Pre.preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) r m) : preW s m := by
  intro ws hw
  simp only [Proof.Bignum.PPC64LE.Pre.preOut, hw] at h
  exact h.2

/-- At the call of `vg_rsa_public_precomputed_checked`. -/
structure AtPubC (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  pre : preW s u.mem
  r3 : u.gpr .r3 = s.gpr .r3
  r4 : u.gpr .r4 = s.gpr .r6
  r5 : u.gpr .r5 = fb s + BitVec.ofNat 64 oPre
  r6 : u.gpr .r6 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)
  r7 : u.gpr .r7 = s.gpr .r7
  r8 : u.gpr .r8 = s.gpr .r8
  r9 : u.gpr .r9 = fb s + BitVec.ofNat 64 oM
  r10 : u.gpr .r10 = s.gpr .r6
  psa0 : u.mem.readW (fb s + BitVec.ofNat 64 96) 64 = stackArg s 10
  psa1 : u.mem.readW (fb s + BitVec.ofNat 64 104) 64 = stackArg s 11

theorem pubArgs_ok {s t : State} (h : PreP s) (A : AtPub s t) :
    WP isa (.block pubArgs) t (AtPubC s) := by
  have hk := h.k2
  have e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := A.r26.trans (gpr_ofNat _)
  have rdm : t.rd = s.rd := A.rd
  have w0 : InRegions t.wr (fb s + BitVec.ofNat 64 96) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide) (by decide)
  have w1 : InRegions t.wr (fb s + BitVec.ofNat 64 104) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide) (by decide)
  have a10 : t.mem.readW (fb s + BitVec.ofNat 64 (arg 10)) 64 = stackArg s 10 := arg_read2 h A.mem (by decide)
  have a11 : (t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 10)).readW
      (fb s + BitVec.ofNat 64 (arg 11)) 64 = stackArg s 11 := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold arg frameBytes; omega))
      (by unfold arg frameBytes; omega) (by decide)) (by decide)]
    exact arg_read2 h A.mem (by decide)
  have i10 := arg_in h rdm (j := 10) (by decide)
  have i11 := arg_in h rdm (j := 11) (by decide)
  have c3 : oPre < 2 ^ 15 := by decide
  have c4 : arg 10 < 2 ^ 15 := by decide
  have c5 : arg 11 < 2 ^ 15 := by decide
  have c6 : arg 10 % 4 = 0 := by decide
  have c7 : arg 11 % 4 = 0 := by decide
  have c8 : oM < 2 ^ 15 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]
    (Q := fun u =>
      u.gpr .r3 = s.gpr .r3 ∧ u.gpr .r4 = s.gpr .r6 ∧ u.gpr .r5 = fb s + BitVec.ofNat 64 oPre ∧
      u.gpr .r6 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧ u.gpr .r7 = s.gpr .r7 ∧
      u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r9 = fb s + BitVec.ofNat 64 oM ∧ u.gpr .r10 = s.gpr .r6 ∧
      u.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 10)).writeW (fb s + BitVec.ofNat 64 104)
        (stackArg s 11)) ?_ rfl) fun u ⟨⟨u3, u4, u5, u6, u7, u8, u9, u10, um⟩, k⟩ => ?_
  · unfold pubArgs preLen
    prun [exec_addSp0, A.sp, w0, w1, c3, c4, c5, c6, c7, c8, i10, i11, a10, a11, e26, preLen_val hk, A.r24,
      A.r27, A.r28, BitVec.or_self, BitVec.add_zero, exec_addi (show Reg.r12 ≠ .r0 by decide) c3,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c8, Impl.AesGcm.PPC64LE.mov]
    all_goals exact (gpr_ofNat _).symm
  · have hg : ∀ r ∈ preserved, u.gpr r = t.gpr r := fun r hr => k.gpr r (by revert r; decide)
    have M1 : Mid s { u with mem := t.mem.writeW (fb s + BitVec.ofNat 64 96) (stackArg s 10) } :=
      A.store (.inr (by decide)) (by decide) _ hg k.sp k.rd k.wr rfl
    have M2 : Mid s u := M1.store (d := 104) (.inr (by decide)) (by decide) _ (fun _ _ => rfl) rfl rfl rfl um
    have fw : Frame [⟨fb s + BitVec.ofNat 64 96, 8⟩, ⟨fb s + BitVec.ofNat 64 104, 8⟩] t.mem u.mem := by
      rw [um]
      exact Frame.writeW (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 96, 64 / 8⟩,
        ⟨fb s + BitVec.ofNat 64 104, 64 / 8⟩] t.mem) (List.mem_cons_self ..) _ (Region.contains_self _ _))
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
    have ap : ∀ {d n : Nat}, 112 ≤ d → d + n ≤ 2 ^ 64 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 8⟩ : Region),
        ⟨fb s + BitVec.ofNat 64 104, 8⟩], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
      intro d n hd hn r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) hn (by decide)
      · exact Offset.disjoint _ (.inr (by omega)) hn (by decide)
    have pwl := pw_le hk
    refine ⟨M2, ?_, ?_, u3, u4, u5, u6, u7, u8, u9, u10, ?_, ?_⟩
    · show Spec.Rsa.written _ _ _ _ _
      rw [fw.readW (Region.contains_self _ _) (ap (by decide) (by decide)) (by decide)]
      exact written_congr (bytes_of_frame (s := t) fw (ap (by decide) (by omega)) (by omega)) A.crt
    · intro ws hw
      rw [words_of_frame fw (ap (by decide) (by omega)) (by omega)]
      exact preW_of A.pre ws hw
    · rw [um, Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    · rw [um, Mem.readW_writeW_self64]

/-- `out`, of `k` bytes. -/
abbrev outR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r6).toNat⟩

theorem outR_eq {s : State} (h : PreP s) : outR s = oR s := by simp only [outR, oR, h.h4]

/-- The regions the call reads and writes. -/
abbrev pubRd (s : State) : List Region := [pwR s, eR s, mR s, ⟨fb s + BitVec.ofNat 64 96, 16⟩]

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
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws →
    Spec.Rsa.written u.mem (s.gpr .r3) (s.gpr .r6).toNat ((u.gpr .r3).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat))

/-- From the call of `vg_rsa_public_precomputed_checked` on: `Mid`, with
`out` written too. -/
structure Late (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = fr s :: s.wr
  r24 : u.gpr .r24 = s.gpr .r3
  r25 : u.gpr .r25 = s.gpr .r5
  r26 : u.gpr .r26 = s.gpr .r6
  r27 : u.gpr .r27 = s.gpr .r7
  r28 : u.gpr .r28 = s.gpr .r8
  r29 : u.gpr .r29 = s.gpr .r9
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, oR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem
  ls : u.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

/-- After the call of `vg_rsa_public_precomputed_checked`. -/
structure AtCmp (s u : State) : Prop extends Late s u where
  crt : crtOutM s u
  pub : pubOut s u

theorem pub_noFrames : Impl.Bignum.PPC64LE.PublicChecked.publicChecked.noFrames = true := by decide +kernel

theorem pubCall_ok {s t : State} (h : PreP s) (A : AtPubC s t) {Q : State → Prop}
    (hQ : ∀ u, AtCmp s u → Q u) : WP isa pubCall t Q := by
  have hk := h.k2
  have pk := pwR_sub h
  have pwl := pw_le hk
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega)
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
    · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oPre frameBytes; omega)))
    · exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp)
    · exact Covers.right (Covers.one (in_fr s _ (by decide) (by unfold oM frameBytes; omega)))
    · exact Covers.right (Covers.one (in_fr s _ (by decide) (by decide)))
  have g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  have hsp : (t.callEntry.withRegions (pubRd s) (pubWr s)).sp = fb s := A.sp
  have ha : stackArgAddr (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = fb s + BitVec.ofNat 64 96 := by
    rw [stackArgAddr_in, hsp]
  have sa0 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = stackArg s 10 := by
    show t.mem.readW _ 64 = _; rw [ha]; exact A.psa0
  have sa1 : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 1 = stackArg s 11 := by
    show t.mem.readW _ 64 = _; rw [stackArgAddr_in, hsp]; exact A.psa1
  have e6 : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
    rw [BitVec.toNat_ofNat]; omega
  have psk : Region.Sub ⟨fb s + BitVec.ofNat 64 96, 16⟩ (kR s) := frame_sub s (by decide)
  have mp : (mR s).Disjoint (pwR s) := Offset.disjoint _ (.inl (by unfold oM oPre; omega))
    (by unfold oM; omega) (by unfold oPre; omega)
  unfold pubCall
  refine WP.call (k := Proof.Bignum.PPC64LE.Pub.fnContract) (rd := pubRd s) (wr := pubWr s)
    Proof.Bignum.PPC64LE.Pub.fn_correct ?_ hc hw
    (fun u hrd hwr hsp' hf hpres _ hpost => hQ u ?_) pub_noFrames
  · simp only [Proof.Bignum.PPC64LE.Pub.fnContract, Proof.Bignum.PPC64LE.Pub.stackArgs, g .r3 (by decide),
      g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide),
      g .r9 (by decide), g .r10 (by decide), A.r3, A.r4, A.r5, A.r6, A.r7, A.r8, A.r9, A.r10, e6, sa0, sa1, hsp,
      ha, State.withRegions_rd, State.withRegions_wr]
    rw [show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s from outR_eq h]
    refine ⟨by omega, trivial, trivial, (h.ko.sub_left pk).symm, h.oe, (h.ko.sub_left mk).symm, h.os,
      (h.ko.sub_left psk).symm, h.ks.sub_left pk, h.es, h.ks.sub_left mk, (h.ks.sub_left psk).symm,
      h.h4 ▸ h.wo, ?_, h.we, ?_, h.ws, ⟨h.k1, h.k2⟩, trivial, trivial, h.e1, h.e2, ?_⟩
    · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega
    · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega
    · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
      unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
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
    have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) hf (fun r hr => frame_pub h (by unfold oM frameBytes; omega) hr) (by omega)
    refine ⟨⟨hsp'.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.r24,
      (hp _ (by decide)).trans A.r25, (hp _ (by decide)).trans A.r26, (hp _ (by decide)).trans A.r27,
      (hp _ (by decide)).trans A.r28, (hp _ (by decide)).trans A.r29,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => frame_pub h (by
        have := saved_offs p hp'; unfold oSave frameBytes at *; omega) hr, ?_⟩, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun r hr => frame_pub h (by decide) hr) (by decide)]; exact A.ls
    · show Spec.Rsa.written _ _ _ _ _
      rw [hf.readW (Region.contains_self _ _) (fun r hr => frame_pub h (by decide) hr) (by decide)]
      exact written_congr hm A.crt
    · intro ws hw
      have he : Spec.Rsa.bytesAt t.mem (s.gpr .r7) (s.gpr .r8).toNat =
          Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat :=
        bytes_of_frame A.mem (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.ke.symm
          · exact h.es) (by have := h.we; omega)
      simp only [Proof.Bignum.PPC64LE.Pub.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
        g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide), A.r3, A.r4, A.r5, A.r6,
        A.r7, A.r8, A.r9, e6, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, he] at hpost
      rw [hm]
      exact hpost _ (by simp [Spec.Rsa.bytesAt]) (by rw [A.pre ws hw]; exact hw)
