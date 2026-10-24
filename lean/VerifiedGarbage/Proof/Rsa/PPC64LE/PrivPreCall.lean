module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCrt
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_private_checked` on PPC64LE: the call of `vg_rsa_public_precompute`

The CRT's status kept in the frame (`preArgs_ok`, into `AtPre`), then the
call by the callee's contract on its registers (`Pre.fnContract`,
`Pre.fn_correct`): `n`'s values into the frame (`preCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem written_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.written m out k r o) :
    Spec.Rsa.written m' out k r o := by
  cases o <;> simp only [Spec.Rsa.written, hb] at h ⊢ <;> exact h

/-- `m` and the CRT's status kept in the frame. -/
abbrev crtOutM (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat
    ((u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- A word of the frame above the slots, in it. -/
theorem word_in {s : State} {d : Nat} (hd : oLr + 8 ≤ d) (hd' : d + 8 ≤ frameBytes) (rs : List Region) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) 8 :=
  in_fr s rs (by unfold oLr at hd; omega) hd'

/-- `Mid` is kept by a write of a word of the frame above the slots. -/
theorem Mid.store {s t : State} (M : Mid s t) {d : Nat} (hd : oLr + 8 ≤ d) (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Mid s u := by
  have hd1 : ∀ {e : Nat}, e + 8 ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, 8⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ := fun he =>
    Offset.disjoint _ (.inl (by omega)) (by unfold oLr at he; omega) (by unfold frameBytes at hd'; omega)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.r24,
    (hg _ (by decide)).trans M.r25, (hg _ (by decide)).trans M.r26, (hg _ (by decide)).trans M.r27,
    (hg _ (by decide)).trans M.r28, (hg _ (by decide)).trans M.r29,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]; exact hd1 (by have := saved_offs p hp; unfold oSave oLr at *; omega), ?_⟩
  · rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')
  · rw [fw.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd1 (by decide))
      (by decide)]
    exact M.ls

/-- Our stack argument `j`, after the frame and the working space changed. -/
theorem arg_read2 {s : State} (h : PreP s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  refine hm.readW (in_aR hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

/-- At the call of `vg_rsa_public_precompute`. -/
structure AtPre (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  r3 : u.gpr .r3 = fb s + BitVec.ofNat 64 oPre
  r4 : u.gpr .r4 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)
  r5 : u.gpr .r5 = s.gpr .r5
  r6 : u.gpr .r6 = s.gpr .r6
  r7 : u.gpr .r7 = stackArg s 10
  r8 : u.gpr .r8 = stackArg s 11

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem preLen_val {k : Nat} (hk : k ≤ 1024) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords k) := by
  rw [Proof.Bignum.PPC64LE.Pre.ofNat_add7_shr3 k (by omega), Proof.Bignum.PPC64LE.Pre.ofNat_shl1]; rfl

theorem preArgs_ok {s t : State} (h : PreP s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgs) t (AtPre s) := by
  have hk := h.k2
  have e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := M.r26.trans (gpr_ofNat _)
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [M.wr]; exact word_in (by decide) (by decide) _
  have rdm : t.rd = s.rd := M.rd
  have hrdw : ∀ {j : Nat}, j < 12 → (t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)).readW
      (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := fun hj => by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold oSt arg frameBytes; omega))
      (by unfold arg frameBytes; omega) (by decide)) (by decide)]
    exact arg_read2 h M.mem hj
  have a10 := hrdw (j := 10) (by decide)
  have a11 := hrdw (j := 11) (by decide)
  have i10 := arg_in h rdm (j := 10) (by decide)
  have i11 := arg_in h rdm (j := 11) (by decide)
  have c1 : oSt < 2 ^ 15 := by decide
  have c2 : oSt % 4 = 0 := by decide
  have c3 : oPre < 2 ^ 15 := by decide
  have c4 : arg 10 < 2 ^ 15 := by decide
  have c5 : arg 11 < 2 ^ 15 := by decide
  have c6 : arg 10 % 4 = 0 := by decide
  have c7 : arg 11 % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6, .r7, .r8] (Q := fun u =>
    u.gpr .r3 = fb s + BitVec.ofNat 64 oPre ∧
      u.gpr .r4 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧ u.gpr .r5 = s.gpr .r5 ∧
      u.gpr .r6 = s.gpr .r6 ∧ u.gpr .r7 = stackArg s 10 ∧ u.gpr .r8 = stackArg s 11 ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)) ?_ rfl) fun u ⟨⟨u3, u4, u5, u6, u7, u8, um⟩, k⟩ => ?_
  · unfold preArgs preLen
    prun [exec_addSp0, M.sp, ho, c1, c2, c3, c4, c5, c6, c7, i10, i11, a10, a11, e26, preLen_val hk, M.r25, M.r26,
      BitVec.or_self, exec_addi (show Reg.r12 ≠ .r0 by decide) c3, Impl.AesGcm.PPC64LE.mov]
    all_goals exact (gpr_ofNat _).symm
  · refine ⟨M.store (d := oSt) (by decide) (by decide) _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd
      k.wr um, ?_, u3, u4, u5, u6, u7, u8⟩
    have hb : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [um]
      exact Frame.bytes (R := mR s) (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
        (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega) (by decide))
        (show (s.gpr .r6).toNat ≤ 2 ^ 64 by omega) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [um, Mem.readW_writeW_self64, ← um]
    exact written_congr hb C

/-- `n`'s values, in the frame. -/
abbrev pwR (s : State) : Region :=
  ⟨fb s + BitVec.ofNat 64 oPre, Spec.Rsa.precomputedWords (s.gpr .r6).toNat * 8⟩

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
  pre : Proof.Bignum.PPC64LE.Pre.preOut (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) (u.gpr .r3) u.mem

theorem pre_noFrames : Impl.Bignum.PPC64LE.Precompute.precompute.noFrames = true := by decide +kernel

theorem preCall_ok {s t : State} (h : PreP s) (A : AtPre s t) {Q : State → Prop}
    (hQ : ∀ u, AtPub s u → Q u) : WP isa preCall t Q := by
  have hk := h.k2
  have pk := pwR_sub h
  have pwl := pw_le hk
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have hw : Covers (preWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oPre; omega) (by unfold oPre frameBytes; omega))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  have hc : Covers ([nR s] ++ preWr s) (t.rd ++ t.wr) := by
    refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.right hw)
    rw [List.mem_singleton.mp hr, A.rd, h.hrd]; simp
  have g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  have e4 : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
    rw [BitVec.toNat_ofNat]; omega
  have hn : Spec.Rsa.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat :=
    bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega)
  unfold preCall
  refine WP.call (k := Proof.Bignum.PPC64LE.Pre.fnContract) (rd := [nR s]) (wr := preWr s)
    Proof.Bignum.PPC64LE.Pre.fn_correct ?_ hc hw
    (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_) pre_noFrames
  · simp only [Proof.Bignum.PPC64LE.Pre.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
      g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), A.r3, A.r4, A.r5, A.r6, A.r7, A.r8, e4,
      State.withRegions_rd, State.withRegions_wr, Proof.Bignum.PPC64LE.Pre.nR, Proof.Bignum.PPC64LE.Pre.preR,
      Proof.Bignum.PPC64LE.Pre.scrR]
    refine ⟨trivial, trivial, h.kn.sub_left pk, h.ks.sub_left pk, h.ns, ?_, h.wn, h.ws, ⟨h.k1, h.k2⟩, trivial, ?_⟩
    · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega
    · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
      unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    have ft : Frame [kR s, sR s] s.mem u.mem := by
      refine (A.mem.trans (hf.sub fun r hr => ?_))
      simp only [preWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., pk⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) hf (fun r hr => below_pre h (by unfold oM oPre; omega) hr) (by omega)
    have hst : u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 :=
      hf.readW (Region.contains_self _ _) (fun r hr => below_pre h (by decide) hr) (by decide)
    refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.r24,
      (hp _ (by decide)).trans A.r25, (hp _ (by decide)).trans A.r26, (hp _ (by decide)).trans A.r27,
      (hp _ (by decide)).trans A.r28, (hp _ (by decide)).trans A.r29,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => below_pre h (by
        have := saved_offs p hp'; unfold oSave oPre at *; omega) hr, ?_⟩, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun r hr => below_pre h (by decide) hr) (by decide)]; exact A.ls
    · show Spec.Rsa.written _ _ _ _ _
      rw [hst]; exact written_congr hm A.crt
    · simp only [Proof.Bignum.PPC64LE.Pre.fnContract, g .r3 (by decide), g .r4 (by decide), g .r5 (by decide),
        g .r6 (by decide), A.r3, A.r4, A.r5, A.r6, e4, State.withRegions_mem, State.withRegions_gpr,
        State.callEntry_mem, hn] at hpost
      exact hpost

end VG.Proof.Rsa.PPC64LE.Priv
