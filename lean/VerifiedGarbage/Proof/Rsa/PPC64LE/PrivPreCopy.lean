module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCorrect
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCorrect
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# `vg_rsa_private_checked_precomputed` on PPC64LE: `n`'s values from `pre`

The contract's precondition (`preP_ofP`): `PreP true`, and `PreX`, the facts
of `pre`. `preArgsP` and `preCopy` copy `pre`'s first `2 ⌈k / 8⌉` words to
the frame, where `vg_rsa_private_checked` has `n`'s computed values
(`step_true`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem stackArgs_fourteen (s : State) :
    List.map (stackArg s) (List.range 14) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13] := rfl

/-- `pre` holds the key's precomputed values. -/
abbrev PreHyp (s : State) : Prop :=
  Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 12) (stackArg s 13).toNat)

/-- What `vg_rsa_private_checked_precomputed`'s precondition adds: `pre`'s facts. -/
structure PreX (s : State) : Prop where
  oP : (oR s).Disjoint (preR s)
  sP : (sR s).Disjoint (preR s)
  kP : (kR s).Disjoint (preR s)
  wP : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  pl : (stackArg s 13).toNat =
    Spec.Rsa.privatePrecomputedWords (s.gpr .r6).toNat (stackArg s 1).toNat (stackArg s 3).toNat
  sp3 : s.sp.toNat + 208 ≤ 2 ^ 64
  hyp : PreHyp s

theorem preP_ofP {s : State} (h : (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre s) :
    PreP true s ∧ PreX s := by
  have e : frameBytes = 3327 + 1 := rfl
  rw [e] at h
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_fourteen, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oP, oa, ns, es, is, ps, qs, dps, dqs, qis, sP,
    sa, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, kP, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, wP, ⟨k1, k2⟩,
    h4, h10, e1, e2, p1, p2, q1, q2, h5, h9, h7, hs, hpl, hk⟩ := h
  exact ⟨⟨sp1, by omega_using [sp2], hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, h10, e1,
    e2, p1, p2, q1, q2, h5, h9, h7, hs⟩, ⟨oP, sP, kP, wP, hpl, by omega_using [sp2], hk⟩⟩

theorem pre_of_prePX {s : State} (h : PreP true s) (X : PreX s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre s := by
  obtain ⟨sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, h10, e1,
    e2, p1, p2, q1, q2, h5, h9, h7, hs⟩ := h
  obtain ⟨oP, sP, kP, wP, hpl, sp3, hk⟩ := X
  have e : frameBytes = 3327 + 1 := rfl
  rw [e]
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_fourteen, List.append_eq, List.range, List.range.loop]
  exact ⟨sp1, by omega_using [sp3], hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oP, oa, ns, es, is, ps, qs, dps, dqs, qis, sP,
    sa, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, kP, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, wP, ⟨k1, k2⟩,
    h4, h10, e1, e2, p1, p2, q1, q2, h5, h9, h7, hs, hpl, hk⟩

theorem in_aR14 {s : State} {j : Nat} (hj : j < 14) : (aR true s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])

theorem arg_inP {s t : State} (h : PreP true s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 14) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 (arg j)) 8 := by
  rw [← stackArgAddr_fb, hrd, h.hrd]
  exact ⟨aR true s, List.mem_append_left _ (by simp), in_aR14 hj⟩

theorem arg_read2P {s : State} (h : PreP true s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat}
    (hj : j < 14) : m.readW (fb s + BitVec.ofNat 64 (arg j)) 64 = stackArg s j := by
  rw [← stackArgAddr_fb]
  refine hm.readW (in_aR14 hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

/-- At the copy of `n`'s values from `pre`. -/
structure AtCopy (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  r3 : u.gpr .r3 = stackArg s 12
  r4 : u.gpr .r4 = fb s + BitVec.ofNat 64 oPre
  r5 : u.gpr .r5 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat)

theorem preArgsP_ok {s t : State} (h : PreP true s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgsP) t (AtCopy s) := by
  have hk := h.k2
  have e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := M.r26.trans (gpr_ofNat _)
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 oSt) 8 := by
    rw [M.wr]; exact word_in (by decide) (by decide) _
  have rdm : t.rd = s.rd := M.rd
  have a12 : (t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)).readW
      (fb s + BitVec.ofNat 64 (arg 12)) 64 = stackArg s 12 := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold oSt arg frameBytes; omega_arith))
      (by unfold arg frameBytes; omega_arith) (by decide)) (by decide)]
    exact arg_read2P h M.mem (by decide)
  have i12 := arg_inP h rdm (j := 12) (by decide)
  have c1 : oSt < 2 ^ 15 := by decide
  have c2 : oSt % 4 = 0 := by decide
  have c3 : oPre < 2 ^ 15 := by decide
  have c4 : arg 12 < 2 ^ 15 := by decide
  have c6 : arg 12 % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5] (Q := fun u =>
    u.gpr .r3 = stackArg s 12 ∧ u.gpr .r4 = fb s + BitVec.ofNat 64 oPre ∧
      u.gpr .r5 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .r3)) ?_ rfl) fun u ⟨⟨u3, u4, u5, um⟩, k⟩ => ?_
  · unfold preArgsP
    prun [exec_addSp0, M.sp, ho, c1, c2, c3, c4, c6, i12, a12, e26, preLen_val hk, M.r26,
      exec_addi (show Reg.r12 ≠ .r0 by decide) c3]
  · refine ⟨M.store (d := oSt) (.inl (by decide)) (by decide) _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd
      k.wr um, ?_, u3, u4, u5⟩
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
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega_arith) (by decide))
        (show (s.gpr .r6).toNat ≤ 2 ^ 64 by omega_arith) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [um, Mem.readW_writeW_self64, ← um]
    exact written_congr hb C

theorem pw_le_pre {s : State} (X : PreX s) :
    Spec.Rsa.precomputedWords (s.gpr .r6).toNat ≤ (stackArg s 13).toNat := by
  rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_arith

/-- `crtOutM` through a write of a word of the frame above `m`. -/
theorem crtOutM_store {s t : State} (h : PreP true s) (C : crtOutM s t) {d : Nat} (hd : oM + 1024 ≤ d)
    (hd' : d + 8 ≤ frameBytes) (v : BitVec 64) {m : Mem} (hm : m = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Spec.Rsa.written m (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat
      ((m.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)) := by
  have hk := h.k2
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem m := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
    bytes_of_frame (s := t) fw (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by unfold oM at *; omega_arith)) (by unfold oM; omega_arith)
        (by unfold frameBytes at hd'; omega_arith)) (by omega_arith)
  rw [fw.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSt oM at *; omega_arith)) (by decide)
      (by unfold frameBytes at hd'; omega_arith)) (by decide)]
  exact written_congr hb C

/-- The copy: `n`'s values, `pre`'s first words, in the frame. -/
theorem preCopy_ok {s t : State} (h : PreP true s) (X : PreX s) (A : AtCopy s t) :
    WP isa preCopy t (AtPub true s) := by
  have hk := h.k1; have hk' := h.k2
  have eP : oPre = 1272 := rfl
  have pwl := pw_le hk'
  have pwp := pw_le_pre X
  have wP := X.wP
  have pw1 : 1 ≤ Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
    unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega_arith
  obtain ⟨N, hN⟩ : ∃ N, Spec.Rsa.precomputedWords (s.gpr .r6).toNat = N := ⟨_, rfl⟩
  rw [hN] at pwl pwp pw1
  have hpre : preR s ∈ s.rd := by rw [h.hrd]; simp
  let Inv : Nat → State → Prop := fun i u =>
    Mid s u ∧ crtOutM s u ∧ u.gpr .r3 = stackArg s 12 + BitVec.ofNat 64 (8 * i) ∧
      u.gpr .r4 = fb s + BitVec.ofNat 64 (oPre + 8 * i) ∧
      ∀ j < i, u.mem.readW (fb s + BitVec.ofNat 64 (oPre + 8 * j)) 64 =
        s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * j)) 64
  refine WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (N := N) (by omega_arith) (by omega_arith) Inv
    (fun i hi u ⟨M, C, j3, j4, jw⟩ _ => ?_)
    ⟨A.toMid, A.crt, by rw [A.r3, Nat.mul_zero, BitVec.add_zero], by rw [A.r4, Nat.mul_zero, Nat.add_zero],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩ (by rw [A.r5, hN])) fun u ⟨M, C, _, _, jw⟩ => ?_
  · have hld : InRegions (u.rd ++ u.wr) (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 8 :=
      ⟨preR s, List.mem_append_left _ (by rw [M.rd]; exact hpre),
        Offset.contains_base (stackArg s 12) (d := 8 * i) (n := 8) (k := (stackArg s 13).toNat * 8)
          (by omega_arith) (by omega_arith)⟩
    have hst : InRegions u.wr (fb s + BitVec.ofNat 64 (oPre + 8 * i)) 8 := by
      rw [M.wr]; exact in_fr s _ (by unfold oPre; omega_arith) (by unfold oPre frameBytes; omega_arith)
    have hv : u.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64 =
        s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64 :=
      M.mem.readW (Offset.contains_base (stackArg s 12) (d := 8 * i) (n := 8) (k := (stackArg s 13).toNat * 8)
          (by omega_arith) (by omega_arith)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact X.kP.symm
        · exact X.sP.symm) (by decide)
    have c0 : (0 : Nat) < 2 ^ 15 ∧ 0 % 4 = 0 := by decide
    refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r0, .r3, .r4, .r5] (Q := fun u' =>
      u'.gpr .r3 = stackArg s 12 + BitVec.ofNat 64 (8 * (i + 1)) ∧
        u'.gpr .r4 = fb s + BitVec.ofNat 64 (oPre + 8 * (i + 1)) ∧
        u'.gpr .r5 = u.gpr .r5 - BitVec.ofNat 64 1 ∧
        u'.mem = u.mem.writeW (fb s + BitVec.ofNat 64 (oPre + 8 * i))
          (s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64)) ?_ (by decide))
      fun u' ⟨⟨a3, a4, a5, am⟩, k⟩ => ⟨⟨?_, ?_, a3, a4, fun j hj => ?_⟩, a5⟩
    · prun [j3, j4, BitVec.add_zero, exec_load_d (show Reg.r3 ≠ .r0 by decide) c0 (by rw [j3, BitVec.add_zero]; exact hld),
        hv, exec_store_d (s := u.write .r0 (s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64))
          (show Reg.r4 ≠ .r0 by decide) c0 (by
            simp only [VG.Proof.Bignum.PPC64LE.gpr_write, reduceCtorEq, ↓reduceIte, VG.Proof.Bignum.PPC64LE.wr_write, j4,
              BitVec.add_zero]; exact hst)]
      exact ⟨by rw [Mont.off, show 8 * (i + 1) = 8 * i + 8 by omega_using []],
        by rw [Mont.off, show oPre + 8 * (i + 1) = oPre + 8 * i + 8 by omega_using []]⟩
    · exact M.store (d := oPre + 8 * i) (.inl (by unfold oLr oPre; omega_arith)) (by unfold oPre frameBytes; omega_arith)
        _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd k.wr am
    · exact crtOutM_store h C (by unfold oM oPre; omega_arith) (by unfold oPre frameBytes; omega_arith) _ am
    · rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), jw j hj]
      · exact Mem.readW_writeW_self64 _ _ _
  · refine ⟨M, C, ?_⟩
    show Spec.Rsa.wordsAt _ _ _ = (if true = true then _ else _)
    simp only [↓reduceIte, Spec.Rsa.wordsAt, hN]
    refine List.map_congr_left fun j hj => ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact jw j (List.mem_range.mp hj)

theorem step_true (s : State) (h : PreP true s) (X : PreX s) : StepOk true s := fun _ _ _ M C hc =>
  WP.seq (WP.seq (WP.mono (preArgsP_ok h M C) fun _ A => WP.mono (preCopy_ok h X A) hc))

theorem wordsAt_take (m : Mem) (p : Addr) {n L : Nat} (h : n ≤ L) :
    Spec.Rsa.wordsAt m p n = (Spec.Rsa.wordsAt m p L).take n := by
  simp only [Spec.Rsa.wordsAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem publicPrecompute_length {nB : List Byte} {w : List (BitVec 64)}
    (h : Spec.Rsa.publicPrecompute nB = some w) : w.length = Spec.Rsa.precomputedWords nB.length := by
  unfold Spec.Rsa.publicPrecompute at h
  dsimp only at h
  split at h
  · cases h
    simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range,
      Spec.Rsa.precomputedWords]; omega_using []
  · cases h

theorem preValOk_of {s : State} (X : PreX s) (hp : PreHyp s) : PreValOk true s := fun ws hw => by
  have hl : ws.length = Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
    rw [publicPrecompute_length hw, Proof.Rsa.bytesAt_length']
  have hpre := hp
  simp only [PreHyp, Spec.Rsa.privatePrecompute] at hpre
  split at hpre
  · rw [hw, Option.map_some, Option.some.injEq] at hpre
    show (if true = true then _ else _) = ws
    simp only [↓reduceIte]
    rw [wordsAt_take _ _ (pw_le_pre X), ← hpre, List.append_assoc, List.take_left' hl]
  · cases hpre

/-- `crtPtr`: our caller's `r31` into the frame, and `r31 :=` the primes'
values in `pre`, after `n`'s. -/
theorem crtPtr_ok {s t : State} (h : PreP true s) (A : AtCrt s t) :
    WP isa (.block crtPtr) t fun u =>
      (u.gpr .r31 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat) ∧
        u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oR31) (s.gpr .r31) ∧ u.sp = t.sp) ∧
      Keep [.r0, .r12, .r31] t u := by
  have hk := h.k2
  have a12 : (t.mem.writeW (fb s + BitVec.ofNat 64 oR31) (t.gpr .r31)).readW
      (fb s + BitVec.ofNat 64 (arg 12)) 64 = stackArg s 12 := by
    rw [Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold oR31 arg frameBytes; omega_arith))
      (by unfold arg frameBytes; omega_arith) (by unfold oR31; omega_arith)) (by decide), ← stackArgAddr_fb]
    exact A.mem.readW (in_aR14 (by decide)) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm)
      (by decide)
  have i12 := arg_inP h A.rd (j := 12) (by decide)
  have iw : InRegions t.wr (fb s + BitVec.ofNat 64 oR31) 8 := by
    rw [A.wr]; exact in_fr s _ (by unfold oR31; omega_arith) (by unfold oR31 frameBytes; omega_arith)
  have c1 : oR31 < 2 ^ 15 := by decide
  have c2 : oR31 % 4 = 0 := by decide
  have c4 : arg 12 < 2 ^ 15 := by decide
  have c6 : arg 12 % 4 = 0 := by decide
  have e26 : t.gpr .r26 = BitVec.ofNat 64 (s.gpr .r6).toNat := A.r26.trans (gpr_ofNat _)
  have e31 : t.gpr .r31 = s.gpr .r31 := A.hi _ (by decide)
  have ev : (BitVec.ofNat 64 (s.gpr .r6).toNat + BitVec.ofNat 64 7) >>> 3 <<< 4 =
      BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat) := by
    rw [Proof.Bignum.PPC64LE.Pre.ofNat_add7_shr3 _ (by omega_arith)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Spec.Rsa.precomputedWords,
      Spec.Rsa.modulusWords]
    rw [Nat.mod_eq_of_lt (a := ((s.gpr .r6).toNat + 7) / 8) (by omega_arith)]
    omega_arith
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  unfold crtPtr
  rw [← e31]
  prun [exec_addSp0, A.sp, e26, i12, a12, iw, c1, c2, c4, c6, ev]

/-- The words from the `n`th of `wordsAt`. -/
theorem wordsAt_off (m : Mem) (p : Addr) (n k : Nat) :
    Spec.Rsa.wordsAt m (p + BitVec.ofNat 64 (8 * n)) k = (Spec.Rsa.wordsAt m p (n + k)).drop n := by
  simp only [Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map]
  rw [List.drop_left' (by simp)]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [Nat.mul_add, ← BitVec.ofNat_add_ofNat, BitVec.add_assoc]

/-- The words after `n`'s in `pre`, when `pre` holds the key's precomputed values. -/
theorem primes_of_hyp {s : State} (X : PreX s) {m : Mem}
    (hm : Spec.Rsa.wordsAt m (stackArg s 12) (stackArg s 13).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 12) (stackArg s 13).toNat) :
    Spec.Rsa.wordsAt m (stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat))
        (Spec.Rsa.primeWords (stackArg s 1).toNat + Spec.Rsa.primeWords (stackArg s 3).toNat) =
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) ++
        Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) := by
  have hpre := X.hyp
  simp only [PreHyp, Spec.Rsa.privatePrecompute] at hpre
  split at hpre
  · cases hw : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) with
    | none => rw [hw] at hpre; cases hpre
    | some ws =>
      rw [hw, Option.map_some, Option.some.injEq] at hpre
      have hl : ws.length = Spec.Rsa.precomputedWords (s.gpr .r6).toNat := by
        rw [publicPrecompute_length hw, Proof.Rsa.bytesAt_length']
      have hL : (stackArg s 13).toNat = Spec.Rsa.precomputedWords (s.gpr .r6).toNat +
          (Spec.Rsa.primeWords (stackArg s 1).toNat + Spec.Rsa.primeWords (stackArg s 3).toNat) := by
        rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
      rw [wordsAt_off, ← hL, hm, ← hpre, List.append_assoc, ← hl, List.drop_left]
  · cases hpre

/-- The primes' values in `pre`, after `n`'s. -/
abbrev r2Rs (s : State) : Region :=
  ⟨stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat),
    8 * (Proof.Bignum.wsWords (stackArg s 1).toNat + Proof.Bignum.wsWords (stackArg s 3).toNat)⟩

theorem r2Rs_sub {s : State} (X : PreX s) : Region.Sub (r2Rs s) (preR s) := by
  refine Offset.sub_base _ ?_
  rw [X.pl]
  unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.primeWords Spec.Rsa.modulusWords Proof.Bignum.wsWords
  omega_using []

/-- `vg_rsa_private_crt_precomputed`'s precondition at the call, after
`crtPtr`. -/
theorem crt_preP {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t) (k : Keep [.r0, .r12, .r31] t u)
    (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oR31) (s.gpr .r31)) (hsp : u.sp = t.sp)
    (h31 : u.gpr .r31 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat)) :
    Proof.Bignum.PPC64LE.Crt.fnContractP.pre (crtEntryG s u [r2Rs s]) := by
  have hk := h.k2
  have hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i) := fun i hi => by
    rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oR31; omega_arith))
      (by omega_arith) (by unfold oR31; omega_arith)) (by decide)]
    exact A.psa i hi
  have kk : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], u.gpr r = t.gpr r := fun r hr =>
    k.gpr _ (by revert r; decide)
  have hc := crt_preG (X := [r2Rs s]) h A kk hpsa hsp
  have g : ∀ r, r ∉ linkRegs → r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] →
      (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun r h1 h2 => (State.callEntry_gpr u h1).trans (kk r h2)
  have e31 : (crtEntryG s u [r2Rs s]).gpr .r31 = stackArg s 12 +
      BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat) :=
    (State.callEntry_gpr u (by decide)).trans h31
  have sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := [r2Rs s]) (i := i) hi
  have hr : Proof.Bignum.PPC64LE.Crt.r2R (crtEntryG s u [r2Rs s]) = r2Rs s := by
    simp only [Proof.Bignum.PPC64LE.Crt.r2R, e31, g .r10 (by decide) (by decide), A.r10, sa 1 (by decide)]
  have sub := r2Rs_sub X
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  have wP := X.wP
  have hpl := X.pl
  refine ⟨hr ▸ hc, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    simp only [g .r3 (by decide) (by decide), g .r4 (by decide) (by decide), A.r3, A.r4]
    exact (X.kP.sub_left mk).sub_right sub
  · rw [hr, sa 8 (by decide), sa 9 (by decide)]
    exact (X.sP.sub_right sub).symm
  · rw [hr, e31]
    rw [hpl] at wP
    unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.primeWords Spec.Rsa.modulusWords at wP
    simp only [Proof.Bignum.wsWords]
    rw [Offset.toNat_add_ofNat]
    all_goals omega_arith
  · have hfu : Frame [kR s] s.mem u.mem := by
      rw [hm]
      exact A.mem.writeW (List.mem_singleton_self _) _
        (frame_contains s (by unfold oR31 frameBytes; omega_arith))
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) hfu (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    have hw : Spec.Rsa.wordsAt u.mem (stackArg s 12) (stackArg s 13).toNat =
        Spec.Rsa.wordsAt s.mem (stackArg s 12) (stackArg s 13).toNat :=
      words_of_frame hfu (fun r hr => by
        rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_arith)
    simp only [State.withRegions_mem, State.callEntry_mem, e31, g .r9 (by decide) (by decide),
      g .r10 (by decide) (by decide), A.r9, A.r10, sa 0 (by decide), sa 1 (by decide), Nat.reduceAdd]
    rw [hb h.kp.symm (by have := h.wp; omega_arith), hb h.kq.symm (by have := h.wq; omega_arith)]
    exact primes_of_hyp X hw

theorem crtP_noFrames : Impl.Bignum.PPC64LE.Crt.crtP.noFrames = true := by decide +kernel

/-- The slot of our caller's `r31` is apart from what the call writes. -/
theorem r31_apart {s : State} (h : PreP true s) {r : Region} (hr : r ∈ crtWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 oR31, 8⟩ r := by
  have hk := h.k2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inr (by unfold oM oR31; omega_arith)) (by unfold oR31; omega_arith)
      (by unfold oM; omega_arith)
  · exact h.ks.sub_left (frame_sub s (by unfold oR31 frameBytes; omega_arith))

/-- The regions of the call of `vg_rsa_private_crt_precomputed`. -/
theorem coversP {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t) (k : Keep [.r0, .r12, .r31] t u) :
    Covers (crtRd s ++ [r2Rs s] ++ crtWr s) (u.rd ++ u.wr) ∧ Covers (crtWr s) u.wr := by
  obtain ⟨hc0, hw0⟩ := crt_covers h A
  refine ⟨?_, by rw [k.wr]; exact hw0⟩
  rw [k.rd, k.wr]
  refine Covers.append_left (Covers.append_left (fun a n ⟨r, hr, c⟩ => hc0 a n ⟨r, List.mem_append_left _ hr, c⟩)
    (Covers.left (Covers.of_sub fun r hr => ?_))) (Covers.right hw0)
  rw [List.mem_singleton.mp hr]
  refine ⟨preR s, by rw [A.rd, h.hrd]; simp [rdL], 8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat, rfl, ?_⟩
  have := X.pl
  unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.primeWords Spec.Rsa.modulusWords at this
  simp only [Proof.Bignum.wsWords]
  omega_using [this]

/-- After `vg_rsa_private_crt_precomputed`, called from the state `u` after
`crtPtr`, from the state `t` at the call of the CRT. -/
def AfterP (s v : State) : Prop :=
  ∃ t u, AtCrt s t ∧ Keep [.r0, .r12, .r31] t u ∧ u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oR31) (s.gpr .r31) ∧
    u.sp = t.sp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧ Frame (crtWr s) u.mem v.mem ∧
    (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
    Proof.Bignum.PPC64LE.Crt.fnContractP.post (crtEntryG s u [r2Rs s])
      (v.withRegions (crtRd s ++ [r2Rs s]) (crtWr s))

theorem callP_ok {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t) (k : Keep [.r0, .r12, .r31] t u)
    (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oR31) (s.gpr .r31)) (hsp : u.sp = t.sp)
    (h31 : u.gpr .r31 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .r6).toNat)) :
    WP isa crtCallP u (AfterP s) := by
  obtain ⟨hc, hw⟩ := coversP h X A k
  unfold crtCallP
  exact WP.call (k := Proof.Bignum.PPC64LE.Crt.fnContractP) Proof.Bignum.PPC64LE.Crt.fn_correctP
    (crt_preP h X A k hm hsp h31) hc hw (fun v hrd hwr hsp' hf hpres _ hpost =>
      ⟨t, u, A, k, hm, hsp, hrd, hwr, hsp', hf, hpres, hpost⟩) crtP_noFrames

/-- Our caller's `r31` back, after `vg_rsa_private_crt_precomputed`: what
`vg_rsa_private_crt` gives. -/
theorem restoreP_ok {s v : State} (h : PreP true s) (hv : AfterP s v) :
    WP isa (.block crtRestore) v fun w => Mid s w ∧ crtOut s w := by
  obtain ⟨t, u, A, k, hm, hsp, hrd, hwr, hsp', hf, hp, hpost⟩ := hv
  have hk := h.k2
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by unfold oM frameBytes; omega_arith)
  have hfu : Frame [kR s] s.mem u.mem := by
    rw [hm]
    exact A.mem.writeW (List.mem_singleton_self _) _ (frame_contains s (by unfold oR31 frameBytes; omega_arith))
  have r31v : v.mem.readW (fb s + BitVec.ofNat 64 oR31) 64 = s.gpr .r31 := by
    rw [hf.readW (Region.contains_self _ _) (fun r hr => r31_apart h hr) (by decide), hm, Mem.readW_writeW_self64]
  have i31 : InRegions (v.rd ++ v.wr) (fb s + BitVec.ofNat 64 oR31) 8 := by
    rw [hrd, hwr, k.rd, k.wr, A.wr]
    exact in_fr' s _ _ (by unfold oR31; omega_arith) (by unfold oR31 frameBytes; omega_arith)
  have vsp : v.sp = fb s := hsp'.trans (hsp.trans A.sp)
  have c1 : oR31 < 2 ^ 15 := by decide
  have c2 : oR31 % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r31] (Q := fun w => w.gpr .r31 = s.gpr .r31 ∧
    w.mem = v.mem ∧ w.sp = v.sp) (by unfold crtRestore; prun [exec_addSp0, vsp, i31, r31v, c1, c2]) rfl)
    fun w ⟨⟨w31, wm, wsp⟩, kw⟩ => ⟨?_, ?_⟩
  · have g : ∀ r, r ∉ [Reg.r12, .r31] → r ∉ [Reg.r0, .r12, .r31] → r ∈ preserved → w.gpr r = t.gpr r :=
      fun r h1 h1' h2 => by rw [kw.gpr _ h1, hp r h2, k.gpr _ h1']
    refine ⟨wsp.trans vsp, by rw [kw.rd, hrd, k.rd, A.rd], by rw [kw.wr, hwr, k.wr, A.wr],
      (g _ (by decide) (by decide) (by decide)).trans A.r24, (g _ (by decide) (by decide) (by decide)).trans A.r25,
      (g _ (by decide) (by decide) (by decide)).trans A.r26, (g _ (by decide) (by decide) (by decide)).trans A.r27,
      (g _ (by decide) (by decide) (by decide)).trans A.r28, (g _ (by decide) (by decide) (by decide)).trans A.r29,
      fun r hr => ?_, ?_, ?_, ?_⟩
    · by_cases e : r = .r31
      · subst e; exact w31
      · exact (g r (by revert e; revert hr; revert r; decide) (by revert e; revert hr; revert r; decide)
          (by clear e; revert hr; revert r; decide)).trans (A.hi r hr)
    · rw [wm]
      refine (hfu.mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
      · simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., mk⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · rw [wm]
      refine (A.sv.frame (rs := [⟨fb s + BitVec.ofNat 64 oR31, 8⟩]) (by
          rw [hm]; exact Frame.writeW (Frame.refl _ t.mem) (List.mem_singleton_self _) _ (Region.contains_self _ _))
        fun p hp' r hr => ?_).frame hf fun p hp' r hr => below_apart h (by
          have := saved_offs p hp'; unfold oSave oM at *; omega_arith) hr
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp'
      exact Offset.disjoint _ (.inl (by unfold oSave oR31 at *; omega_arith)) (by unfold oSave at *; omega_arith)
        (by unfold oR31; omega_arith)
    · rw [wm, hf.readW (Region.contains_self _ _) (fun r hr => below_apart h (by decide) hr) (by decide), hm,
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide)]
      exact A.ls
  · have g : ∀ r, r ∉ linkRegs → r ∈ [Reg.r3, .r5, .r6, .r7, .r9, .r10] →
        (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun r h1 h2 =>
      (State.callEntry_gpr u h1).trans (k.gpr _ (by clear h1; revert h2; revert r; decide))
    have hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s (2 + i) := fun i hi => by
      rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oR31; omega_arith))
        (by omega_arith) (by unfold oR31; omega_arith)) (by decide)]
      exact A.psa i hi
    have sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := [r2Rs s]) (i := i) hi
    simp only [Proof.Bignum.PPC64LE.Crt.fnContractP, Proof.Bignum.PPC64LE.Crt.postCore,
      g .r3 (by decide) (by decide), g .r5 (by decide) (by decide), g .r6 (by decide) (by decide),
      g .r7 (by decide) (by decide), g .r9 (by decide) (by decide), g .r10 (by decide) (by decide),
      A.r3, A.r5, A.r6, A.r7, A.r9, A.r10,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    have ei : (⟨s.gpr .r9, (s.gpr .r6).toNat⟩ : Region) = iR s := by simp only [iR, h.h10]
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) hfu (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_arith), hb (ei ▸ h.ki.symm) (by have := h.k2; omega_arith),
      hb h.kp.symm (by have := h.wp; omega_arith), hb h.kq.symm (by have := h.wq; omega_arith),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega_arith), hb (h.h7 ▸ h.kdq.symm) (by have := h.wdq; omega_arith),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega_arith)] at hpost
    show Spec.Rsa.written w.mem _ _ ((w.gpr .r3).setWidth 32) _
    rw [wm, kw.gpr .r3 (by decide)]
    exact hpost

/-- With the key's precomputed values: `vg_rsa_private_crt_precomputed`, given
the primes' values in `r31`, our caller's `r31` kept in the frame. -/
theorem crt_true (s : State) (h : PreP true s) (X : PreX s) : CrtOk true s := fun t Q A hQ => by
  unfold crtStep
  refine WP.seq (WP.mono (crtPtr_ok h A) fun u ⟨⟨h31, hm, hsp⟩, k⟩ => ?_)
  exact WP.seq (WP.mono (callP_ok h X A k hm hsp h31) fun v hv =>
    WP.mono (restoreP_ok h hv) fun w ⟨M, C⟩ => hQ w M C)

theorem codeP_correct (s : State) (hpre : (Proof.Rsa.privateCheckedPrecomputedContract abi frameBytes).pre s) :
    ∃ tr t, Exec isa codeP s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  obtain ⟨h, X⟩ := preP_ofP hpre
  exact WP.mono (codeG_correct s h (crt_true s h X) (step_true s h X)) fun t ⟨ha, hf⟩ =>
    ⟨ha, hf (preValOk_of X X.hyp)⟩

end VG.Proof.Rsa.PPC64LE.Priv
