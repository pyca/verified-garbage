module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCorrect
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# `vg_rsa_private_checked_precomputed` on RISC-V: `n`'s values from `pre`

The contract's precondition (`preP_ofP`): `PreP true`, and `PreX`, the facts
of `pre`. `preArgsP` and `preCopy` copy `pre`'s first `2 ⌈k / 8⌉` words to
the frame, where `vg_rsa_private_checked` has `n`'s computed values
(`step_true`). `crtPtr` keeps `out` in the frame and points `s1` at the
primes' values in `pre`, for `vg_rsa_private_crt_precomputed`; `crtRestore`
puts `out` back (`crt_true`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

theorem stackArgs_fourteen (s : State) :
    List.map (stackArg s) (List.range 14) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13] := rfl

/-- `pre` holds the key's precomputed values. -/
abbrev PreHyp (s : State) : Prop :=
  Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
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
    Spec.Rsa.privatePrecomputedWords (s.gpr .a3).toNat (stackArg s 1).toNat (stackArg s 3).toNat
  sp3 : s.sp.toNat + 112 ≤ 2 ^ 64
  hyp : PreHyp s
  alP : (stackArg s 12).toNat % 8 = 0

theorem preP_ofP {s : State} (h : (Proof.Rsa.privateCheckedPrecomputedContract RISCV64.abi frameBytes).pre s) :
    PreP true s ∧ PreX s := by
  have e : frameBytes = 3247 + 1 := rfl
  rw [e] at h
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs, stackArgs_fourteen, List.append_eq, List.range,
    List.range.loop] at h
  obtain ⟨sp16, sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oP, oa, ns, es, is, ps, qs, dps, dqs,
    qis, sP, sa, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, kP, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, wP,
    ⟨k1, k2⟩, h1, h7, e1, e2, p1, p2, q1, q2, h5, h9, h7', hs, hpl, hk, al, alP⟩ := h
  exact ⟨⟨sp16, sp1, by omega, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs,
    qis, sa, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h1,
    h7, e1, e2, p1, p2, q1, q2, h5, h9, h7', hs, al⟩, ⟨oP, sP, kP, wP, hpl, sp2, hk, alP⟩⟩

theorem pre_of_prePX {s : State} (h : PreP true s) (X : PreX s) :
    (Proof.Rsa.privateCheckedPrecomputedContract RISCV64.abi frameBytes).pre s := by
  obtain ⟨sp16, sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h1, h7, e1,
    e2, p1, p2, q1, q2, h5, h9, h7', hs, al⟩ := h
  obtain ⟨oP, sP, kP, wP, hpl, sp3, hk, alP⟩ := X
  have e : frameBytes = 3247 + 1 := rfl
  rw [e]
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs, stackArgs_fourteen, List.append_eq, List.range,
    List.range.loop]
  exact ⟨sp16, sp1, sp3, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oP, oa, ns, es, is, ps, qs, dps, dqs,
    qis, sP, sa, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, kP, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, wP,
    ⟨k1, k2⟩, h1, h7, e1, e2, p1, p2, q1, q2, h5, h9, h7', hs, hpl, hk, al, alP⟩

theorem in_aR14 {s : State} {j : Nat} (hj : j < 14) : (aR true s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by simp only [↓reduceIte]; omega) (by omega)

theorem arg_inP {s t : State} (h : PreP true s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 14) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd, h.hrd]
  exact ⟨aR true s, List.mem_append_left _ (by simp), in_aR14 hj⟩

theorem arg_read2P {s : State} (h : PreP true s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat}
    (hj : j < 14) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine hm.readW (in_aR14 hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

theorem stackArgAddr_alP {s : State} (h : PreP true s) (X : PreX s) (j : Nat) (_hj : j < 14) :
    (stackArgAddr s j).toNat % 8 = 0 := by
  have := h.sp16; have := X.sp3
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- At the copy of `n`'s values from `pre`. -/
structure AtCopy (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  a0 : u.gpr .a0 = stackArg s 12
  a1 : u.gpr .a1 = fb s + BitVec.ofNat 64 oPre
  a2 : u.gpr .a2 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)

/-- `preArgsP` up to `argBase`, and after it. -/
abbrev preP1 : List Instr := [.addSp .t0 0, .store .d .a0 .t0 oSt]
abbrev preP2 : List Instr := [.load .d .a0 .t6 96, .addi .a1 .t0 oPre] ++ preLen .a2

theorem preArgsP_eq : preArgsP = preP1 ++ (argBase ++ preP2) := by simp only [preArgsP, List.append_assoc]

theorem preP1_ok {s t : State} (h : PreP true s) (M : Mid s t) :
    WP isa (.block preP1) t fun w =>
      (w.gpr .t0 = fb s ∧ w.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0)) ∧ Keep [.t0] t w := by
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 152) 8 := by
    rw [M.wr]; exact in_fr s _ (by decide)
  have hal : (fb s + BitVec.ofNat 64 152).toNat % 8 = 0 := fb_al8 h (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [preP1, exec_addSp, M.sp, BitVec.add_zero, ho, hal, oSt]

theorem preP2_ok {s x : State} (h : PreP true s) (X : PreX s) (hrd : x.rd = s.rd)
    (hm : Frame [kR s, sR s] s.mem x.mem) (h6 : x.gpr .t6 = s.sp) (h0 : x.gpr .t0 = fb s)
    (h3 : x.gpr .s3 = s.gpr .a3) :
    WP isa (.block preP2) x fun u =>
      (u.gpr .a0 = stackArg s 12 ∧ u.gpr .a1 = fb s + BitVec.ofNat 64 oPre ∧
        u.gpr .a2 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧ u.mem = x.mem) ∧
      Keep [.a0, .a1, .a2] x u := by
  have i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 96) 8 := arg_inP h hrd (j := 12) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 96).toNat % 8 = 0 := stackArgAddr_alP h X 12 (by decide)
  have r0 : x.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = stackArg s 12 := arg_read2P h hm (j := 12) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [preP2, h6, i0, l0, r0, h0, h3, oPre, preLen, preLen_val h.k2]

theorem preArgsP_ok {s t : State} (h : PreP true s) (X : PreX s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgsP) t (AtCopy s) := by
  have hk := h.k2
  rw [preArgsP_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (preP1_ok h M)) fun w ⟨⟨⟨w0, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans M.sp) fun x x6 kx xm xsp => ?_
  have hmw : Frame [kR s, sR s] s.mem x.mem := by
    rw [xm, wm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s (by decide))
  refine WP.mono (WP.rdwr (preP2_ok h X (kx.2.1.trans (wrd.trans M.rd)) hmw x6
    ((kx.gpr (by decide)).trans w0) ((kx.gpr (by decide)).trans ((kw.gpr (by decide)).trans M.s3))))
    fun u ⟨⟨⟨u0, u1, u2, um⟩, ku⟩, urd, uwr, usp⟩ => ?_
  have hum : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0) := by rw [um, xm, wm]
  refine ⟨M.store (d := oSt) (.inl (by decide)) (by decide) _ (fun r hr => ?_) (usp.trans (xsp.trans wsp))
    (urd.trans (kx.2.1.trans wrd)) (uwr.trans (kx.2.2.trans wwr)) hum, ?_, u0, u1, u2⟩
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

theorem pw_le_pre {s : State} (X : PreX s) :
    Spec.Rsa.precomputedWords (s.gpr .a3).toNat ≤ (stackArg s 13).toNat := by
  rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega

/-- `crtOutM` through a write of a word of the frame above `m`. -/
theorem crtOutM_store {s t : State} (h : PreP true s) (C : crtOutM s t) {d : Nat} (hd : oM + 1024 ≤ d)
    (hd' : d + 8 ≤ frameBytes) (v : BitVec 64) {m : Mem} (hm : m = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Spec.Rsa.written m (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat
      ((m.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
      (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)) := by
  have hk := h.k2
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem m := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat :=
    bytes_of_frame (s := t) fw (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by unfold oM at *; omega)) (by unfold oM; omega)
        (by unfold frameBytes at hd'; omega)) (by omega)
  rw [fw.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSt oM at *; omega)) (by decide)
      (by unfold frameBytes at hd'; omega)) (by decide)]
  exact written_congr hb C

/-- The copy: `n`'s values, `pre`'s first words, in the frame. -/
theorem preCopy_ok {s t : State} (h : PreP true s) (X : PreX s) (A : AtCopy s t) :
    WP isa preCopy t (AtPub true s) := by
  have hk := h.k1; have hk' := h.k2
  have eP : oPre = 1200 := rfl
  have pwl := pw_le hk'
  have pwp := pw_le_pre X
  have wP := X.wP
  have alP := X.alP
  have fbt := fb_toNat h.sp1
  have fal := fb_al h
  unfold frameBytes at fbt
  have pw1 : 1 ≤ Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
    unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega
  obtain ⟨N, hN⟩ : ∃ N, Spec.Rsa.precomputedWords (s.gpr .a3).toNat = N := ⟨_, rfl⟩
  rw [hN] at pwl pwp pw1
  have hpre : preR s ∈ s.rd := by rw [h.hrd]; simp
  let Inv : Nat → State → Prop := fun i u =>
    Mid s u ∧ crtOutM s u ∧ u.gpr .a0 = stackArg s 12 + BitVec.ofNat 64 (8 * i) ∧
      u.gpr .a1 = fb s + BitVec.ofNat 64 (oPre + 8 * i) ∧
      ∀ j < i, u.mem.readW (fb s + BitVec.ofNat 64 (oPre + 8 * j)) 64 =
        s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * j)) 64
  refine WP.mono (Proof.Bignum.RISCV64.wp_countdown (N := N) (by omega) (by omega) Inv
    (fun i hi u ⟨M, C, j0, j1, jw⟩ _ => ?_)
    ⟨A.toMid, A.crt, by rw [A.a0, Nat.mul_zero, BitVec.add_zero], by rw [A.a1, Nat.mul_zero, Nat.add_zero],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩ (by rw [A.a2, hN])) fun u ⟨M, C, _, _, jw⟩ => ?_
  · have hld : InRegions (u.rd ++ u.wr) (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 8 :=
      ⟨preR s, List.mem_append_left _ (by rw [M.rd]; exact hpre),
        Offset.contains_base (stackArg s 12) (d := 8 * i) (n := 8) (k := (stackArg s 13).toNat * 8)
          (by omega) (by omega)⟩
    have hla : (stackArg s 12 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hst : InRegions u.wr (fb s + BitVec.ofNat 64 (oPre + 8 * i)) 8 := by
      rw [M.wr]; exact in_fr s _ (by unfold frameBytes; omega)
    have hsa : (fb s + BitVec.ofNat 64 (oPre + 8 * i)).toNat % 8 = 0 := fb_al8 h (by omega)
    have hv : u.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64 =
        s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64 :=
      M.mem.readW (Offset.contains_base (stackArg s 12) (d := 8 * i) (n := 8) (k := (stackArg s 13).toNat * 8)
          (by omega) (by omega)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact X.kP.symm
        · exact X.sP.symm) (by decide)
    refine WP.mono (WP.rdwr (WP.keep [.t1, .a0, .a1, .a2] (Q := fun u' =>
      u'.gpr .a0 = stackArg s 12 + BitVec.ofNat 64 (8 * (i + 1)) ∧
        u'.gpr .a1 = fb s + BitVec.ofNat 64 (oPre + 8 * (i + 1)) ∧
        u'.gpr .a2 = u.gpr .a2 - BitVec.ofNat 64 1 ∧
        u'.mem = u.mem.writeW (fb s + BitVec.ofNat 64 (oPre + 8 * i))
          (s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64)) ?_ (by rfl) (by rfl)))
      fun u' ⟨⟨⟨a0, a1, a2, am⟩, k⟩, krd, kwr, ksp⟩ => ⟨⟨?_, ?_, a0, a1, fun j hj => ?_⟩, a2⟩
    · brun [j0, j1, Proof.Bignum.RISCV64.add_ofNat_zero, hld, hla, hv, hst, hsa]
      exact ⟨by rw [Mont.off, show 8 * i + 8 = 8 * (i + 1) by omega],
        by rw [Mont.off, show oPre + 8 * i + 8 = oPre + 8 * (i + 1) by omega]⟩
    · exact M.store (d := oPre + 8 * i) (.inl (by unfold oRa; omega)) (by unfold frameBytes; omega)
        _ (fun r hr => k.gpr (by revert r; decide)) ksp krd kwr am
    · exact crtOutM_store h C (by unfold oM; omega) (by unfold frameBytes; omega) _ am
    · rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), jw j hj]
      · exact Mem.readW_writeW_self64 _ _ _
  · refine ⟨M, C, ?_⟩
    show Spec.Rsa.wordsAt _ _ _ = (if true = true then _ else _)
    simp only [↓reduceIte, Spec.Rsa.wordsAt, hN]
    refine List.map_congr_left fun j hj => ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact jw j (List.mem_range.mp hj)

theorem step_true (s : State) (h : PreP true s) (X : PreX s) : StepOk true s := fun _ _ _ M C hc =>
  WP.seq (WP.seq (WP.mono (preArgsP_ok h X M C) fun _ A => WP.mono (preCopy_ok h X A) hc))

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
      Spec.Rsa.precomputedWords]; omega
  · cases h

theorem preValOk_of {s : State} (X : PreX s) (hp : PreHyp s) : PreValOk true s := fun ws hw => by
  have hl : ws.length = Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
    rw [publicPrecompute_length hw, Proof.Rsa.bytesAt_length']
  have hpre := hp
  simp only [PreHyp, Spec.Rsa.privatePrecompute] at hpre
  split at hpre
  · rw [hw, Option.map_some, Option.some.injEq] at hpre
    show (if true = true then _ else _) = ws
    simp only [↓reduceIte]
    rw [wordsAt_take _ _ (pw_le_pre X), ← hpre, List.append_assoc, List.take_left' hl]
  · cases hpre

/-! ## The primes' values: `vg_rsa_private_crt_precomputed` -/

/-- `crtPtr` up to `argBase`, and after it. -/
abbrev ptr1 : List Instr := [.addSp .t0 0, .store .d .s1 .t0 oS1]
abbrev ptr2 : List Instr :=
  [.load .d .s1 .t6 96, .addi .t1 .s3 7, .shift .srl .d .t1 .t1 3, .shift .sll .d .t1 .t1 4, .add .s1 .s1 .t1]

theorem crtPtr_eq : crtPtr = ptr1 ++ (argBase ++ ptr2) := by simp only [crtPtr, List.append_assoc]

theorem ptrLen_val {x : BitVec 64} (hk : x.toNat ≤ 1024) :
    (x + BitVec.ofNat 64 7) >>> 3 <<< 4 = BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
  omega

/-- `crtPtr`: `out` into the frame, and `s1 :=` the primes' values in `pre`,
after `n`'s. -/
theorem crtPtr_ok {s t : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t) :
    WP isa (.block crtPtr) t fun u =>
      (u.gpr .s1 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧
        u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0) ∧ u.sp = t.sp) ∧
      Keep [.t0, .s1, .t6, .t1] t u := by
  have hk := h.k2
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 168) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide)
  have hal : (fb s + BitVec.ofNat 64 168).toNat % 8 = 0 := fb_al8 h (by decide)
  rw [crtPtr_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (WP.keep [.t0] (Q := fun w => w.gpr .t0 = fb s ∧
      w.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0))
    (by brun [ptr1, exec_addSp, A.sp, BitVec.add_zero, ho, hal, oS1, A.s1]) (by rfl) (by rfl)))
    fun w ⟨⟨⟨_, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans A.sp) fun x x6 kx xm xsp => ?_
  have hmw : Frame [kR s, sR s] s.mem x.mem := by
    rw [xm, wm]
    exact (A.mem.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).writeW
      (List.mem_cons_self ..) _ (frame_contains s (by decide))
  have hrd : x.rd = s.rd := kx.2.1.trans (wrd.trans A.rd)
  have i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 96) 8 := arg_inP h hrd (j := 12) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 96).toNat % 8 = 0 := stackArgAddr_alP h X 12 (by decide)
  have r0 : x.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = stackArg s 12 := arg_read2P h hmw (j := 12) (by decide)
  have h3 : x.gpr .s3 = s.gpr .a3 := (kx.gpr (by decide)).trans ((kw.gpr (by decide)).trans A.s3)
  refine WP.mono (WP.rdwr (WP.keep [.s1, .t1] (Q := fun u => u.gpr .s1 =
      stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧ u.mem = x.mem)
    (by brun [ptr2, x6, i0, l0, r0, h3, ptrLen_val hk]) (by rfl) (by rfl)))
    fun u ⟨⟨⟨u1, um⟩, ku⟩, _, _, usp⟩ => ⟨⟨u1, by rw [um, xm, wm], usp.trans (xsp.trans wsp)⟩, ?_⟩
  exact ((kw.trans kx).trans ku).mono (by decide)

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
    Spec.Rsa.wordsAt m (stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat))
        (Spec.Rsa.primeWords (stackArg s 1).toNat + Spec.Rsa.primeWords (stackArg s 3).toNat) =
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) ++
        Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) := by
  have hpre := X.hyp
  simp only [PreHyp, Spec.Rsa.privatePrecompute] at hpre
  split at hpre
  · cases hw : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) with
    | none => rw [hw] at hpre; cases hpre
    | some ws =>
      rw [hw, Option.map_some, Option.some.injEq] at hpre
      have hl : ws.length = Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
        rw [publicPrecompute_length hw, Proof.Rsa.bytesAt_length']
      have hL : (stackArg s 13).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat +
          (Spec.Rsa.primeWords (stackArg s 1).toNat + Spec.Rsa.primeWords (stackArg s 3).toNat) := by
        rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega
      rw [wordsAt_off, ← hL, hm, ← hpre, List.append_assoc, ← hl, List.drop_left]
  · cases hpre

/-- `p q = n`, from the precomputed values' hypothesis. -/
theorem pq_of_hyp {s : State} (X : PreX s) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) *
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) := by
  have hpre := X.hyp
  simp only [PreHyp, Spec.Rsa.privatePrecompute] at hpre
  split at hpre
  · assumption
  · cases hpre

/-- The primes' values in `pre`, after `n`'s. -/
abbrev r2Rs (s : State) : Region :=
  ⟨stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat),
    8 * (Proof.Bignum.RISCV64.Crt.wordsOf (stackArg s 1).toNat +
      Proof.Bignum.RISCV64.Crt.wordsOf (stackArg s 3).toNat)⟩

theorem r2Rs_len {s : State} (X : PreX s) :
    8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat + 8 * (Proof.Bignum.RISCV64.Crt.wordsOf (stackArg s 1).toNat +
      Proof.Bignum.RISCV64.Crt.wordsOf (stackArg s 3).toNat) = (stackArg s 13).toNat * 8 := by
  rw [X.pl, ← Proof.Bignum.RISCV64.Crt.primeWords_eq, ← Proof.Bignum.RISCV64.Crt.primeWords_eq]
  unfold Spec.Rsa.privatePrecomputedWords; omega

theorem r2Rs_sub {s : State} (X : PreX s) : Region.Sub (r2Rs s) (preR s) :=
  Offset.sub_base _ (by have := r2Rs_len X; omega)

/-- `vg_rsa_private_crt_precomputed`'s precondition at the call, after
`crtPtr`. -/
theorem crt_preP {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t) (k : Keep [.t0, .s1, .t6, .t1] t u)
    (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0)) (hsp : u.sp = t.sp)
    (h1 : u.gpr .s1 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat)) :
    Proof.Bignum.RISCV64.Crt.fnContractP.pre (crtEntryG s u [r2Rs s]) := by
  have hk := h.k2
  have hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i) := fun i hi => by
    rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oS1; omega)) (by omega) (by unfold oS1; omega))
      (by decide)]
    exact A.psa i hi
  have kk : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], u.gpr r = t.gpr r := fun r hr =>
    k.gpr (by revert r; decide)
  have hc := crt_preG (X := [r2Rs s]) h A kk hpsa hsp
  have g : ∀ r, r ∉ linkRegs → r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] →
      (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun r h1 h2 => (State.callEntry_gpr u h1).trans (kk r h2)
  have e1 : (crtEntryG s u [r2Rs s]).gpr .s1 = stackArg s 12 +
      BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat) :=
    (State.callEntry_gpr u (by decide)).trans h1
  have sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := [r2Rs s]) (i := i) hi
  have hr : Proof.Bignum.RISCV64.Crt.r2R (crtEntryG s u [r2Rs s]) = r2Rs s := by
    simp only [Proof.Bignum.RISCV64.Crt.r2R, e1, g .a7 (by decide) (by decide), A.a7, sa 1 (by decide)]
  have sub := r2Rs_sub X
  have mk := mR_sub h
  have wP := X.wP
  have hl := r2Rs_len X
  have alP := X.alP
  have hfu : Frame [kR s] s.mem u.mem := by
    rw [hm]
    exact A.mem.writeW (List.mem_singleton_self _) _ (frame_contains s (by unfold oS1 frameBytes; omega))
  have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
    bytes_of_frame (s := s) (rs := [kR s]) hfu (p := p) (len := len)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
  refine ⟨hr ▸ hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    simp only [g .a0 (by decide) (by decide), g .a1 (by decide) (by decide), A.a0, A.a1]
    exact (X.kP.sub_left mk).sub_right sub
  · rw [hr, sa 8 (by decide), sa 9 (by decide)]
    exact (X.sP.sub_right sub).symm
  · rw [hr, e1]
    simp only
    rw [Offset.toNat_add_ofNat] <;> omega
  · rw [e1, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have hw : Spec.Rsa.wordsAt u.mem (stackArg s 12) (stackArg s 13).toNat =
        Spec.Rsa.wordsAt s.mem (stackArg s 12) (stackArg s 13).toNat :=
      words_of_frame hfu (fun r hr => by
        rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by omega)
    simp only [State.withRegions_mem, State.callEntry_mem, e1, g .a6 (by decide) (by decide),
      g .a7 (by decide) (by decide), A.a6, A.a7, sa 0 (by decide), sa 1 (by decide), Nat.reduceAdd,
      ← Proof.Bignum.RISCV64.Crt.primeWords_eq]
    rw [hb h.kp.symm (by have := h.wp; omega), hb h.kq.symm (by have := h.wq; omega)]
    exact primes_of_hyp X hw
  · simp only [State.withRegions_mem, State.callEntry_mem, g .a2 (by decide) (by decide),
      g .a3 (by decide) (by decide), g .a6 (by decide) (by decide), g .a7 (by decide) (by decide), A.a2, A.a3,
      A.a6, A.a7, sa 0 (by decide), sa 1 (by decide)]
    rw [hb h.kp.symm (by have := h.wp; omega), hb h.kq.symm (by have := h.wq; omega),
      hb h.kn.symm (by have := h.wn; omega)]
    exact pq_of_hyp X

theorem crtP_noFrames : Impl.Bignum.RISCV64.Crt.crtP.noFrames = true := by decide +kernel

/-- The slot of `out` is apart from what the call writes. -/
theorem s1_apart {s : State} (h : PreP true s) {r : Region} (hr : r ∈ crtWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 oS1, 8⟩ r := by
  have hk := h.k2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by unfold oM; omega)
  · exact h.ks.sub_left (frame_sub s (by decide))

/-- The regions of the call of `vg_rsa_private_crt_precomputed`. -/
theorem coversP {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t)
    (k : Keep [.t0, .s1, .t6, .t1] t u) :
    Covers (crtRd s ++ [r2Rs s] ++ crtWr s) (u.rd ++ u.wr) ∧ Covers (crtWr s) u.wr := by
  obtain ⟨hc0, hw0⟩ := crt_covers h A
  refine ⟨?_, by rw [k.2.2]; exact hw0⟩
  rw [k.2.1, k.2.2]
  refine Covers.append_left (Covers.append_left (fun a n ⟨r, hr, c⟩ => hc0 a n ⟨r, List.mem_append_left _ hr, c⟩)
    (Covers.left (Covers.of_sub fun r hr => ?_))) (Covers.right hw0)
  rw [List.mem_singleton.mp hr]
  refine ⟨preR s, by rw [A.rd, h.hrd]; simp [rdL], 8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat, rfl, ?_⟩
  have := r2Rs_len X
  simp only
  omega

/-- After `vg_rsa_private_crt_precomputed`, called from the state `u` after
`crtPtr`, from the state `t` at the call of the CRT. -/
def AfterP (s v : State) : Prop :=
  ∃ t u, AtCrt s t ∧ Keep [.t0, .s1, .t6, .t1] t u ∧
    u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0) ∧
    u.sp = t.sp ∧ v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧ Frame (crtWr s) u.mem v.mem ∧
    (∀ r ∈ preserved, v.gpr r = u.gpr r) ∧
    Proof.Bignum.RISCV64.Crt.fnContractP.post (crtEntryG s u [r2Rs s])
      (v.withRegions (crtRd s ++ [r2Rs s]) (crtWr s))

theorem callP_ok {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t)
    (k : Keep [.t0, .s1, .t6, .t1] t u)
    (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0)) (hsp : u.sp = t.sp)
    (h1 : u.gpr .s1 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat)) :
    WP isa crtCallP u (AfterP s) := by
  obtain ⟨hc, hw⟩ := coversP h X A k
  unfold crtCallP
  exact WP.call (k := Proof.Bignum.RISCV64.Crt.fnContractP) Proof.Bignum.RISCV64.Crt.fn_correctP
    (crt_preP h X A k hm hsp h1) hc hw (fun v hrd hwr hsp' hf hpres _ hpost =>
      ⟨t, u, A, k, hm, hsp, hrd, hwr, hsp', hf, hpres, hpost⟩) crtP_noFrames

/-- `out` back into `s1`, after `vg_rsa_private_crt_precomputed`: what
`vg_rsa_private_crt` gives. -/
theorem restoreP_ok {s v : State} (h : PreP true s) (hv : AfterP s v) :
    WP isa (.block crtRestore) v fun w => Mid s w ∧ crtOut s w := by
  obtain ⟨t, u, A, k, hm, hsp, hrd, hwr, hsp', hf, hp, hpost⟩ := hv
  have hk := h.k2
  have mk := mR_sub h
  have hfu : Frame [kR s] s.mem u.mem := by
    rw [hm]
    exact A.mem.writeW (List.mem_singleton_self _) _ (frame_contains s (by unfold oS1 frameBytes; omega))
  have s1v : v.mem.readW (fb s + BitVec.ofNat 64 168) 64 = s.gpr .a0 := by
    rw [hf.readW (Region.contains_self _ _) (fun r hr => s1_apart h hr) (by decide), hm]
    exact Mem.readW_writeW_self64 _ _ _
  have i1 : InRegions (v.rd ++ v.wr) (fb s + BitVec.ofNat 64 168) 8 := by
    rw [hrd, hwr, k.2.1, k.2.2, A.wr]
    exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), frame_contains s (by decide)⟩
  have l1 : (fb s + BitVec.ofNat 64 168).toNat % 8 = 0 := fb_al8 h (by decide)
  have vsp : v.sp = fb s := hsp'.trans (hsp.trans A.sp)
  refine WP.mono (WP.rdwr (WP.keep [.t0, .s1] (Q := fun w => w.gpr .s1 = s.gpr .a0 ∧ w.mem = v.mem)
    (by brun [crtRestore, exec_addSp, vsp, BitVec.add_zero, i1, l1, s1v, oS1]) (by rfl) (by rfl)))
    fun w ⟨⟨⟨w1, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ⟨?_, ?_⟩
  · have g : ∀ r, r ∉ [Reg.t0, .s1] → r ∉ [Reg.t0, .s1, .t6, .t1] → r ∈ preserved → w.gpr r = t.gpr r :=
      fun r h1 h1' h2 => by rw [kw.gpr h1, hp r h2, k.gpr h1']
    refine ⟨wsp.trans vsp, by rw [wrd, hrd, k.2.1, A.rd], by rw [wwr, hwr, k.2.2, A.wr], w1,
      (g _ (by decide) (by decide) (by decide)).trans A.s2, (g _ (by decide) (by decide) (by decide)).trans A.s3,
      (g _ (by decide) (by decide) (by decide)).trans A.s4, (g _ (by decide) (by decide) (by decide)).trans A.s5,
      (g _ (by decide) (by decide) (by decide)).trans A.s6,
      fun r hr => (g r (by revert r; decide) (by revert r; decide) (by revert r; decide)).trans (A.hi r hr), ?_, ?_⟩
    · rw [wm]
      refine (hfu.mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
      · simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., mk⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · rw [wm]
      refine (A.sv.frame (rs := [⟨fb s + BitVec.ofNat 64 oS1, 8⟩]) (by
          rw [hm]; exact Frame.writeW (Frame.refl _ t.mem) (List.mem_singleton_self _) _ (Region.contains_self _ _))
        fun p hp' r hr => ?_).frame hf fun p hp' r hr => below_apart h (by
          have := saved_offs p hp'; unfold oSave oM at *; omega) hr
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp'
      exact Offset.disjoint _ (.inl (by unfold oSave oS1 at *; omega)) (by unfold oSave at *; omega)
        (by decide)
  · have g : ∀ r, r ∉ linkRegs → r ∈ [Reg.a0, .a2, .a3, .a4, .a6, .a7] →
        (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun r h1 h2 =>
      (State.callEntry_gpr u h1).trans (k.gpr (by clear h1; revert h2; revert r; decide))
    have hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i) := fun i hi => by
      rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oS1; omega)) (by omega) (by unfold oS1; omega))
        (by decide)]
      exact A.psa i hi
    have sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := [r2Rs s]) (i := i) hi
    simp only [Proof.Bignum.RISCV64.Crt.fnContractP, Proof.Bignum.RISCV64.Crt.postCore,
      g .a0 (by decide) (by decide), g .a2 (by decide) (by decide), g .a3 (by decide) (by decide),
      g .a4 (by decide) (by decide), g .a6 (by decide) (by decide), g .a7 (by decide) (by decide),
      A.a0, A.a2, A.a3, A.a4, A.a6, A.a7,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) hfu (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega), hb (iR_eq h ▸ h.ki.symm) (by have := h.k2; omega),
      hb h.kp.symm (by have := h.wp; omega), hb h.kq.symm (by have := h.wq; omega),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega), hb (h.h7' ▸ h.kdq.symm) (by have := h.wdq; omega),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega)] at hpost
    show Spec.Rsa.written w.mem _ _ ((w.gpr .a0).setWidth 32) _
    rw [wm, kw.gpr (by decide)]
    exact hpost

/-- With the key's precomputed values: `vg_rsa_private_crt_precomputed`, given
the primes' values in `s1`, `out` kept in the frame. -/
theorem crt_true (s : State) (h : PreP true s) (X : PreX s) : CrtOk true s := fun t Q A hQ => by
  unfold crtStep
  refine WP.seq (WP.mono (crtPtr_ok h X A) fun u ⟨⟨h1, hm, hsp⟩, k⟩ => ?_)
  exact WP.seq (WP.mono (callP_ok h X A k hm hsp h1) fun v hv =>
    WP.mono (restoreP_ok h hv) fun w ⟨M, C⟩ => hQ w M C)

theorem codeP_correct (s : State)
    (hpre : (Proof.Rsa.privateCheckedPrecomputedContract RISCV64.abi frameBytes).pre s) :
    ∃ tr t, Exec isa codeP s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  obtain ⟨h, X⟩ := preP_ofP hpre
  exact WP.mono (codeG_correct s h (crt_true s h X) (step_true s h X)) fun t ⟨ha, hf⟩ =>
    ⟨ha, hf (preValOk_of X X.hyp)⟩

end VG.Proof.Rsa.RISCV64.Priv
