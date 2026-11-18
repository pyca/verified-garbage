module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivTaint
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCT
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCT
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPubCall
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivResult
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivFinal

/-! ### `Rsa.RISCV64.PrivPreCopy`, which this module and modules that import it used -/

section

/-! ### `Rsa.RISCV64.PrivCorrect`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on RISC-V: correctness

The restores (`restore_ok`), then the blocks and calls in order
(`codeG_correct`, for `code` `code_correct`), from the frame's `alloc` to its `free`, to the outcome
(`final_ok`), on the registers and the stack (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

variable {pc : Bool}

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

theorem Late.keep {s t u : State} (L : Late s t) {rs : List Reg} (k : Keep rs t u) (hsp : u.sp = t.sp)
    (hm : u.mem = t.mem) (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : Late s u :=
  ⟨hsp.trans L.sp, k.2.1.trans L.rd, k.2.2.trans L.wr, (k.gpr (hrs _ (by decide))).trans L.s1,
    (k.gpr (hrs _ (by decide))).trans L.s2, (k.gpr (hrs _ (by decide))).trans L.s3,
    (k.gpr (hrs _ (by decide))).trans L.s4, (k.gpr (hrs _ (by decide))).trans L.s5,
    (k.gpr (hrs _ (by decide))).trans L.s6,
    fun r hr => (k.gpr (hrs r (by revert r; decide))).trans (L.hi r hr), hm ▸ L.mem, hm ▸ L.sv⟩

/-- The frame's words are apart from `out` and `m`. -/
theorem slot_apart {s : State} (h : PreP pc s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ [oR s, mR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ko.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_using [hd]))
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega_using [hd]) (by have := h.k2; unfold oM; omega_using [this])

theorem Late.release {s t u : State} (h : PreP pc s) (L : Late s t) (k : Keep [.a1, .a2, .t2, .t3, .t5] t u)
    (hsp : u.sp = t.sp) (hf : Frame [oR s, mR s] t.mem u.mem) : Late s u := by
  refine ⟨hsp.trans L.sp, k.2.1.trans L.rd, k.2.2.trans L.wr, (k.gpr (by decide)).trans L.s1,
    (k.gpr (by decide)).trans L.s2, (k.gpr (by decide)).trans L.s3, (k.gpr (by decide)).trans L.s4,
    (k.gpr (by decide)).trans L.s5, (k.gpr (by decide)).trans L.s6,
    fun r hr => (k.gpr (by revert r; decide)).trans (L.hi r hr), L.mem.trans (hf.sub fun r hr => ?_),
    L.sv.frame hf fun p hp r hr => slot_apart h (by have := saved_offs p hp; unfold oSave oM at *; omega_using [this]) hr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., mR_sub h⟩

/-- The restores. -/
theorem restore_ok {s w : State} (h : PreP pc s) (L : Late s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.gpr .ra = s.gpr .ra ∧ v.sp = fb s ∧ v.mem = w.mem ∧
        v.gpr .a0 = w.gpr .a0 := by
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide),
    WP.block_nil ?_⟩)
  refine WP.mono (Spill.restore_wp (b := .t0) (B := fb s) (by have := fb_al h; omega_using [this])
    (by rw [gpr_write_self, L.sp]; exact BitVec.add_zero _) restored_offs restorable (fun p hp => by
      have := saved_offs p (restored_saved p hp)
      show InRegions (w.rd ++ w.wr) _ 8
      rw [L.wr]
      exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..),
        frame_contains s (by unfold oSave frameBytes at *; omega_using [this])⟩)
    (L.sv.sub restored_saved)) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rcases preserved_split hr with hs | hs
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      exact R.gpr p ((by decide : ∀ p ∈ saved, p ∈ restored) p hp)
    · have : r ∉ restored.map Prod.fst := by revert r; decide
      rw [R.other r this, gpr_write_of_ne _ _ (by revert r; decide)]
      exact L.hi r hs
  · exact R.gpr (.ra, oRa) (by decide)
  · rw [R.sp]; exact L.sp
  · rw [R.mem]; rfl
  · rw [R.other _ (by decide), gpr_write_of_ne _ _ (by decide)]

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .a0) (s.gpr .a3).toNat ((s'.gpr .a0).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- The CRT's result in the frame, from the state after the setup. -/
def CrtOk (pc : Bool) (s : State) : Prop :=
  ∀ t (Q : State → Prop), AtCrt s t → (∀ u, Mid s u → crtOut s u → Q u) → WP isa (crtStep pc) t Q

/-- `n`'s values put in the frame, from the state after `vg_rsa_private_crt`. -/
def StepOk (pc : Bool) (s : State) : Prop :=
  ∀ t (c : Prog isa) (Q : State → Prop), Mid s t → crtOut s t → (∀ u, AtPub pc s u → WP isa c u Q) →
    WP isa (.seq (preStep pc) c) t Q

/-- `n`'s values in the frame are its precomputed values, if they are valid. -/
abbrev PreValOk (pc : Bool) (s : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = some ws →
    preVal pc s = ws

/-- `writtenOutcome` reads the memory only in the output. -/
theorem writtenOutcome_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

theorem codeG_correct (s : State) (h : PreP pc s) (hcrt : CrtOk pc s) (hstep : StepOk pc s) :
    WP isa (.frame (.alloc frameBytes) (bodyG pc) (.free frameBytes)) s fun t =>
      abiPreserved s t ∧ (PreValOk pc s → fnPost s t) := by
  have hk := h.k2
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ h.sp1 ?_
  unfold bodyG
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (hcrt t₁ _ A fun t₂ M C => ?_)
  refine hstep t₂ _ _ M C fun t₄ Q4 => ?_
  refine WP.seq (WP.mono (pubArgs_ok h Q4) fun t₅ R => ?_)
  refine WP.seq (pubCall_ok h R fun t₆ C6 => ?_)
  refine WP.seq (WP.mono (cmpArgs_ok h C6) fun t₇ L => ?_)
  refine WP.seq (WP.mono (WP.rdwr (compare_ok h L)) fun t₈ ⟨⟨a8, m8, k8⟩, _, _, sp8⟩ => ?_)
  have L8 : Late s t₈ := L.toLate.keep k8 sp8 m8
  have iSt : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 152) 8 := by
    rw [L8.wr]; exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), frame_contains s (by decide)⟩
  have iEs : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 160) 8 := by
    rw [L8.wr]; exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), frame_contains s (by decide)⟩
  refine WP.seq (WP.mono (WP.rdwr (result_ok (cs := t₇.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)
    (es := t₇.mem.readW (fb s + BitVec.ofNat 64 oEs) 64) h L8.sp iSt iEs (by rw [m8]) (by rw [m8]) a8
    (cmpAcc_lt _ _ _ _) L8.s1 L8.s3))
    fun t₉ ⟨⟨⟨r0, r3, r5, r2, r3', m9⟩, k9⟩, _, _, sp9⟩ => ?_)
  have L9 : Late s t₉ := L8.keep k9 sp9 m9
  refine WP.seq (WP.mono (WP.rdwr (release_ok h L9 (fun b => Proof.Rsa.low_and_mask b _ _) r5 r2 r3' r3))
    fun t₁₀ ⟨⟨hout, f10, k10⟩, _, _, sp10⟩ => ?_)
  have L10 := L9.release h k10 sp10 f10
  refine WP.mono (restore_ok h L10) fun v ⟨vp, vra, vs, vm, v0⟩ mL _ fl => ?_
  refine ⟨⟨fun r hr => vp r hr, ?_, vra⟩, fun hv => ?_⟩
  · show v.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [vs]; exact BitVec.sub_add_cancel _ _
  · -- The `free` loses the frame's bytes, which lie apart from the output.
    have hb : Spec.Rsa.bytesAt mL (s.gpr .a0) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt v.mem (s.gpr .a0) (s.gpr .a3).toNat :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := outR s) (by rw [outR_eq h]; exact h.ko.symm) (List.mem_range.mp hi)
    refine writtenOutcome_congr hb ?_
    show Spec.Rsa.writtenOutcome v.mem (s.gpr .a0) (s.gpr .a3).toNat ((v.gpr .a0).setWidth 32) _
    rw [vm, v0, k10.gpr (by decide), r0]
    have m97 : t₉.mem = t₇.mem := m9.trans m8
    rw [m97] at hout
    have hx : Spec.Rsa.bytesAt t₇.mem (s.gpr .a6) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat :=
      bytes_of_frame L.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [iR_eq h]
        rcases hr with rfl | rfl | rfl
        · exact h.ki.symm
        · exact h.oi.symm
        · exact h.is) (by have := h.wi; rw [h.h7] at this; omega_using [])
    refine final_ok (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) L.crt (fun ws hw => L.pub ws hw (hv ws hw)) ?_ hout
    rw [cmpAcc_eq_zero, ← hx, Proof.Rsa.bytesAt_eq_iff]

theorem step_false (s : State) (h : PreP false s) : StepOk false s := fun _ _ _ M C hc =>
  WP.seq (WP.seq (WP.mono (preArgs_ok h M C) fun _ P => preCall_ok h P hc))

theorem code_correct (s : State) (hpre : (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  have h := preP_of hpre
  exact WP.mono (codeG_correct s h (fun _ _ A hQ => crtCall_ok h A hQ) (step_false s h)) fun t ⟨ha, hf⟩ =>
    ⟨ha, hf fun ws hw => by simp only [preVal, Bool.false_eq_true, ↓reduceIte, hw, Option.getD_some]⟩

end VG.Proof.Rsa.RISCV64.Priv

end

end

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
  sig_split h
  rename_i sp16 sp1 sp2 hrd hwr on oe oi op oq odp odq oqi os oP oa ns es is ps qs dps dqs qis sP sa ko kn ke ki
    kp kq kdp kdq kqi ks kP ka wo wn we wi wp wq wdp wdq wqi ws wP h_k1_k2 h1 h7 e1 e2 p1 p2 q1 q2 h5 h9 h7' hs
    hpl hk al
  have alP := h
  obtain ⟨k1, k2⟩ := h_k1_k2
  exact ⟨⟨sp16, sp1, by omega_using [sp2], hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs,
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
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by simp only [↓reduceIte]; omega_using [hj]) (by omega_using [hj])

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
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

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
  obtain ho : InRegions t.wr (fb s + BitVec.ofNat 64 152) 8 := by
    rw [M.wr]; exact in_fr s _ (by decide)
  obtain hal : (fb s + BitVec.ofNat 64 152).toNat % 8 = 0 := fb_al8 h (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [preP1, exec_addSp, M.sp, BitVec.add_zero, ho, hal, oSt]

theorem preP2_ok {s x : State} (h : PreP true s) (X : PreX s) (hrd : x.rd = s.rd)
    (hm : Frame [kR s, sR s] s.mem x.mem) (h6 : x.gpr .t6 = s.sp) (h0 : x.gpr .t0 = fb s)
    (h3 : x.gpr .s3 = s.gpr .a3) :
    WP isa (.block preP2) x fun u =>
      (u.gpr .a0 = stackArg s 12 ∧ u.gpr .a1 = fb s + BitVec.ofNat 64 oPre ∧
        u.gpr .a2 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧ u.mem = x.mem) ∧
      Keep [.a0, .a1, .a2] x u := by
  obtain i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 96) 8 := arg_inP h hrd (j := 12) (by decide)
  obtain l0 : (s.sp + BitVec.ofNat 64 96).toNat % 8 = 0 := stackArgAddr_alP h X 12 (by decide)
  obtain r0 : x.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = stackArg s 12 := arg_read2P h hm (j := 12) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [preP2, h6, i0, l0, r0, h0, h3, oPre, preLen, preLen_val h.k2]

theorem preArgsP_ok {s t : State} (h : PreP true s) (X : PreX s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgsP) t (AtCopy s) := by
  have hk := h.k2
  rw [preArgsP_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (preP1_ok h M)) fun w ⟨⟨⟨w0, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans M.sp) fun x x6 kx xm xsp => ?_
  obtain hmw : Frame [kR s, sR s] s.mem x.mem := by
    rw [xm, wm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s (by decide))
  refine WP.mono (WP.rdwr (preP2_ok h X (kx.2.1.trans (wrd.trans M.rd)) hmw x6
    ((kx.gpr (by decide)).trans w0) ((kx.gpr (by decide)).trans ((kw.gpr (by decide)).trans M.s3))))
    fun u ⟨⟨⟨u0, u1, u2, um⟩, ku⟩, urd, uwr, usp⟩ => ?_
  obtain hum : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0) := by rw [um, xm, wm]
  refine ⟨M.store (d := oSt) (.inl (by decide)) (by decide) _ (fun r hr => ?_) (usp.trans (xsp.trans wsp))
    (urd.trans (kx.2.1.trans wrd)) (uwr.trans (kx.2.2.trans wwr)) hum, ?_, u0, u1, u2⟩
  · rw [ku.gpr (by revert r; decide), kx.gpr (by revert r; decide), kw.gpr (by revert r; decide)]
  · have hb : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      rw [hum]
      exact Frame.bytes (R := mR s) (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
        (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega_using [hk]) (by decide))
        (show (s.gpr .a3).toNat ≤ 2 ^ 64 by omega_using []) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [hum, Mem.readW_writeW_self64, ← hum]
    exact written_congr hb C

theorem pw_le_pre {s : State} (X : PreX s) :
    Spec.Rsa.precomputedWords (s.gpr .a3).toNat ≤ (stackArg s 13).toNat := by
  rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []

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
  obtain fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem m := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hb : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat :=
    bytes_of_frame (s := t) fw (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by unfold oM at *; omega_using [hd, hk])) (by unfold oM; omega_using [hk])
        (by unfold frameBytes at hd'; omega_using [hd'])) (by omega_using [])
  rw [fw.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSt oM at *; omega_using [hd])) (by decide)
      (by unfold frameBytes at hd'; omega_using [hd'])) (by decide)]
  exact written_congr hb C

/-- The copy: `n`'s values, `pre`'s first words, in the frame. -/
theorem preCopy_ok {s t : State} (h : PreP true s) (X : PreX s) (A : AtCopy s t) :
    WP isa preCopy t (AtPub true s) := by
  obtain hk := h.k1; have hk' := h.k2
  have eP : oPre = 1200 := rfl
  obtain pwl := pw_le hk'
  obtain pwp := pw_le_pre X
  have wP := X.wP
  have alP := X.alP
  obtain fbt := fb_toNat h.sp1
  obtain fal := fb_al h
  unfold frameBytes at fbt
  obtain pw1 : 1 ≤ Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
    unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega_using [hk]
  obtain ⟨N, hN⟩ : ∃ N, Spec.Rsa.precomputedWords (s.gpr .a3).toNat = N := ⟨_, rfl⟩
  rw [hN] at pwl pwp pw1
  obtain hpre : preR s ∈ s.rd := by rw [h.hrd]; simp
  let Inv : Nat → State → Prop := fun i u =>
    Mid s u ∧ crtOutM s u ∧ u.gpr .a0 = stackArg s 12 + BitVec.ofNat 64 (8 * i) ∧
      u.gpr .a1 = fb s + BitVec.ofNat 64 (oPre + 8 * i) ∧
      ∀ j < i, u.mem.readW (fb s + BitVec.ofNat 64 (oPre + 8 * j)) 64 =
        s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * j)) 64
  refine WP.mono (Proof.Bignum.RISCV64.wp_countdown (N := N) (by omega_using [pwp]) (by omega_using [pw1]) Inv
    (fun i hi u ⟨M, C, j0, j1, jw⟩ _ => ?_)
    ⟨A.toMid, A.crt, by rw [A.a0, Nat.mul_zero, BitVec.add_zero], by rw [A.a1, Nat.mul_zero, Nat.add_zero],
      fun _ h => absurd h (Nat.not_lt_zero _)⟩ (by rw [A.a2, hN])) fun u ⟨M, C, _, _, jw⟩ => ?_
  · have hld : InRegions (u.rd ++ u.wr) (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 8 :=
      ⟨preR s, List.mem_append_left _ (by rw [M.rd]; exact hpre),
        Offset.contains_base (stackArg s 12) (d := 8 * i) (n := 8) (k := (stackArg s 13).toNat * 8)
          (by omega_using [pwp, hi]) (by omega_using [pwl, hi])⟩
    obtain hla : (stackArg s 12 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [alP]
    obtain hst : InRegions u.wr (fb s + BitVec.ofNat 64 (oPre + 8 * i)) 8 := by
      rw [M.wr]; exact in_fr s _ (by unfold frameBytes; omega_using [eP, pwl, hi])
    obtain hsa : (fb s + BitVec.ofNat 64 (oPre + 8 * i)).toNat % 8 = 0 := fb_al8 h (by omega_using [eP])
    obtain hv : u.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64 =
        s.mem.readW (stackArg s 12 + BitVec.ofNat 64 (8 * i)) 64 :=
      M.mem.readW (Offset.contains_base (stackArg s 12) (d := 8 * i) (n := 8) (k := (stackArg s 13).toNat * 8)
          (by omega_using [pwp, hi]) (by omega_using [wP, pwp, hi])) (fun r hr => by
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
      exact ⟨by rw [Mont.off, show 8 * i + 8 = 8 * (i + 1) by omega_using []],
        by rw [Mont.off, show oPre + 8 * i + 8 = oPre + 8 * (i + 1) by omega_using []]⟩
    · exact M.store (d := oPre + 8 * i) (.inl (by unfold oRa; omega_using [eP])) (by unfold frameBytes; omega_using [eP, pwl, hi])
        _ (fun r hr => k.gpr (by revert r; decide)) ksp krd kwr am
    · exact crtOutM_store h C (by unfold oM; omega_using [eP]) (by unfold frameBytes; omega_using [eP, pwl, hi]) _ am
    · rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hj]) (by omega_arith) (by omega_arith)) (by decide), jw j hj]
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
      Spec.Rsa.precomputedWords]; omega_using []
  · cases h

theorem preValOk_of {s : State} (X : PreX s) (hp : PreHyp s) : PreValOk true s := fun ws hw => by
  obtain hl : ws.length = Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
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
  obtain ho : InRegions t.wr (fb s + BitVec.ofNat 64 168) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide)
  obtain hal : (fb s + BitVec.ofNat 64 168).toNat % 8 = 0 := fb_al8 h (by decide)
  rw [crtPtr_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (WP.keep [.t0] (Q := fun w => w.gpr .t0 = fb s ∧
      w.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0))
    (by brun [ptr1, exec_addSp, A.sp, BitVec.add_zero, ho, hal, oS1, A.s1]) (by rfl) (by rfl)))
    fun w ⟨⟨⟨_, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans A.sp) fun x x6 kx xm xsp => ?_
  obtain hmw : Frame [kR s, sR s] s.mem x.mem := by
    rw [xm, wm]
    exact (A.mem.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..).writeW
      (List.mem_cons_self ..) _ (frame_contains s (by decide))
  obtain hrd : x.rd = s.rd := kx.2.1.trans (wrd.trans A.rd)
  obtain i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 96) 8 := arg_inP h hrd (j := 12) (by decide)
  obtain l0 : (s.sp + BitVec.ofNat 64 96).toNat % 8 = 0 := stackArgAddr_alP h X 12 (by decide)
  obtain r0 : x.mem.readW (s.sp + BitVec.ofNat 64 96) 64 = stackArg s 12 := arg_read2P h hmw (j := 12) (by decide)
  obtain h3 : x.gpr .s3 = s.gpr .a3 := (kx.gpr (by decide)).trans ((kw.gpr (by decide)).trans A.s3)
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
      obtain hl : ws.length = Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
        rw [publicPrecompute_length hw, Proof.Rsa.bytesAt_length']
      obtain hL : (stackArg s 13).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat +
          (Spec.Rsa.primeWords (stackArg s 1).toNat + Spec.Rsa.primeWords (stackArg s 3).toNat) := by
        rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
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
  unfold Spec.Rsa.privatePrecomputedWords; omega_using []

theorem r2Rs_sub {s : State} (X : PreX s) : Region.Sub (r2Rs s) (preR s) :=
  Offset.sub_base _ (by have := r2Rs_len X; omega_using [this])

/-- `vg_rsa_private_crt_precomputed`'s precondition at the call, after
`crtPtr`. -/
theorem crt_preP {s t u : State} (h : PreP true s) (X : PreX s) (A : AtCrt s t) (k : Keep [.t0, .s1, .t6, .t1] t u)
    (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oS1) (s.gpr .a0)) (hsp : u.sp = t.sp)
    (h1 : u.gpr .s1 = stackArg s 12 + BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat)) :
    Proof.Bignum.RISCV64.Crt.fnContractP.pre (crtEntryG s u [r2Rs s]) := by
  have hk := h.k2
  obtain hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i) := fun i hi => by
    rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oS1; omega_using [hi])) (by omega_using [hi]) (by unfold oS1; omega_using []))
      (by decide)]
    exact A.psa i hi
  obtain kk : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], u.gpr r = t.gpr r := fun r hr =>
    k.gpr (by revert r; decide)
  obtain hc := crt_preG (X := [r2Rs s]) h A kk hpsa hsp
  obtain g : ∀ r, r ∉ linkRegs → r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] →
      (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun r h1 h2 => (State.callEntry_gpr u h1).trans (kk r h2)
  obtain e1 : (crtEntryG s u [r2Rs s]).gpr .s1 = stackArg s 12 +
      BitVec.ofNat 64 (8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat) :=
    (State.callEntry_gpr u (by decide)).trans h1
  obtain sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := [r2Rs s]) (i := i) hi
  obtain hr : Proof.Bignum.RISCV64.Crt.r2R (crtEntryG s u [r2Rs s]) = r2Rs s := by
    simp only [Proof.Bignum.RISCV64.Crt.r2R, e1, g .a7 (by decide) (by decide), A.a7, sa 1 (by decide)]
  obtain sub := r2Rs_sub X
  obtain mk := mR_sub h
  have wP := X.wP
  obtain hl := r2Rs_len X
  have alP := X.alP
  obtain hfu : Frame [kR s] s.mem u.mem := by
    rw [hm]
    exact A.mem.writeW (List.mem_singleton_self _) _ (frame_contains s (by unfold oS1 frameBytes; omega_using []))
  obtain hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
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
    rw [Offset.toNat_add_ofNat] <;> omega_using [wP, hl]
  · rw [e1, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [alP]
  · have hw : Spec.Rsa.wordsAt u.mem (stackArg s 12) (stackArg s 13).toNat =
        Spec.Rsa.wordsAt s.mem (stackArg s 12) (stackArg s 13).toNat :=
      words_of_frame hfu (fun r hr => by
        rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by omega_using [wP])
    simp only [State.withRegions_mem, State.callEntry_mem, e1, g .a6 (by decide) (by decide),
      g .a7 (by decide) (by decide), A.a6, A.a7, sa 0 (by decide), sa 1 (by decide), Nat.reduceAdd,
      ← Proof.Bignum.RISCV64.Crt.primeWords_eq]
    rw [hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using [])]
    exact primes_of_hyp X hw
  · simp only [State.withRegions_mem, State.callEntry_mem, g .a2 (by decide) (by decide),
      g .a3 (by decide) (by decide), g .a6 (by decide) (by decide), g .a7 (by decide) (by decide), A.a2, A.a3,
      A.a6, A.a7, sa 0 (by decide), sa 1 (by decide)]
    rw [hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using []),
      hb h.kn.symm (by have := h.wn; omega_using [])]
    exact pq_of_hyp X

theorem crtP_noFrames : Impl.Bignum.RISCV64.Crt.crtP.noFrames = true := by decide +kernel

/-- The slot of `out` is apart from what the call writes. -/
theorem s1_apart {s : State} (h : PreP true s) {r : Region} (hr : r ∈ crtWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 oS1, 8⟩ r := by
  have hk := h.k2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by unfold oM; omega_using [hk])
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
  omega_using [this]

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
  obtain mk := mR_sub h
  obtain hfu : Frame [kR s] s.mem u.mem := by
    rw [hm]
    exact A.mem.writeW (List.mem_singleton_self _) _ (frame_contains s (by unfold oS1 frameBytes; omega_using []))
  obtain s1v : v.mem.readW (fb s + BitVec.ofNat 64 168) 64 = s.gpr .a0 := by
    rw [hf.readW (Region.contains_self _ _) (fun r hr => s1_apart h hr) (by decide), hm]
    exact Mem.readW_writeW_self64 _ _ _
  obtain i1 : InRegions (v.rd ++ v.wr) (fb s + BitVec.ofNat 64 168) 8 := by
    rw [hrd, hwr, k.2.1, k.2.2, A.wr]
    exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), frame_contains s (by decide)⟩
  obtain l1 : (fb s + BitVec.ofNat 64 168).toNat % 8 = 0 := fb_al8 h (by decide)
  obtain vsp : v.sp = fb s := hsp'.trans (hsp.trans A.sp)
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
          have := saved_offs p hp'; unfold oSave oM at *; omega_using [this]) hr
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp'
      exact Offset.disjoint _ (.inl (by unfold oSave oS1 at *; omega_using [this])) (by unfold oSave at *; omega_using [this])
        (by decide)
  · have g : ∀ r, r ∉ linkRegs → r ∈ [Reg.a0, .a2, .a3, .a4, .a6, .a7] →
        (crtEntryG s u [r2Rs s]).gpr r = t.gpr r := fun r h1 h2 =>
      (State.callEntry_gpr u h1).trans (k.gpr (by clear h1; revert h2; revert r; decide))
    obtain hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i) := fun i hi => by
      rw [hm, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oS1; omega_using [hi])) (by omega_using [hi]) (by unfold oS1; omega_using []))
        (by decide)]
      exact A.psa i hi
    obtain sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := [r2Rs s]) (i := i) hi
    simp only [Proof.Bignum.RISCV64.Crt.fnContractP, Proof.Bignum.RISCV64.Crt.postCore,
      g .a0 (by decide) (by decide), g .a2 (by decide) (by decide), g .a3 (by decide) (by decide),
      g .a4 (by decide) (by decide), g .a6 (by decide) (by decide), g .a7 (by decide) (by decide),
      A.a0, A.a2, A.a3, A.a4, A.a6, A.a7,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    obtain hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) hfu (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb (iR_eq h ▸ h.ki.symm) (by have := h.k2; omega_using []),
      hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using []),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega_using []), hb (h.h7' ▸ h.kdq.symm) (by have := h.wdq; omega_using []),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega_using [])] at hpost
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

end

end

/-!
# `vg_rsa_private_checked` on RISC-V: constant time

Two runs are related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each
step, both satisfying the same predicate for the same public data
(`dataOf`): the blocks between the calls by the taint analysis
(`PrivTaint.lean`), and the calls by the callees' constant time
(`RelCT.callEx`), whose public data at the call the correctness facts fix
(`crt_pub`, `pre_pub`, `pub_pub`); what each run satisfies after each step
follows from correctness (`two_post`). The frame's `alloc` and `free` leak
nothing (`relCT_alloc`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post)

/-- Allocating and freeing a buffer leaks nothing. -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- The public data. -/
def dataOf (s : State) : List (BitVec 64) × List (BitVec 64) × List Nat × Addr :=
  (argRegs.map s.gpr, (List.range 12).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat ++
      Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).map (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  have e : frameBytes = 3247 + 1 := rfl
  rw [e] at h
  sig_pub [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_twelve, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  unfold dataOf
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_twelve, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hsp]

/-- The public data's facts, of `vg_rsa_private_checked` or, with `pc`, of
`vg_rsa_private_checked_precomputed`. -/
structure Same (pc : Bool) (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  arg : ∀ i < 12, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat =
    Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat =
    Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat
  arg12 : pc = true → stackArg s₁ 12 = stackArg s₂ 12
  pv : preVal pc s₁ = preVal pc s₂

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same false s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have h3 : s₁.gpr .a3 = s₂.gpr .a3 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [Proof.Rsa.bytesAt_length', h3])
  have hn' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn
  exact ⟨gr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp, hn',
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he, (fun h => nomatch h),
    by simp only [preVal, Bool.false_eq_true, ↓reduceIte]; rw [hn', h3]⟩

/-- On entry, with the public data `d`. -/
def Φ0 (d : List (BitVec 64) × List (BitVec 64) × List Nat × Addr) (s : State) : Prop :=
  (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre s ∧ dataOf s = d

/-- Two states for the same public data. -/
theorem same {d} {s₁ s₂ : State} (h₁ : Φ0 d s₁) (h₂ : Φ0 d s₂) : Same false s₁ s₂ :=
  same_of (h₁.2.trans h₂.2.symm)

theorem fb_same {pc : Bool} {s₁ s₂ : State} (S : Same pc s₁ s₂) : fb s₁ = fb s₂ := by simp only [fb, S.sp]

theorem r_same {pc : Bool} {s₁ s₂ : State} (S : Same pc s₁ s₂) {r : Reg} (hr : r ∈ argRegs := by decide) :
    s₁.gpr r = s₂.gpr r := S.gpr r hr

/-! ## The calls -/

variable {pc : Bool}

theorem crt_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP pc s₁) (h₂ : PreP pc s₂) (S : Same pc s₁ s₂) (A₁ : AtCrt s₁ t₁)
    (A₂ : AtCrt s₂ t₂) : Proof.Bignum.RISCV64.Crt.fnContract.pub (crtEntry s₁ t₁) (crtEntry s₂ t₂) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have hn : ∀ {s t : State}, PreP pc s → AtCrt s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega_using [])
  have hl : ∀ {s t : State}, AtCrt s t →
      (List.range 10).map (stackArg (crtEntry s t)) = (List.range 10).map fun i => stackArg s (2 + i) :=
    fun A => List.map_congr_left fun i hi => crtEntry_stackArg A (List.mem_range.mp hi)
  refine ⟨fun r hr => ?_, by rw [show (crtEntry s₁ t₁).sp = fb s₁ from A₁.sp,
      show (crtEntry s₂ t₂).sp = fb s₂ from A₂.sp, fb_same S], ?_, ?_⟩
  · rw [g r (fun h => by revert r; decide), g r (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, fb_same S]
    · rw [A₁.a1, A₂.a1, r_same S]
    · rw [A₁.a2, A₂.a2, r_same S]
    · rw [A₁.a3, A₂.a3, r_same S]
    · rw [A₁.a4, A₂.a4, r_same S]
    · rw [A₁.a5, A₂.a5, r_same S]
    · rw [A₁.a6, A₂.a6, S.arg 0 (by decide)]
    · rw [A₁.a7, A₂.a7, S.arg 1 (by decide)]
  · rw [hl A₁, hl A₂]
    exact List.map_congr_left fun i hi => S.arg _ (by have := List.mem_range.mp hi; omega_using [this])
  · show Spec.Rsa.bytesAt t₁.mem ((crtEntry s₁ t₁).gpr .a2) ((crtEntry s₁ t₁).gpr .a3).toNat =
      Spec.Rsa.bytesAt t₂.mem ((crtEntry s₂ t₂).gpr .a2) ((crtEntry s₂ t₂).gpr .a3).toNat
    rw [g .a2 (by decide), g .a3 (by decide), g .a2 (by decide), g .a3 (by decide), A₁.a2, A₁.a3, A₂.a2,
      A₂.a3, hn h₁ A₁, hn h₂ A₂, S.n]

theorem pre_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP pc s₁) (h₂ : PreP pc s₂) (S : Same pc s₁ s₂) (A₁ : AtPre s₁ t₁)
    (A₂ : AtPre s₂ t₂) : Proof.Bignum.RISCV64.Pre.fnContract.pub (t₁.callEntry.withRegions [nR s₁] (preWr s₁))
      (t₂.callEntry.withRegions [nR s₂] (preWr s₂)) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have hn : ∀ {s t : State}, PreP pc s → AtPre s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega_using [])
  simp only [Proof.Bignum.RISCV64.Pre.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
    g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), A₁.a0, A₁.a1, A₁.a2, A₁.a3, A₁.a4, A₁.a5, A₂.a0,
    A₂.a1, A₂.a2, A₂.a3, A₂.a4, A₂.a5, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
    State.callEntry_sp, A₁.sp, A₂.sp]
  rw [hn h₁ A₁, hn h₂ A₂, S.n, fb_same S, r_same S (r := .a2), r_same S (r := .a3), S.arg 10 (by decide),
    S.arg 11 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pubEntry_sa {s t : State} (A : AtPubC pc s t) :
    stackArg (pubEntry s t) 0 = stackArg s 10 ∧ stackArg (pubEntry s t) 1 = stackArg s 11 := by
  have hsp : (pubEntry s t).sp = fb s := A.sp
  refine ⟨?_, ?_⟩
  · show t.mem.readW ((pubEntry s t).sp + _) 64 = _; rw [hsp]; exact A.psa0
  · show t.mem.readW ((pubEntry s t).sp + _) 64 = _; rw [hsp]; exact A.psa1

theorem pub_pub {s₁ s₂ t₁ t₂ : State} (h₁ : PreP pc s₁) (h₂ : PreP pc s₂) (S : Same pc s₁ s₂) (A₁ : AtPubC pc s₁ t₁)
    (A₂ : AtPubC pc s₂ t₂) : Proof.Bignum.RISCV64.Pub.fnContract.pub (pubEntry s₁ t₁) (pubEntry s₂ t₂) := by
  have g : ∀ {s t : State}, ∀ r, r ∉ linkRegs → (pubEntry s t).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr _ hr
  have he : ∀ {s t : State}, PreP pc s → AtPubC pc s t →
      Spec.Rsa.bytesAt t.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat :=
    fun h A => bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.ke.symm
      · exact h.es) (by have := h.we; omega_using [])
  obtain ⟨a₁, b₁⟩ := pubEntry_sa A₁
  obtain ⟨a₂, b₂⟩ := pubEntry_sa A₂
  simp only [Proof.Bignum.RISCV64.Pub.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
    g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), A₁.a0, A₁.a1,
    A₁.a2, A₁.a3, A₁.a4, A₁.a5, A₁.a6, A₁.a7, A₂.a0, A₂.a1, A₂.a2, A₂.a3, A₂.a4, A₂.a5, A₂.a6, A₂.a7, a₁, b₁, a₂,
    b₂, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp, State.callEntry_sp, A₁.sp, A₂.sp,
    pre_toNat h₁, pre_toNat h₂]
  rw [A₁.pre, A₂.pre, S.pv, he h₁ A₁, he h₂ A₂, S.e, fb_same S, r_same S (r := .a0), r_same S (r := .a3),
    r_same S (r := .a4), r_same S (r := .a5), S.arg 10 (by decide), S.arg 11 (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The chain -/

/-- The public data. -/
abbrev Data := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

/-- What the chain needs of the entry states `E d s` for the public data `d`. -/
structure EntryOk {D : Type} (pc : Bool) (E : D → State → Prop) : Prop where
  pre : ∀ d s, E d s → PreP pc s
  same : ∀ d s₁ s₂, E d s₁ → E d s₂ → Same pc s₁ s₂

section

variable {D : Type} (E : D → State → Prop)

def Φ1 (d : D) (u : State) : Prop := ∃ s, E d s ∧ u = allocd frameBytes s
def Ψ1 (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtCrt s u
def Ψ2 (d : D) (u : State) : Prop := ∃ s, E d s ∧ Mid s u ∧ crtOut s u
def Ψ3 (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtPre s u
def ΨC (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtCopy s u
def Ψ4 (pc : Bool) (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtPub pc s u
def Ψ5 (pc : Bool) (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtPubC pc s u
def Ψ6 (pc : Bool) (d : D) (u : State) : Prop := ∃ s, E d s ∧ AtCmp pc s u

variable {E}

theorem crt_rel (hE : EntryOk pc E) : RelCT isa (Two (Ψ1 E)) crtCall fun _ _ => True := by
  unfold crtCall
  refine RelCT.callEx Proof.Bignum.RISCV64.Crt.fn_correct Proof.Bignum.RISCV64.Crt.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  exact ⟨crtRd s₁, crtWr s₁, crtRd s₂, crtWr s₂, crt_pre h₁ A₁, crt_pre h₂ A₂,
    crt_pub h₁ h₂ (hE.same _ _ _ φ₁ φ₂) A₁ A₂, (crt_covers h₁ A₁).1, (crt_covers h₁ A₁).2, (crt_covers h₂ A₂).1,
    (crt_covers h₂ A₂).2⟩

theorem pre_rel (hE : EntryOk false E) : RelCT isa (Two (Ψ3 E)) preCall fun _ _ => True := by
  unfold preCall
  refine RelCT.callEx Proof.Bignum.RISCV64.Pre.fn_correct Proof.Bignum.RISCV64.Pre.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  exact ⟨[nR s₁], preWr s₁, [nR s₂], preWr s₂, pre_pre h₁ A₁, pre_pre h₂ A₂,
    pre_pub h₁ h₂ (hE.same _ _ _ φ₁ φ₂) A₁ A₂, (pre_covers h₁ A₁).1, (pre_covers h₁ A₁).2, (pre_covers h₂ A₂).1,
    (pre_covers h₂ A₂).2⟩

theorem pub_rel (hE : EntryOk pc E) : RelCT isa (Two (Ψ5 E pc)) pubCall fun _ _ => True := by
  unfold pubCall
  refine RelCT.callEx Proof.Bignum.RISCV64.Pub.fn_correct Proof.Bignum.RISCV64.Pub.fn_ct
    fun u₁ u₂ ⟨_, ⟨s₁, φ₁, A₁⟩, ⟨s₂, φ₂, A₂⟩, _⟩ => ?_
  have h₁ := hE.pre _ _ φ₁
  have h₂ := hE.pre _ _ φ₂
  obtain ⟨p₁, c₁, w₁⟩ := pub_pre h₁ A₁
  obtain ⟨p₂, c₂, w₂⟩ := pub_pre h₂ A₂
  exact ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, p₁, p₂, pub_pub h₁ h₂ (hE.same _ _ _ φ₁ φ₂) A₁ A₂, c₁, w₁, c₂,
    w₂⟩

theorem pins_Ψ6 (hE : EntryOk pc E) : Pins (Ψ6 E pc) [.s1, .s3, .s6] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := hE.same _ _ _ φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [A₁.s1, A₂.s1, r_same S]
  · rw [A₁.s3, A₂.s3, r_same S]
  · rw [A₁.s6, A₂.s6, r_same S]

theorem pins_ΨC (hE : EntryOk true E) : Pins (ΨC E) [.a0, .a1, .a2] := by
  rintro d u₁ u₂ ⟨s₁, φ₁, A₁⟩ ⟨s₂, φ₂, A₂⟩ r hr
  have S := hE.same _ _ _ φ₁ φ₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [A₁.a0, A₂.a0, S.arg12 rfl]
  · rw [A₁.a1, A₂.a1, fb_same S]
  · rw [A₁.a2, A₂.a2, r_same S]

/-- `n`'s values computed. -/
theorem step_rel_false (hE : EntryOk false E) : RelCT isa (Two (Ψ2 E)) (preStep false) (Two (Ψ4 E false)) :=
  RelCT.seq (two_post (Ψ := Ψ3 E) (preArgs_taint (Ψ2 E)) fun _ _ ⟨s, φ, M, C⟩ =>
    WP.mono (preArgs_ok (hE.pre _ _ φ) M C) fun _ A => ⟨s, φ, A⟩)
    (two_post (pre_rel hE) fun _ _ ⟨s, φ, A⟩ => preCall_ok (hE.pre _ _ φ) A fun _ B => ⟨s, φ, B⟩)

/-- `n`'s values copied from `pre`. -/
theorem step_rel_true (hE : EntryOk true E) (hX : ∀ d s, E d s → PreX s) :
    RelCT isa (Two (Ψ2 E)) (preStep true) (Two (Ψ4 E true)) :=
  RelCT.seq (two_post (Ψ := ΨC E) (preArgsP_taint (Ψ2 E)) fun _ _ ⟨s, φ, M, C⟩ =>
    WP.mono (preArgsP_ok (hE.pre _ _ φ) (hX _ _ φ) M C) fun _ A => ⟨s, φ, A⟩)
    (two_post (preCopy_taint (pins_ΨC hE)) fun _ _ ⟨s, φ, A⟩ =>
      WP.mono (preCopy_ok (hE.pre _ _ φ) (hX _ _ φ) A) fun _ B => ⟨s, φ, B⟩)

/-- `vg_rsa_private_crt`. -/
theorem crt_step_rel_false (hE : EntryOk false E) : RelCT isa (Two (Ψ1 E)) (crtStep false) (Two (Ψ2 E)) :=
  two_post (crt_rel hE) fun _ _ ⟨s, φ, A⟩ => crtCall_ok (hE.pre _ _ φ) A fun _ M C => ⟨s, φ, M, C⟩

theorem body_rel (hE : EntryOk pc E) (hcrt : RelCT isa (Two (Ψ1 E)) (crtStep pc) (Two (Ψ2 E)))
    (hstep : RelCT isa (Two (Ψ2 E)) (preStep pc) (Two (Ψ4 E pc))) :
    RelCT isa (Two (Φ1 E)) (bodyG pc) fun _ _ => True := by
  unfold bodyG
  refine RelCT.seq (two_post (Ψ := Ψ1 E) (setup_taint (Φ1 E)) fun d u ⟨s, φ, e⟩ =>
    e ▸ WP.mono (setup_ok (hE.pre _ _ φ)) fun v A => ⟨s, φ, A⟩) ?_
  refine RelCT.seq hcrt ?_
  refine RelCT.seq hstep ?_
  refine RelCT.seq (two_post (Ψ := Ψ5 E pc) (pubArgs_taint (Ψ4 E pc)) fun d u ⟨s, φ, A⟩ =>
    WP.mono (pubArgs_ok (hE.pre _ _ φ) A) fun v B => ⟨s, φ, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := Ψ6 E pc) (pub_rel hE) fun d u ⟨s, φ, A⟩ =>
    pubCall_ok (hE.pre _ _ φ) A fun v B => ⟨s, φ, B⟩) ?_
  exact tail_taint (pins_Ψ6 hE)

theorem codeG_rel (hE : EntryOk pc E) (hcrt : RelCT isa (Two (Ψ1 E)) (crtStep pc) (Two (Ψ2 E)))
    (hstep : RelCT isa (Two (Ψ2 E)) (preStep pc) (Two (Ψ4 E pc))) :
    RelCT isa (Two E) (.frame (.alloc frameBytes) (bodyG pc) (.free frameBytes)) fun _ _ => True :=
  relCT_alloc ((body_rel hE hcrt hstep).mono (fun a b ⟨s, t, ⟨d, φs, φt, hsp⟩, ea, eb⟩ =>
    ⟨d, ⟨s, φs, ea⟩, ⟨t, φt, eb⟩, by rw [ea, eb]; simp only [allocd, hsp]⟩) fun _ _ h => h)

end

theorem entry_ok : EntryOk false Φ0 := ⟨fun _ _ φ => preP_of φ.1, fun _ _ _ φ₁ φ₂ => same φ₁ φ₂⟩

theorem code_rel : RelCT isa (Two Φ0) code fun _ _ => True :=
  codeG_rel entry_ok (crt_step_rel_false entry_ok) (step_rel_false entry_ok)

theorem code_ct : ConstantTime isa (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre
    (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pub code :=
  RelCT.constantTime (code_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, (pub_data hp).symm⟩, (same_of (pub_data hp)).sp⟩) fun _ _ h => h)

end VG.Proof.Rsa.RISCV64.Priv
