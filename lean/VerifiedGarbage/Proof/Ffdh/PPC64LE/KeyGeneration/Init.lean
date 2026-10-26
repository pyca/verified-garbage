module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.KeyGeneration.Init
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import Mathlib.Tactic.SplitIfs

/-! # Native FFDH key-generation initialization on PPC64LE: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Ffdh.PPC64LE VG.Impl.Ffdh.PPC64LE.KeyGeneration
open VG.Impl.Ffdh.PPC64LE.Generation (lt clear)

theorem high_ok (s : State) :
    WP isa (.block high) s fun t => t.gpr .r12 = s.gpr .r4 >>> 11 ∧ t.mem = s.mem := by
  unfold high
  crunr

/-- `validate`: with `p_len < 2^11`, `r12` is 1 exactly for a width in `64..=1024`. -/
theorem validate_ok (s : State) {n : Nat} (hx : s.gpr .r4 = BitVec.ofNat 64 n) (hn : n < 2 ^ 11) :
    WP isa (.block validate) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (if 64 ≤ n ∧ n ≤ 1024 then 1 else 0) ∧ t.mem = s.mem := by
  unfold validate lt
  crunr [hx, List.cons_append, List.nil_append]
  rw [lt_bit (by omega) (by decide), lt_bit (by omega) (by decide)]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem clear_ok {s : State} (h : StateWr s) :
    WP isa (.block clear) s fun t => t.gpr .r3 = 0 ∧ t.mem = initWritten s.mem (s.gpr .r3) 0 0 0 0 := by
  unfold clear initWritten
  crunr [st0 h, st h 8 (by decide), st h 16 (by decide), st h 24 (by decide)]
  rfl

theorem initialize_ok {s : State} (h : StateWr s) :
    WP isa (.block initializeState) s fun t => t.gpr .r3 = 1 ∧
      t.mem = initWritten s.mem (s.gpr .r3) 128 128 (s.gpr .r4) (s.gpr .r4) := by
  unfold initializeState initWritten
  crunr [st0 h, st h 8 (by decide), st h 16 (by decide), st h 24 (by decide)]
  rfl

def initPre (s : State) : Prop := s.rd = [] ∧ StateWr s

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.keyInit (s.gpr .r4).toNat with
  | none => ((t.gpr .r3).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = List.replicate 4 0
  | some values => ((t.gpr .r3).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem keyInit_none {n : Nat} (h : ¬(64 ≤ n ∧ n ≤ 1024)) : Spec.Ffdh.keyInit n = none := by
  simp only [Spec.Ffdh.keyInit]
  exact ite_eq_right (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h)

theorem clear_post {s u : State} {rs : List Reg} (h : StateWr s) (k : Keep rs s u) (hr : .r3 ∉ rs) (hn : ¬(64 ≤ (s.gpr .r4).toNat ∧
    (s.gpr .r4).toNat ≤ 1024)) (hm : u.mem = s.mem) :
    WP isa (.block clear) u (initPost s) := by
  have h3 : u.gpr .r3 = s.gpr .r3 := k.gpr hr
  have hu : StateWr u := by rw [StateWr, k.2.2, h3]; exact h
  refine WP.mono (clear_ok hu) fun t ⟨ht, hmt⟩ => ?_
  simp only [initPost, keyInit_none hn]
  refine ⟨by rw [ht]; rfl, ?_⟩
  rw [hmt, hm, h3, initWritten_words]
  rfl

theorem init_ok {s : State} (h : StateWr s) : WP isa init s (initPost s) := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .r4 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .r4).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hxn : (s.gpr .r4).toNat = n := by rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  unfold init
  refine WP.seq (WP.mono (WP.keep [.r12] (high_ok s) (by decide +kernel)) fun u ⟨⟨h12, hm⟩, k⟩ => ?_)
  by_cases hb : n < 2 ^ 11
  · refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12, hx,
        shr_zero hl, decide_eq_true hb]) (fun _ => ?_) (by simp)
    have h4 : u.gpr .r4 = BitVec.ofNat 64 n := (k.gpr (by decide)).trans hx
    refine WP.seq (WP.mono (WP.keep [.r9, .r10, .r11, .r12] (validate_ok u h4 hb) (by decide +kernel))
      fun v ⟨⟨h12', hm'⟩, k'⟩ => ?_)
    have kv := k.trans k'
    by_cases hv : 64 ≤ n ∧ n ≤ 1024
    · rw [ite_eq_left hv] at h12'
      refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12']; rfl)
        (by simp) (fun _ => ?_)
      have h3 : v.gpr .r3 = s.gpr .r3 := kv.gpr (by decide)
      have hv4 : v.gpr .r4 = s.gpr .r4 := kv.gpr (by decide)
      have hvw : StateWr v := by rw [StateWr, kv.2.2, h3]; exact h
      refine WP.mono (initialize_ok hvw) fun t ⟨ht, hmt⟩ => ?_
      have he : Spec.Ffdh.keyInit (s.gpr .r4).toNat = some [128, 128, n, n] := by
        simp [Spec.Ffdh.keyInit, hxn, hv.1, hv.2]
      simp only [initPost, he]
      refine ⟨by rw [ht]; rfl, ?_⟩
      rw [hmt, hm', hm, h3, hv4, initWritten_words, hx]
      rfl
    · rw [ite_eq_right hv] at h12'
      refine WP.ite true (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12']; rfl)
        (fun _ => ?_) (by simp)
      exact clear_post h kv (by decide) (by rw [hxn]; exact hv) (hm'.trans hm)
  · refine WP.ite false (by simp only [VG.PPC64LE.eval, State.read, BitVec.setWidth_eq, h12, hx,
        shr_zero hl, decide_eq_false hb]) (by simp) (fun _ => ?_)
    exact clear_post h k (by decide) (by rw [hxn]; omega) hm

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.r3, .r9, .r10, .r11, .r12] (init_ok h.2) (by decide +kernel)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), hp⟩

private def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | _ => 0
  lr := 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified target init (Spec.Ffdh.keyInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.1, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_implies [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
      initContract, initPre, initPost, initPub, StateWr, abi, argRegs] [initSat] using initSat

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
