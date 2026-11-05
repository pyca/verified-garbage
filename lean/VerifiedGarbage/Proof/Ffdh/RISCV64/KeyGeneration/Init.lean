module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Impl.Ffdh.RISCV64.KeyGeneration.Init
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native FFDH key-generation initialization on RISC-V: correctness, constant time

`validate_ok`: `t0` is zero exactly for a width in `64..=1024`;
`initialize_ok` and `clear_ok`: the four public words (`initWritten`) and
the result. The code branches on `p_len` alone, which is public
(`init_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.KeyGeneration

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Bignum VG.Impl.Ffdh.RISCV64.KeyGeneration
open VG.Proof.Bignum.RISCV64 (add_ofNat_zero fin64_exec_li_lit fin64_exec_li_zero)

/-- The four public words written. -/
def initWritten (m : Mem) (B : Addr) (a b c d : BitVec 64) : Mem :=
  (((m.writeW B a).writeW (off B 8) b).writeW (off B 16) c).writeW (off B 24) d

theorem initWritten_words (m : Mem) (B : Addr) (a b c d : BitVec 64) :
    Spec.Rsa.wordsAt (initWritten m B a b c d) B 4 = [a, b, c, d] := by
  change [word (initWritten m B a b c d) B (8 * 0), word (initWritten m B a b c d) B (8 * 1),
    word (initWritten m B a b c d) B (8 * 2), word (initWritten m B a b c d) B (8 * 3)] = _
  have hm : initWritten m B a b c d =
      (((m.writeW (off B (8 * 0)) a).writeW (off B (8 * 1)) b).writeW (off B (8 * 2)) c).writeW
        (off B (8 * 3)) d := by
    simp only [initWritten, off, Nat.mul_zero, BitVec.add_zero]
  rw [hm]
  simp only [Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (0 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (1 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (2 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 3) (by decide) (by decide : (3 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 2) (by decide) (by decide : (0 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 2) (by decide) (by decide : (1 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 2) (by decide) (by decide : (2 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 1) (by decide) (by decide : (0 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 1) (by decide) (by decide : (1 : Nat) < 16),
    Control.controller_store_word _ _ _ (i := 0) (by decide) (by decide : (0 : Nat) < 16),
    Nat.reduceEqDiff, ite_true, ite_false]

/-- The state's 128 bytes, the only region the code may write, aligned. -/
def StateWr (s : State) : Prop :=
  s.wr = [⟨s.gpr .a0, 128⟩] ∧ (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a0).toNat % 8 = 0

theorem st {s : State} (h : StateWr s) (d : Nat) (hd : d + 8 ≤ 128) :
    InRegions s.wr (s.gpr .a0 + BitVec.ofNat 64 d) 8 := by
  rw [h.1]
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega_arith)⟩

theorem al {s : State} (h : StateWr s) (d : Nat) (hd : d + 8 ≤ 128) (h8 : d % 8 = 0) :
    (s.gpr .a0 + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have h1 := h.2.1
  have h2 := h.2.2
  have e : (s.gpr .a0 + BitVec.ofNat 64 d).toNat = (s.gpr .a0).toNat + d := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  rw [e]
  omega_arith

theorem st0 {s : State} (h : StateWr s) : InRegions s.wr (s.gpr .a0) 8 := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using st h 0 (by decide)

theorem al0 {s : State} (h : StateWr s) : (s.gpr .a0).toNat % 8 = 0 := h.2.2

theorem valid_bit {n : Nat} (hn : n < 2 ^ 64) :
    ((if BitVec.ofNat 64 n < BitVec.ofNat 64 64 then (1 : BitVec 64) else 0) |||
      (if BitVec.ofNat 64 1024 < BitVec.ofNat 64 n then (1 : BitVec 64) else 0) == 0) =
      decide (64 ≤ n ∧ n ≤ 1024) := by
  have e1 : (BitVec.ofNat 64 n < BitVec.ofNat 64 64) ↔ n < 64 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have e2 : (BitVec.ofNat 64 1024 < BitVec.ofNat 64 n) ↔ 1024 < n := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  by_cases h1 : n < 64 <;> by_cases h2 : 1024 < n <;>
    simp only [e1, e2, h1, h2, ↓reduceIte] <;> first | decide | (simp; omega_arith)

/-- `validate`: `t0` is zero exactly for a width in `64..=1024`. -/
theorem validate_ok (s : State) {n : Nat} (hx : s.gpr .a1 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block validate) s fun t =>
      ((t.gpr .t0 == 0) = decide (64 ≤ n ∧ n ≤ 1024) ∧ t.mem = s.mem) ∧ Keep [.t0, .t1, .t2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold validate
  brun [hx, exec_sltu, fin64_exec_li_lit (show 64 < 2048 by decide), fin64_exec_li_lit (show 1024 < 2048 by decide)]
  exact valid_bit hn

theorem clear_ok {s : State} (h : StateWr s) :
    WP isa (.block clear) s fun t => (t.gpr .a0 = 0 ∧ t.mem = initWritten s.mem (s.gpr .a0) 0 0 0 0) ∧
      Keep [.a0, .t2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold clear initWritten
  brun [st0 h, al0 h, st h 0 (by decide), st h 8 (by decide), st h 16 (by decide), st h 24 (by decide),
    al h 0 (by decide) (by decide), al h 8 (by decide) (by decide), al h 16 (by decide) (by decide),
    al h 24 (by decide) (by decide), fin64_exec_li_zero, add_ofNat_zero]
  all_goals rfl

theorem initialize_ok {s : State} (h : StateWr s) :
    WP isa (.block initializeState) s fun t => (t.gpr .a0 = 1 ∧
      t.mem = initWritten s.mem (s.gpr .a0) 128 128 (s.gpr .a1) (s.gpr .a1)) ∧ Keep [.a0, .t2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold initializeState initWritten
  brun [st0 h, al0 h, st h 0 (by decide), st h 8 (by decide), st h 16 (by decide), st h 24 (by decide),
    al h 0 (by decide) (by decide), al h 8 (by decide) (by decide), al h 16 (by decide) (by decide),
    al h 24 (by decide) (by decide), fin64_exec_li_lit (show 128 < 2048 by decide),
    fin64_exec_li_lit (show 1 < 2048 by decide), add_ofNat_zero]
  exact ⟨rfl, rfl⟩

def initPre (s : State) : Prop := StateWr s

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.keyInit (s.gpr .a1).toNat with
  | none => ((t.gpr .a0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = List.replicate 4 0
  | some values => ((t.gpr .a0).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_ok {s : State} (h : StateWr s) : WP isa init s (initPost s) := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .a1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .a1).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hxn : (s.gpr .a1).toNat = n := by rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  unfold init
  refine WP.seq (WP.mono (validate_ok s hx hl) fun u ⟨⟨h0, hm⟩, k⟩ => ?_)
  have h3 : u.gpr .a0 = s.gpr .a0 := k.gpr (by decide)
  have h4 : u.gpr .a1 = s.gpr .a1 := k.gpr (by decide)
  have hu : StateWr u := by rw [StateWr, k.2.2, h3]; exact h
  refine WP.ite (u.gpr .t0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h0, decide_eq_true_eq] at hb
    refine WP.mono (initialize_ok hu) fun t ⟨⟨ht, hmt⟩, _⟩ => ?_
    have he : Spec.Ffdh.keyInit (s.gpr .a1).toNat = some [128, 128, n, n] := by
      simp [Spec.Ffdh.keyInit, hxn, hb.1, hb.2]
    simp only [initPost, he]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, hm, h3, h4, initWritten_words, hx]
    rfl
  · rw [h0] at hb
    have hn : ¬(64 ≤ n ∧ n ≤ 1024) := by simpa using hb
    refine WP.mono (clear_ok hu) fun t ⟨⟨ht, hmt⟩, _⟩ => ?_
    have he : Spec.Ffdh.keyInit (s.gpr .a1).toNat = none := by
      simp only [Spec.Ffdh.keyInit, hxn]
      exact ite_eq_right (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hn)
    simp only [initPost, he]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, hm, h3, initWritten_words]
    rfl

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.a0, .t0, .t1, .t2] (init_ok h) (by rfl)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide), hp⟩

private def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

/-- `vg_ffdh_key_generation_init`. -/
theorem init_verified : Verified RISCV64.target init (Spec.Ffdh.keyInitContract RISCV64.abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
    intro s t _ _ h
    refine ⟨h.1, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · sig_implies [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
      initContract, initPre, initPost, initPub, StateWr, RISCV64.abi, RISCV64.argRegs] [initSat] using initSat

end VG.Proof.Ffdh.RISCV64.KeyGeneration
