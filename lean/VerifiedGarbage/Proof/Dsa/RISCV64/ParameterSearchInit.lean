module

public import VerifiedGarbage.Impl.Dsa.RISCV64.ParameterSearch
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Dsa.RISCV64.ParameterSearch
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # Starting the DSA parameter search on RISC-V: correctness, constant time

As on x86-64 (`Proof/Dsa/X86_64/ParameterSearchInit.lean`), with the RISC-V
idioms of the RSA prime search's initialization
(`Proof/RsaKeyGen/RISCV64/SearchInit.lean`): for a supported width the four
words of `Spec.Dsa.parameterInit` and 1 (`words_ok`), otherwise zeros and 0
(`zeros_ok`), by the three comparisons with `p_len` (`init_ok`). Every
argument is public: the code's taint is checked with `a0` and `a1` public. -/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.ParameterSearchInit

open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.RsaKeyGen.SearchInit (written written_words shl_ofNat add_ofNat)
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The four words `parameterInit` gives for a supported width `L`. -/
def words (L : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 4096, BitVec.ofNat 64 L, BitVec.ofNat 64 (32769 * L), BitVec.ofNat 64 (512 * L)]

theorem lui1 : sext32 ((1 : BitVec 20) ++ (0 : BitVec 12)) = BitVec.ofNat 64 4096 := by decide

theorem words_ok {s : State} {B : Addr} {L : Nat} (scr : Scr s B 32) (h0 : s.gpr .a0 = B)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 L) (hL : L ≤ 384) :
    WP isa (.block initWords) s fun t => t.gpr .a0 = 1 ∧ t.mem = written s.mem B (words L) := by
  have e15 := shl_ofNat L 15 (by omega)
  have e9 := shl_ofNat L 9 (by omega)
  have e1 : BitVec.ofNat 64 (L * 2 ^ 15) + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e2 : BitVec.ofNat 64 (L * 2 ^ 9) = BitVec.ofNat 64 (512 * L) := by congr 1; omega
  unfold initWords written words
  brun [h0, h1, exec_li, exec_lui, lui1, e15, e9, e1, e2,
    scr.st (d := 0) (n := 8) (by decide), scr.st (d := 8) (n := 8) (by decide),
    scr.st (d := 16) (n := 8) (by decide), scr.st (d := 24) (n := 8) (by decide),
    scr.al8 (d := 0) (by decide) (by decide), scr.al8 (d := 8) (by decide) (by decide),
    scr.al8 (d := 16) (by decide) (by decide), scr.al8 (d := 24) (by decide) (by decide), off]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_zero]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

theorem zeros_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .a0 = B) :
    WP isa (.block initZeros) s fun t => t.gpr .a0 = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  unfold initZeros written
  brun [h0, exec_li, scr.st (d := 0) (n := 8) (by decide), scr.st (d := 8) (n := 8) (by decide),
    scr.st (d := 16) (n := 8) (by decide), scr.st (d := 24) (n := 8) (by decide),
    scr.al8 (d := 0) (by decide) (by decide), scr.al8 (d := 8) (by decide) (by decide),
    scr.al8 (d := 16) (by decide) (by decide), scr.al8 (d := 24) (by decide) (by decide), off]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_zero]
  exact ⟨rfl, rfl⟩

/-! ## The guards -/

theorem toNat_eq_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ofNat_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  · rintro rfl; rfl

/-- `li t3 n`, then `a1 = t3` is `L = n`. -/
theorem guard_ok (s : State) {L : Nat} (hL : L < 2 ^ 64) (h1 : s.gpr .a1 = BitVec.ofNat 64 L) {n : Nat}
    (hn : n < 2048) :
    WP isa (.block [.li .t3 n]) s fun t =>
      (isa.eval (.eq .a1 .t3) t = some (decide (L = n)) ∧ t.mem = s.mem) ∧ Keep [.t3] s t := by
  refine VG.RISCV64.Steps.wp_li hn fun t u => WP.block_nil ⟨⟨?_, u.mem⟩,
    fun r hr => u.other r (by simpa using hr), u.rd, u.wr⟩
  show some (t.gpr .a1 == t.gpr .t3) = _
  rw [u.other _ (by decide), u.gpr, h1, ofNat_beq hL (by omega)]

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L : Nat) (m : Mem) (B : Addr) (t : State) : Prop :=
  if Spec.Dsa.generationPLenValid L then t.gpr .a0 = 1 ∧ t.mem = written m B (words L)
  else t.gpr .a0 = 0 ∧ t.mem = written m B [0, 0, 0, 0]

theorem words_post {t : State} {B : Addr} {L : Nat} {m : Mem} (scr : Scr t B 32)
    (h0 : t.gpr .a0 = B) (h1 : t.gpr .a1 = BitVec.ofNat 64 L) (hm : t.mem = m)
    (hv : L = 128 ∨ L = 256 ∨ L = 384) :
    WP isa (.block initWords) t (InitPost L m B) := by
  refine WP.mono (words_ok scr h0 h1 (by omega)) fun u ⟨ha, hu⟩ => ?_
  have hvalid : Spec.Dsa.generationPLenValid L = true := by
    rcases hv with rfl | rfl | rfl <;> rfl
  simp only [InitPost, hvalid, ↓reduceIte]
  exact ⟨ha, by rw [hu, hm]⟩

theorem init_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .a0 = B) :
    WP isa init s (InitPost (s.gpr .a1).toNat s.mem B) := by
  generalize hLdef : (s.gpr .a1).toNat = L
  have hL : L < 2 ^ 64 := by rw [← hLdef]; exact (s.gpr .a1).isLt
  have h1 : s.gpr .a1 = BitVec.ofNat 64 L := by rw [← hLdef]; exact toNat_eq_ofNat _
  unfold init
  refine WP.seq (WP.mono (guard_ok s hL h1 (n := 128) (by decide)) fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  have hu0 : u.gpr .a0 = B := (k.gpr (by decide)).trans h0
  have hu1 : u.gpr .a1 = BitVec.ofNat 64 L := (k.gpr (by decide)).trans h1
  have scu : Scr u B 32 := scr.congr k.2.2
  refine WP.ite _ he (fun h => words_post scu hu0 hu1 hm (.inl (of_decide_eq_true h))) fun hn1 => ?_
  have hn1 : L ≠ 128 := of_decide_eq_false hn1
  refine WP.seq (WP.mono (guard_ok u hL hu1 (n := 256) (by decide)) fun v ⟨⟨he, hmv⟩, kv⟩ => ?_)
  have hv0 : v.gpr .a0 = B := (kv.gpr (by decide)).trans hu0
  have hv1 : v.gpr .a1 = BitVec.ofNat 64 L := (kv.gpr (by decide)).trans hu1
  have scv : Scr v B 32 := scu.congr kv.2.2
  have hmv' : v.mem = s.mem := hmv.trans hm
  refine WP.ite _ he (fun h => words_post scv hv0 hv1 hmv' (.inr (.inl (of_decide_eq_true h)))) fun hn2 => ?_
  have hn2 : L ≠ 256 := of_decide_eq_false hn2
  refine WP.seq (WP.mono (guard_ok v hL hv1 (n := 384) (by decide)) fun w ⟨⟨he, hmw⟩, kw⟩ => ?_)
  have hw0 : w.gpr .a0 = B := (kw.gpr (by decide)).trans hv0
  have hw1 : w.gpr .a1 = BitVec.ofNat 64 L := (kw.gpr (by decide)).trans hv1
  have scw : Scr w B 32 := scv.congr kw.2.2
  have hmw' : w.mem = s.mem := hmw.trans hmv'
  refine WP.ite _ he (fun h => words_post scw hw0 hw1 hmw' (.inr (.inr (of_decide_eq_true h)))) fun hn3 => ?_
  have hn3 : L ≠ 384 := of_decide_eq_false hn3
  refine WP.mono (zeros_ok scw hw0) fun t ⟨ha, ht⟩ => ?_
  have hvalid : Spec.Dsa.generationPLenValid L = false := by
    simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨hn1, hn2⟩, hn3⟩
  simp only [InitPost, hvalid, Bool.false_eq_true, ↓reduceIte]
  exact ⟨ha, by rw [ht, hmw']⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 32⟩] ∧ (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a0).toNat % 8 = 0

def initPost (s t : State) : Prop :=
  match Spec.Dsa.parameterInit (s.gpr .a1).toNat with
  | none => ((t.gpr .a0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = List.replicate 4 0
  | some values => ((t.gpr .a0).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a0) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem request_zero (L : Nat) : Spec.Dsa.parameterRequest L 0 = 512 * L := by
  simp only [Spec.Dsa.parameterRequest, Spec.Entropy.request, Spec.Dsa.parameterEntropy]
  omega

private theorem result_post {s t : State} (h : InitPost (s.gpr .a1).toNat s.mem (s.gpr .a0) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost Spec.Dsa.parameterInit
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    refine ⟨by rw [h.1]; rfl, ?_⟩
    rw [h.2, words, written_words, request_zero]
    rfl
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, written_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom, hal⟩ := h
  have scr : Scr s (s.gpr .a0) 32 := Scr.of_mem (by rw [hwr]; simp) hroom hal
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.a0, .t2, .t3] (init_ok scr rfl) (by decide +kernel)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide), result_post hp⟩

theorem init_agree {s₁ s₂ : State} (h : initPub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.a0, .a1]) s₁ s₂ := by
  obtain ⟨hsp, h0, h1⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init :=
  RelCT.constantTime ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1])
    (fun _ _ h => init_agree h) (by taint_decide)).mono (fun _ _ h => h.2.2) fun _ _ h => h)

private def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 128 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 32⟩]

end VG.Proof.Dsa.RISCV64.ParameterSearchInit

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 ParameterSearchInit

/-- `vg_dsa_parameter_search_init`. -/
theorem init_verified :
    Verified RISCV64.target Impl.Dsa.RISCV64.ParameterSearch.init (Spec.Dsa.parameterInitContract RISCV64.abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Dsa.RISCV64
