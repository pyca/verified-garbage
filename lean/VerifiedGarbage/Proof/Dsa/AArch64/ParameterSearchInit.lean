module

public import VerifiedGarbage.Impl.Dsa.AArch64.ParameterSearch
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.ParameterSearch
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Starting the DSA parameter search on AArch64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.ParameterSearchInit

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.RsaKeyGen.SearchInit (written written_words shl_ofNat add_ofNat)
open VG.Impl.Dsa.AArch64.ParameterSearch

/-- The four words for a supported width `L`: `parameterInit`'s three and the
first tape's length. -/
def words (L : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 4096, BitVec.ofNat 64 L, BitVec.ofNat 64 (32769 * L), BitVec.ofNat 64 (512 * L)]

theorem movi64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ## The blocks -/

theorem words_ok {s : State} {B : Addr} {L : Nat} (scr : Scr s B 32) (h0 : s.gpr .x0 = B)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 L) (hL : L ≤ 384) :
    WP isa (.block initWords) s fun t => t.gpr .x0 = 1 ∧
      t.mem = written s.mem B (words L) := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  have hc : BitVec.ofNat 64 L <<< 15 + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [shl_ofNat L 15 (by omega), add_ofNat]
    congr 1
    omega
  have hr : BitVec.ofNat 64 L <<< 9 = BitVec.ofNat 64 (512 * L) := by
    rw [shl_ofNat L 9 (by omega)]
    congr 1
    omega
  unfold initWords written words
  brun [h0, h1, movi64 (show 1 < 65536 by decide), movi64 (show 4096 < 65536 by decide), h00,
    scr.st (d := 8) (by decide), scr.st (d := 16) (by decide), scr.st (d := 24) (by decide), hc, hr,
    List.getD_cons_zero, List.getD_cons_succ]

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .x0 = B) :
    WP isa (.block clear) s fun t => t.gpr .x0 = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  unfold clear written
  brun [h0, movi64 (show 0 < 65536 by decide), h00, scr.st (d := 8) (by decide), scr.st (d := 16) (by decide),
    scr.st (d := 24) (by decide), List.getD_cons_zero, List.getD_cons_succ]
  rfl

theorem test_ok (s : State) {n : Nat} (hn : n = 128 ∨ n = 256 ∨ n = 384) :
    WP isa (.block (test n)) s fun t =>
      (isa.eval (.zero .x .x9) t = some (decide ((s.gpr .x1).toNat = n)) ∧ t.mem = s.mem) ∧ Keep [.x9] s t := by
  refine WP.keep [.x9] ?_ (by rcases hn with rfl | rfl | rfl <;> decide) rfl
    (by rcases hn with rfl | rfl | rfl <;> decide +kernel)
  unfold test
  brun [exec_subImm_x' (show n < 4096 by omega), eval]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  have hz : (0 : BitVec 64) + BitVec.ofNat 64 n = BitVec.ofNat 64 n := BitVec.zero_add _
  constructor
  · intro h; rw [h, hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact (BitVec.zero_add _).symm

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L : Nat) (m : Mem) (B : Addr) (t : State) : Prop :=
  if Spec.Dsa.generationPLenValid L then t.gpr .x0 = 1 ∧
    t.mem = written m B (words L)
  else t.gpr .x0 = 0 ∧ t.mem = written m B [0, 0, 0, 0]

theorem words_post {t : State} {B : Addr} {L : Nat} {m : Mem} (scr : Scr t B 32)
    (h0 : t.gpr .x0 = B) (h1 : t.gpr .x1 = BitVec.ofNat 64 L) (hm : t.mem = m)
    (hv : L = 128 ∨ L = 256 ∨ L = 384) :
    WP isa (.block initWords) t (InitPost L m B) := by
  refine WP.mono (words_ok scr h0 h1 (by omega)) fun u ⟨ha, hu⟩ => ?_
  have hvalid : Spec.Dsa.generationPLenValid L = true := by
    rcases hv with rfl | rfl | rfl <;> rfl
  simp only [InitPost, hvalid, ↓reduceIte]
  exact ⟨ha, by rw [hu, hm]⟩

theorem init_ok {s : State} {B : Addr} (scr : Scr s B 32) (h0 : s.gpr .x0 = B) :
    WP isa init s (InitPost (s.gpr .x1).toNat s.mem B) := by
  let L := (s.gpr .x1).toNat
  change WP isa init s (InitPost L s.mem B)
  have h1 : s.gpr .x1 = BitVec.ofNat 64 L := by
    simp only [L, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold init
  refine WP.seq (WP.mono (test_ok s (n := 128) (Or.inl rfl)) fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  have h0u : u.gpr .x0 = B := (k.gpr .x0 (by decide)).trans h0
  have h1u : u.gpr .x1 = BitVec.ofNat 64 L := (k.gpr .x1 (by decide)).trans h1
  have scu : Scr u B 32 := scr.congr k.wr
  refine WP.ite _ he (fun h => words_post scu h0u h1u hm (Or.inl (of_decide_eq_true h))) fun n1 => ?_
  have n1 : L ≠ 128 := of_decide_eq_false n1
  refine WP.seq (WP.mono (test_ok u (n := 256) (Or.inr (Or.inl rfl))) fun v ⟨⟨he, hmv⟩, kv⟩ => ?_)
  rw [k.gpr .x1 (by decide)] at he
  have h0v : v.gpr .x0 = B := (kv.gpr .x0 (by decide)).trans h0u
  have h1v : v.gpr .x1 = BitVec.ofNat 64 L := (kv.gpr .x1 (by decide)).trans h1u
  have scv : Scr v B 32 := scu.congr kv.wr
  have hmv' : v.mem = s.mem := hmv.trans hm
  refine WP.ite _ he (fun h => words_post scv h0v h1v hmv' (Or.inr (Or.inl (of_decide_eq_true h)))) fun n2 => ?_
  have n2 : L ≠ 256 := of_decide_eq_false n2
  refine WP.seq (WP.mono (test_ok v (n := 384) (Or.inr (Or.inr rfl))) fun w ⟨⟨he, hmw⟩, kw⟩ => ?_)
  rw [kv.gpr .x1 (by decide), k.gpr .x1 (by decide)] at he
  have h0w : w.gpr .x0 = B := (kw.gpr .x0 (by decide)).trans h0v
  have h1w : w.gpr .x1 = BitVec.ofNat 64 L := (kw.gpr .x1 (by decide)).trans h1v
  have scw : Scr w B 32 := scv.congr kw.wr
  have hmw' : w.mem = s.mem := hmw.trans hmv'
  refine WP.ite _ he (fun h => words_post scw h0w h1w hmw' (Or.inr (Or.inr (of_decide_eq_true h)))) fun n3 => ?_
  have n3 : L ≠ 384 := of_decide_eq_false n3
  refine WP.mono (clear_ok scw h0w) fun t ⟨ha, ht⟩ => ?_
  have hvalid : Spec.Dsa.generationPLenValid L = false := by
    simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨n1, n2⟩, n3⟩
  simp only [InitPost, hvalid, Bool.false_eq_true, ↓reduceIte]
  exact ⟨ha, by rw [ht, hmw']⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 32⟩] ∧ (s.gpr .x0).toNat + 32 ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  match Spec.Dsa.parameterInit (s.gpr .x1).toNat with
  | none => ((t.gpr .x0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = List.replicate 4 0
  | some values => ((t.gpr .x0).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
      Spec.Entropy.RequestValid (Spec.Dsa.parameterEntropy (s.gpr .x1).toNat) 0 first

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem result_post {s t : State} (h : InitPost (s.gpr .x1).toNat s.mem (s.gpr .x0) t) :
    initPost s t := by
  unfold InitPost at h
  unfold initPost Spec.Dsa.parameterInit
  split at h
  · rename_i hv
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
    have hp : 0 < (s.gpr .x1).toNat := by
      simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv
      omega
    refine ⟨by rw [h.1]; rfl, 512 * (s.gpr .x1).toNat, ?_, ?_⟩
    · rw [h.2, words, written_words]
      rfl
    · unfold Spec.Entropy.RequestValid Spec.Dsa.parameterEntropy
      omega
  · rename_i hv
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    exact ⟨by rw [h.1]; rfl, by rw [h.2, written_words]; rfl⟩

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom⟩ := h
  have scr : Scr s (s.gpr .x0) 32 := Scr.of_mem (by rw [hwr]; simp) hroom
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.x0, .x9, .x10] (init_ok scr rfl) (by decide +kernel)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩, result_post hp⟩

def InitInput (p : Addr × BitVec 64) (s : State) : Prop :=
  s.gpr .x0 = p.1 ∧ s.gpr .x1 = p.2

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have ct : RelCT isa (Two InitInput) init fun _ _ => True :=
    two_taint [.x0, .x1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hsp, hx0, hx1⟩ := h
  exact ⟨(s.gpr .x0, s.gpr .x1), ⟨rfl, rfl⟩, ⟨hx0.symm, hx1.symm⟩, hsp⟩

def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.Dsa.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Dsa.AArch64.ParameterSearchInit
