module

public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Starting the DSA parameter search on x86-64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.ParameterSearchInit

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ParameterSearch
open VG.Proof.RsaKeyGen.SearchInit (written written_words shl_ofNat add_ofNat)

/-- The four words `parameterInit` gives for a supported width `L`. -/
def words (L : Nat) : List (BitVec 64) :=
  [BitVec.ofNat 64 4096, BitVec.ofNat 64 L, BitVec.ofNat 64 (32769 * L), BitVec.ofNat 64 (512 * L)]

/-! ## The two blocks -/

theorem words_ok {s : State} {B : Addr} {L : Nat} (scr : Scr s B 32) (hdi : s.gpr .rdi = B)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 L) (hL : L ≤ 384) :
    WP isa (.block initWords) s fun t => t.gpr .rax = 1 ∧ t.mem = written s.mem B (words L) := by
  have h0 : InRegions s.wr B 8 := by
    have h := scr.st (d := 0) (by decide)
    rwa [off, BitVec.add_zero] at h
  have h1 : InRegions s.wr (B + BitVec.ofNat 64 8) 8 := scr.st (d := 8) (by decide)
  have h2 : InRegions s.wr (B + BitVec.ofNat 64 16) 8 := scr.st (d := 16) (by decide)
  have h3 : InRegions s.wr (B + BitVec.ofNat 64 24) 8 := scr.st (d := 24) (by decide)
  have h15 := shl_ofNat L 15 (by omega_using [hL])
  have h9 := shl_ofNat L 9 (by omega_using [hL])
  have e32769 : BitVec.ofNat 64 (L * 2 ^ 15) + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    rw [add_ofNat]; congr 1; omega
  have e512 : BitVec.ofNat 64 (L * 2 ^ 9) = BitVec.ofNat 64 (512 * L) := by congr 1; omega
  unfold written words initWords
  have hw : BitVec.setWidth 64 (4096 : BitVec 32) = BitVec.ofNat 64 4096 := by decide
  xrun [State.ea, BitVec.ofInt_ofNat, hw, hdi, hsi, h15, h9, e32769, e512,
    h0, h1, h2, h3, off, List.getD_cons_zero, List.getD_cons_succ]

theorem zeros_ok {s : State} {B : Addr} (scr : Scr s B 32) (hdi : s.gpr .rdi = B) :
    WP isa (.block initZeros) s fun t => t.gpr .rax = 0 ∧ t.mem = written s.mem B [0, 0, 0, 0] := by
  have h0 : InRegions s.wr B 8 := by
    have h := scr.st (d := 0) (by decide)
    rwa [off, BitVec.add_zero] at h
  have h1 : InRegions s.wr (B + BitVec.ofNat 64 8) 8 := scr.st (d := 8) (by decide)
  have h2 : InRegions s.wr (B + BitVec.ofNat 64 16) 8 := scr.st (d := 16) (by decide)
  have h3 : InRegions s.wr (B + BitVec.ofNat 64 24) 8 := scr.st (d := 24) (by decide)
  unfold written initZeros
  have hw : BitVec.setWidth 64 (0 : BitVec 32) = (0 : BitVec 64) := by decide
  xrun [State.ea, BitVec.ofInt_ofNat, hw, hdi,
    h0, h1, h2, h3, off, List.getD_cons_zero, List.getD_cons_succ]

/-! ## The guards -/

/-- `cmp rsi, c` for an immediate `c` that sign-extends to `n`. -/
theorem eq_guard (s : State) (c : BitVec 32) (n : Nat) (hn : n < 2 ^ 31)
    (hc : BitVec.signExtend 64 c = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun t =>
      (eval .e t = some (decide ((s.gpr .rsi).toNat = n)) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t =>
    eval .e t = some (decide ((s.gpr .rsi).toNat = n)) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi) ?_ rfl) fun t ⟨⟨he, hm, hr⟩, k⟩ => ⟨⟨he, hm⟩, ⟨fun q _ => by
      by_cases hq : q = .rsi
      · subst hq; exact hr
      · exact k.gpr (by simpa only [List.mem_singleton] using hq), k.2⟩⟩
  xrun [hc, eval]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
  have hz : (0 : BitVec 64) + BitVec.ofNat 64 n = BitVec.ofNat 64 n := BitVec.zero_add _
  constructor
  · intro h; rw [h, hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · intro h; rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact (BitVec.zero_add _).symm

/-! ## The whole initialization -/

/-- The four words written, or zeros. -/
def InitPost (L : Nat) (m : Mem) (B : Addr) (t : State) : Prop :=
  if Spec.Dsa.generationPLenValid L then t.gpr .rax = 1 ∧ t.mem = written m B (words L)
  else t.gpr .rax = 0 ∧ t.mem = written m B [0, 0, 0, 0]

private theorem keep_gpr {a b : State} (k : Keep [] a b) (r : Reg) : b.gpr r = a.gpr r :=
  k.gpr (by simp)

private theorem words_post {t : State} {B : Addr} {L : Nat} {m : Mem} (scr : Scr t B 32)
    (hdi : t.gpr .rdi = B) (hsi : t.gpr .rsi = BitVec.ofNat 64 L) (hm : t.mem = m)
    (hv : L = 128 ∨ L = 256 ∨ L = 384) :
    WP isa (.block initWords) t (InitPost L m B) := by
  refine WP.mono (words_ok scr hdi hsi (by omega)) fun u ⟨ha, hu⟩ => ?_
  have hvalid : Spec.Dsa.generationPLenValid L = true := by
    rcases hv with rfl | rfl | rfl <;> rfl
  simp only [InitPost, hvalid, ↓reduceIte]
  exact ⟨ha, by rw [hu, hm]⟩

theorem init_ok {s : State} {B : Addr} (scr : Scr s B 32) (hdi : s.gpr .rdi = B) :
    WP isa init s (InitPost (s.gpr .rsi).toNat s.mem B) := by
  let L := (s.gpr .rsi).toNat
  change WP isa init s (InitPost L s.mem B)
  have hsL : s.gpr .rsi = BitVec.ofNat 64 L := by
    simp only [L, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold init
  refine WP.seq (WP.mono (eq_guard s 128 128 (by decide) (by decide)) fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  have hdu : u.gpr .rdi = B := (keep_gpr k _).trans hdi
  have hsu : u.gpr .rsi = BitVec.ofNat 64 L := (keep_gpr k _).trans hsL
  have scu : Scr u B 32 := scr.congr k.2.2
  refine WP.ite _ he (fun h => words_post scu hdu hsu hm (Or.inl (of_decide_eq_true h))) fun h1 => ?_
  have h1 : L ≠ 128 := of_decide_eq_false h1
  refine WP.seq (WP.mono (eq_guard u 256 256 (by decide) (by decide)) fun v ⟨⟨he, hmv⟩, kv⟩ => ?_)
  rw [keep_gpr k] at he
  have hdv : v.gpr .rdi = B := (keep_gpr kv _).trans hdu
  have hsv : v.gpr .rsi = BitVec.ofNat 64 L := (keep_gpr kv _).trans hsu
  have scv : Scr v B 32 := scu.congr kv.2.2
  have hmv' : v.mem = s.mem := hmv.trans hm
  refine WP.ite _ he (fun h => words_post scv hdv hsv hmv' (Or.inr (Or.inl (of_decide_eq_true h))))
    fun h2 => ?_
  have h2 : L ≠ 256 := of_decide_eq_false h2
  refine WP.seq (WP.mono (eq_guard v 384 384 (by decide) (by decide)) fun w ⟨⟨he, hmw⟩, kw⟩ => ?_)
  rw [keep_gpr kv, keep_gpr k] at he
  have hdw : w.gpr .rdi = B := (keep_gpr kw _).trans hdv
  have hsw : w.gpr .rsi = BitVec.ofNat 64 L := (keep_gpr kw _).trans hsv
  have scw : Scr w B 32 := scv.congr kw.2.2
  have hmw' : w.mem = s.mem := hmw.trans hmv'
  refine WP.ite _ he (fun h => words_post scw hdw hsw hmw' (Or.inr (Or.inr (of_decide_eq_true h))))
    fun h3 => ?_
  have h3 : L ≠ 384 := of_decide_eq_false h3
  refine WP.mono (zeros_ok scw hdw) fun t ⟨ha, ht⟩ => ?_
  have hvalid : Spec.Dsa.generationPLenValid L = false := by
    simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨h1, h2⟩, h3⟩
  simp only [InitPost, hvalid, Bool.false_eq_true, ↓reduceIte]
  exact ⟨ha, by rw [ht, hmw']⟩

/-! ## The contract -/

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 32⟩] ∧ (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩

def initPost (s t : State) : Prop :=
  match Spec.Dsa.parameterInit (s.gpr .rsi).toNat with
  | none => ((t.gpr .rax).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = List.replicate 4 0
  | some values => ((t.gpr .rax).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop :=
  s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem request_zero (L : Nat) : Spec.Dsa.parameterRequest L 0 = 512 * L := by
  simp only [Spec.Dsa.parameterRequest, Spec.Entropy.request, Spec.Dsa.parameterEntropy]
  omega

private theorem result_post {s t : State} (h : InitPost (s.gpr .rsi).toNat s.mem (s.gpr .rdi) t) :
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
  obtain ⟨_, hwr, hroom, hret⟩ := h
  have scr : Scr s (s.gpr .rdi) 32 := Scr.of_mem (by rw [hwr]; simp) hroom
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.rax, .rsi] (init_ok scr rfl) (by decide +kernel)
  have safe : SpSafe init := SpSafe.of_all (Code.all_of_allInstrs (by decide +kernel))
  have hd : init.x86_64Depth = 0 := rfl
  have hf := Exec.stackFrame safe he (by rw [hd]; decide)
  rw [hwr, hd] at hf
  have hr : t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
    refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hret
    · exact Offset.base_disjoint_below _ (by decide)
  refine ⟨tr, t, he, abiPreserved_of_exec (by decide +kernel) he ⟨?_, hr⟩, result_post hp⟩
  intro r hr
  exact k.gpr (by revert r; decide)

def InitInput (p : Addr × BitVec 64) (s : State) : Prop :=
  s.gpr .rdi = p.1 ∧ s.gpr .rsi = p.2

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have ct : RelCT isa (Two InitInput) init fun _ _ => True :=
    two_taint [.rdi, .rsi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hdi, hsi⟩ := h
  exact ⟨(s.gpr .rdi, s.gpr .rsi), ⟨rfl, rfl⟩, hdi.symm, hsi.symm⟩

private def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rsp => 0x3000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.Dsa.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Dsa.X86_64.ParameterSearchInit
