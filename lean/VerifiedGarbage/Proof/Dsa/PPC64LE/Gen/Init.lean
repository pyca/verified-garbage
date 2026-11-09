module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Generation
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.InitCommon
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Starting the DSA parameter search on PPC64LE: correctness, constant time

`init` writes `[4096, p_len, 32769 p_len, 512 p_len]` and returns 1 for a
supported width, else zeros and 0; it branches on `p_len` alone, which is
public, as is the state's address.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen

open VG VG.PPC64LE VG.Proof.Ffdh.PPC64LE VG.Impl.Dsa.PPC64LE.Generation

/-- The state's 32 bytes, the only region the code may write. -/
def InitWr (s : State) : Prop :=
  s.wr = [⟨s.gpr .r3, 32⟩] ∧ (s.gpr .r3).toNat + 32 ≤ 2 ^ 64

theorem InitWr.st {s : State} (h : InitWr s) (d : Nat) (hd : d + 8 ≤ 32) :
    InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 d) 8 := by
  rw [h.1]
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩

theorem InitWr.st0 {s : State} (h : InitWr s) : InRegions s.wr (s.gpr .r3) 8 := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h.st 0 (by decide)

theorem initWords_ok {s : State} (h : InitWr s) {L : Nat} (hL : s.gpr .r4 = BitVec.ofNat 64 L) :
    WP isa (.block initWords) s fun t => t.gpr .r3 = 1 ∧
      t.mem = initWritten s.mem (s.gpr .r3) (BitVec.ofNat 64 4096) (BitVec.ofNat 64 L)
        (BitVec.ofNat 64 (32769 * L)) (BitVec.ofNat 64 (512 * L)) := by
  have hc : BitVec.ofNat 64 L <<< 15 + BitVec.ofNat 64 L = BitVec.ofNat 64 (32769 * L) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have hr : BitVec.ofNat 64 L <<< 9 = BitVec.ofNat 64 (512 * L) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  unfold initWords initWritten
  crunr [hL, hc, hr, h.st0, h.st 8 (by decide), h.st 16 (by decide), h.st 24 (by decide)]
  rfl

theorem initZeros_ok {s : State} (h : InitWr s) :
    WP isa (.block initZeros) s fun t => t.gpr .r3 = 0 ∧ t.mem = initWritten s.mem (s.gpr .r3) 0 0 0 0 := by
  unfold initZeros initWritten
  crunr [h.st0, h.st 8 (by decide), h.st 16 (by decide), h.st 24 (by decide)]
  rfl

/-- `subi r0, r4, c`: whether `p_len` is `c`. -/
theorem initGuard_ok (s : State) {L : Nat} (hL : s.gpr .r4 = BitVec.ofNat 64 L) (hl : L < 2 ^ 64) {c : Nat}
    (hc : c ≤ 2 ^ 15) :
    WP isa (.block [.subi .r0 .r4 c]) s fun t =>
      isa.eval (.zero .d .r0) t = some (decide (L = c)) ∧ Keep [.r0] s t ∧ t.mem = s.mem := by
  refine wp_subi (d := .r0) (by decide) hc fun t u => WP.block_nil ⟨?_, ⟨fun r hr => u.other r (by simpa using hr),
    u.rd, u.wr⟩, u.mem⟩
  rw [eval_zero, u.gpr, hL]
  by_cases e : L = c
  · subst e; simp
  · rw [decide_eq_false e]
    refine congrArg some (beq_false_of_ne fun e' => e ?_)
    have e'' : BitVec.ofNat 64 L = BitVec.ofNat 64 c := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 L) (BitVec.ofNat 64 c), e']; simp
    have := congrArg BitVec.toNat e''
    simp only [BitVec.toNat_ofNat] at this
    omega

def initPre (s : State) : Prop := s.rd = [] ∧ InitWr s

def initPost (s t : State) : Prop :=
  match Spec.Dsa.parameterInit (s.gpr .r4).toNat with
  | none => ((t.gpr .r3).setWidth 32).toNat = 0 ∧ Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = List.replicate 4 0
  | some values => ((t.gpr .r3).setWidth 32).toNat = 1 ∧ ∃ first,
      Spec.Rsa.wordsAt t.mem (s.gpr .r3) 4 = (values ++ [first]).map (BitVec.ofNat 64) ∧
      Spec.Entropy.RequestValid (Spec.Dsa.parameterEntropy (s.gpr .r4).toNat) 0 first

def initPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem initWords_post {s u : State} {rs : List Reg} (h : InitWr s) (k : Keep rs s u) (hr : .r3 ∉ rs)
    (h4 : .r4 ∉ rs) (hm : u.mem = s.mem) (hv : Spec.Dsa.generationPLenValid (s.gpr .r4).toNat = true) :
    WP isa (.block initWords) u (initPost s) := by
  have h3 : u.gpr .r3 = s.gpr .r3 := k.gpr hr
  have hu : InitWr u := by rw [InitWr, k.2.2, h3]; exact h
  have hp : 0 < (s.gpr .r4).toNat := by
    simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv; omega
  refine WP.mono (initWords_ok hu (L := (s.gpr .r4).toNat) (by rw [k.gpr h4, BitVec.ofNat_toNat,
    BitVec.setWidth_eq])) fun t ⟨ht, hmt⟩ => ?_
  simp only [initPost, Spec.Dsa.parameterInit, hv, ↓reduceIte]
  refine ⟨by rw [ht]; rfl, 512 * (s.gpr .r4).toNat, ?_, ?_⟩
  · rw [hmt, hm, h3, initWritten_words]; rfl
  · unfold Spec.Entropy.RequestValid Spec.Dsa.parameterEntropy; omega

theorem initZeros_post {s u : State} {rs : List Reg} (h : InitWr s) (k : Keep rs s u) (hr : .r3 ∉ rs)
    (hm : u.mem = s.mem) (hv : Spec.Dsa.generationPLenValid (s.gpr .r4).toNat = false) :
    WP isa (.block initZeros) u (initPost s) := by
  have h3 : u.gpr .r3 = s.gpr .r3 := k.gpr hr
  have hu : InitWr u := by rw [InitWr, k.2.2, h3]; exact h
  refine WP.mono (initZeros_ok hu) fun t ⟨ht, hmt⟩ => ?_
  simp only [initPost, Spec.Dsa.parameterInit, hv, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by rw [ht]; rfl, by rw [hmt, hm, h3, initWritten_words]; rfl⟩

theorem init_ok {s : State} (h : InitWr s) : WP isa init s (initPost s) := by
  have hL : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hl := (s.gpr .r4).isLt
  unfold init
  refine WP.seq (WP.mono (initGuard_ok s hL hl (c := 128) (by decide)) fun u ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.ite _ e₁ (fun h₁ => initWords_post h k₁ (by decide) (by decide) m₁ (by
    simp [Spec.Dsa.generationPLenValid, of_decide_eq_true h₁])) fun h₁ => ?_
  have hu : u.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := (k₁.gpr (by decide)).trans hL
  refine WP.seq (WP.mono (initGuard_ok u hu hl (c := 256) (by decide)) fun v ⟨e₂, k₂, m₂⟩ => ?_)
  have k₂' := k₁.trans k₂
  refine WP.ite _ e₂ (fun h₂ => initWords_post h k₂' (by decide) (by decide) (m₂.trans m₁) (by
    simp [Spec.Dsa.generationPLenValid, of_decide_eq_true h₂])) fun h₂ => ?_
  have hv : v.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := (k₂.gpr (by decide)).trans hu
  refine WP.seq (WP.mono (initGuard_ok v hv hl (c := 384) (by decide)) fun w ⟨e₃, k₃, m₃⟩ => ?_)
  have k₃' := k₂'.trans k₃
  refine WP.ite _ e₃ (fun h₃ => initWords_post h k₃' (by decide) (by decide)
    (m₃.trans (m₂.trans m₁)) (by simp [Spec.Dsa.generationPLenValid, of_decide_eq_true h₃])) fun h₃ => ?_
  refine initZeros_post h k₃' (by decide) (m₃.trans (m₂.trans m₁)) ?_
  simp [Spec.Dsa.generationPLenValid, of_decide_eq_false h₁, of_decide_eq_false h₂, of_decide_eq_false h₃]

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.r0, .r3, .r5] (init_ok h.2) (by decide +kernel)
  exact ⟨tr, t, he, abiPreserved_of_keep he k (by decide) (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), hp⟩

theorem init_relCT (B : Addr) (L : BitVec 64) (sp : Addr) :
    RelCT isa (fun s₁ s₂ => (s₁.gpr .r3 = B ∧ s₁.gpr .r4 = L ∧ s₁.sp = sp) ∧
      (s₂.gpr .r3 = B ∧ s₂.gpr .r4 = L ∧ s₂.sp = sp)) init fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r3, .r4]) (fun s₁ s₂ ⟨⟨a3, a4, asp⟩, ⟨b3, b4, bsp⟩⟩ =>
    ⟨asp.trans bsp.symm, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact a3.trans b3.symm
      · exact a4.trans b4.symm⟩) (by taint_decide)

private def initSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 128 | _ => 0
  lr := 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 32⟩]

theorem init_verified : Verified target init (Spec.Dsa.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp e₁ e₂
    obtain ⟨hsp, h3, h4⟩ := hp
    exact (init_relCT (s₁.gpr .r3) (s₁.gpr .r4) s₁.sp _ _ _ _ _ _ ⟨⟨rfl, rfl, rfl⟩, ⟨h3.symm, h4.symm, hsp.symm⟩⟩
      e₁ e₂).1
  · sig_implies [Spec.Dsa.parameterInitContract, Spec.Dsa.parameterInitSig,
      initContract, initPre, initPost, initPub, InitWr, abi, argRegs] [initSat] using initSat

end VG.Proof.Dsa.PPC64LE.Gen
