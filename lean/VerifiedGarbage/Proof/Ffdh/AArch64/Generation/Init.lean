module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Spec.Ffdh.GenerationContract
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import Mathlib.Tactic.SplitIfs

/-! # Native FFDH parameter-generation initialization on AArch64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (controller_store_word)
open VG.Impl.Ffdh.AArch64.Generation

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
  simp only [controller_store_word _ _ _ (i := 3) (by decide) (by decide : (0 : Nat) < 16),
    controller_store_word _ _ _ (i := 3) (by decide) (by decide : (1 : Nat) < 16),
    controller_store_word _ _ _ (i := 3) (by decide) (by decide : (2 : Nat) < 16),
    controller_store_word _ _ _ (i := 3) (by decide) (by decide : (3 : Nat) < 16),
    controller_store_word _ _ _ (i := 2) (by decide) (by decide : (0 : Nat) < 16),
    controller_store_word _ _ _ (i := 2) (by decide) (by decide : (1 : Nat) < 16),
    controller_store_word _ _ _ (i := 2) (by decide) (by decide : (2 : Nat) < 16),
    controller_store_word _ _ _ (i := 1) (by decide) (by decide : (0 : Nat) < 16),
    controller_store_word _ _ _ (i := 1) (by decide) (by decide : (1 : Nat) < 16),
    controller_store_word _ _ _ (i := 0) (by decide) (by decide : (0 : Nat) < 16),
    Nat.reduceEqDiff, ite_true, ite_false]

theorem imm64 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Whether `init` accepts `bits` and the generator. -/
def initValid (bits g : Nat) : Prop := 512 ≤ bits ∧ bits ≤ 8192 ∧ (g = 2 ∨ g = 5)

instance (bits g : Nat) : Decidable (initValid bits g) := by unfold initValid; infer_instance

theorem zext32 (x : BitVec 64) :
    ((x.setWidth 32 + BitVec.ofNat 32 0).setWidth 64) = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `validate`: `x13` is 1 exactly for valid parameters. -/
theorem validate_ok (s : State) :
    WP isa (.block validate) s fun t =>
      (t.gpr .x13 = (if initValid (s.gpr .x1).toNat ((s.gpr .x2).setWidth 32).toNat then 1 else 0) ∧
        t.mem = s.mem) ∧ Keep [.x2, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .x1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .x1).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  obtain ⟨g, hg, hgx⟩ : ∃ g, g < 2 ^ 32 ∧ ((s.gpr .x2).setWidth 32).toNat = g := ⟨_, BitVec.isLt _, rfl⟩
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, hgx]
  refine WP.keep [.x2, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] ?_ (by decide) (by decide)
    (by decide +kernel)
  unfold validate
  brun [hx, VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), zext32, hgx, imm64 (show 512 < 65536 by decide),
    imm64 (show 8193 < 65536 by decide), imm64 (show 2 < 65536 by decide), imm64 (show 3 < 65536 by decide),
    imm64 (show 5 < 65536 by decide), imm64 (show 6 < 65536 by decide),
    imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
    subs_ge hl (show 512 < 2 ^ 64 by decide), subs_ge hl (show 8193 < 2 ^ 64 by decide),
    subs_ge (show g < 2 ^ 64 by omega) (show 2 < 2 ^ 64 by decide),
    subs_ge (show g < 2 ^ 64 by omega) (show 3 < 2 ^ 64 by decide),
    subs_ge (show g < 2 ^ 64 by omega) (show 5 < 2 ^ 64 by decide),
    subs_ge (show g < 2 ^ 64 by omega) (show 6 < 2 ^ 64 by decide)]
  by_cases hv : initValid n g
  · rw [ite_eq_left hv]
    obtain ⟨h1, h2, h3⟩ := hv
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> first | rfl | (exfalso; omega)
  · rw [ite_eq_right hv]
    simp only [initValid, not_and, not_or] at hv
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> first | rfl | (exfalso; omega)

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 128) (h0 : s.gpr .x0 = B) :
    WP isa (.block clear) s fun t => t.gpr .x0 = 0 ∧ t.mem = initWritten s.mem B 0 0 0 0 := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  unfold clear initWritten
  brun [h0, imm64 (show 0 < 65536 by decide), h00, scr.st (d := 8) (by decide), scr.st (d := 16) (by decide),
    scr.st (d := 24) (by decide)]
  rfl

theorem shift_ofNat (n k : Nat) : (BitVec.ofNat 64 n) <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod]

theorem initialize_ok {s : State} {B : Addr} {bits : Nat} (scr : Scr s B 128) (h0 : s.gpr .x0 = B)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 bits) (hhi : bits ≤ 8192) :
    WP isa (.block initializeState) s fun t => t.gpr .x0 = 1 ∧
      t.mem = initWritten s.mem B (BitVec.ofNat 64 (Spec.Ffdh.parameterAttempts bits))
        (BitVec.ofNat 64 ((bits + 7) / 8)) (BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy bits))
        (BitVec.ofNat 64 (512 * ((bits + 7) / 8))) := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  have hw : (BitVec.ofNat 64 bits + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have hm : (BitVec.ofNat 64 bits * BitVec.ofNat 64 bits) <<< 6 = BitVec.ofNat 64 (bits * bits * 64) := by
    rw [← BitVec.ofNat_mul, shift_ofNat]
  have hc : BitVec.ofNat 64 ((bits + 7) / 8) <<< 15 + BitVec.ofNat 64 ((bits + 7) / 8) =
      BitVec.ofNat 64 (32769 * ((bits + 7) / 8)) := by
    rw [shift_ofNat, ← BitVec.ofNat_add]
    congr 1
    simp only [Nat.reducePow]
    omega
  have hr : BitVec.ofNat 64 ((bits + 7) / 8) <<< 9 = BitVec.ofNat 64 (512 * ((bits + 7) / 8)) := by
    rw [shift_ofNat]
    congr 1
    simp only [Nat.reducePow]
    omega
  unfold initializeState initWritten Spec.Ffdh.parameterAttempts Spec.Ffdh.parameterEntropy
  brun [h0, h1, imm64 (show 1 < 65536 by decide), h00, scr.st (d := 8) (by decide), scr.st (d := 16) (by decide),
    scr.st (d := 24) (by decide), hw, hm, hc, hr]

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 128⟩] ∧ (s.gpr .x0).toNat + 128 ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.parameterInit (s.gpr .x1).toNat ((s.gpr .x2).setWidth 32).toNat with
  | none => ((t.gpr .x0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = List.replicate 4 0
  | some values => ((t.gpr .x0).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop :=
  s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ (s.gpr .x2).setWidth 32 = (t.gpr .x2).setWidth 32

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem parameterInit_of {bits g : Nat} (h : initValid bits g) :
    Spec.Ffdh.parameterInit bits g = some [Spec.Ffdh.parameterAttempts bits, (bits + 7) / 8,
      Spec.Ffdh.parameterEntropy bits, 512 * ((bits + 7) / 8)] := by
  obtain ⟨h1, h2, h3⟩ := h
  have hg : (g == 2 || g == 5) = true := by rcases h3 with rfl | rfl <;> rfl
  simp [Spec.Ffdh.parameterInit, h1, h2, hg]

theorem parameterInit_none {bits g : Nat} (h : ¬initValid bits g) : Spec.Ffdh.parameterInit bits g = none := by
  unfold Spec.Ffdh.parameterInit
  refine ite_eq_right ?_
  intro hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hc
  exact h ⟨hc.1.1, hc.1.2, hc.2⟩

theorem init_ok {s : State} (scr : Scr s (s.gpr .x0) 128) :
    WP isa init s (initPost s) := by
  unfold init
  refine WP.seq (WP.mono (validate_ok s) fun u ⟨⟨h13, hm⟩, k⟩ => ?_)
  have scr' := scr.congr k.wr
  have h0 : u.gpr .x0 = s.gpr .x0 := k.gpr .x0 (by decide)
  have h1 : u.gpr .x1 = s.gpr .x1 := k.gpr .x1 (by decide)
  by_cases hv : initValid (s.gpr .x1).toNat ((s.gpr .x2).setWidth 32).toNat
  · rw [ite_eq_left hv] at h13
    have hb : u.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [h1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl) (fun h => by cases h)
      fun _ => WP.mono (initialize_ok scr' h0 hb hv.2.1) fun t ⟨ht, hmt⟩ => ?_
    simp only [initPost, parameterInit_of hv]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, hm, initWritten_words]
    rfl
  · rw [ite_eq_right hv] at h13
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl)
      (fun _ => WP.mono (clear_ok scr' h0) fun t ⟨ht, hmt⟩ => ?_) fun h => by cases h
    simp only [initPost, parameterInit_none hv]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, initWritten_words]
    rfl

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom⟩ := h
  have scr : Scr s (s.gpr .x0) 128 := Scr.of_mem (by rw [hwr]; simp) hroom
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.x0, .x2, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]
    (init_ok scr) (by decide +kernel)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩, hp⟩

def InitInput (p : Addr × BitVec 64 × BitVec 32) (s : State) : Prop :=
  s.gpr .x0 = p.1 ∧ s.gpr .x1 = p.2.1 ∧ (s.gpr .x2).setWidth 32 = p.2.2

/-- After `validate`: `x13` is a function of the public arguments. -/
def InitValid (p : Addr × BitVec 64 × BitVec 32) (s : State) : Prop :=
  s.gpr .x0 = p.1 ∧ s.gpr .x13 = (if initValid p.2.1.toNat p.2.2.toNat then 1 else 0)

private theorem validate_ready (p : Addr × BitVec 64 × BitVec 32) (s : State) (h : InitInput p s) :
    WP isa (.block validate) s (InitValid p) :=
  WP.mono (validate_ok s) fun _ ⟨⟨h13, _⟩, k⟩ =>
    ⟨(k.gpr .x0 (by decide)).trans h.1, by rw [h13, h.2.1, h.2.2]⟩

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have pins : Pins InitInput [.x0] := fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h₁.1.trans h₂.1.symm
  have pins' : Pins (fun p s => InitValid p s ∧ isa.eval (.zero .x .x13) s = some true) [.x0] :=
    fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h₁.1.1.trans h₂.1.1.symm
  have pins'' : Pins (fun p s => InitValid p s ∧ isa.eval (.zero .x .x13) s = some false) [.x0] :=
    fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h₁.1.1.trans h₂.1.1.symm
  have ct : RelCT isa (Two InitInput) init fun _ _ => True := by
    unfold init
    refine RelCT.seq (two_piece [.x0] pins (by taint_decide) validate_ready) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => ?_) (two_taint [.x0] pins' (by taint_decide))
      (two_taint [.x0] pins'' (by taint_decide))
    rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, h₁.2, h₂.2]
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hsp, hx0, hx1, hx2⟩ := h
  exact ⟨(s.gpr .x0, s.gpr .x1, (s.gpr .x2).setWidth 32), ⟨rfl, rfl, rfl⟩, ⟨hx0.symm, hx1.symm, hx2.symm⟩, hsp⟩

private def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 512 | .x2 => 2 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified target init (Spec.Ffdh.parameterInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Ffdh.parameterInitContract, Spec.Ffdh.parameterInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Ffdh.AArch64.Generation
