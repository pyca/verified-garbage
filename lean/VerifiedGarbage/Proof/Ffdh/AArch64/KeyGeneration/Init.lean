module

public import VerifiedGarbage.Impl.Ffdh.AArch64.KeyGeneration.Init
import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Ffdh.AArch64.KeyGeneration.Init
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Native FFDH key-generation initialization on AArch64: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (controller_store_word)
open VG.Impl.Ffdh.AArch64.KeyGeneration

/-- The four public words written. -/
def initWritten (m : Mem) (B : Addr) (a b : BitVec 64) : Mem :=
  (((m.writeW B a).writeW (off B 8) a).writeW (off B 16) b).writeW (off B 24) b

theorem initWritten_words (m : Mem) (B : Addr) (a b : BitVec 64) :
    Spec.Rsa.wordsAt (initWritten m B a b) B 4 = [a, a, b, b] := by
  change [word (initWritten m B a b) B (8 * 0), word (initWritten m B a b) B (8 * 1),
    word (initWritten m B a b) B (8 * 2), word (initWritten m B a b) B (8 * 3)] = _
  have hm : initWritten m B a b =
      (((m.writeW (off B (8 * 0)) a).writeW (off B (8 * 1)) a).writeW (off B (8 * 2)) b).writeW
        (off B (8 * 3)) b := by
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

/-- `validate`: `x13` is 1 exactly for a width in `64..=1024`. -/
theorem validate_ok (s : State) :
    WP isa (.block validate) s fun t =>
      (t.gpr .x13 = (if 64 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 1024 then 1 else 0) ∧
        t.mem = s.mem) ∧ Keep [.x9, .x10, .x11, .x12, .x13, .x14] s t := by
  obtain ⟨n, hl, hx⟩ : ∃ n, n < 2 ^ 64 ∧ s.gpr .x1 = BitVec.ofNat 64 n :=
    ⟨_, (s.gpr .x1).isLt, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  refine WP.keep [.x9, .x10, .x11, .x12, .x13, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  unfold validate
  brun [hx, imm64 (show 64 < 65536 by decide), imm64 (show 1025 < 65536 by decide),
    imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide), subs_ge hl (show 64 < 2 ^ 64 by decide), subs_ge hl (show 1025 < 2 ^ 64 by decide)]
  split_ifs <;> simp only [decide_eq_true_eq] at * <;>
    first | rfl | (exfalso; omega)

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 128) (h0 : s.gpr .x0 = B) :
    WP isa (.block clear) s fun t => t.gpr .x0 = 0 ∧ t.mem = initWritten s.mem B 0 0 := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  unfold clear initWritten
  brun [h0, imm64 (show 0 < 65536 by decide), h00, scr.st (d := 8) (by decide), scr.st (d := 16) (by decide),
    scr.st (d := 24) (by decide)]
  rfl

theorem initialize_ok {s : State} {B : Addr} (scr : Scr s B 128) (h0 : s.gpr .x0 = B) :
    WP isa (.block initializeState) s fun t => t.gpr .x0 = 1 ∧
      t.mem = initWritten s.mem B (BitVec.ofNat 64 128) (s.gpr .x1) := by
  have h00 : InRegions s.wr B 8 := by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)
  unfold initializeState initWritten
  brun [h0, imm64 (show 128 < 65536 by decide), imm64 (show 1 < 65536 by decide), h00,
    scr.st (d := 8) (by decide), scr.st (d := 16) (by decide), scr.st (d := 24) (by decide)]

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 128⟩] ∧ (s.gpr .x0).toNat + 128 ≤ 2 ^ 64

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.keyInit (s.gpr .x1).toNat with
  | none => ((t.gpr .x0).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = List.replicate 4 0
  | some values => ((t.gpr .x0).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x0) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

theorem init_ok {s : State} (scr : Scr s (s.gpr .x0) 128) :
    WP isa init s (initPost s) := by
  unfold init
  refine WP.seq (WP.mono (validate_ok s) fun u ⟨⟨h13, hm⟩, k⟩ => ?_)
  have scr' := scr.congr k.wr
  have h0 : u.gpr .x0 = s.gpr .x0 := k.gpr .x0 (by decide)
  have h1 : u.gpr .x1 = s.gpr .x1 := k.gpr .x1 (by decide)
  by_cases hv : 64 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 1024
  · rw [ite_eq_left hv] at h13
    refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl) (fun h => by cases h)
      fun _ => WP.mono (initialize_ok scr' h0) fun t ⟨ht, hmt⟩ => ?_
    have he : Spec.Ffdh.keyInit (s.gpr .x1).toNat =
        some [128, 128, (s.gpr .x1).toNat, (s.gpr .x1).toNat] := by
      simp [Spec.Ffdh.keyInit, hv.1, hv.2]
    simp only [initPost, he]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, hm, h1, initWritten_words]
    simp only [List.map_cons, List.map_nil, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [ite_eq_right hv] at h13
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, h13]; rfl)
      (fun _ => WP.mono (clear_ok scr' h0) fun t ⟨ht, hmt⟩ => ?_) fun h => by cases h
    have he : Spec.Ffdh.keyInit (s.gpr .x1).toNat = none := by
      simp only [Spec.Ffdh.keyInit]
      exact ite_eq_right (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hv)
    simp only [initPost, he]
    refine ⟨by rw [ht]; rfl, ?_⟩
    rw [hmt, initWritten_words]
    rfl

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom⟩ := h
  have scr : Scr s (s.gpr .x0) 128 := Scr.of_mem (by rw [hwr]; simp) hroom
  obtain ⟨tr, t, he, hp, k⟩ := WP.keep [.x0, .x9, .x10, .x11, .x12, .x13, .x14] (init_ok scr)
    (by decide +kernel)
  exact ⟨tr, t, he, ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩, hp⟩

def InitInput (p : Addr × BitVec 64) (s : State) : Prop := s.gpr .x0 = p.1 ∧ s.gpr .x1 = p.2

/-- After `validate`: `x13` is a function of the public width. -/
def InitValid (p : Addr × BitVec 64) (s : State) : Prop :=
  InitInput p s ∧ s.gpr .x13 = (if 64 ≤ p.2.toNat ∧ p.2.toNat ≤ 1024 then 1 else 0)

private theorem validate_ready (p : Addr × BitVec 64) (s : State) (h : InitInput p s) :
    WP isa (.block validate) s (InitValid p) :=
  WP.mono (validate_ok s) fun _ ⟨⟨h13, _⟩, k⟩ =>
    ⟨⟨(k.gpr .x0 (by decide)).trans h.1, (k.gpr .x1 (by decide)).trans h.2⟩, by rw [h13, h.2]⟩

theorem init_constantTime : ConstantTime isa (fun _ => True) initPub init := by
  have pins : Pins InitInput [.x0, .x1] := fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]
  have pins' : Pins (fun p s => InitValid p s ∧ isa.eval (.zero .x .x13) s = some true) [.x0] :=
    fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h₁.1.1.1.trans h₂.1.1.1.symm
  have pins'' : Pins (fun p s => InitValid p s ∧ isa.eval (.zero .x .x13) s = some false) [.x0] :=
    fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h₁.1.1.1.trans h₂.1.1.1.symm
  have ct : RelCT isa (Two InitInput) init fun _ _ => True := by
    unfold init
    refine RelCT.seq (two_piece [.x0, .x1] pins (by taint_decide) validate_ready) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => ?_) (two_taint [.x0] pins' (by taint_decide))
      (two_taint [.x0] pins'' (by taint_decide))
    rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, h₁.2, h₂.2]
  refine RelCT.constantTime (ct.mono (fun s t h => ?_) fun _ _ h => h)
  obtain ⟨_, _, hsp, hx0, hx1⟩ := h
  exact ⟨(s.gpr .x0, s.gpr .x1), ⟨rfl, rfl⟩, ⟨hx0.symm, hx1.symm⟩, hsp⟩

private def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | _ => 0
  sp := 0x3000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified target init (Spec.Ffdh.keyInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Ffdh.AArch64.KeyGeneration
