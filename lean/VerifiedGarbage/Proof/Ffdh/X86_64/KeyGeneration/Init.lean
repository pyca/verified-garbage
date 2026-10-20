module

public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitGuards
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Init
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitGuards
meta import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Native FFDH key-generation initialization: correctness, constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (controller_store_word cleared clear_ok cleared_words)
open VG.Impl.Ffdh.X86_64.Generation (field clear)
open VG.Impl.Ffdh.X86_64.KeyGeneration

/-- The four public words of `keyInit`. -/
def keyInitialized (m : Mem) (B : Addr) (len : Nat) : Mem :=
  (((m.writeW B (BitVec.ofNat 64 128)).writeW (off B 8) (BitVec.ofNat 64 128)).writeW
    (off B 16) (BitVec.ofNat 64 len)).writeW (off B 24) (BitVec.ofNat 64 len)

theorem initialize_ok {s : State} {B : Addr} {len : Nat}
    (scr : Scr s B 128) (hdi : s.gpr .rdi = B) (hsi : s.gpr .rsi = BitVec.ofNat 64 len) :
    WP isa initializeState s fun t => t.gpr .rax = 1 ∧ t.mem = keyInitialized s.mem B len := by
  have hstore : ∀ j < 4, InRegions s.wr (off B (8 * j)) 8 :=
    fun j hj => scr.st (by omega_using [hj])
  unfold initializeState keyInitialized
  xrun [field, State.ea, off, BitVec.ofInt_natCast, hdi, hsi, hstore 0 (by decide),
    hstore 1 (by decide), hstore 2 (by decide), hstore 3 (by decide)]
  simp only [Nat.reduceMul, BitVec.add_zero]
  rfl

theorem keyInitialized_words (m : Mem) (B : Addr) (len : Nat) :
    Spec.Rsa.wordsAt (keyInitialized m B len) B 4 =
      [BitVec.ofNat 64 128, BitVec.ofNat 64 128, BitVec.ofNat 64 len, BitVec.ofNat 64 len] := by
  change [word (keyInitialized m B len) B 0, word (keyInitialized m B len) B 8,
    word (keyInitialized m B len) B 16, word (keyInitialized m B len) B 24] = _
  have hm : keyInitialized m B len =
      (((m.writeW (off B (8 * 0)) (BitVec.ofNat 64 128)).writeW
        (off B (8 * 1)) (BitVec.ofNat 64 128)).writeW
        (off B (8 * 2)) (BitVec.ofNat 64 len)).writeW
        (off B (8 * 3)) (BitVec.ofNat 64 len) := by
    simp only [keyInitialized, off, Nat.mul_zero, BitVec.add_zero]
  rw [hm]
  have hword (j : Nat) (hj : j < 16) :
      word
        ((((m.writeW (off B (8 * 0)) (BitVec.ofNat 64 128)).writeW
          (off B (8 * 1)) (BitVec.ofNat 64 128)).writeW
          (off B (8 * 2)) (BitVec.ofNat 64 len)).writeW
          (off B (8 * 3)) (BitVec.ofNat 64 len)) B (8 * j) =
        if j = 3 then BitVec.ofNat 64 len else
        if j = 2 then BitVec.ofNat 64 len else
        if j = 1 then BitVec.ofNat 64 128 else
        if j = 0 then BitVec.ofNat 64 128 else word m B (8 * j) := by
    rw [controller_store_word _ _ _ (i := 3) (by decide) hj,
      controller_store_word _ _ _ (i := 2) (by decide) hj,
      controller_store_word _ _ _ (i := 1) (by decide) hj,
      controller_store_word _ _ _ (i := 0) (by decide) hj]
  rw [hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]
  rfl

/-- The full initialization result, including an invalid length. -/
def InitPost (len : Nat) (m : Mem) (B : Addr) (t : State) : Prop :=
  match Spec.Ffdh.keyInit len with
  | none => t.gpr .rax = 0 ∧ t.mem = cleared m B
  | some _ => t.gpr .rax = 1 ∧ t.mem = keyInitialized m B len

private theorem compared_keep {s t : State} {r : Reg}
    (k : Keep [r] s t) (hr : t.gpr r = s.gpr r) : Keep [] s t := by
  refine ⟨fun q _ => ?_, k.2⟩
  by_cases he : q = r
  · subst he; exact hr
  · exact k.gpr (by simpa only [List.mem_singleton] using he)

private theorem lower_guard (s : State) :
    WP isa (.block [.alu .cmp .rsi (.imm 64)]) s fun t =>
      (eval .b t = some (decide ((s.gpr .rsi).toNat < 64)) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t =>
    eval .b t = some (decide ((s.gpr .rsi).toNat < 64)) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi) ?_ rfl) fun t ⟨⟨he, hm, hr⟩, k⟩ =>
        ⟨⟨he, hm⟩, compared_keep k hr⟩
  have h : BitVec.signExtend 64 (64 : BitVec 32) = (64 : BitVec 64) := by decide
  xrun [h, eval]
  rfl

private theorem upper_guard (s : State) :
    WP isa (.block [.alu .cmp .rsi (.imm 1025)]) s fun t =>
      (eval .ae t = some (decide (1025 ≤ (s.gpr .rsi).toNat)) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t =>
    eval .ae t = some (decide (1025 ≤ (s.gpr .rsi).toNat)) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi) ?_ rfl) fun t ⟨⟨he, hm, hr⟩, k⟩ =>
        ⟨⟨he, hm⟩, compared_keep k hr⟩
  have h : BitVec.signExtend 64 (1025 : BitVec 32) = (1025 : BitVec 64) := by decide
  xrun [h, eval]
  change (!decide ((s.gpr .rsi).toNat < 1025)) = decide (1025 ≤ (s.gpr .rsi).toNat)
  by_cases hb : 1025 ≤ (s.gpr .rsi).toNat
  · simp only [show ¬(s.gpr .rsi).toNat < 1025 by omega_using [hb], decide_false,
      Bool.not_false, hb, decide_true]
  · simp only [show (s.gpr .rsi).toNat < 1025 by omega_using [hb], decide_true,
      Bool.not_true, hb, decide_false]

private theorem clear_result {s : State} {B : Addr} {len : Nat} {m : Mem}
    (scr : Scr s B 128) (hdi : s.gpr .rdi = B) (hm : s.mem = m)
    (hinvalid : Spec.Ffdh.keyInit len = none) :
    WP isa clear s (InitPost len m B) := by
  refine WP.mono (clear_ok scr hdi) fun t ⟨ha, ht⟩ => ?_
  simp only [InitPost, hinvalid]
  exact ⟨ha, by simpa only [hm] using ht⟩

theorem init_ok {s : State} {B : Addr} (scr : Scr s B 128) (hdi : s.gpr .rdi = B) :
    WP isa init s (InitPost (s.gpr .rsi).toNat s.mem B) := by
  let len := (s.gpr .rsi).toNat
  change WP isa init s (InitPost len s.mem B)
  unfold init
  refine WP.seq (WP.mono (lower_guard s) fun u ⟨⟨he, hm⟩, k⟩ => ?_)
  change eval .b u = some (decide (len < 64)) at he
  have hdu : u.gpr .rdi = B := (k.gpr (by decide)).trans hdi
  refine WP.ite (decide (len < 64)) he ?_ ?_
  · intro hlow
    refine clear_result (scr.congr k.2.2) hdu hm ?_
    have hn : ¬64 ≤ len := by omega_using [of_decide_eq_true hlow]
    simp [Spec.Ffdh.keyInit, hn]
  · intro hlow
    have hlo : 64 ≤ len := by omega_using [of_decide_eq_false hlow]
    refine WP.seq (WP.mono (upper_guard u) fun v ⟨⟨he2, hm2⟩, kv⟩ => ?_)
    have hbu : (u.gpr .rsi).toNat = len := by rw [k.gpr (by decide)]
    rw [hbu] at he2
    have hdv : v.gpr .rdi = B := (kv.gpr (by decide)).trans hdu
    have hmv : v.mem = s.mem := hm2.trans hm
    refine WP.ite (decide (1025 ≤ len)) he2 ?_ ?_
    · intro hhigh
      refine clear_result ((scr.congr k.2.2).congr kv.2.2) hdv hmv ?_
      have hn : ¬len ≤ 1024 := by omega_using [of_decide_eq_true hhigh]
      simp [Spec.Ffdh.keyInit, hn]
    · intro hhigh
      have hhi : len ≤ 1024 := by omega_using [of_decide_eq_false hhigh]
      have hsv : v.gpr .rsi = BitVec.ofNat 64 len := by
        rw [kv.gpr (by decide), k.gpr (by decide)]
        simp only [len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      refine WP.mono (initialize_ok ((scr.congr k.2.2).congr kv.2.2) hdv hsv) fun t ⟨ha, ht⟩ => ?_
      have hv : Spec.Ffdh.keyInit len = some [128, 128, len, len] := by
        simp [Spec.Ffdh.keyInit, hlo, hhi]
      simp only [InitPost, hv]
      exact ⟨ha, by simpa only [hmv] using ht⟩

def initPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 128⟩] ∧ (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 128⟩

def initPost (s t : State) : Prop :=
  match Spec.Ffdh.keyInit (s.gpr .rsi).toNat with
  | none => ((t.gpr .rax).setWidth 32).toNat = 0 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = List.replicate 4 0
  | some values => ((t.gpr .rax).setWidth 32).toNat = 1 ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .rdi) 4 = values.map (BitVec.ofNat 64)

def initPub (s t : State) : Prop := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi

def initContract : Contract isa where
  pre := initPre
  post := initPost
  pub := initPub

private theorem result_post {s t : State}
    (h : InitPost (s.gpr .rsi).toNat s.mem (s.gpr .rdi) t) : initPost s t := by
  unfold InitPost at h
  unfold initPost
  cases he : Spec.Ffdh.keyInit (s.gpr .rsi).toNat with
  | none =>
    simp only [he] at h
    refine ⟨?_, ?_⟩
    · rw [h.1]; rfl
    · rw [h.2]; exact cleared_words _ _
  | some values =>
    simp only [he] at h
    have hv : values = [128, 128, (s.gpr .rsi).toNat, (s.gpr .rsi).toNat] := by
      unfold Spec.Ffdh.keyInit at he
      split at he
      · exact (Option.some.inj he).symm
      · cases he
    refine ⟨?_, ?_⟩
    · rw [h.1]; rfl
    · rw [h.2, hv, keyInitialized_words]
      rfl

theorem init_correct (s : State) (h : initPre s) :
    ∃ tr t, Exec isa init s tr t ∧ abiPreserved s t ∧ initPost s t := by
  obtain ⟨_, hwr, hroom, hret⟩ := h
  have scr : Scr s (s.gpr .rdi) 128 := Scr.of_mem (by rw [hwr]; simp) hroom
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

def InitInput (p : Addr × BitVec 64) (s : State) : Prop := s.gpr .rdi = p.1 ∧ s.gpr .rsi = p.2

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
    | .rdi => 0x1000 | .rsi => 64 | .rsp => 0x3000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩]

theorem init_verified : Verified target init (Spec.Ffdh.keyInitContract abi) := by
  refine Verified.of_correct (k := initContract) init_correct ?_ ?_
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ _ _ hp h₁ h₂
    exact init_constantTime s₁ s₂ tr₁ tr₂ t₁ t₂ trivial trivial hp h₁ h₂
  · sig_implies [Spec.Ffdh.keyInitContract, Spec.Ffdh.keyInitSig,
      initContract, initPre, initPost, initPub, abi, argRegs] [initSat] using initSat

end VG.Proof.Ffdh.X86_64.KeyGeneration
