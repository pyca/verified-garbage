module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Attempt
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on PPC64LE: the controller

`sLoop_vp`: the seeds, one at a time from the cursor `fC`, with `fSeedLeft`
seeds left, until one gives a domain (`fStatus` := 1, p‖q‖g at `sPacked`),
`rand` runs out (2) or the seeds do (3), as `Spec.Dsa.parameterSearch` tries
them (`Proof/Dsa/Generation/RefillSearch.lean`): the stage it ends at is
`cFin`, and its result as the spec states it `cRes`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Dsa.Generation (refillAttempt ranOutResult)

/-- What a geometry's code and the tape give the search. -/
structure GenOk (G : GP) (g : Geo) (HO : HashOk g.G) (Lq Lp : Impl.Dsa.ProbablePrime.Layout) : Prop where
  okq : PrimeOk Lq g.qCode
  qlay : QLay G g Lq
  okp : PrimeOk Lp g.pCode
  lay : PLay G g Lp
  gcert : CertC G.pLen G.qLen
  hck : CheckOk g.checkCode
  hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32)
  hp : g.pLen = G.pLen
  hq : g.qLen = G.qLen
  hk4 : 4 * g.G.k = G.qLen
  hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m
  hwl : G.witB.length = G.witLen
  hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen
  h64 : G.witLen < 2 ^ 64
  hqL : G.qLen = Spec.Dsa.generationQLen G.pLen
  k0 : G.k0 ≤ Spec.Dsa.parameterSeeds

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

theorem GenOk.attempt_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout}
    (O : GenOk G g HO Lq Lp) {k u : Nat} {n : BitVec 64} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen) :
    VP (St G ((aBase G HO k n).setV fUsed (BitVec.ofNat 64 u)) X) g.attempt
      (St G (aOut G HO k n (refillAttempt G.pLen G.qLen (seedAt G k) (G.witB.drop u))) X) :=
  VG.Proof.Dsa.PPC64LE.Gen.attempt_vp HO O.okq O.qlay O.okp O.lay O.gcert O.hck O.hlq O.hp O.hq O.hk4 O.hwl O.hH
    O.hwl O.hlen O.h64 hk hu

/-! ## The controller's pieces -/

/-- Whether a seed's octets are left after the cursor `c`. -/
theorem avail_vp {d : Cfg} {c q : Nat} (hC : fC ∈ d.LS) (hCv : d.V fC = BitVec.ofNat 64 c) (hc : c ≤ G.witLen)
    (h64 : G.witLen < 2 ^ 64) (hq : q < 2 ^ 15) :
    VP (St G d X) (.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 q] ++ ltR))
      (fun σ s => St G d X σ s ∧ isa.eval (.zero .d .r0) s = some (decide (G.witLen - c < q))) := by
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 q] ++ ltR)), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine h.ldK (o := fWitLen) (by decide) (by decide) (h.gi.fixedV (v := BitVec.ofNat 64 G.witLen)
    (by simp [fixedWords])) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fC) (by decide) (by decide) ((h₁.gi.slotV hC).trans hCv) (by decide) fun s₂ h₂ u₂ => ?_
  refine h₂.wrK exec_sub (by decide) fun s₃ h₃ u₃ => ?_
  refine h₃.wrK (exec_li hq) (by decide) fun s₄ h₄ u₄ => ?_
  have e3 : s₄.gpr .r3 = BitVec.ofNat 64 (G.witLen - c) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ltR_ok e3 u₄.gpr fun t K m sp _ e => WP.block_nil ⟨⟨h₄.of_keep K m sp, x⟩, e.trans ?_⟩
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The seed at the cursor `c`: `fSeed` := `rand + c`, its witnesses from `c + q_len`. -/
theorem seedStart_vp {g : Geo} (hq : g.qLen = G.qLen) {d : Cfg} {c : Nat} (hC : fC ∈ d.LS)
    (hCv : d.V fC = BitVec.ofNat 64 c) (hq15 : G.qLen < 2 ^ 15) :
    VP (St G d X) (.block g.seedStart)
      (St G ((d.setV fSeed (G.seeds + BitVec.ofNat 64 c)).setV fUsed (BitVec.ofNat 64 (c + G.qLen))) X) := by
  unfold Geo.seedStart
  rw [hq]
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block [ld .r3 fWit, ld .r4 fC, .add .r3 .r3 .r4, st .r3 fSeed, .addi .r4 .r4 G.qLen,
      st .r4 fUsed]), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fWit) (by decide) (by decide) (h.gi.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fC) (by decide) (by decide) ((h₁.gi.slotV hC).trans hCv) (by decide) fun s₂ h₂ u₂ => ?_
  refine h₂.wrK exec_add (by decide) fun s₃ h₃ u₃ => ?_
  have e3 : s₃.gpr .r3 = G.seeds + BitVec.ofNat 64 c := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr]
  refine h₃.stF (o := fSeed) (varOk_of (by decide)) fun s₄ h₄ m₄ _ => ?_
  rw [e3] at h₄
  refine h₄.wrK (exec_addi (by decide) hq15) (by decide) fun s₅ h₅ u₅ => ?_
  have e5 : s₅.gpr .r4 = BitVec.ofNat 64 (c + G.qLen) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.gpr, BitVec.ofNat_add]
  refine h₅.stF (o := fUsed) (varOk_of (by decide)) fun t ht _ _ => WP.block_nil ⟨?_, x⟩
  rw [e5] at ht; exact ht

/-- A rejected seed: the cursor past it, one seed fewer left. -/
theorem rejected_vp {d : Cfg} {u j : Nat} (hU : fUsed ∈ d.LS) (hUv : d.V fUsed = BitVec.ofNat 64 u)
    (hL : fSeedLeft ∈ d.LS) (hLv : d.V fSeedLeft = BitVec.ofNat 64 (j + 1)) (hj : j + 1 < 2 ^ 64) :
    VP (St G d X) (.block Geo.rejected)
      (St G ((d.setV fC (BitVec.ofNat 64 u)).setV fSeedLeft (BitVec.ofNat 64 j)) X) := by
  refine VP.pub (SS.pub (c := fun _ => d) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block Geo.rejected), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  refine h.ldK (o := fUsed) (by decide) (by decide) ((h.gi.slotV hU).trans hUv) (by decide) fun s₁ h₁ u₁ => ?_
  refine h₁.stF (o := fC) (varOk_of (by decide)) fun s₂ h₂ m₂ _ => ?_
  rw [u₁.gpr] at h₂
  refine h₂.ldK (o := fSeedLeft) (by decide) (by decide)
    ((h₂.gi.slotV (List.mem_cons_of_mem _ hL)).trans ((upd_ne (o := fC) d.V (BitVec.ofNat 64 u) (by decide)).trans hLv)) (by decide)
    fun s₃ h₃ u₃ => ?_
  refine h₃.wrK (exec_subi (by decide) (by decide)) (by decide) fun s₄ h₄ u₄ => ?_
  have e4 : s₄.gpr .r3 = BitVec.ofNat 64 j := by
    rw [u₄.gpr, u₃.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := hj
    omega
  refine h₄.stF (o := fSeedLeft) (varOk_of (by decide)) fun t ht _ _ => WP.block_nil ⟨?_, x⟩
  rw [e4] at ht; exact ht

/-! ## The controller's spec -/

/-- The seed at the cursor `c`, as the code runs it. -/
abbrev sR (G : GP) (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  refillAttempt G.pLen G.qLen (seedAt G c) (G.witB.drop (c + G.qLen))

/-- The controller's seeds left and cursor after `i` iterations. -/
def sPos (G : GP) : Nat → Nat × Nat
  | 0 => (G.k0, 0)
  | i + 1 => match sR G (sPos G i).2 with
    | some (none, rest) => ((sPos G i).1 - 1, G.witLen - rest.length)
    | _ => sPos G i

/-- The iterations, from the `i`-th at the cursor `c` with `j` seeds left. -/
def sCount (G : GP) : Nat → Nat → Nat → Nat
  | 0, _, i => i + 1
  | j + 1, c, i => if G.witLen - c < G.qLen then i + 1 else match sR G c with
    | some (none, rest) => sCount G j (G.witLen - rest.length) (i + 1)
    | _ => i + 1

theorem sCount_gt (G : GP) : ∀ j c i, i < sCount G j c i
  | 0, c, i => by simp [sCount]
  | j + 1, c, i => by
    have := sCount_gt G j
    simp only [sCount]; split
    · omega
    · split
      · exact Nat.lt_of_succ_lt (this _ _)
      all_goals omega

/-- How the controller ends. -/
inductive COut where
  | found (a : Spec.Dsa.Params) (u : Nat)
  | noSeeds (c : Nat)
  | ranOut (j c : Nat)

/-- The controller's end from seeds left `j` and the cursor `c`. -/
def cOutAt (G : GP) : Nat × Nat → COut
  | (0, c) => .noSeeds c
  | (j + 1, c) => if G.witLen - c < G.qLen then .ranOut (j + 1) c else match sR G c with
    | some (some a, rest) => .found a (G.witLen - rest.length)
    | _ => .ranOut (j + 1) c

/-- The stage it ends at. -/
def cFin (G : GP) : COut → Cfg
  | .found a u => ({ cl := [(sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a)] } : Cfg).setV fUsed
      (BitVec.ofNat 64 u) |>.setV fStatus 1
  | .noSeeds c => (({} : Cfg).setV fC (BitVec.ofNat 64 c)).setV fStatus 3
  | .ranOut j c => ((({} : Cfg).setV fC (BitVec.ofNat 64 c)).setV fSeedLeft (BitVec.ofNat 64 j)).setV fStatus 2

/-- Its result, as the spec states it. -/
def cRes (G : GP) : COut → Spec.Dsa.ParameterSearchResult
  | .found a u => ⟨.accepted a, u, []⟩
  | .noSeeds c => ⟨.exhausted, c, []⟩
  | .ranOut j c => ranOutResult G.pLen j (G.witLen - c) c

/-- Its words' bounds. -/
def cOk (G : GP) : COut → Prop
  | .found _ u => u ≤ G.witLen
  | .noSeeds c => c ≤ G.witLen
  | .ranOut j c => c ≤ G.witLen ∧ j ≤ Spec.Dsa.parameterSeeds

/-- The whole search's result. -/
abbrev sW (G : GP) : Spec.Dsa.ParameterSearchResult := Spec.Dsa.parameterSearch G.pLen G.k0 G.witB

/-- The controller's stage at the cursor `c` with `j` seeds left. -/
abbrev cBase (G : GP) (HO : HashOk Gh) (c j : Nat) : Cfg :=
  ((({ cl := [(sMsg + G.qLen, padTail HO.md G.qLen)] } : Cfg).setV fC (BitVec.ofNat 64 c)).setV fSeedLeft
    (BitVec.ofNat 64 j)).setV fStatus 0

/-- The search with `r` iterations left of `N`. -/
abbrev sInv (G : GP) (HO : HashOk Gh) (N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ sCount G (sPos G (N - r)).1 (sPos G (N - r)).2 (N - r) = N ∧
    (Spec.Dsa.parameterSearch G.pLen (sPos G (N - r)).1 (G.witB.drop (sPos G (N - r)).2)).consume
      (sPos G (N - r)).2 [] = sW G ∧
    (sPos G (N - r)).2 ≤ G.witLen ∧ (sPos G (N - r)).1 ≤ Spec.Dsa.parameterSeeds) ∧
    St G (cBase G HO (sPos G (N - r)).2 (sPos G (N - r)).1) X σ s

/-- The controller's end. -/
abbrev cOut (G : GP) (N : Nat) : COut := cOutAt G (sPos G (N - 1))

theorem sBody_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp)
    {N : Nat} (r : Nat) :
    VP (sInv G HO N X (r + 1)) (seqs [.block (cmpF fSeedLeft 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 3))
          (seqs [.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 g.qLen] ++ ltR),
            .ite (.zero .d .r0) (.block (stImm fStatus 2))
              (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite (.zero .d .r0) (.block Geo.rejected) (.block [])])]),
        .block (cmpF fStatus 0)])
      (fun σ s => isa.eval (.zero .d .r0) s = some (decide (0 < r)) ∧
        (r = 0 → St G (cFin G (cOut G N)) X σ s ∧ cRes G (cOut G N) = sW G ∧ cOk G (cOut G N)) ∧
        (0 < r → sInv G HO N X r σ s)) := by
  refine VP.intro fun ⟨hr, hc, hW, hcw, hj⟩ => ?_
  have hq0 : 0 < G.qLen := by have := O.hlq; omega
  have hq15 : G.qLen < 2 ^ 15 := by have := O.hlq; omega
  have hpL : 0 < G.pLen := by have := O.hlq; omega
  have h64 := O.h64
  have hwl := O.hwl
  have hqL := O.hqL
  generalize hii : N - (r + 1) = i at hc hW hcw hj
  generalize hp : sPos G i = jc at hc hW hcw hj
  obtain ⟨j, c⟩ := jc
  dsimp only at hc hW hcw hj
  have hNi : N - 1 = i + r := by omega
  rw [O.hq]
  refine VP.seq (G := fun σ s => St G (cBase G HO c j) X σ s ∧
      isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 j == BitVec.ofNat 64 0))
    (cmpF_vp (x := BitVec.ofNat 64 j) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd, fSeedLeft, fStatus]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, e⟩) ?_
  have jl : j < 2 ^ 64 := by simp only [Spec.Dsa.parameterSeeds] at hj; omega
  rcases j with _ | j
  · -- No seeds left: `fStatus` := 3.
    have r0 : r = 0 := by simp only [sCount] at hc; omega
    subst r0
    have hout : cOut G N = .noSeeds c := by simp only [cOut, hNi, Nat.add_zero, hp, cOutAt]
    refine VP.seq (G := St G ((cBase G HO c 0).setV fStatus (BitVec.ofNat 64 3)) X) (VP.ite
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
      (stImm_vp (c := fun _ => cBase G HO c 0) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
      (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z)) ?_
    refine cmpF_vp (x := BitVec.ofNat 64 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
      fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
    · rw [hout]
      refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
        (fun _ h' => absurd h' (by simp [cFin]))
      change o ∈ [fStatus, fC] at ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
    · rw [hout, ← hW]; exact (VG.Proof.Dsa.Generation.search_zero _ _ _).symm
    · rw [hout]; exact hcw
  · have e0 : (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0) = false := by
      refine beq_false_of_ne fun e => ?_
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    have notZ : ∀ {G₁ : State → State → Prop} {c' : Prog isa}, VP (fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0)) ∧
        isa.eval (.zero .d .r0) s = some true) c' G₁ :=
      VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e, e0] at z; simp at z
    have avail := (avail_vp (X := X) (d := cBase G HO c (j + 1)) (by simp) (by simp [upd, fC, fSeedLeft, fStatus])
      hcw h64 hq15).mono (F' := fun σ s => (St G (cBase G HO c (j + 1)) X σ s ∧
        isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0)) ∧
        isa.eval (.zero .d .r0) s = some false) (fun σ s h => h.1.1) fun _ _ h => h
    by_cases hshort : G.witLen - c < G.qLen
    · -- Too few octets for a seed: `fStatus` := 2.
      have r0 : r = 0 := by simp only [sCount, hshort, ↓reduceIte] at hc; omega
      subst r0
      have hout : cOut G N = .ranOut (j + 1) c := by
        simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte]
      refine VP.seq (G := St G ((cBase G HO c (j + 1)).setV fStatus (BitVec.ofNat 64 2)) X)
        (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (stImm_vp (c := fun _ => cBase G HO c (j + 1)) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
            fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z)))) ?_
      refine cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.gi.slotV (by simp)).trans (by simp [upd]))
        fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
      · rw [hout]
        refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
          (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
        change o ∈ [fStatus, fSeedLeft, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl <;> exact ⟨by simp, by simp [cFin, upd, fStatus, fC, fSeedLeft]⟩
      · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_short (by rw [hwl, ← hqL]; exact hshort), hwl]
      · rw [hout]; exact ⟨hcw, hj⟩
    · -- A seed.
      have hcq : c + G.qLen ≤ G.witLen := by omega
      have attempt := O.attempt_vp (X := X) (k := c) (u := c + G.qLen) (n := BitVec.ofNat 64 (j + 1)) hcq hcq
      have hmono : ∀ σ s, St G (((cBase G HO c (j + 1)).setV fSeed (G.seeds + BitVec.ofNat 64 c)).setV fUsed
          (BitVec.ofNat 64 (c + G.qLen))) X σ s →
          St G ((aBase G HO c (BitVec.ofNat 64 (j + 1))).setV fUsed (BitVec.ofNat 64 (c + G.qLen))) X σ s := by
        intro σ s h
        refine ⟨h.1.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
          (fun _ h' => absurd h' (by simp)), h.2⟩
        change o ∈ [fUsed, fStatus, fSeedLeft, fSeed, fC] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp [upd, fUsed, fStatus, fSeedLeft, fSeed, fC]⟩
      have start := (seedStart_vp (X := X) O.hq (d := cBase G HO c (j + 1)) (c := c) (by simp)
        (by simp [upd, fC, fSeedLeft, fStatus]) hq15).mono (F' := fun σ s =>
          (St G (cBase G HO c (j + 1)) X σ s ∧ isa.eval (.zero .d .r0) s = some (decide (G.witLen - c < G.qLen))) ∧
          isa.eval (.zero .d .r0) s = some false) (fun σ s h => h.1.1) hmono
      have wrap : ∀ {G₁ : State → State → Prop}, VP (St G ((aBase G HO c (BitVec.ofNat 64 (j + 1))).setV fUsed
          (BitVec.ofNat 64 (c + G.qLen))) X) (seqs [g.attempt, .block (cmpF fStatus 0),
            .ite (.zero .d .r0) (.block Geo.rejected) (.block [])]) G₁ →
          VP (fun σ s => St G (cBase G HO c (j + 1)) X σ s ∧
            isa.eval (.zero .d .r0) s = some (BitVec.ofNat 64 (j + 1) == BitVec.ofNat 64 0))
            (.ite (.zero .d .r0) (.block (stImm fStatus 3))
              (seqs [.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 G.qLen] ++ ltR),
                .ite (.zero .d .r0) (.block (stImm fStatus 2))
                  (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                    .ite (.zero .d .r0) (.block Geo.rejected) (.block [])])])) G₁ := fun k =>
        VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) notZ (VP.seq avail (VP.ite
          (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
          (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hshort] at z) (VP.seq start k)))
      have hRc : (G.witB.drop c).take (Spec.Dsa.generationQLen G.pLen) = seedAt G c := by
        show _ = (G.witB.drop c).take G.qLen; rw [hqL]
      have hcq' : c + Spec.Dsa.generationQLen G.pLen ≤ G.witB.length := by rw [hwl, ← hqL]; exact hcq
      have suffix : ∀ {x : Option Spec.Dsa.Params} {rest : List Byte}, sR G c = some (x, rest) →
          G.witB.drop (G.witLen - rest.length) = rest := fun {x rest} e => by
        rw [← hwl]
        exact VG.Proof.Dsa.Generation.suffix_drop_length
          ((VG.Proof.Dsa.Generation.refillAttempt_suffix e).trans (List.drop_suffix _ _))
      have rlen : ∀ {x : Option Spec.Dsa.Params} {rest : List Byte}, sR G c = some (x, rest) →
          G.witLen - rest.length ≤ G.witLen := fun _ => Nat.sub_le _ _
      change VP _ _ (St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) (sR G c)) X) at attempt
      rcases hR : sR G c with _ | ⟨_ | a, rest⟩ <;> rw [hR] at attempt
      · -- `rand` ran out inside the seed.
        have r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega
        subst r0
        have hout : cOut G N = .ranOut (j + 1) c := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) none) X σ s ∧ isa.eval (.zero .d .r0) s = some false)
          (cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 64 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine h'.mono (fun o ho => ?_) (fun y hy => absurd hy (by simp [cFin]))
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;> exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fC, fSeedLeft, fSeed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_attemptNone hpL hcq' (by rw [hRc, ← hqL]; exact hR),
            hwl]
        · rw [hout]; exact ⟨hcw, hj⟩
      · -- Rejected: the next seed.
        have hsuf := suffix hR
        have hcs : sCount G (j + 1) c i = sCount G j (G.witLen - rest.length) (i + 1) := by
          simp only [sCount, hshort, ↓reduceIte, hR]
        have hgt := sCount_gt G j (G.witLen - rest.length) (i + 1)
        have rpos : 0 < r := by omega
        have hNr : N - r = i + 1 := by omega
        have hp1 : sPos G (i + 1) = (j, G.witLen - rest.length) := by
          simp only [sPos, hp, hR, Nat.add_sub_cancel]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) (some (none, rest))) X σ s ∧
            isa.eval (.zero .d .r0) s = some true)
          (cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus]))
            fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            ((rejected_vp (u := G.witLen - rest.length) (j := j) (by simp [aOut]) (by simp [aOut, upd])
              (by simp [aOut]) (by simp [aOut, upd, fUsed, fStatus, fSeedLeft]) (by omega)).mono
                (fun σ s h => h.1.1) fun _ _ h => h)
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 64 0) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd, fUsed, fStatus, fC, fSeedLeft]))
          fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; simp [rpos], fun h0 => absurd h0 (by omega), fun _ => ?_⟩
        simp only [sInv, hNr, hp1]
        refine ⟨⟨by omega, by rw [← hcs]; exact hc, ?_, Nat.sub_le _ _, by omega⟩, ?_, x⟩
        · rw [← hW, VG.Proof.Dsa.Generation.search_rejected hpL hcq' (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm))
            (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · refine h'.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => absurd h' (by simp))
            (fun _ h' => absurd h' (by simp))
          change o ∈ [fStatus, fSeedLeft, fC] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl <;>
            exact ⟨by simp [aOut], by simp [aOut, upd, fStatus, fC, fSeedLeft, fUsed]⟩
      · -- Parameters: `fStatus` = 1.
        have hsuf := suffix hR
        have r0 : r = 0 := by
          simp only [sCount, hshort, ↓reduceIte, hR] at hc; omega
        subst r0
        have hout : cOut G N = .found a (G.witLen - rest.length) := by
          simp only [cOut, hNi, Nat.add_zero, hp, cOutAt, hshort, ↓reduceIte, hR]
        refine VP.seq (wrap (VP.seq attempt (VP.seq (G := fun σ s =>
            St G (aOut G HO c (BitVec.ofNat 64 (j + 1)) (some (some a, rest))) X σ s ∧
            isa.eval (.zero .d .r0) s = some false)
          (cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
            (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
            fun σ s t ⟨_, x⟩ h' _ e => ⟨⟨h', x⟩, by rw [e]; rfl⟩)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z) (VP.block_nil fun σ s h => h.1.1))))) ?_
        refine cmpF_vp (x := BitVec.ofNat 64 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.gi.slotV (by simp [aOut])).trans (by simp [aOut, upd]))
          fun σ s t ⟨_, x⟩ h' _ e => ⟨by rw [e]; rfl, fun _ => ⟨⟨?_, x⟩, ?_, ?_⟩, fun h0 => absurd h0 (by decide)⟩
        · rw [hout]
          refine h'.mono (fun o ho => ?_) (fun y hy => hy)
            (fun _ h' => absurd h' (by simp [cFin])) (fun _ h' => absurd h' (by simp [cFin]))
          change o ∈ [fStatus, fUsed] at ho
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl <;> exact ⟨by simp [aOut], by simp [aOut, cFin, upd, fStatus, fUsed]⟩
        · rw [hout, ← hW, cRes, VG.Proof.Dsa.Generation.search_accepted hpL hcq' (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_eq hwl.symm))
            (by rw [hRc, ← hqL, hsuf]; exact hR)]
        · rw [hout]; exact Nat.sub_le _ _

/-- The seeds, from the cursor 0 with `state[0]` seeds left. -/
theorem sLoop_vp {g : Geo} {HO : HashOk g.G} {Lq Lp : Impl.Dsa.ProbablePrime.Layout} (O : GenOk G g HO Lq Lp) :
    VP (St G (cBase G HO 0 G.k0) X)
      (.loop (seqs [.block (cmpF fSeedLeft 0),
        .ite (.zero .d .r0) (.block (stImm fStatus 3))
          (seqs [.block ([ld .r3 fWitLen, ld .r4 fC, .sub .r3 .r3 .r4, .li .r4 g.qLen] ++ ltR),
            .ite (.zero .d .r0) (.block (stImm fStatus 2))
              (seqs [.block g.seedStart, g.attempt, .block (cmpF fStatus 0),
                .ite (.zero .d .r0) (.block Geo.rejected) (.block [])])]),
        .block (cmpF fStatus 0)]) (.zero .d .r0))
      (fun σ s => St G (cFin G (cOut G (sCount G G.k0 0 0))) X σ s ∧
        cRes G (cOut G (sCount G G.k0 0 0)) = sW G ∧ cOk G (cOut G (sCount G G.k0 0 0))) := by
  have hN := sCount_gt G G.k0 0 0
  generalize hNN : sCount G G.k0 0 0 = N at hN ⊢
  refine VP.mono (F := sInv G HO N X (N - 1 + 1)) ?_ (fun σ s h => ⟨⟨by omega,
    by rw [show N - (N - 1 + 1) = 0 by omega]; exact hNN,
    by rw [show N - (N - 1 + 1) = 0 by omega]; simp [sPos, sW, Spec.Entropy.Result.consume],
    by rw [show N - (N - 1 + 1) = 0 by omega]; simp [sPos], by rw [show N - (N - 1 + 1) = 0 by omega]; exact O.k0⟩,
    by rw [show N - (N - 1 + 1) = 0 by omega]; exact h⟩) fun _ _ h => h
  exact VP.loop (I := sInv G HO N X) (fun r => (sBody_vp O r).mono (fun _ _ h => h)
    fun σ s ⟨e, h0, hp⟩ => ⟨e, fun z => h0 z, hp⟩) _

end

end VG.Proof.Dsa.PPC64LE.Gen
