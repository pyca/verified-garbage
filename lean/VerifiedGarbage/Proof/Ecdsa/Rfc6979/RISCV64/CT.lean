module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.Correct
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.HmacCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on RISC-V: constant time, up to the number of candidates

As for PBKDF2 (`Proof/Pbkdf2/Whole/RISCV64/CT.lean`): two runs from states
whose public data agree (`PubEq`: the pointers, the stack pointer and the
number of candidates RFC 6979 tries, which the contract lets leak) are
related piece by piece. The code between the calls of HMAC's `init` and
`finalize` and of the signature with a given `k`, the calls of the
streaming `update` and of the order's addition included, is checked by the
taint analysis (`Checks`, which the kernel evaluates for each hash
function), from the registers that hold pointers; the calls whose callees
restore the callee-saved registers from memory are related by their
contracts (`hi_rel`, `hf_rel`, `core_rel`), with the arguments each run's
correctness gives. Each run's correctness then says what the registers hold
after a piece (`RelCT.wp`), so that they agree again. The loop's branch
agrees, since in both runs it goes on after candidate `i` iff `i` is before
the candidate it stops at (`go_iff`, `exitAt`); the frame's `alloc` and
`free` leak nothing (`rel_alloc`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (eval_nonzero wp_li)
open VG.Impl.Ecdsa.Rfc6979.RISCV64
open Spec.Sha256 (bytesAt)

/-- The taint checks of the pieces of the function between the calls. -/
structure Checks (c : Cfg) : Prop where
  pro : Ck [.a0, .a1, .a2, .a4, .a5] (.block Cfg.prologue)
  red : Ck [.s0, .s1, .s4] c.reduce
  kv : Ck [.s1] (.block c.initKV)
  sep0 : Ck [.s1] (.block (c.sep 0))
  sep1 : Ck [.s1] (.block (c.sep 1))
  h : HCks c
  cnt : Ck [] (.block c.initCnt)
  ca : Ck [.s0, .s1, .s2, .s3, .s4] (.block Cfg.coreArgs)
  go : Ck [.s5] (.block Cfg.goOn)
  ag : Ck [] (.block Cfg.again)
  st : Ck [] (.block Cfg.stop)
  fin : Ck [.s1] (.block (c.wipe ++ Cfg.restore))
  /-- If `wide`: `core`'s arguments, and the copy of `V₂`'s first bytes. -/
  caW : Ck [.s0, .s1, .s2, .s3, .s4] (.block c.coreArgsW)
  cpW : Ck [.s1] (.block (Impl.Words.RISCV64.copyBytes .t0 .s1 .s1 fV (c.fT + c.D) (c.Q - c.D)))

variable {P : Rfc}

/-! ## Pieces that keep `KR` -/

theorem initKV_kr {s₀ : State} (hp : Pre P s₀) {s : State} (h : KR P s₀ s) :
    WP isa (.block P.c.initKV) s (KR P s₀) := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.initKV
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hp h (doff := fK) (bs := List.replicate P.c.D 0) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fK, List.length_replicate]; have := (sizes P).Q; have := (sizes P).H; omega)) fun t₁ h₁ => ?_
  exact WP.mono (store_ok hp h₁.1 (doff := fV) (bs := List.replicate P.c.D 1) (fun i hi => by
      simp only [List.length_replicate] at hi; simp [List.getD_eq_getElem?_getD, hi])
    (by simp only [fV, List.length_replicate]; have := (sizes P).Q; have := (sizes P).H; omega)) fun t₂ h₂ => h₂.1

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

theorem hmacV_kk : RelCT isa (KK P s₀ s₀') P.c.hmacV (KK P s₀ s₀') := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.hmacV
  exact hmac_kk hp hp' hq hc.h (ps := [(.s1, fV, P.c.D)]) (dst := fV) (fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'
      exact .inl ⟨rfl, by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩)
    (by simp only [total]; rcases hz.B with h' | h' <;> omega) ⟨by decide, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩

omit hc in
theorem sep_kk {b : Nat} (hb : b < 256) (cs : Ck [.s1] (.block (P.c.sep b))) :
    RelCT isa (KK P s₀ s₀') (.block (P.c.sep b)) (KK P s₀ s₀') := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  have hw : ∀ {σ : State} (hσ : Pre P σ) {s : State}, KS P σ s → WP isa (.block (P.c.sep b)) s (KS P σ) :=
    fun hσ s h => VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (store_ok hσ h.1 (doff := fV + P.c.D) (bs := [b]) (fun i hi => by
      simp only [List.length_singleton] at hi; obtain rfl : i = 0 := by omega
      simpa using hb) (by simp only [fV, List.length_singleton]; have := (sizes P).Q; have := (sizes P).H; omega))
      fun _ h' y => ⟨h'.1, y.trans h.2⟩
  exact (rel_kr hq (by decide) (fun _ h => h.1) (fun _ h => h.1) cs (fun s h => hw hp h) fun s h => hw hp' h).mono
    (fun _ _ h => h) fun _ _ h => h

theorem rekeyFull_kk {b : Nat} (hb : b < 256) (cs : Ck [.s1] (.block (P.c.sep b))) :
    RelCT isa (KK P s₀ s₀') (P.c.rekeyFull b) (KK P s₀ s₀') := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.rekeyFull
  refine (sep_kk hp hp' hq hb cs).seq ((hmac_kk hp hp' hq hc.h (fun p hp' => ?_) ?_ ⟨by decide, ?_⟩).seq
    (hmacV_kk hp hp' hq hc))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact .inl ⟨rfl, by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩
    · exact .inr ⟨rfl, rfl, Nat.le_of_eq (sizes P).Q.2.2.1⟩
    · exact .inl ⟨rfl, by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; omega, by (try dsimp only); have := (sizes P).H; have := (sizes P).Q; have := (sizes P).Q; have := (sizes P).H; omega⟩
  · simp only [total]; have := (sizes P).Q; rcases hz.B with h' | h' <;> omega
  · simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega

theorem rekey_kk : RelCT isa (KK P s₀ s₀') P.c.rekey (KK P s₀ s₀') := by
  have hz := sizes P
  have hzH := hz.H
  obtain ⟨hD1, hD2⟩ := hz.D
  unfold Cfg.rekey
  refine (sep_kk hp hp' hq (b := 0) (by decide) hc.sep0).seq ((hmac_kk hp hp' hq hc.h (fun p hp' => ?_) ?_
    ⟨by decide, ?_⟩).seq (hmacV_kk hp hp' hq hc))
  · simp only [List.mem_singleton] at hp'; subst hp'
    exact .inl ⟨rfl, by simp only [fV]; have := (sizes P).H; have := (sizes P).Q; omega, by simp only [fV]; have := (sizes P).Q; have := (sizes P).H; omega⟩
  · simp only [total]; rcases hz.B with h' | h' <;> omega
  · simp only [fK]; have := (sizes P).Q; have := (sizes P).H; omega

end

/-! ## Where the loop stops -/

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : Rfc) (s₀ : State) : Nat :=
  if (result P.I s₀.mem (dk s₀) (dg s₀)).2 = 0 then P.c.tries - 1 else (result P.I s₀.mem (dk s₀) (dg s₀)).2 - 1

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {s₀ : State} {i : Nat} (hi : i < P.c.tries) (hf : ∀ j < i, sigI P s₀ j = none) :
    (sigI P s₀ i = none ∧ i + 1 < P.c.tries) ↔ i < exitAt P s₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P s₀ ∧ xOf P s₀ < P.kit.E.curve.n
  · simp only [hv, and_self, ite_true]
    rw [VG.Proof.Ecdsa.Rfc6979.searchB_shift (b := nb P) rfl i P.c.tries (by omega) hf,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by omega]
    cases hs : sigI P s₀ i with
    | some rs =>
      rw [VG.Proof.Ecdsa.Rfc6979.searchB_ok (b := nb P) rfl hs]
      simp
    | none =>
      rw [VG.Proof.Ecdsa.Rfc6979.searchB_fail (b := nb P) rfl hs]
      by_cases h7 : i + 1 < P.c.tries
      · have := VG.Proof.Ecdsa.Rfc6979.searchB_pos (C := P.kit.E.curve) (H := P.hH.SH.H) (hlen := P.c.D)
          (d := xOf P s₀) (e := eOf P s₀) (n := P.c.tries - 2 - i)
          (K := (VG.Proof.Ecdsa.Rfc6979.stepB P.hH.SH.H (nb P)
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H (nb P) (kv0 P s₀).1 (kv0 P s₀).2 i).1
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H (nb P) (kv0 P s₀).1 (kv0 P s₀).2 i).2).1)
          (V := (VG.Proof.Ecdsa.Rfc6979.stepB P.hH.SH.H (nb P)
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H (nb P) (kv0 P s₀).1 (kv0 P s₀).2 i).1
            (VG.Proof.Ecdsa.Rfc6979.kvAtB P.hH.SH.H (nb P) (kv0 P s₀).1 (kv0 P s₀).2 i).2).2) (b := nb P) rfl
        rw [show P.c.tries - 1 - i = P.c.tries - 2 - i + 1 by omega]
        simp only [true_and, h7]
        rw [true_iff]
        split <;> omega
      · rw [show P.c.tries - 1 - i = 0 by omega]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P s₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

theorem PubEq.exitAt {s₀ s₀' : State} (hq : PubEq P s₀ s₀') :
    RISCV64.exitAt P s₀ = RISCV64.exitAt P s₀' := by
  unfold RISCV64.exitAt; rw [hq.lk]

/-! ## One candidate, in two runs -/

/-- Where `core` reads `k`: `V`, or if `wide` the candidate's place. -/
def kof (P : Rfc) : Nat := if P.c.wide then P.c.fT else fV

/-- `V` after candidate `i`. -/
abbrev vC (P : Rfc) (s₀ : State) (i : Nat) : List Byte :=
  (Spec.Ecdsa.Rfc6979.genT P.hH.SH.H (kvI P s₀ i).1 (nb P) (kvI P s₀ i).2).2

/-- `core`'s arguments, with `k` at `kof`. -/
abbrev coreArgsK (P : Rfc) : List Instr :=
  [Impl.Hmac.Stream.RISCV64.mov .a0 .s2, Impl.Hmac.Stream.RISCV64.mov .a1 .s3,
    Impl.Hmac.Stream.RISCV64.mov .a2 .s4, .addi .a3 .s1 (kof P), Impl.Hmac.Stream.RISCV64.mov .a4 .s0]

theorem kof_ok (P : Rfc) : 64 ≤ kof P ∧ kof P + P.Q ≤ P.c.frB := by
  have hz := sizes P
  have hzQ := hz.Q
  have hzH := hz.H
  have hzD := hz.D
  unfold kof
  cases hwd : P.c.wide
  · have := hz.W.mp hwd
    simp only [Bool.false_eq_true, ↓reduceIte, fV]
    omega
  · have hnu : P.c.nums = 2 := by rw [hz.nums, hwd]; rfl
    have hfr := hzQ.2.2.2.1.1
    rw [hnu] at hfr
    simp only [↓reduceIte, Cfg.fT, P.hnw]
    omega

/-- What every piece of a candidate needs: `K`, `V` after the candidate and
the candidates left, and that the earlier candidates failed. -/
structure T0 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop where
  kvh : KVH P s₀ (kvI P s₀ i).1 (vC P s₀ i) t
  cnt : t.gpr .s5 = BitVec.ofNat 64 (P.c.tries - i)
  lt : i < P.c.tries
  fails : ∀ j < i, sigI P s₀ j = none
  sy : t.syms = s₀.syms

/-- After the candidate: what `core` will read is its signature's input. -/
def T1 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  T0 P s₀ i t ∧ sgOf P.kit.E P.Q P.kit.G P.kit.sh t.mem (dk s₀) (dg s₀) (sA s₀ (kof P)) = sigI P s₀ i

/-- After `core`'s arguments. -/
def T2 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  T1 P s₀ i t ∧ CoreArgsG P.Q P.kit.G P.kit.K t (out s₀) (dk s₀) (dg s₀) (sA s₀ (kof P)) (scr s₀)

/-- After `core`. -/
def T3 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  T0 P s₀ i t ∧ ResultIs P s₀ (sigI P s₀ i) t

/-- After `goOn`. -/
def T4 (P : Rfc) (s₀ : State) (i : Nat) (t : State) : Prop :=
  KVH P s₀ (kvI P s₀ i).1 (vC P s₀ i) t ∧ i < P.c.tries ∧ (∀ j < i, sigI P s₀ j = none) ∧
    isa.eval (.nonzero .t6) t = some (decide (sigI P s₀ i = none ∧ i + 1 < P.c.tries)) ∧ t.syms = s₀.syms

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

/-- The candidate's code. -/
abbrev candC (P : Rfc) : Prog isa := if P.c.wide then P.c.candW else P.c.hmacV

theorem t1_ok {i : Nat} {t : State} (h : LoopInv P s₀ i t) : WP isa (candC P) t (T1 P s₀ i) := by
  have hz := sizes P
  have hzQ := hz.Q
  unfold candC
  cases hwd : P.c.wide
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    have hk : kof P = fV := by simp only [kof, hwd, Bool.false_eq_true, ↓reduceIte]
    have e : vC P s₀ i = Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2 :=
      congrArg Prod.snd (genT_one P hwd _ _)
    exact VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (hmacV_ok hp h.kvh h.sy) fun _ ⟨k, pr⟩ y =>
      ⟨⟨by rw [e]; exact k, by rw [pr _ (by decide), h.cnt], h.lt, h.fails, y.trans h.sy⟩,
        by rw [hk]; exact sg_eq hp hwd k.kr k.v⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    have hk : kof P = P.c.fT := by simp only [kof, hwd, ↓reduceIte]
    have e : vC P s₀ i = Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1
        (Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2) := congrArg Prod.snd (genT_two P hwd _ _)
    have hc : candI P s₀ i = Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2 ++
        (Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (Spec.Hmac.hmac P.hH.SH.H (kvI P s₀ i).1 (kvI P s₀ i).2) ++ []) :=
      congrArg Prod.fst (genT_two P hwd _ _)
    refine VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (candW_ok hp hwd h.kvh h.sy) fun u ⟨k, T, pr⟩ y => ?_
    have hT : bytesAt u.mem (sA s₀ P.c.fT) P.Q = (candI P s₀ i).take P.Q := by rw [T, hc, List.append_nil]
    have hl : P.Q ≤ (candI P s₀ i).length := by
      have := congrArg List.length hT
      rw [VG.Proof.Hmac.Common.bytesAt_length, List.length_take] at this
      omega
    exact ⟨⟨by rw [e]; exact k, by rw [pr _ (by decide), h.cnt], h.lt, h.fails, y.trans h.sy⟩,
      by rw [hk]; exact sg_eqW hp hwd k.kr hT hl⟩

theorem t2_ok {i : Nat} {t : State} (h : T1 P s₀ i t) : WP isa (.block (coreArgsK P)) t (T2 P s₀ i) :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreArgs_ok hp h.1.kvh h.1.sy (kof_ok P)) fun _ ⟨k, pr, mm, a⟩ y =>
    ⟨⟨⟨k, by rw [pr _ (by decide), h.1.cnt], h.1.lt, h.1.fails, y.trans h.1.sy⟩, by rw [mm]; exact h.2⟩, a⟩

theorem t3_ok {i : Nat} {t : State} (h : T2 P s₀ i t) : WP isa (.call P.c.coreN P.c.coreC) t (T3 P s₀ i) :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (coreCall_ok hp h.1.1.kvh h.1.2 h.2) fun _ ⟨k, pr, r⟩ y =>
    ⟨⟨k, by rw [pr _ (by decide), h.1.1.cnt], h.1.1.lt, h.1.1.fails, y.trans h.1.1.sy⟩, r⟩

omit hp in
theorem t4_ok {i : Nat} {t : State} (h : T3 P s₀ i t) : WP isa (.block Cfg.goOn) t (T4 P s₀ i) :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (goOn_ok h.1.kvh h.1.lt h.1.cnt h.2) fun _ ⟨k, _, _, e⟩ y =>
    ⟨k, h.1.lt, h.1.fails, e, y.trans h.1.sy⟩

end

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

/-- If `wide`, two runs of a candidate's code. -/
theorem candW_kk (hwd : P.c.wide = true) : RelCT isa (KK P s₀ s₀') P.c.candW (KK P s₀ s₀') := by
  have hz := sizes P
  have hzH := hz.H
  have hzQ := hz.Q
  obtain ⟨hD1, hD2⟩ := hz.D
  have hnu : P.c.nums = 2 := by rw [hz.nums, hwd]; rfl
  have hfr := hzQ.2.2.2.1.1
  rw [hnu] at hfr
  have hfT : P.c.fT = P.c.fH + 8 * P.kit.nw := by rw [Cfg.fT, P.hnw]
  have hQD : P.c.D < P.Q := by
    have := hz.W
    rw [hwd] at this
    simp only [Bool.true_eq_false, false_iff, Nat.not_le] at this
    exact this
  have hcQ : P.c.Q = P.Q := P.hQ
  unfold Cfg.candW
  refine (hmac_kk hp hp' hq hc.h (fun p hp' => ?_) ?_ ⟨by omega, by omega⟩).seq
    ((hmac_kk hp hp' hq hc.h (fun p hp' => ?_) ?_ ⟨by simp only [fV]; omega, by simp only [fV]; omega⟩).seq ?_)
  · simp only [List.mem_singleton] at hp'; subst hp'
    exact .inl ⟨rfl, by (try dsimp only); simp only [fV]; omega, by (try dsimp only); simp only [fV]; omega⟩
  · simp only [total]; rcases hz.B with h' | h' <;> omega
  · simp only [List.mem_singleton] at hp'; subst hp'
    exact .inl ⟨rfl, by (try dsimp only); omega, by (try dsimp only); omega⟩
  · simp only [total]; rcases hz.B with h' | h' <;> omega
  · have hw : ∀ {σ : State} (hσ : Pre P σ) {s : State}, KS P σ s →
        WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 .s1 .s1 fV (P.c.fT + P.c.D) (P.c.Q - P.c.D))) s
          (KS P σ) := fun {σ} hσ s h' => by
      have h := h'.1
      rw [hcQ]
      refine VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (copyFr_ok hσ h (src := .s1) (by decide) (soff := fV) (doff := P.c.fT + P.c.D)
        (n := P.Q - P.c.D) (by simp only [fV]; omega) ⟨by omega, by omega⟩
        (fun i hi => by rw [h.s1]; exact in_fr' hσ h.wr (o := fV + i) (n := 1) (by simp only [fV]; omega))
        (fun i hi => by
          rw [h.s1]
          exact part_disj (s₀ := σ) (a := fV + i) (m := 1) (b := P.c.fT + P.c.D) (n := P.Q - P.c.D)
            (.inl (by simp only [fV]; omega)) (by simp only [fV]; omega) (by omega) _ (Region.contains_self _ _)))
        fun _ x y => ⟨x.1, y.trans h'.2⟩
    exact (rel_kr hq (by decide) (fun _ h => h.1) (fun _ h => h.1) hc.cpW (fun s h => hw hp h) fun s h => hw hp' h).mono
      (fun _ _ h => h) fun _ _ h => h

/-- Two runs of a candidate. -/
theorem tryOne_rel {i : Nat} :
    RelCT isa (fun t t' => LoopInv P s₀ i t ∧ LoopInv P s₀' i t') P.c.tryOne fun _ _ => True := by
  have hck : RelCT isa (KK P s₀ s₀') (candC P) (KK P s₀ s₀') := by
    unfold candC
    cases hwd : P.c.wide
    · exact hmacV_kk hp hp' hq hc
    · exact candW_kk hp hp' hq hc hwd
  have hca : Ck [.s0, .s1, .s2, .s3, .s4] (.block (coreArgsK P)) := by
    unfold coreArgsK kof
    cases hwd : P.c.wide
    · exact hc.ca
    · exact hc.caW
  have hcode : P.c.tryOne = .seq (candC P) (.seq (.block (coreArgsK P)) (.seq (.call P.c.coreN P.c.coreC)
      (.seq (.block Cfg.goOn) (.ite (.nonzero .t6) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop))))) := by
    unfold Cfg.tryOne candC coreArgsK kof
    cases P.c.wide <;> rfl
  rw [hcode]
  have r₁ := rel_wp (P₁ := LoopInv P s₀ i) (P₂ := LoopInv P s₀' i) (G₁ := T1 P s₀ i) (G₂ := T1 P s₀' i)
    (hck.mono (fun _ _ h => ⟨⟨h.1.kvh.kr, h.1.sy⟩, ⟨h.2.kvh.kr, h.2.sy⟩⟩) fun _ _ _ => trivial)
    (fun _ h => t1_ok hp h) (fun _ h => t1_ok hp' h)
  have r₂ := rel_kr hq (P₁ := T1 P s₀ i) (P₂ := T1 P s₀' i) (G₁ := T2 P s₀ i) (G₂ := T2 P s₀' i) (by decide)
    (fun _ h => h.1.kvh.kr) (fun _ h => h.1.kvh.kr) hca (fun _ h => t2_ok hp h) (fun _ h => t2_ok hp' h)
  have r₃ : RelCT isa (fun t t' => T2 P s₀ i t ∧ T2 P s₀' i t') (.call P.c.coreN P.c.coreC)
      fun t t' => T3 P s₀ i t ∧ T3 P s₀' i t' := by
    refine rel_wp ?_ (fun _ h => t3_ok hp h) (fun _ h => t3_ok hp' h)
    rw [P.hcC]
    refine P.kit.core_rel (f := s₀.syms) fun t t' ⟨h, h'⟩ => ⟨h.2, ?_, by rw [h.1.1.kvh.kr.sp, h'.1.1.kvh.kr.sp, hq.sp],
      fun cn hcn => ⟨by rw [h.1.1.sy], by rw [h'.1.1.sy]; exact (hq.sy cn hcn).symm⟩⟩
    have a := h'.2
    rwa [hq.sA, show out s₀' = out s₀ from hq.a0.symm, show dk s₀' = dk s₀ from hq.a1.symm,
      show dg s₀' = dg s₀ from hq.a2.symm, show scr s₀' = scr s₀ from hq.a4.symm] at a
  have r₄ := rel_agree (P₁ := T3 P s₀ i) (P₂ := T3 P s₀' i) (G₁ := T4 P s₀ i) (G₂ := T4 P s₀' i) (rs := [.s5])
    (fun t t' h h' => ⟨by rw [h.1.kvh.kr.sp, h'.1.kvh.kr.sp, hq.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.cnt, h'.1.cnt]⟩) hc.go
    (fun _ h => t4_ok h) (fun _ h => t4_ok h)
  have r₅ : RelCT isa (fun t t' => T4 P s₀ i t ∧ T4 P s₀' i t')
      (.ite (.nonzero .t6) (.seq P.c.rekey (.block Cfg.again)) (.block Cfg.stop)) fun _ _ => True := by
    refine RelCT.ite (fun t t' ⟨h, h'⟩ => ?_) ?_ ?_
    · rw [h.2.2.2.1, h'.2.2.2.1]
      congr 1
      exact decide_eq_decide.mpr ((go_iff h.2.1 h.2.2.1).trans (by rw [hq.exitAt]) |>.trans
        (go_iff h'.2.1 h'.2.2.1).symm)
    · obtain ⟨_, ha⟩ := hc.ag
      refine ((rekey_kk hp hp' hq hc).mono (fun _ _ h => ⟨⟨h.1.1.1.kr, h.1.1.2.2.2.2⟩, ⟨h.1.2.1.kr, h.1.2.2.2.2.2⟩⟩)
        fun _ _ h => h).seq
        ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun t t' h => ⟨by rw [h.1.1.sp, h.2.1.sp, hq.sp], fun r hr => by
          simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) ha))
    · obtain ⟨_, hs⟩ := hc.st
      exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun t t' h => ⟨by
        rw [h.1.1.1.kr.sp, h.1.2.1.kr.sp, hq.sp], fun r hr => by
          simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) hs
  exact r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))

/-- Two runs of the loop. -/
theorem loop_rel :
    RelCT isa (fun t t' => LoopInv P s₀ 0 t ∧ LoopInv P s₀' 0 t') (.loop P.c.tryOne (.nonzero .t6))
      fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t' := by
  refine (RelCT.loop (Q := fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t')
    (fun n t t' => ∃ i, n = P.c.tries - i ∧ LoopInv P s₀ i t ∧ LoopInv P s₀' i t')
    (fun n => RelCT.exists_ fun i => ?_) P.c.tries).mono (fun t t' h => ⟨0, rfl, h⟩) fun _ _ h => h
  by_cases hn : n = P.c.tries - i
  · subst hn
    refine ((tryOne_rel hp hp' hq hc).wp
      (F₁ := fun u => (i < P.c.tries ∧ ∀ j < i, sigI P s₀ j = none) ∧ _)
      (F₂ := fun u => (i < P.c.tries ∧ ∀ j < i, sigI P s₀' j = none) ∧ _)
      fun t t' h => ⟨WP.mono (tryOne_ok hp h.1) fun u x => ⟨⟨h.1.lt, h.1.fails⟩, x⟩,
        WP.mono (tryOne_ok hp' h.2) fun u x => ⟨⟨h.2.lt, h.2.fails⟩, x⟩⟩).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩)
      fun u u' ⟨_, ⟨⟨hi, hf⟩, e, on, off⟩, ⟨⟨hi', hf'⟩, e', on', off'⟩⟩ => ?_
    have hg : (sigI P s₀ i = none ∧ i + 1 < P.c.tries) ↔ (sigI P s₀' i = none ∧ i + 1 < P.c.tries) :=
      (go_iff hi hf).trans (by rw [hq.exitAt]) |>.trans (go_iff hi' hf').symm
    refine ⟨by rw [e, e', decide_eq_decide.mpr hg], fun hz => ?_, fun hz => ?_⟩
    · have hn : ¬ (sigI P s₀ i = none ∧ i + 1 < P.c.tries) := by
        intro h'; rw [e, decide_eq_true h'] at hz; cases hz
      exact ⟨⟨i, off hn⟩, i, off' (fun h' => hn (hg.mpr h'))⟩
    · have hy : sigI P s₀ i = none ∧ i + 1 < P.c.tries := by
        by_contra h'; rw [e, decide_eq_false h'] at hz; cases hz
      exact ⟨P.c.tries - (i + 1), by omega, i + 1, rfl, on hy, on' (hg.mp hy)⟩
  · exact RelCT.of_false fun _ _ h => hn h.1

end

/-! ## The whole function -/

/-- What follows code from a state naming the symbols as `s₀` does names them so too. -/
theorem wp_sy {s₀ s : State} {c : Prog isa} {Q : State → Prop} (h : WP isa c s Q) (hs : s.syms = s₀.syms) :
    WP isa c s fun t => Q t ∧ t.syms = s₀.syms :=
  VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms h fun _ q y => ⟨q, y.trans hs⟩

section
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem reduceKR_ok {s : State} (h : KR P s₀ s) :
    WP isa P.c.reduce s fun t => KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀ :=
  reduceAny_ok hp h

omit hp in
/-- The candidates left: `LoopInv` before the first. -/
theorem initCnt_ok {s : State}
    (h : KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 s) (hsy : s.syms = s₀.syms) :
    WP isa (.block P.c.initCnt) s (LoopInv P s₀ 0) := by
  unfold Cfg.initCnt
  refine VG.Proof.Ecdsa.RISCV64.Comb.WP.of_syms (wp_li (imm := P.c.tries) P.hT' fun s₆ u₆ =>
    WP.block_nil fun y₆ => ?_)
  refine ⟨P.hT, ⟨h.kr.upd (by decide) u₆, ?_, ?_, ?_⟩, by rw [u₆.gpr, Nat.sub_zero], fun j hj => absurd hj (by omega),
    y₆.trans hsy⟩
  · rw [u₆.mem]; exact h.k
  · rw [u₆.mem]; exact h.v
  · rw [u₆.mem]; exact h.h

/-- Steps d–g, in the form `kv0` gives. -/
theorem stagesDG_ok {s : State} (h : KVH P s₀ (List.replicate P.c.D 0) (List.replicate P.c.D 1) s)
    (hsy : s.syms = s₀.syms) :
    WP isa (.seq (P.c.rekeyFull 0) (P.c.rekeyFull 1)) s (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2) := by
  refine WP.seq (VG.Proof.Ecdsa.RISCV64.Comb.WP.mono_syms (rekeyFull_ok hp h hsy (b := 0) (by decide))
    fun s₄ h₄ y₄ => ?_)
  refine WP.mono (rekeyFull_ok hp h₄ (y₄.trans hsy) (b := 1) (by decide)) fun s₅ h₅ => ?_
  have e := kv0_eq P s₀
  rw [e]
  exact h₅

end

section
variable {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq P s₀ s₀') (hc : Checks P.c)
include hp hp' hq hc

/-- Two runs of the frame's body. -/
theorem main_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') P.c.main fun _ _ => True := by
  unfold Cfg.main
  have rp := rel_agree (P₁ := fun s => s = s₀) (P₂ := fun s => s = s₀')
    (G₁ := fun t => KR P s₀ t ∧ t.syms = s₀.syms) (G₂ := fun t => KR P s₀' t ∧ t.syms = s₀'.syms)
    (rs := [.a0, .a1, .a2, .a4, .a5]) (fun s s' h h' => by
      subst h h'
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [hq.a0, hq.a1, hq.a2, hq.a4, hq.a5]) hc.pro
    (fun s h => by subst h; exact wp_sy (prologue_ok hp) rfl) (fun s h => by subst h; exact wp_sy (prologue_ok hp') rfl)
  have rr := rel_kr hq (P₁ := fun t => KR P s₀ t ∧ t.syms = s₀.syms) (P₂ := fun t => KR P s₀' t ∧ t.syms = s₀'.syms)
    (G₁ := fun t => (KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀) ∧ t.syms = s₀.syms)
    (G₂ := fun t => (KR P s₀' t ∧ hOf P s₀' t.mem = hSpec P s₀') ∧ t.syms = s₀'.syms)
    (by decide) (fun _ h => h.1) (fun _ h => h.1) hc.red
    (fun s h => wp_sy (reduceKR_ok hp h.1) h.2) (fun s h => wp_sy (reduceKR_ok hp' h.1) h.2)
  have rk := rel_kr hq (P₁ := fun t => (KR P s₀ t ∧ hOf P s₀ t.mem = hSpec P s₀) ∧ t.syms = s₀.syms)
    (P₂ := fun t => (KR P s₀' t ∧ hOf P s₀' t.mem = hSpec P s₀') ∧ t.syms = s₀'.syms)
    (G₁ := fun t => KVH P s₀ (List.replicate P.c.D 0) (List.replicate P.c.D 1) t ∧ t.syms = s₀.syms)
    (G₂ := fun t => KVH P s₀' (List.replicate P.c.D 0) (List.replicate P.c.D 1) t ∧ t.syms = s₀'.syms)
    (by decide) (fun _ h => h.1.1) (fun _ h => h.1.1) hc.kv
    (fun s h => wp_sy (initKV_ok hp h.1.1 h.1.2) h.2) (fun s h => wp_sy (initKV_ok hp' h.1.1 h.1.2) h.2)
  have rd : RelCT isa (fun t t' =>
        (KVH P s₀ (List.replicate P.c.D 0) (List.replicate P.c.D 1) t ∧ t.syms = s₀.syms) ∧
        (KVH P s₀' (List.replicate P.c.D 0) (List.replicate P.c.D 1) t' ∧ t'.syms = s₀'.syms))
      (.seq (P.c.rekeyFull 0) (P.c.rekeyFull 1))
      fun t t' => (KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 t ∧ t.syms = s₀.syms) ∧
        (KVH P s₀' (kv0 P s₀').1 (kv0 P s₀').2 t' ∧ t'.syms = s₀'.syms) :=
    rel_wp (((rekeyFull_kk hp hp' hq hc (b := 0) (by decide) hc.sep0).seq
        (rekeyFull_kk hp hp' hq hc (b := 1) (by decide) hc.sep1)).mono
        (fun _ _ h => ⟨⟨h.1.1.kr, h.1.2⟩, ⟨h.2.1.kr, h.2.2⟩⟩) fun _ _ _ => trivial)
      (fun s h => wp_sy (stagesDG_ok hp h.1 h.2) h.2) (fun s h => wp_sy (stagesDG_ok hp' h.1 h.2) h.2)
  have rc := rel_kr hq (P₁ := fun t => KVH P s₀ (kv0 P s₀).1 (kv0 P s₀).2 t ∧ t.syms = s₀.syms)
    (P₂ := fun t => KVH P s₀' (kv0 P s₀').1 (kv0 P s₀').2 t ∧ t.syms = s₀'.syms)
    (rs := []) (by decide) (fun _ h => h.1.kr) (fun _ h => h.1.kr) hc.cnt
    (fun s h => initCnt_ok h.1 h.2) (fun s h => initCnt_ok h.1 h.2)
  have rl := loop_rel hp hp' hq hc
  obtain ⟨_, hf⟩ := hc.fin
  have re : RelCT isa (fun t t' => (∃ i, Exit P s₀ i t) ∧ ∃ i, Exit P s₀' i t') (.block (P.c.wipe ++ Cfg.restore))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.s1]) (fun t t' ⟨⟨i, x⟩, ⟨i', x'⟩⟩ => ⟨by rw [x.kr.sp, x'.kr.sp, hq.sp],
      fun r hr => by
        rw [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr
        rw [x.kr.s1, x'.kr.s1, hq.sp]⟩) hf
  exact rp.seq (rr.seq (rk.seq (RelCT.assoc (rd.seq (rc.seq (rl.seq re))))))

end

/-! ## The frame, and `Verified` -/

/-- Two runs of a frame allocating `n` bytes, which leaks nothing itself. -/
theorem rel_alloc {n : Nat} {body : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (fun a b => ∃ s₁ s₂, Q s₁ s₂ ∧ a = allocd n s₁ ∧ b = allocd n s₂) body fun _ _ => True) :
    RelCT isa Q (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.alloc n) s = some a → a = allocd n s := by
    intro s a h'
    simp only [isa, push] at h'
    split at h' <;> cases h'
    rfl
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

/-- The function is constant time but for the number of candidates, given
the taint checks of its pieces. -/
theorem ct (hc : Checks P.c) :
    ConstantTime isa (rfcRC P.kit.K P.I P.H P.c.f P.N).pre (rfcRC P.kit.K P.I P.H P.c.f P.N).pub P.c.sign := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  have hp := pre_alloc h; have hp' := pre_alloc h'
  obtain ⟨⟨qsp, q0, q1, q2, q4, q5, qi, qu, qf, qlk⟩, qsy⟩ := hpub
  have hq : PubEq P (allocd P.c.frB e) (allocd P.c.frB e') :=
    ⟨q0, q1, q2, q4, q5, by simp only [allocd, qsp], qi, qu, qf, qlk, qsy⟩
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q P.c.sign fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold Cfg.sign
  refine rel_alloc ((main_rel hp hp' hq hc).mono ?_ fun _ _ h => h)
  rintro x y ⟨u, v, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem stripConsts_nil (s : State) : stripConsts [] s = s := by
  cases s; simp [stripConsts, State.withRegions]

theorem constsOk_nil (st : Nat) (s : State) : ConstsOk [] st s :=
  ⟨by simp [constRegs, Abi.constRegions], fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

end VG.Proof.Ecdsa.Rfc6979.RISCV64
