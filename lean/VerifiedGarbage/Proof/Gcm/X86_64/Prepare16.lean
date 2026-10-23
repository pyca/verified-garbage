module

public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareAvx.Step
public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_aes_gcm_prepare16_vpclmul`

`Prepare16.prepare16`: the setup leaves `H'` in `xmm3`, and each step of
`plan` computes a pair from two the registers hold, in each lane (on the
SSE code of `PrepareAvx`, `WP.lanes`), or puts two lower lanes together, or
stores a pair. `Inv` says which power each lane of each register holds, and
which pairs are stored; `valid`, decided on the plan, checks each step
against it (`op_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Prepare16

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Prepare16 (Op plan setup mulD fold prepare16)
open VG.Impl.Gcm.X86_64.Stitch (storesK)
open VG.Proof.Gcm.X86_64.PrepareAvx (sqS mulDS sqS_ok mulDS_ok scratch not_scratch)
open VG.Proof.Gcm.X86_64.Pclmul (Only eq_prepared const_ok ldrev_ok hInv_ok rev_eq)
open VG.Proof.Gcm.X86_64.Stitch (in_sub_int storesK_ok)
open VG.Proof.Gcm.X86_64.Prepare (bytesAt_frame satState)
open VG.Spec.Gcm (Block hpow)

/-- What `vg_aes_gcm_prepare16` does from `s₀`: the 16 prepared powers of the
hash subkey at `C + 240` into pairs 0–7 of the context at `C`, nothing else
written, and the registers but `rax` kept. -/
def PrepOk16 (s₀ s : State) : Prop :=
  (∀ k < 8, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 256⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-! ## The steps, lane by lane -/

theorem lane_sq {d a : XReg} (ha8 : a ≠ .xmm8) (ha10 : a ≠ .xmm10) (hd8 : d ≠ .xmm8) (hd10 : d ≠ .xmm10) :
    laneSseBlock (Impl.Gcm.X86_64.Prepare16.sq d a) = some (sqS d a) := by
  simp [Impl.Gcm.X86_64.Prepare16.sq, fold, sqS, Impl.Gcm.X86_64.Pclmul.fold, laneSseBlock, laneSse, laneSseV, VBinOp.sse,
    ha8, ha10, Ne.symm hd8, Ne.symm hd10]

theorem lane_mulD {d a b : XReg} (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10) (ha11 : a ≠ .xmm11)
    (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11)
    (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10) :
    laneSseBlock (mulD d a b) = some (mulDS d a b) := by
  simp [mulD, fold, mulDS, Impl.Gcm.X86_64.Pclmul.fold, laneSseBlock, laneSse, laneSseV, VBinOp.sse, ha8,
    ha9, ha10, ha11, hb8, hb9, hb10, hb11, Ne.symm hd9, Ne.symm hd10]

/-- What a lane-wise step keeps. -/
structure Keep (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  lane : ∀ r, r ∉ rs → ∀ l < 2, s'.lane r l = s.lane r l

theorem keep_of {rs : List XReg} {s s' : State} (k : VKeep s s')
    (o : ∀ l < 2, Only rs (s.proj l) (s'.proj l)) : Keep rs s s' :=
  ⟨k.gpr, k.mem, k.rd, k.wr, fun r hr l hl => by simpa using (o l hl).xmm r hr⟩

theorem sqY_ok {d a : XReg} (s : State) (ha8 : a ≠ .xmm8) (ha10 : a ≠ .xmm10)
    (hd8 : d ≠ .xmm8) (hd10 : d ≠ .xmm10) (hd11 : d ≠ .xmm11) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (Impl.Gcm.X86_64.Prepare16.sq d a)) s fun s' =>
      (∀ l < 2, φ (s'.lane d l) = x * φ (s.lane a l) * φ (s.lane a l)) ∧
      Keep [.xmm8, .xmm10, .xmm11, d] s s' :=
  WP.mono (WP.lanes (lane_sq ha8 ha10 hd8 hd10) fun l hl =>
      sqS_ok d a (s.proj l) ha8 ha10 hd8 hd10 hd11 (by simpa using h1 l hl))
    fun s' ⟨k, q⟩ => ⟨fun l hl => by simpa using (q l hl).1, keep_of k fun l hl => (q l hl).2⟩

theorem mulY_ok {d a b : XReg} (s : State) (ha8 : a ≠ .xmm8) (ha9 : a ≠ .xmm9) (ha10 : a ≠ .xmm10)
    (ha11 : a ≠ .xmm11) (hb8 : b ≠ .xmm8) (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11)
    (hd8 : d ≠ .xmm8) (hd9 : d ≠ .xmm9) (hd10 : d ≠ .xmm10) (hd11 : d ≠ .xmm11)
    (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (mulD d a b)) s fun s' =>
      (∀ l < 2, φ (s'.lane d l) = x * φ (s.lane a l) * φ (s.lane b l)) ∧
      Keep [.xmm8, .xmm9, .xmm10, .xmm11, d] s s' :=
  WP.mono (WP.lanes (lane_mulD ha8 ha9 ha10 ha11 hb8 hb9 hb10 hb11 hd9 hd10) fun l hl =>
      mulDS_ok d a b (s.proj l) ha8 ha9 ha10 hb8 hb9 hb10 hb11 hd8 hd9 hd10 hd11 (by simpa using h1 l hl))
    fun s' ⟨k, q⟩ => ⟨fun l hl => by simpa using (q l hl).1, keep_of k fun l hl => (q l hl).2⟩

theorem ins_ok (d a b : XReg) (s : State) :
    WP isa (.block [.vop (.vinserti128 d a b 1)]) s fun s' =>
      s'.lane d 0 = s.lane a 0 ∧ s'.lane d 1 = s.lane b 0 ∧ Keep [d] s s' := by
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ⟨?_, ?_, rfl, rfl, rfl, rfl, fun r hr l hl => ?_⟩⟩
  · simp [VOp.exec, State.setV, State.lane]
  · simp [VOp.exec, State.setV, State.lane]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [hr, VOp.exec, State.setV, State.lane]

/-! ## The plan -/

/-- The power `H'ᵉ` lane `l` of `r` holds, if `e` is known. -/
def Holds (H : Block) (t : State) (r : XReg) (l : Nat) (e : Option Nat) : Prop :=
  ∀ n, e = some n → x * φ (t.lane r l) = φ H ^ n

/-- The powers of the registers: of each lane, if known. -/
abbrev Env := List (XReg × Option Nat × Option Nat)

/-- The power of a product, if both are known. -/
def addE (a b : Option Nat) : Option Nat := a.bind fun m => b.map (m + ·)

/-- No step reads or writes a scratch register; each step's operands hold
powers; each pair stored is the pair of its place. -/
def valid : Env → List Op → Bool
  | _, [] => true
  | env, .sq d a :: ops =>
    !scratch.contains d && !scratch.contains a &&
    (match env.lookup a with
     | some (a0, a1) => valid ((d, a0.map (2 * ·), a1.map (2 * ·)) :: env) ops
     | none => false)
  | env, .mul d a b :: ops =>
    !scratch.contains d && !scratch.contains a && !scratch.contains b &&
    (match env.lookup a, env.lookup b with
     | some (a0, a1), some (b0, b1) => valid ((d, addE a0 b0, addE a1 b1) :: env) ops
     | _, _ => false)
  | env, .ins d a b :: ops =>
    !scratch.contains d &&
    (match env.lookup a, env.lookup b with
     | some (a0, _), some (b0, _) => valid ((d, a0, b0) :: env) ops
     | _, _ => false)
  | env, .st r k :: ops =>
    decide (k < 8) && env.lookup r == some (some (2 * k + 2), some (2 * k + 1)) && valid env ops

/-- The pairs stored by the steps, and before them. -/
def storedAfter : List Nat → List Op → List Nat
  | S, [] => S
  | S, .st _ k :: ops => storedAfter (k :: S) ops
  | S, _ :: ops => storedAfter S ops

/-- What holds between steps. -/
structure Inv (H : Block) (C : Addr) (m₀ : Mem) (env : Env) (S : List Nat) (t : State) : Prop where
  h1 : ∀ l < 2, t.lane .xmm1 l = poly
  pw : ∀ r e0 e1, env.lookup r = some (e0, e1) → r ∉ scratch ∧ Holds H t r 0 e0 ∧ Holds H t r 1 e1
  st : ∀ k ∈ S, k < 8 ∧ ∀ l < 2, t.mem.readW (C + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (hpow H (2 * k + 2 - l))
  fr : Frame [⟨C + BitVec.ofNat 64 256, 256⟩] m₀ t.mem
  rdi : t.gpr .rdi = C
  wr : InRegions t.wr C 1024
  wrap : C.toNat + 1024 ≤ 2 ^ 64

theorem lookup_cons {env : Env} {d r : XReg} {v : Option Nat × Option Nat} :
    ((d, v) :: env).lookup r = if r = d then some v else env.lookup r := by
  rw [List.lookup_cons]
  by_cases h : r = d
  · subst h; simp
  · rw [beq_false_of_ne h]; simp [h]

/-- A register step: `d` gets `v`, and the registers `rs` (scratch, and `d`)
are all it writes. -/
theorem Inv.set {H : Block} {C : Addr} {m₀ : Mem} {env : Env} {S : List Nat} {t t' : State} {d : XReg}
    {v : Option Nat × Option Nat} (hi : Inv H C m₀ env S t) (hd : d ∉ scratch)
    (k : Keep [.xmm8, .xmm9, .xmm10, .xmm11, d] t t')
    (h0 : Holds H t' d 0 v.1) (h1 : Holds H t' d 1 v.2) :
    Inv H C m₀ ((d, v) :: env) S t' := by
  obtain ⟨d1, d8, d9, d10, d11⟩ := not_scratch hd
  refine ⟨fun l hl => ?_, fun r e0 e1 hr => ?_, fun j hj => ?_, by rw [k.mem]; exact hi.fr,
    by rw [k.gpr]; exact hi.rdi, by rw [k.wr]; exact hi.wr, hi.wrap⟩
  · rw [k.lane _ (by simp [Ne.symm d1]) l hl]; exact hi.h1 l hl
  · rw [lookup_cons] at hr
    split at hr
    · next hrd => subst hrd; cases hr; exact ⟨hd, h0, h1⟩
    · next hrd =>
      obtain ⟨hs, p0, p1⟩ := hi.pw r e0 e1 hr
      obtain ⟨-, r8, r9, r10, r11⟩ := not_scratch hs
      have kr : ∀ l < 2, t'.lane r l = t.lane r l := k.lane r (by simp [r8, r9, r10, r11, hrd])
      exact ⟨hs, fun n hn => by rw [kr 0 (by decide)]; exact p0 n hn,
        fun n hn => by rw [kr 1 (by decide)]; exact p1 n hn⟩
  · rw [k.mem]; exact hi.st j hj

theorem keep_weaken {rs rs' : List XReg} {s s' : State} (k : Keep rs s s') (h : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s s' := ⟨k.gpr, k.mem, k.rd, k.wr, fun r hr => k.lane r fun h' => hr (h r h')⟩

theorem pow_mul {H : Block} {a b d : Q} {m n : Nat} (hd : d = x * a * b) (ha : x * a = φ H ^ m)
    (hb : x * b = φ H ^ n) : x * d = φ H ^ (m + n) := by
  rw [hd, show x * (x * a * b) = (x * a) * (x * b) by ring, ha, hb, pow_add]

theorem holds_mul {H : Block} {t t' : State} {d a b : XReg} {l : Nat} {ea eb : Option Nat}
    (he : φ (t'.lane d l) = x * φ (t.lane a l) * φ (t.lane b l)) (ha : Holds H t a l ea)
    (hb : Holds H t b l eb) : Holds H t' d l (addE ea eb) := fun n hn => by
  simp only [addE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hn
  obtain ⟨m, hm, n', hn', rfl⟩ := hn
  exact pow_mul he (ha m hm) (hb n' hn')

theorem holds_sq {H : Block} {t t' : State} {d a : XReg} {l : Nat} {ea : Option Nat}
    (he : φ (t'.lane d l) = x * φ (t.lane a l) * φ (t.lane a l)) (ha : Holds H t a l ea) :
    Holds H t' d l (ea.map (2 * ·)) := fun n hn => by
  simp only [Option.map_eq_some_iff] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  rw [two_mul]; exact pow_mul he (ha m hm) (ha m hm)

/-- One step. -/
theorem op_ok {H : Block} {C : Addr} {m₀ : Mem} {env : Env} {S : List Nat} {op : Op} {ops : List Op}
    (hv : valid env (op :: ops) = true) (t : State) (hi : Inv H C m₀ env S t) :
    WP isa (.block op.code) t fun t' =>
      ∃ env', valid env' ops = true ∧ Inv H C m₀ env' (storedAfter S [op]) t' ∧
        (∀ q, q ≠ .rax → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  cases op with
  | sq d a =>
    simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hv
    obtain ⟨⟨hd, ha⟩, hm⟩ := hv
    obtain ⟨-, a8, -, a10, -⟩ := not_scratch ha
    obtain ⟨-, d8, -, d10, d11⟩ := not_scratch hd
    revert hm
    cases hl : env.lookup a with
    | none => simp
    | some p =>
      obtain ⟨a0, a1⟩ := p
      intro hm
      obtain ⟨-, pa0, pa1⟩ := hi.pw a a0 a1 hl
      refine WP.mono (sqY_ok t a8 a10 d8 d10 d11 hi.h1) fun t' ⟨e, k⟩ =>
        ⟨_, hm, hi.set hd (keep_weaken k fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h])
          (holds_sq (e 0 (by decide)) pa0) (holds_sq (e 1 (by decide)) pa1),
          fun q _ => by rw [k.gpr], k.rd, k.wr⟩
  | mul d a b =>
    simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hv
    obtain ⟨⟨⟨hd, ha⟩, hb⟩, hm⟩ := hv
    obtain ⟨-, a8, a9, a10, a11⟩ := not_scratch ha
    obtain ⟨-, b8, b9, b10, b11⟩ := not_scratch hb
    obtain ⟨-, d8, d9, d10, d11⟩ := not_scratch hd
    revert hm
    cases hla : env.lookup a with
    | none => simp
    | some p =>
      cases hlb : env.lookup b with
      | none => simp
      | some q =>
        obtain ⟨a0, a1⟩ := p
        obtain ⟨b0, b1⟩ := q
        intro hm
        obtain ⟨-, pa0, pa1⟩ := hi.pw a a0 a1 hla
        obtain ⟨-, pb0, pb1⟩ := hi.pw b b0 b1 hlb
        exact WP.mono (mulY_ok t a8 a9 a10 a11 b8 b9 b10 b11 d8 d9 d10 d11 hi.h1) fun t' ⟨e, k⟩ =>
          ⟨_, hm, hi.set hd k (holds_mul (e 0 (by decide)) pa0 pb0) (holds_mul (e 1 (by decide)) pa1 pb1),
            fun q _ => by rw [k.gpr], k.rd, k.wr⟩
  | ins d a b =>
    simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hv
    obtain ⟨hd, hm⟩ := hv
    revert hm
    cases hla : env.lookup a with
    | none => simp
    | some p =>
      cases hlb : env.lookup b with
      | none => simp
      | some q =>
        obtain ⟨a0, a1⟩ := p
        obtain ⟨b0, b1⟩ := q
        intro hm
        obtain ⟨-, pa0, -⟩ := hi.pw a a0 a1 hla
        obtain ⟨-, pb0, -⟩ := hi.pw b b0 b1 hlb
        exact WP.mono (ins_ok d a b t) fun t' ⟨e0, e1, k⟩ =>
          ⟨_, hm, hi.set hd (keep_weaken k fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; simp [hr])
            (fun n hn => by rw [e0]; exact pa0 n hn) (fun n hn => by rw [e1]; exact pb0 n hn),
            fun q _ => by rw [k.gpr], k.rd, k.wr⟩
  | st r j =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
    obtain ⟨⟨hj, hl⟩, hm⟩ := hv
    obtain ⟨-, p0, p1⟩ := hi.pw r _ _ hl
    have hin : ∀ k < [r].length, InRegions t.wr (t.gpr .rdi + BitVec.ofInt 64 ((32 * (8 + j + k) : Nat) : Int)) 32 :=
      fun k hk => by
        simp only [List.length_singleton] at hk
        rw [hi.rdi]; exact in_sub_int hi.wr (by omega)
    refine WP.mono (storesK_ok .rdi [r] (8 + j) t hin (by rw [hi.rdi]; simp only [List.length_singleton]; have := hi.wrap; omega))
      fun t' ⟨sv, sf, g, rd, wr, ln⟩ => ⟨env, hm, ⟨fun l hl => by rw [ln]; exact hi.h1 l hl,
        fun q e0 e1 hq => ?_, fun k hk => ?_, ?_, by rw [g]; exact hi.rdi, by rw [wr]; exact hi.wr, hi.wrap⟩,
        fun q _ => by rw [g], rd, wr⟩
    · obtain ⟨hs, q0, q1⟩ := hi.pw q e0 e1 hq
      exact ⟨hs, fun n hn => by rw [ln]; exact q0 n hn, fun n hn => by rw [ln]; exact q1 n hn⟩
    · rw [hi.rdi] at sv sf
      simp only [List.length_singleton, Nat.mul_one] at sf
      simp only [storedAfter, List.mem_cons] at hk
      by_cases hkj : k = j
      · subst hkj
        refine ⟨hj, fun l hl => ?_⟩
        have e := sv 0 (by simp) l hl
        rw [show 32 * (8 + k + 0) + 16 * l = 256 + 32 * k + 16 * l by omega] at e
        rw [e]
        simp only [List.getElem_cons_zero]
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact eq_prepared (p0 _ rfl)
        · exact eq_prepared (p1 _ rfl)
      · obtain ⟨hk8, hs⟩ := hi.st k (hk.resolve_left hkj)
        refine ⟨hk8, fun l hl => ?_⟩
        rw [← hs l hl]
        exact sf.readW (Region.contains_self _ _) (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact Offset.disjoint C (by omega) (by omega) (by have := hi.wrap; omega)) (by decide)
    · rw [hi.rdi] at sf
      simp only [List.length_singleton, Nat.mul_one] at sf
      exact hi.fr.trans (sf.sub fun r' hr' => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact Offset.sub C (by omega) (by omega)⟩)

/-- The steps, one after the other. -/
theorem plan_ok {H : Block} {C : Addr} {m₀ : Mem} :
    ∀ (ops : List Op) (env : Env) (S : List Nat) (t : State), valid env ops = true →
      Inv H C m₀ env S t →
      WP isa (.block (ops.flatMap Op.code)) t fun t' =>
        (∃ env', Inv H C m₀ env' (storedAfter S ops) t') ∧ (∀ q, q ≠ .rax → t'.gpr q = t.gpr q) ∧
          t'.rd = t.rd ∧ t'.wr = t.wr
  | [], env, _, _, _, hi => WP.block_nil ⟨⟨env, hi⟩, fun _ _ => rfl, rfl, rfl⟩
  | op :: ops, env, S, t, hv, hi => by
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (op_ok hv t hi) fun t₁ ⟨env₁, hv₁, hi₁, g₁, rd₁, wr₁⟩ => ?_
    have e : storedAfter S (op :: ops) = storedAfter (storedAfter S [op]) ops := by
      cases op <;> rfl
    rw [e]
    refine WP.mono (plan_ok ops env₁ _ t₁ hv₁ hi₁) fun t' ⟨hi', g', rd', wr'⟩ =>
      ⟨hi', fun q hq => by rw [g' q hq, g₁ q hq], rd'.trans rd₁, wr'.trans wr₁⟩

theorem plan_valid : valid [(.xmm3, some 1, none)] plan = true := by decide

theorem plan_stored : ∀ k < 8, k ∈ storedAfter [] plan := by decide

/-- The setup: `H'` in `xmm3`, and the reduction constant in both lanes. -/
theorem setup_ok (t : State) (hw : InRegions t.wr (t.gpr .rdi) 1024) (hwrap : (t.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) :
    WP isa (.block setup) t fun t' =>
      Inv (Spec.Gcm.ctxH t.mem (t.gpr .rdi)) (t.gpr .rdi) t.mem [(.xmm3, some 1, none)] [] t' ∧
        (∀ q, q ≠ .rax → t'.gpr q = t.gpr q) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofInt 64 ((240 : Nat) : Int)) 16 := by
    obtain ⟨r, hr, hc⟩ := in_sub_int (off := 240) (n := 16) hw (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ t (by decide)) fun t₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ t₁ (by decide)) fun t₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 t₂ (by decide) (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact hin)) fun t₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok t₃) fun t₄ ⟨h₄, o₄⟩ => ?_
  have o₁₄ := (o₁₂.trans o₃).trans o₄
  rw [o₁₂.mem, o₁₂.gpr _ (by decide)] at l₃
  have p₁ : t₄.xmm .xmm1 = poly := by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  refine WP.mono (ins_ok .xmm1 .xmm1 .xmm1 t₄) fun t' ⟨e0, e1, k⟩ =>
    ⟨⟨fun l hl => ?_, fun r e0 e1 hr => ?_, fun j hj => absurd hj (by simp),
      by rw [k.mem, o₁₄.mem]; exact Frame.refl _ _, by rw [k.gpr, o₁₄.gpr _ (by decide)],
      by rw [k.wr, o₁₄.wr]; exact hw, hwrap⟩,
      fun q hq => by rw [k.gpr, o₁₄.gpr q hq], by rw [k.rd, o₁₄.rd], by rw [k.wr, o₁₄.wr]⟩
  · rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · rw [e0]; exact p₁
    · rw [e1]; exact p₁
  · rw [lookup_cons] at hr
    split at hr
    · next h =>
      subst h; cases hr
      refine ⟨by decide, fun n hn => ?_, fun n hn => by cases hn⟩
      cases hn
      rw [k.lane _ (by decide) 0 (by decide), pow_one]
      show x * φ (t₄.xmm .xmm3) = _
      rw [h₄, l₃, BitVec.ofInt_natCast]
      rfl
    · cases hr

/-- `prepare16`: the 16 prepared powers of the hash subkey at `C + 240` into
pairs 0–7 of the context at `C`, nothing else written. -/
theorem prepare16_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hwrap : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) :
    WP isa prepare16 s₀ (PrepOk16 s₀) := by
  simp only [prepare16]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (setup_ok s₀ hw hwrap) fun t₁ ⟨hi₁, g₁, rd₁, wr₁⟩ => ?_
  refine WP.mono (plan_ok plan _ _ t₁ plan_valid hi₁) fun t₂ ⟨⟨_, hi₂⟩, g₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (Prepare.vzu_ok t₂) fun s ⟨g, m, rd, wr⟩ =>
    ⟨fun k hk l hl => ?_, by rw [m]; exact hi₂.fr, fun r hr => by rw [g, g₂ r hr, g₁ r hr],
      by rw [rd, rd₂, rd₁], by rw [wr, wr₂, wr₁]⟩
  rw [m]; exact (hi₂.st k (plan_stored k hk)).2 l hl

/-- It writes none of the context from byte 512 on. -/
theorem prepare16_written (s : State) (t : List Leak) (s' : State)
    (hs : (Spec.Gcm.prepare16Contract X86_64.abi).pre s) (he : Exec isa prepare16 s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Gcm.prepareSig [("ctx", 512)] s s' :=
  written16 (fun _ hw hwrap => WP.mono (prepare16_ok hw hwrap) fun _ h => h.2.1) s t s' hs he

theorem correct16 {s₀ : State} (hp : prepare16X86_64.pre s₀) :
    WP isa prepare16 s₀ fun s => gprPreserved s₀ s ∧ prepare16X86_64.post s₀ s := by
  obtain ⟨_, hwr, hwrap, hret⟩ := hp
  have hw : InRegions s₀.wr (s₀.gpr .rdi) 1024 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (prepare16_ok hw hwrap) fun s ⟨pw, fr, g, _, _⟩ => ?_
  have keep : Spec.Aes.bytesAt s.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) 256 :=
    bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  have hH : Spec.Gcm.ctxH s.mem (s₀.gpr .rdi) = Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi) := by
    simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
    rw [bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (Offset.disjoint (s₀.gpr .rdi) (d := 240) (n := 16) (e := 256) (k := 256) (.inl (by decide)) (by decide)
        (by omega)).sub_left (Region.sub_prefix (Nat.le_refl _))) (by decide)]
  refine ⟨⟨fun r hr => g r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩, keep, fun k hk => ?_⟩
  · exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)
  · rw [hH]
    have p0 := pw k hk 0 (by decide)
    have p1 := pw k hk 1 (by decide)
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
    rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
    exact ⟨p0, p1⟩

theorem prepare16_correct (s : State) (hs : prepare16X86_64.pre s) :
    ∃ t s', Exec isa prepare16 s t s' ∧ abiPreserved s s' ∧ prepare16X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct16 hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem prepare16_verified :
    Verified X86_64.target prepare16 (Spec.Gcm.prepare16Contract X86_64.abi) :=
  Verified.of_correct prepare16_correct prepare16_ct (by
    sig_implies [Spec.Gcm.prepare16Contract, Spec.Gcm.prepareSig, Spec.Gcm.prepare16Post, prepare16X86_64,
      X86_64.abi, X86_64.argRegs] [satState] using satState)

end VG.Proof.Gcm.X86_64.Prepare16
