module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.CT
public import VerifiedGarbage.Proof.HashTable.Arm
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.CT
meta import VerifiedGarbage.Proof.HashTable.Arm
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`):
`vg_ecdsa_<curve>_sign` (`signCode`) loads the index of the hash function
from the table `hash` (its word 3; `hash` is stack argument 1) into `r12`
and runs the code for that index's digest length and block size (`cfgT`,
chosen by comparisons, `byIdx_wp`, `byIdx_ct`), which calls the table's
functions. For the variants `vs` of the hash functions that pass the
registration's checks (`OK`), the table of each variant `w` makes it the
code for `w`'s hash function (`hashOf`, with `cfgT_eq`), which meets the
contract with that hash function fixed (`sign_ok`, `sign_ct`). `tabK`
states that contract for whichever of the tables `hash` holds, on entry;
`TableSpec.lean` shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.HashTable.Arm (TVar tables fnsOf names Coh tableOf mem_names tabOK_of)
open VG.Proof.RsaOaep.Arm (tA)
open VG.Proof.X25519.Arm (op2_imm)

/-! ## The choice by the index -/

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def TwoA {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂

theorem twoA_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (TwoA Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (TwoA Φ) c (TwoA Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂⟩

theorem twoA_mono {α : Type} {Φ Φ' : α → State → Prop} (h : ∀ a s, Φ a s → Φ' a s) {s₁ s₂ : State}
    (hp : TwoA Φ s₁ s₂) : TwoA Φ' s₁ s₂ :=
  let ⟨a, h₁, h₂⟩ := hp; ⟨a, h a _ h₁, h a _ h₂⟩

/-- A branch whose condition `Φ a` fixes. -/
theorem twoA_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (TwoA fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (TwoA fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (TwoA Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩

/-- The comparison of `r12` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.cmp .r12 (.imm (BitVec.ofNat 32 j))]

/-- What the comparisons with the indices `is` need: immediates that encode. -/
def CmpOk (is : List Nat) : Prop := ∀ j ∈ is, j < 256 ∧ encodable (BitVec.ofNat 32 j) = true

theorem cmpOk_idxs : CmpOk idxs := by unfold CmpOk idxs; decide

theorem sub_beq {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) :
    (BitVec.ofNat 32 i - BitVec.ofNat 32 j == 0) = decide (i = j) := by
  by_cases h : i = j
  · subst h; simp
  · have hne : BitVec.ofNat 32 i ≠ BitVec.ofNat 32 j := fun e => h (by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
      exact this)
    have : BitVec.ofNat 32 i - BitVec.ofNat 32 j ≠ 0 := fun e => hne (by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 i) (BitVec.ofNat 32 j), e]; exact BitVec.zero_add _)
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

/-- A comparison of `r12` with `j`: the state kept but for the flags. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 256) (hj : j < 256) (he : encodable (BitVec.ofNat 32 j) = true)
    (h12 : t.gpr .r12 = BitVec.ofNat 32 i) :
    WP isa (cmpIdx j) t fun t' => FupdS t t' ∧ isa.eval .eq t' = some (decide (i = j)) :=
  wp_cmpS (op2_imm he) fun t' v z => WP.block_nil ⟨v, by
    show some t'.z = _; rw [z, h12, sub_beq (by omega) (by omega)]⟩

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → CmpOk is → t.gpr .r12 = BitVec.ofNat 32 i →
    (∀ t', FupdS t t' → WP isa (b i) t' Q) → WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi List.not_mem_nil
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | j :: k :: is, i, t, hi, hlt, h12, h => by
    have hil := (hlt i hi).1
    obtain ⟨hjl, hje⟩ := hlt j List.mem_cons_self
    simp only [byIdx]
    refine WP.seq (WP.mono (cmpIdx_ok hil hjl hje h12) fun t' ⟨k', hz⟩ => ?_)
    refine WP.ite (M := isa) _ hz (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      subst hb
      exact h t' k'
    · rw [decide_eq_false_iff_not] at hb
      have hi' : i ∈ k :: is := (List.mem_cons.mp hi).resolve_left hb
      exact byIdx_wp hi' (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) (by rw [k'.gpr]; exact h12)
        fun t'' k'' => h t'' ⟨⟨by rw [k''.gpr, k'.gpr], by rw [k''.mem, k'.mem], by rw [k''.rd, k'.rd],
          by rw [k''.wr, k'.wr], by rw [k''.sp, k'.sp]⟩, by rw [k''.syms, k'.syms]⟩

/-- A comparison accesses no memory. -/
theorem cmpIdx_ct {P : State → State → Prop} (j : Nat) : RelCT isa P (cmpIdx j) fun _ _ => True :=
  block_cons_ct (R := fun _ _ => True) (fun _ _ _ _ _ _ _ => ⟨rfl, trivial⟩) (RelCT.block_nil fun _ _ _ => trivial)

/-- `byIdx b is` in two runs whose `r12` is the index `idx a` of the
anchor: the comparisons, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → FupdS t t' → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .r12 = BitVec.ofNat 32 (idx a)) →
    CmpOk is →
    (∀ j ∈ is, RelCT isa (TwoA fun a t => Φ a t ∧ idx a = j) (b j) Q) →
    RelCT isa (TwoA Φ) (byIdx b is) Q
  | [], _, _, hΦ, _, _ => RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by simpa using (hΦ a _ h₁).1
  | [j], _, _, hΦ, _, hb => (hb j (List.mem_singleton_self _)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁, List.mem_singleton.mp (hΦ a _ h₁).1⟩, ⟨h₂, List.mem_singleton.mp (hΦ a _ h₁).1⟩⟩)
    fun _ _ h => h
  | j :: k :: is, Φ, hkeep, hΦ, hlt, hb => by
    simp only [byIdx]
    have ih := byIdx_ct idx (is := k :: is) (Φ := fun a t => Φ a t ∧ idx a ≠ j)
      (fun a t t' ⟨h, hn⟩ k' => ⟨hkeep a t t' h k', hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => twoA_mono fun _ _ h => ⟨h.1.1, h.2⟩)
        fun _ _ h => h)
    refine RelCT.seq (twoA_post (Ψ := fun a t => Φ a t ∧ isa.eval .eq t = some (decide (idx a = j)))
      (cmpIdx_ct j) fun a t h => ?_) (twoA_ite (fun a t₁ t₂ h₁ h₂ => ?_)
        ((hb j List.mem_cons_self).mono (fun _ _ => twoA_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h)
        (ih.mono (fun _ _ => twoA_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h))
    · obtain ⟨hm, h12⟩ := hΦ a t h
      exact WP.mono (cmpIdx_ok (hlt _ hm).1 (hlt j List.mem_cons_self).1 (hlt j List.mem_cons_self).2 h12)
        fun t' ⟨k', hz⟩ => ⟨hkeep a t t' h k', hz⟩
    · rw [h₁.2, h₂.2]
    · rw [hz] at he
      simpa using he
    · rw [hz] at he
      simpa using he

/-! ## The code -/

/-- The code for the hash function of index `i`, on the curve `R`, with the
bound on candidates `tries` and the tables of `vs`. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : Cfg where
  D := (shapeOf i).1
  B := (shapeOf i).2
  f := fnsOf vs
  w := 2 * R.E.n - (if R.E.C.len = 28 then 1 else 0)
  len := R.E.C.len
  sh := R.sh
  hHigh := R.hHigh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (R : RfcCurve) (tries : Nat) (vs : List TVar) : Prog isa := signT (cfgT R tries vs)

/-- The stack it uses: the most of any hash function's. -/
def stackT : Nat := 512

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), its index is one of the code's, and that index's code is
for `w`'s digest length and block size; and its states fit the ones in
`scratch`. -/
def WOk (w : TVar) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.g.G with
    | some F => F.blockSize = w.g.H.B
    | none => False) ∧
  Spec.HashTable.index w.g.G < 8 ∧ shapeOf (Spec.HashTable.index w.g.G) = (w.g.H.D, w.g.H.B) ∧ w.g.H.S ≤ 192

instance (w : TVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.Ecdsa.Rfc6979.hmacOf w.g.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem shapeOf_mem (i : Nat) : shapeOf i ∈ shapes := by
  unfold shapeOf; split <;> simp [shapes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : TVar} (hw : WOk w) : Spec.Ecdsa.Rfc6979.hmacOf w.g.G = some w.g.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.Ecdsa.Rfc6979.hmacOf w.g.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.Ecdsa.Rfc6979.hmacOf_hash _ (List.mem_of_getElem? w.idx) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.g.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.g.hash x)⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.g.ok.SH.H
  hashLen := w.g.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 16

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List TVar)
    (w : TVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.g.H
  ok := w.g.ok
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  macLen := fun x => by rw [← w.g.hash, w.g.valid.2, w.g.glen]
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.2.1 ▸ shapeOf_mem _
  hS := hw.2.2.2
  hWb := by have := w.g.ok.hWb; have := w.g.ok.hW; omega

theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List TVar)
    {w : TVar} (hw : WOk w) : cfgT R T.tries vs (Spec.HashTable.index w.g.G) = cfgOf (hashOf hC vs w hw) := by
  unfold cfgT cfgOf; rw [hw.2.2.1]; rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.g.G w.g.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.g.glen]

/-! ## The contract on entry -/

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (w : TVar) (s : State) : Prop :=
  (rfcArm (instOf T w) stackT R.coreConsts (tabFacts w.g.H (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (tA (stackArg s 1) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table `hash` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.g.G w.g.ok.SH.H s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcArm (instOf T w) stackT R.coreConsts (tabFacts w.g.H (fnsOf vs)) (names vs)).pub s₁ s₂

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {I : Spec.Ecdsa.Rfc6979.Instance} {N N' : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} {s : State} (hN : N' ≤ N) (h : (rfcArm I N cs F ns).pre s) :
    (rfcArm I N' cs F ns).pre s := by
  obtain ⟨hrd, hwr, od, og, oc, ot, oa, dc, gc, ct, ca, ko, kd, kg, kc, kt, ka, no, nd, ng, nc, nt, na, hsp,
    tables, hF⟩ := h
  have hsub : Region.Sub (stkR s.sp N') (stkR s.sp N) := Offset.sub_below _ hN (by omega)
  refine ⟨hrd, hwr, od, og, oc, ot, oa, dc, gc, ct, ca, ko.sub_left hsub, kd.sub_left hsub, kg.sub_left hsub,
    kc.sub_left hsub, kt.sub_left hsub, ka.sub_left hsub, no, nd, ng, nc, nt, na, by omega,
    fun c hc => ⟨(tables c hc).1, (tables c hc).2.1, fun r hr => ?_, (tables c hc).2.2.2⟩, hF⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (tables c hc).2.2.1 _ (by simp)
  · exact (tables c hc).2.2.1 _ (by simp)
  · exact ((tables c hc).2.2.1 _ (by simp)).sub_right hsub

/-- The contract the proof is written against, of a state with the same
arguments, regions, memory and symbols. -/
theorem rfc_congr {I : Spec.Ecdsa.Rfc6979.Instance} {N : Nat} {cs : List (String × List (BitVec 64))}
    {G : Impl.Pbkdf2.Stream.Arm.Hash} {f : Impl.RsaOaep.Arm.Fns} {ns : List String} {s t : State}
    (h : (rfcArm I N cs (tabFacts G f) ns).pre s)
    (hg : ∀ r ∈ [Reg.r0, .r1, .r2], t.gpr r = s.gpr r) (hsp : t.sp = s.sp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcArm I N cs (tabFacts G f) ns).pre t := by
  have e₀ := hg .r0 (by simp); have e₁ := hg .r1 (by simp); have e₂ := hg .r2 (by simp)
  simp only [rfcArm, TablesOk, tabFacts, tabR, argsR, stkR, stackArg, stackArgAddr] at h ⊢
  rw [e₀, e₁, e₂, hsp, hrd, hwr, hm, hsy]
  exact h

/-! ## Correctness -/

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Spec.Mgf1.hashes) (hG' : G' ∈ Spec.Mgf1.hashes)
    (h : Spec.HashTable.index G = Spec.HashTable.index G') : G = G' := by
  simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : TVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 32 (Spec.HashTable.index w'.g.G) = BitVec.ofNat 32 (Spec.HashTable.index w.g.G)) :
    w'.g.G = w.g.G ∧ w'.g.ok.SH.H = w.g.ok.SH.H := by
  have e : Spec.HashTable.index w'.g.G = Spec.HashTable.index w.g.G := by
    have h₁ := hw.2.1; have h₂ := hw'.2.1
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG := index_inj (List.mem_of_getElem? w'.idx) (List.mem_of_getElem? w.idx) e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

theorem exec_ldrSp {s : State} {t : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    exec (.ldrSp t off) s = some (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  simp only [reduceExec, ho, ite_true, State.load32, h, Option.map_some]

/-- What `entry` leaves: the table's word 3 in `r12`, and all else. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .r12 → u.gpr r = σ.gpr r) ∧ u.gpr .r12 = σ.mem.readW (tA (stackArg σ 1) 12) 32 ∧
    u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.syms = σ.syms

/-- `entry`: the table's index to `r12`. -/
theorem tentry_ok {I : Spec.Ecdsa.Rfc6979.Instance} {N : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} {s : State} (h : (rfcArm I N cs F ns).pre s) :
    WP isa (.block entry) s (EntryF s) := by
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nt, na, -⟩ := h
  have h1 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4 := by
    refine ⟨argsR s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 8⟩ : Region).Contains _ 4
    rw [Nat.mul_zero, BitVec.add_zero, addr_add (by omega)]
    exact Offset.contains_base _ (by decide) (by omega)
  let u₁ := s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32)
  have hu₁ : u₁.gpr .r12 = stackArg s 1 := by simp only [u₁, State.setReg, ↓reduceIte]; rfl
  have h2 : InRegions (u₁.rd ++ u₁.wr) (State.addr (u₁.gpr .r12 + BitVec.ofNat 32 12)) 4 := by
    rw [hu₁]
    refine ⟨tabR s, List.mem_append_left _ (by show tabR s ∈ s.rd; rw [hrd]; simp), ?_⟩
    rw [addr_add (by omega)]
    exact Offset.contains_base _ (by decide) (by omega)
  refine VG.Proof.X25519.Arm.WP.cons (exec_ldrSp (by decide) h1)
    (VG.Proof.X25519.Arm.WP.cons (exec_ldr (by decide) h2) (WP.block_nil ?_))
  refine ⟨fun r hr => ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [State.setReg, hr, ↓reduceIte]
  · simp only [State.setReg, ↓reduceIte]
    rfl

theorem idx_mem {w : TVar} (hw : WOk w) : Spec.HashTable.index w.g.G ∈ idxs := by
  have := hw.2.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The frame of the hash function's code fits the stack. -/
theorem stack_le (P : RfcHash) : 240 + 4 * P.e ≤ stackT := by
  have := P.wsizes
  show _ ≤ 512; omega

/-- After `entry` and the comparisons: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : TVar} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hg : ∀ r, r ≠ .r12 → t.gpr r = s.gpr r) (hsp : t.sp = s.sp) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsy : t.syms = s.syms) :
    (rfcP (hashOf hC vs w hw) (names vs)).pre t :=
  rfc_mono (stack_le _) (rfc_congr hp.1 (fun r hr => hg r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) hsp hrd hwr hm hsy)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and the stack pointer. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCode R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCode signT
  refine WP.seq (WP.mono (tentry_ok hp.1) fun t ⟨hg, h12, hm, hrd, hwr, hsp, hsy⟩ => ?_)
  refine byIdx_wp (idx_mem hw) cmpOk_idxs (h12.trans hp.2) fun t' k' => ?_
  rw [cfgT_eq hC vs hw]
  have hg' : ∀ r, r ≠ .r12 → t'.gpr r = s.gpr r := fun r hr => by rw [k'.gpr]; exact hg r hr
  have hpre := pre_at hC hw hp hg' (k'.sp.trans hsp) (k'.mem.trans hm) (k'.rd.trans hrd) (k'.wr.trans hwr)
    (k'.syms.trans hsy)
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hsp'⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hne : r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr, hg' r hne]
  · rw [hsp', k'.sp, hsp]
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
    have e₀ := hg' .r0 (by decide)
    have e₁ := hg' .r1 (by decide)
    have e₂ := hg' .r2 (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t'.mem (State.addr (t'.gpr .r1)) (State.addr (t'.gpr .r2))).1 with
      | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem
          (State.addr (t'.gpr .r0)) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧ Spec.Ecdsa.bytesAt s'.mem
          (State.addr (t'.gpr .r0)) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₀, e₁, e₂, k'.mem.trans hm] at hpost'
    exact hpost'

/-! ## Constant time -/

/-- Public data that agree. -/
theorem pub_trans {I : Spec.Ecdsa.Rfc6979.Instance} {N N' : Nat} {cs : List (String × List (BitVec 64))}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h₁ : (rfcArm I N cs F ns).pub a b)
    (h₂ : (rfcArm I N cs F ns).pub a c) : (rfcArm I N' cs F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, fun c hc => (p₈ c hc).symm.trans (q₈ c hc),
    fun n hn => (p₉ n hn).symm.trans (q₉ n hn)⟩

theorem pub_refl {I : Spec.Ecdsa.Rfc6979.Instance} {N : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} (a : State) : (rfcArm I N cs F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same arguments, memory and symbols. -/
theorem pub_congr {I : Spec.Ecdsa.Rfc6979.Instance} {N N' : Nat} {cs : List (String × List (BitVec 64))}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcArm I N cs F ns).pub a b)
    (hg : ∀ r ∈ [Reg.r0, .r1, .r2], c.gpr r = b.gpr r) (hsp : c.sp = b.sp) (hm : c.mem = b.mem)
    (hsy : c.syms = b.syms) : (rfcArm I N' cs F' ns).pub a c := by
  have e₀ := hg .r0 (by simp); have e₁ := hg .r1 (by simp); have e₂ := hg .r2 (by simp)
  simp only [rfcArm, stackArg, stackArgAddr] at h ⊢
  rw [e₀, e₁, e₂, hsp, hm, hsy]
  exact h

/-- The proof's hash function and the public data: the variant `w` (by its
place in `vs`), and the state the other run agrees with. -/
abbrev Anc (vs : List TVar) := _root_.Fin vs.length × State

/-- The variant of `a`. -/
abbrev Anc.w (a : Anc vs) : TVar := vs.get a.1

theorem Anc.hv (a : Anc vs) : a.w ∈ vs := List.get_mem _ _

/-- After `entry`: the contract with `a.w`'s hash function fixed, public
data that agree with `a.2`'s, and the table's index in `r12`. -/
def PhiT (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t : State) : Prop :=
  (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pre t ∧
    (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pub a.2 t ∧
    t.gpr .r12 = BitVec.ofNat 32 (Spec.HashTable.index a.w.g.G)

theorem entryF_ok {w : TVar} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) :=
  tentry_ok h.1

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK R T vs).pre σ₁ ∧ (tabK R T vs).pre σ₂ ∧ (tabK R T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  refine (RelCT.wpDep (Q := fun _ _ => True) (F := EntryF) ?_
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨entryF_ok h₁, entryF_ok h₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  unfold entry
  refine block_cons_ct (R := fun a b => a.gpr .r12 = b.gpr .r12)
    (fun a b a' b' ⟨_, _, w, _, _, p₁, p₂, hpub⟩ ha hb => ?_) ?_
  · obtain ⟨hsp, -, -, -, -, ha1, -⟩ := hpub
    obtain ⟨hrd₁, -⟩ := p₁.1
    obtain ⟨hrd₂, -⟩ := p₂.1
    have n₁ := p₁.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have n₂ := p₂.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hin : ∀ {s : State}, s.rd = [⟨State.addr (s.gpr .r1), T.ecdsa.curve.len⟩,
        ⟨State.addr (s.gpr .r2), w.g.H.D⟩, tabR s, argsR s] ++
          Abi.constRegions (fun n => State.addr (s.syms n)) R.coreConsts → s.sp.toNat + 8 ≤ 2 ^ 32 →
        InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4 := fun {s} hrd hna => by
      refine ⟨argsR s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
      show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 8⟩ : Region).Contains _ 4
      rw [Nat.mul_zero, BitVec.add_zero, addr_add (by omega)]
      exact Offset.contains_base _ (by decide) (by omega)
    rw [exec_ldrSp (by decide) (hin hrd₁ n₁)] at ha
    rw [exec_ldrSp (by decide) (hin hrd₂ n₂)] at hb
    cases ha; cases hb
    refine ⟨by show [_] = [_]; rw [hsp], ?_⟩
    simp only [State.setReg, ↓reduceIte]
    exact ha1
  · refine block_cons_ct (R := fun _ _ => True) (fun a b a' b' h _ _ => ⟨?_, trivial⟩)
      (RelCT.block_nil fun _ _ _ => trivial)
    show [_] = [_]; rw [h]

theorem phiT_keep (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t t' : State) (h : PhiT hC hO a t)
    (k : FupdS t t') : PhiT hC hO a t' :=
  ⟨rfc_mono (Nat.le_refl _) (rfc_congr h.1 (fun r _ => by rw [k.gpr]) k.sp k.rd k.wr k.mem k.syms),
    pub_congr h.2.1 (fun r _ => by rw [k.gpr]) k.sp k.mem k.syms, by rw [k.gpr]; exact h.2.2⟩

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table's branch, which is constant time for its hash function. -/
theorem signT_ct (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCode R T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCode signT
  refine entry_ct.seq ((byIdx_ct (α := Anc vs) (b := fun i => (cfgT R T.tries vs i).sign) (Q := fun _ _ => True)
    (fun a : Anc vs => Spec.HashTable.index a.w.g.G) (Φ := PhiT hC hO) (phiT_keep hC hO)
    (fun (a : Anc vs) _ h => ⟨idx_mem (hO _ a.hv), h.2.2⟩) cmpOk_idxs
    fun j _ => ?_).mono ?_ fun _ _ h => h)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, ⟨h₁, e⟩, ⟨h₂, _⟩⟩ e₁ e₂
    subst e
    rw [cfgT_eq hC vs (hO _ a.hv)] at e₁ e₂
    have hns : ∀ n ∈ [(hashOf hC vs a.w (hO _ a.hv)).H.initN, (hashOf hC vs a.w (hO _ a.hv)).H.updN,
        (hashOf hC vs a.w (hO _ a.hv)).H.finN], n ∈ names vs := by
      have := mem_names a.hv
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2
    exact ⟨sign_ct hns s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 (pub_trans h₁.2.1 h₂.2.1) e₁ e₂, trivial⟩
  · rintro u₁ u₂ ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩
    have reg : ∀ {σ u : State}, EntryF σ u → ∀ r ∈ [Reg.r0, .r1, .r2], u.gpr r = σ.gpr r :=
      fun {σ u} f r hr => f.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    have q₁ := pre_at hC hw p₁ f₁.1 f₁.2.2.2.2.2.1 f₁.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1 f₁.2.2.2.2.2.2
    have q₂ := pre_at hC hw p₂ f₂.1 f₂.2.2.2.2.2.1 f₂.2.2.1 f₂.2.2.2.1 f₂.2.2.2.2.1 f₂.2.2.2.2.2.2
    obtain ⟨k, rfl⟩ := List.get_of_mem hv
    have pu : (rfcP (hashOf hC vs (vs.get k) (hO _ (List.get_mem _ _))) (names vs)).pub u₁ u₂ :=
      pub_trans (a := σ₁) (N := stackT) (F := tabFacts (vs.get k).g.H (fnsOf vs))
        (pub_congr (pub_refl (N := stackT) (F := tabFacts (vs.get k).g.H (fnsOf vs)) _) (reg f₁)
          f₁.2.2.2.2.2.1 f₁.2.2.1 f₁.2.2.2.2.2.2)
        (pub_congr hpub (reg f₂) f₂.2.2.2.2.2.1 f₂.2.2.1 f₂.2.2.2.2.2.2)
    exact ⟨(k, u₁), ⟨q₁, pub_refl _, f₁.2.1.trans p₁.2⟩, ⟨q₂, pu, f₂.2.1.trans p₂.2⟩⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
