module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CT
public import VerifiedGarbage.Proof.HashTable.X86
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CT
meta import VerifiedGarbage.Proof.HashTable.X86
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
meta import VerifiedGarbage.Proof.RsaPss.X86.NoSp
meta import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety

/-!
# Deterministic ECDSA on x86 (32-bit): the hash function of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): `vg_ecdsa_<curve>_sign`
(`signCode`) loads the table `hash` (our argument 5) and its index (its
word 3) into `ecx` (`entry₁`, `entry₂`), and runs the code for that index's
digest length and block size (`cfgT`), which calls the table's functions
(`byIdx`: `byIdx_wp`, and `byIdx_ct` in two runs with the same `ecx`). For
the variants `vs` of the hash functions that pass the registration's checks
(`OK`: their functions of the same name have the same code, and each is of
one of the hash functions with HMAC, of the sizes its index's code is for),
the table of each variant `w` makes it the code for `w`'s hash function
(`hashOf`, with `cfgT_eq`), which meets the contract with that hash
function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hash` holds, on entry.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.HashTable.X86 (TVar tables fnsOf names Coh tableOf mem_names tabOK_of fnsOf_noSp)
open VG.Proof.Sha256.X86.Stream (Fupd wp_cmpi)

/-! ## The choice by the table's index -/

/-- The comparison of `ecx` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.alu .cmp .ecx (.imm (BitVec.ofNat 32 j))]

theorem ofNat_sub_beq32 {j N : Nat} (hj : j < 2 ^ 32) (hN : N < 2 ^ 32) :
    (BitVec.ofNat 32 j - BitVec.ofNat 32 N == 0) = decide (j = N) := by
  by_cases h : j = N
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have e : BitVec.ofNat 32 j = BitVec.ofNat 32 N := by bv_omega
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hN] at this

/-- A comparison of `ecx`, holding `i`, with `j`: the state kept but for the flags. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32) (hcx : t.gpr .ecx = BitVec.ofNat 32 i) :
    WP isa (cmpIdx j) t fun t' => Fupd t t' ∧ t'.syms = t.syms ∧ isa.eval .e t' = some (decide (i = j)) :=
  WP.mono_syms (Q := fun t' => Fupd t t' ∧ t'.zf = some (t.gpr .ecx - BitVec.ofNat 32 j == 0))
    (wp_cmpi fun t' f _ z => WP.block_nil ⟨f, z⟩) fun t' ⟨f, z⟩ sy =>
    ⟨f, sy, by show eval .e t' = _; simp only [eval, z, hcx, ofNat_sub_beq32 hi hj]⟩

theorem fupd_trans {a b c : State} (h₁ : Fupd a b) (h₂ : Fupd b c) : Fupd a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → (∀ j ∈ is, j < 2 ^ 32) → t.gpr .ecx = BitVec.ofNat 32 i →
    (∀ t', Fupd t t' → t'.syms = t.syms → WP isa (b i) t' Q) → WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi List.not_mem_nil
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t ⟨rfl, rfl, rfl, rfl⟩ rfl
  | j :: k :: is, i, t, hi, hlt, hcx, h => by
    simp only [byIdx]
    refine WP.seq (WP.mono (cmpIdx_ok (hlt i hi) (hlt j (List.mem_cons_self ..)) hcx) fun t' ⟨f, sy, hz⟩ => ?_)
    refine WP.ite (M := isa) _ hz (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      subst hb
      exact h t' f sy
    · rw [decide_eq_false_iff_not] at hb
      exact byIdx_wp ((List.mem_cons.mp hi).resolve_left hb) (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
        (by rw [f.gpr]; exact hcx) fun t'' f' sy' => h t'' (fupd_trans f f') (sy'.trans sy)

theorem cmp_taint (j : Nat) : TaintOk [] [.alu .cmp .ecx (.imm (BitVec.ofNat 32 j))] :=
  taintOk_erase (is₀ := [.alu .cmp .ecx (.imm (BitVec.ofNat 32 0))]) ⟨_, by taint_decide⟩ rfl

/-- `byIdx b is` in two runs whose `ecx` is the index `idx a` of the anchor
`a`: the comparisons, of which nothing leaks, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → Fupd t t' → t'.syms = t.syms → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .ecx = BitVec.ofNat 32 (idx a)) →
    (∀ j ∈ is, j < 2 ^ 32) →
    (∀ j ∈ is, RelCT isa (fun s₁ s₂ => ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ idx a = j) (b j) Q) →
    RelCT isa (fun s₁ s₂ => ∃ a, Φ a s₁ ∧ Φ a s₂) (byIdx b is) Q
  | [], _, _, hΦ, _, _ => RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by simpa using (hΦ a _ h₁).1
  | [j], _, _, hΦ, _, hb => (hb j (List.mem_singleton_self _)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁, h₂, List.mem_singleton.mp (hΦ a _ h₁).1⟩) fun _ _ h => h
  | j :: k :: is, Φ, hkeep, hΦ, hlt, hb => by
    simp only [byIdx]
    have ih := byIdx_ct idx (is := k :: is) (Φ := fun a t => Φ a t ∧ idx a ≠ j)
      (fun a t t' ⟨h, hn⟩ f sy => ⟨hkeep a t t' h f sy, hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ ⟨a, ⟨h₁, _⟩, ⟨h₂, _⟩, e⟩ => ⟨a, h₁, h₂, e⟩)
        fun _ _ h => h)
    have hc : RelCT isa (fun s₁ s₂ => ∃ a, Φ a s₁ ∧ Φ a s₂) (cmpIdx j) fun s₁ s₂ =>
        ∃ a, (Φ a s₁ ∧ isa.eval .e s₁ = some (decide (idx a = j))) ∧
          (Φ a s₂ ∧ isa.eval .e s₂ = some (decide (idx a = j))) := by
      refine RelCT.exists_ (M := isa) (P := fun a (s₁ s₂ : State) => Φ a s₁ ∧ Φ a s₂) fun a => ?_
      obtain ⟨_, ht⟩ := cmp_taint j
      have hw := RelCT.wpDep (M := isa) (P := fun (s₁ s₂ : State) => Φ a s₁ ∧ Φ a s₂) (c := cmpIdx j)
        (F := fun (σ u : State) => Fupd σ u ∧ u.syms = σ.syms ∧ isa.eval .e u = some (decide (idx a = j)))
        (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun r hr => absurd hr (by simp)) ht)
        fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨cmpIdx_ok (hlt _ (hΦ a _ h₁).1) (hlt j (List.mem_cons_self ..)) (hΦ a _ h₁).2,
          cmpIdx_ok (hlt _ (hΦ a _ h₂).1) (hlt j (List.mem_cons_self ..)) (hΦ a _ h₂).2⟩
      refine hw.mono (fun _ _ h => h) ?_
      rintro _ _ ⟨-, σ₁, σ₂, ⟨h₁, h₂⟩, ⟨f₁, sy₁, z₁⟩, ⟨f₂, sy₂, z₂⟩⟩
      exact ⟨a, ⟨hkeep a _ _ h₁ f₁ sy₁, z₁⟩, ⟨hkeep a _ _ h₂ f₂ sy₂, z₂⟩⟩
    refine RelCT.seq hc (RelCT.ite (fun _ _ ⟨_, ⟨_, z₁⟩, ⟨_, z₂⟩⟩ => z₁.trans z₂.symm) ?_ ?_)
    · exact (hb j (List.mem_cons_self ..)).mono (fun _ _ ⟨⟨a, ⟨h₁, z₁⟩, ⟨h₂, _⟩⟩, he⟩ =>
        ⟨a, h₁, h₂, by rw [z₁] at he; simpa using he⟩) fun _ _ h => h
    · exact ih.mono (fun _ _ ⟨⟨a, ⟨h₁, z₁⟩, ⟨h₂, _⟩⟩, he⟩ =>
        ⟨a, ⟨h₁, by rw [z₁] at he; simpa using he⟩, ⟨h₂, by rw [z₁] at he; simpa using he⟩⟩) fun _ _ h => h

/-! ## The code -/

/-- The code for the hash function of index `i`, on the curve `R`, with the
bound on candidates `tries` and the tables of `vs`. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : Cfg where
  D := (shapeOf i).1
  B := (shapeOf i).2
  f := fnsOf vs
  w := R.E.n
  len := R.E.C.len
  sh := R.sh
  hHigh := R.hHigh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (R : RfcCurve) (tries : Nat) (vs : List TVar) : Prog isa := signT (cfgT R tries vs)

/-- The stack it uses: the most of any hash function's frame and its calls. -/
def stackT : Nat := 544

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), its index is one of the code's, and that index's code is
for `w`'s digest length and block size. -/
def WOk (w : TVar) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.g.G with
    | some F => F.blockSize = w.g.H.B
    | none => False) ∧
  Spec.HashTable.index w.g.G < 8 ∧ shapeOf (Spec.HashTable.index w.g.G) = (w.g.H.D, w.g.H.B)

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
  tries_lt : T.tries < 2 ^ 32

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List TVar)
    (w : TVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.g.H
  ok := w.g.ok
  f := fnsOf vs
  fInit := (fnsOf_noSp vs).1
  fUpd := (fnsOf_noSp vs).2.1
  fFin := (fnsOf_noSp vs).2.2
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  macLen x := by rw [← w.g.hash, w.g.valid.2, w.g.glen]
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.2 ▸ shapeOf_mem _

theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List TVar)
    {w : TVar} (hw : WOk w) : cfgT R T.tries vs (Spec.HashTable.index w.g.G) = cfgOf (hashOf hC vs w hw) := by
  unfold cfgT cfgOf; rw [hw.2.2]; rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.g.G w.g.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.g.glen]

/-! ## The contract on entry -/

/-- The contract with the table of `w`, on entry: the contract the proof is
written against, for `stackT` bytes of stack, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (w : TVar) (s : State) : Prop :=
  (rfcX86 (instOf T w) stackT R.E.combConsts (tabFacts w.g.H (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (addr (arg s 5) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.g.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` our argument 5 is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.g.G w.g.ok.SH.H s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
        bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
        bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcX86 (instOf T w) stackT R.E.combConsts (tabFacts w.g.H (fnsOf vs)) (names vs)).pub s₁ s₂

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} {s : State} (hS : S' ≤ S) (h : (rfcX86 I S cs F ns).pre s) :
    (rfcX86 I S' cs F ns).pre s := by
  obtain ⟨hsp, h28, hrd, hwr, od, og, oc, dc, gc, ao, ac, ro, rc, ko, kd, kg, kc, no, nd, ng, nc, ⟨held, ht⟩, nt,
    tout, tsc, tstk, hF⟩ := h
  have hsub : Region.Sub ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S', S'⟩
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S, S⟩ :=
    Offset.sub_below _ hS (by omega)
  refine ⟨by omega, h28, hrd, hwr, od, og, oc, dc, gc, ao, ac, ro, rc, ko.sub_left hsub, kd.sub_left hsub,
    kg.sub_left hsub, kc.sub_left hsub, no, nd, ng, nc, ⟨held, fun t htm => ⟨(ht t htm).1, fun r hr => ?_⟩⟩, nt,
    tout, tsc, tstk.sub_right hsub, hF⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (ht t htm).2 _ (by simp)
  · exact (ht t htm).2 _ (by simp)
  · exact (ht t htm).2 _ (by simp)
  · exact ((ht t htm).2 _ (by simp)).sub_right hsub

theorem arg_congr {s t : State} (hsp : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (i : Nat) :
    arg t i = arg s i := by
  simp only [arg, argAddr, hsp, hm]

/-- The contract the proof is written against, of a state with the same
`esp`, regions, memory and symbols. -/
theorem rfc_congr {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {cs : List (String × List (BitVec 64))}
    {G : Impl.Pbkdf2.Stream.X86.Hash} {f : Impl.RsaOaep.X86.Fns} {ns : List String} {s t : State}
    (h : (rfcX86 I S cs (tabFacts G f) ns).pre s) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcX86 I S cs (tabFacts G f) ns).pre t := by
  simp only [rfcX86, TblsOk, tabFacts, arg, argAddr] at h ⊢
  rw [hsp, hrd, hwr, hm, hsy]
  exact h

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : TVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 32 (Spec.HashTable.index w'.g.G) = BitVec.ofNat 32 (Spec.HashTable.index w.g.G)) :
    w'.g.G = w.g.G ∧ w'.g.ok.SH.H = w.g.ok.SH.H := by
  have e : Spec.HashTable.index w'.g.G = Spec.HashTable.index w.g.G := by
    have h₁ := hw.2.1; have h₂ := hw'.2.1
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG : w'.g.G = w.g.G := by
    have h₁ := w.idx; have h₂ := w'.idx
    rw [e, h₁] at h₂
    exact (Option.some.inj h₂).symm
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- What `entry₁` and `entry₂` leave: the table's address in `ecx`, then its
index; nothing else changes. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .ecx → u.gpr r = σ.gpr r) ∧ u.gpr .ecx = σ.mem.readW (addr (arg σ 5) 12) 32 ∧ u.mem = σ.mem ∧
    u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.syms = σ.syms

/-- What `entry₁` leaves. -/
def Entry₁ (σ u : State) : Prop :=
  (∀ r, r ≠ .ecx → u.gpr r = σ.gpr r) ∧ u.gpr .ecx = arg σ 5 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.syms = σ.syms

theorem entry₁_ok {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} {s : State} (h : (rfcX86 I S cs F ns).pre s) :
    WP isa (.block entry₁) s (Entry₁ s) := by
  obtain ⟨-, h28, hrd, -⟩ := h
  have hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 24) 4 := by
    refine ⟨⟨argAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
    rw [show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega),
      addr_eq (by omega), show (24 : Nat) = 4 + 20 from rfl, ← Offset.add_add]
    exact Offset.contains_base _ (by decide) (by decide)
  exact Wp.wp_ldm rfl hin fun s' u => WP.block_nil ⟨u.other, u.gpr, u.mem, u.rd, u.wr, u.syms⟩

theorem entry₂_ok {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} {σ s : State} (h : (rfcX86 I S cs F ns).pre σ) (he : Entry₁ σ s) :
    WP isa (.block entry₂) s (EntryF σ) := by
  obtain ⟨-, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nt, -⟩ := h
  have hin : InRegions (s.rd ++ s.wr) (addr (arg σ 5) 12) 4 := by
    refine ⟨⟨(arg σ 5).setWidth 64, 20⟩, by rw [he.2.2.2.1, hrd]; simp, ?_⟩
    rw [addr_eq (by omega)]
    exact Offset.contains_base _ (by decide) (by decide)
  refine Wp.wp_ldm he.2.1 hin fun s' u => WP.block_nil ⟨fun r hr => ?_, by rw [u.gpr, he.2.2.1], by rw [u.mem, he.2.2.1],
    by rw [u.rd, he.2.2.2.1], by rw [u.wr, he.2.2.2.2.1], by rw [u.syms, he.2.2.2.2.2]⟩
  rw [u.other _ hr, he.1 _ hr]

theorem idx_mem {w : TVar} (hw : WOk w) : Spec.HashTable.index w.g.G ∈ idxs := by
  have := hw.2.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem idxs_lt : ∀ j ∈ idxs, j < 2 ^ 32 := by decide

/-- The frame of the hash function's code fits the stack. -/
theorem stack_le (P : RfcHash) : 272 + 4 * P.e ≤ stackT := by
  have : P.e ≤ 68 := by nums
  show _ ≤ 544; omega

/-- After `entry₁`, `entry₂` and the comparisons: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : TVar} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hsp : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hsy : t.syms = s.syms) : (rfcP (hashOf hC vs w hw) (names vs)).pre t :=
  rfc_mono (stack_le _) (rfc_congr hp.1 hsp hrd hwr hm hsy)

theorem cs_ne_ecx {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .ecx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCode R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCode signT
  refine WP.seq (WP.mono (entry₁_ok hp.1) fun t₁ h₁ => WP.seq (WP.mono (entry₂_ok hp.1 h₁) fun t h => ?_))
  obtain ⟨hg, hcx, hm, hrd, hwr, hsy⟩ := h
  rw [hp.2] at hcx
  refine byIdx_wp (idx_mem hw) idxs_lt hcx fun t' f' sy' => ?_
  rw [cfgT_eq hC vs hw]
  have hg' : ∀ r, r ≠ .ecx → t'.gpr r = s.gpr r := fun r h₁ => (congrFun f'.gpr r).trans (hg r h₁)
  have hm' : t'.mem = s.mem := f'.mem.trans hm
  have hsp : t'.gpr .esp = s.gpr .esp := hg' .esp (by decide)
  have hpre := pre_at hC hw hp hsp hm' (f'.rd.trans hrd) (f'.wr.trans hwr) (sy'.trans hsy)
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hret⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [hcs r hr, hg' r (cs_ne_ecx hr)]
  · rw [hsp, hm'] at hret; exact hret
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t'.mem ((arg t' 1).setWidth 64) ((arg t' 2).setWidth 64)).1 with
      | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem
          ((arg t' 0).setWidth 64) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧ Spec.Ecdsa.bytesAt s'.mem
          ((arg t' 0).setWidth 64) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, arg_congr hsp hm', arg_congr hsp hm', arg_congr hsp hm', hm'] at hpost'
    exact hpost'

/-! ## Constant time -/

theorem pub_trans {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {cs : List (String × List (BitVec 64))}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h₁ : (rfcX86 I S cs F ns).pub a b)
    (h₂ : (rfcX86 I S cs F ns).pub a c) : (rfcX86 I S' cs F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉, p₁₀⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉, q₁₀⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, p₈.symm.trans q₈, fun c hc => (p₉ c hc).symm.trans (q₉ c hc),
    fun n hn => (p₁₀ n hn).symm.trans (q₁₀ n hn)⟩

theorem pub_refl {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {cs : List (String × List (BitVec 64))}
    {F : State → Prop} {ns : List String} (a : State) : (rfcX86 I S cs F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same `esp`, memory and symbols. -/
theorem pub_congr {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {cs : List (String × List (BitVec 64))}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcX86 I S cs F ns).pub a b)
    (hsp : c.gpr .esp = b.gpr .esp) (hm : c.mem = b.mem) (hsy : c.syms = b.syms) :
    (rfcX86 I S' cs F' ns).pub a c := by
  simp only [rfcX86, arg, argAddr] at h ⊢
  rw [hsp, hm, hsy]
  exact h

/-- The proof's hash function and the public data: the variant `w` (by its
place in `vs`), and the state the other run agrees with. -/
abbrev Anc (vs : List TVar) := Fin vs.length × State

/-- The variant of `a`. -/
abbrev Anc.w (a : Anc vs) : TVar := vs.get a.1

theorem Anc.hv (a : Anc vs) : a.w ∈ vs := List.get_mem _ _

/-- After the entry: the contract with `a.w`'s hash function fixed, public
data that agree with `a.2`'s, and the table's index in `ecx`. -/
def PhiT (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t : State) : Prop :=
  (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pre t ∧
    (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pub a.2 t ∧
    t.gpr .ecx = BitVec.ofNat 32 (Spec.HashTable.index a.w.g.G)

/-- The relation of two runs on entry. -/
abbrev Rel₀ (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s₁ s₂ : State) : Prop :=
  (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂

/-- Runs whose public data agree: the table's address loaded from the same slot. -/
theorem entry₁_ct :
    RelCT isa (Rel₀ R T vs) (.block entry₁)
      fun u₁ u₂ => ∃ σ₁ σ₂, Rel₀ R T vs σ₁ σ₂ ∧ Entry₁ σ₁ u₁ ∧ Entry₁ σ₂ u₂ := by
  obtain ⟨_, h₁⟩ : TaintOk [.esp] entry₁ := ⟨_, by taint_decide⟩
  exact (RelCT.wpDep (F := Entry₁) (RelCT.taint (A := taint) (τr [.esp])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, hsp, _⟩⟩ => agree_regs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hsp) h₁)
    fun _ _ ⟨⟨_, _, _, p₁⟩, ⟨_, _, _, p₂⟩, _⟩ => ⟨entry₁_ok p₁.1, entry₁_ok p₂.1⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- `EntryF` of the state on entry, from that of another the entry's first
block took to the same state. -/
theorem entryF_of {τ σ u v : State} (a : Entry₁ τ u) (b : Entry₁ σ u) (f : EntryF τ v) : EntryF σ v := by
  have hm : τ.mem = σ.mem := a.2.2.1.symm.trans b.2.2.1
  refine ⟨fun r hr => (f.1 r hr).trans ((a.1 r hr).symm.trans (b.1 r hr)), ?_, f.2.2.1.trans hm,
    f.2.2.2.1.trans (a.2.2.2.1.symm.trans b.2.2.2.1), f.2.2.2.2.1.trans (a.2.2.2.2.1.symm.trans b.2.2.2.2.1),
    f.2.2.2.2.2.trans (a.2.2.2.2.2.symm.trans b.2.2.2.2.2)⟩
  rw [f.2.1, ← a.2.1, b.2.1, hm]

/-- The table's index loaded from the same table. -/
theorem entry₂_ct :
    RelCT isa (fun u₁ u₂ => ∃ σ₁ σ₂, Rel₀ R T vs σ₁ σ₂ ∧ Entry₁ σ₁ u₁ ∧ Entry₁ σ₂ u₂) (.block entry₂)
      fun v₁ v₂ => ∃ σ₁ σ₂, Rel₀ R T vs σ₁ σ₂ ∧ EntryF σ₁ v₁ ∧ EntryF σ₂ v₂ := by
  obtain ⟨_, h₂⟩ : TaintOk [.ecx] entry₂ := ⟨_, by taint_decide⟩
  refine (RelCT.wpDep (F := fun u v => ∃ σ, (tabK R T vs).pre σ ∧ Entry₁ σ u ∧ EntryF σ v)
      (RelCT.taint (A := taint) (τr [.ecx])
      (fun _ _ ⟨σ₁, σ₂, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, p₆, _⟩, e₁, e₂⟩ => agree_regs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [e₁.2.1, e₂.2.1]; exact p₆) h₂)
    fun u₁ u₂ ⟨σ₁, σ₂, ⟨k₁, k₂, _⟩, e₁, e₂⟩ => ?_).mono (fun _ _ h => h) ?_
  · rintro v₁ v₂ ⟨-, u₁, u₂, ⟨σ₁, σ₂, hk, e₁, e₂⟩, ⟨τ₁, -, e₁', f₁⟩, ⟨τ₂, -, e₂', f₂⟩⟩
    exact ⟨σ₁, σ₂, hk, entryF_of e₁' e₁ f₁, entryF_of e₂' e₂ f₂⟩
  · obtain ⟨w₁, _, _, p₁⟩ := k₁
    obtain ⟨w₂, _, _, p₂⟩ := k₂
    exact ⟨WP.mono (entry₂_ok p₁.1 e₁) fun v hv => ⟨σ₁, ⟨w₁, ‹_›, ‹_›, p₁⟩, e₁, hv⟩,
      WP.mono (entry₂_ok p₂.1 e₂) fun v hv => ⟨σ₂, ⟨w₂, ‹_›, ‹_›, p₂⟩, e₂, hv⟩⟩

theorem phiT_keep (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t t' : State) (h : PhiT hC hO a t)
    (f : Fupd t t') (hsy : t'.syms = t.syms) : PhiT hC hO a t' :=
  ⟨rfc_congr h.1 (congrFun f.gpr _) f.rd f.wr f.mem hsy, pub_congr h.2.1 (congrFun f.gpr _) f.mem hsy,
    (congrFun f.gpr _).trans h.2.2⟩

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table's branch, which is constant time for its hash function. -/
theorem signT_ct (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCode R T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCode signT
  refine RelCT.seq entry₁_ct (RelCT.seq entry₂_ct ((byIdx_ct (α := Anc vs) (b := fun i => (cfgT R T.tries vs i).sign)
    (Q := fun _ _ => True) (fun a : Anc vs => Spec.HashTable.index a.w.g.G) (Φ := PhiT hC hO) (phiT_keep hC hO)
    (fun (a : Anc vs) _ h => ⟨idx_mem (hO _ a.hv), h.2.2⟩) idxs_lt fun j _ => ?_).mono ?_ fun _ _ h => h))
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, h₁, h₂, e⟩ e₁ e₂
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
  · rintro v₁ v₂ ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩
    have q₁ := pre_at hC hw p₁ (f₁.1 _ (by decide)) f₁.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1 f₁.2.2.2.2.2
    have q₂ := pre_at hC hw p₂ (f₂.1 _ (by decide)) f₂.2.2.1 f₂.2.2.2.1 f₂.2.2.2.2.1 f₂.2.2.2.2.2
    obtain ⟨k, rfl⟩ := List.get_of_mem hv
    have pu : (rfcP (hashOf hC vs (vs.get k) (hO _ (List.get_mem _ _))) (names vs)).pub v₁ v₂ :=
      pub_trans (a := σ₁) (S := stackT) (F := tabFacts (vs.get k).g.H (fnsOf vs))
        (pub_congr (pub_refl (S := stackT) (F := tabFacts (vs.get k).g.H (fnsOf vs)) _) (f₁.1 _ (by decide))
          f₁.2.2.1 f₁.2.2.2.2.2)
        (pub_congr hpub (f₂.1 _ (by decide)) f₂.2.2.1 f₂.2.2.2.2.2)
    exact ⟨(k, v₁), ⟨q₁, pub_refl _, f₁.2.1.trans p₁.2⟩, ⟨q₂, pu, f₂.2.1.trans p₂.2⟩⟩

/-! ## No instruction writes `esp` but the frames' -/

/-- The blocks for index `i`'s sizes, which the curve's file checks. -/
theorem rfcT_cfgT (R : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : RfcT (cfgT R tries vs i) :=
  have h := R.blkT _ _ (shapeOf_mem i)
  { msgF := h.msgF, msgF₁ := h.msgF₁, msgN := h.msgN, prepW := h.prepW, coreArgs := h.coreArgs,
    keepV := h.keepV, candTop := h.candTop, wipe := h.wipe, digestPtr := h.digestPtr, padI := h.padI,
    padO := h.padO, hfinCopyK := h.hfinCopyK, hfinCopyV := h.hfinCopyV, iMsgF₀ := h.iMsgF₀, iMsgF₁ := h.iMsgF₁,
    iMsgN := h.iMsgN, iPrep := h.iPrep, iCoreArgs := h.iCoreArgs, iKeepV := h.iKeepV, iCandTop := h.iCandTop,
    iWipe := h.iWipe, iDigestPtr := h.iDigestPtr, iPadI := h.iPadI, iPadO := h.iPadO, iCopyK := h.iCopyK,
    iCopyV := h.iCopyV, m8 := h.m8, mD := h.mD }

open VG.Proof.RsaPkcs1Sig.X86 (noSp_seq noSp_frame)
open VG.Proof.RsaPss.X86 (noSp_ite)

/-- The branch on the index, when each branch writes `esp` only through its frames. -/
theorem byIdx_noSp {b : Nat → Prog isa} : ∀ {is : List Nat}, (∀ i ∈ is, NoSp (b i)) → NoSp (byIdx b is)
  | [], _ => NoSp.of_all rfl
  | [i], h => h i (List.mem_singleton_self _)
  | i :: _ :: _, h => noSp_seq (NoSp.of_all rfl) (noSp_ite (h i (List.mem_cons_self ..))
      (byIdx_noSp fun i' hi' => h i' (List.mem_cons_of_mem _ hi')))

/-- No instruction of `vg_ecdsa_<curve>_sign`, or of the functions it calls,
writes `esp` but the frames' push and pop. -/
theorem signCode_noSp (R : RfcCurve) (tries : Nat) (vs : List TVar) : NoSp (signCode R tries vs) := by
  unfold signCode signT
  refine noSp_seq (NoSp.of_all rfl) (noSp_seq (NoSp.of_all rfl) (byIdx_noSp fun i _ => ?_))
  have hb := body_noSp' (rfcT_cfgT R tries vs i) (fnsOf_noSp vs) R.coreNs
  exact noSp_frame rfl rfl hb

theorem signCode_sp (R : RfcCurve) (tries : Nat) (vs : List TVar) :
    (signCode R tries vs).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (signCode_noSp R tries vs)

end VG.Proof.Ecdsa.Rfc6979.X86
