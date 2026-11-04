module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.ByIdx
public import VerifiedGarbage.Proof.HashTable.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.ByIdx
meta import VerifiedGarbage.Proof.HashTable.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp

/-!
# Deterministic ECDSA on PPC64LE: the hash function of a table

`vg_ecdsa_<curve>_sign` (`signCode`) moves `scratch` to `r6`, loads the
index of the hash function from the table `hash` (its word 3) and runs the
code for that index's digest length and block size (`cfgT`), which calls the
table's functions. For the hash functions `vs` that pass the registration's
checks (`OK`: their functions of the same name have the same code, and each
is of one of the hash functions with HMAC, of the sizes its index's code is
for), the table of each `w` makes it the code for `w`'s hash function
(`rfcOf`), which meets the contract with that hash function fixed
(`sign_ok`, `sign_ct`). `tabK` states that contract for whichever of the
tables `hash` holds, on entry; `TableSpec.lean` shows
`TableInstance.signContract` implies it.

What the proof needs of the curve is `RfcCurve` (`Curve.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only wp_mov wp_ld)

/-- The code for the hash function of index `i`, on the curve `C`, with the
bound on candidates `tries` and the tables of `vs`. -/
def cfgT (C : RfcCurve) (tries : Nat) (vs : List TVar) (i : Nat) : Cfg :=
  ⟨(shapeOf i).1, (shapeOf i).2, fnsOf vs, C.R.E.curve.len, C.R.E.curve.n, tries, C.R.N, C.R.C⟩

/-- `vg_ecdsa_<curve>_sign`. -/
def signCode (C : RfcCurve) (tries : Nat) (vs : List TVar) : Prog isa := signT (cfgT C tries vs)

/-- The stack it uses: the most of any hash function's code. -/
def stackT : Nat := 672

/-! ## The variants -/

/-- What the code needs of a hash function `w`: it has HMAC (over `w`'s block
size), its index is one of `hidx`, and that index's code is for `w`'s digest
length and block size; and the working space and states of `w`'s streaming
functions fit `scratch`'s. -/
def WOk (w : TVar) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.l.G with
    | some F => F.blockSize = w.H.B
    | none => False) ∧
  Spec.HashTable.index w.l.G ∈ hidx ∧ shapeOf (Spec.HashTable.index w.l.G) = (w.H.D, w.H.B) ∧
  sWork + w.H.W ≤ sPad ∧ w.H.S ≤ 192

instance (w : TVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.Ecdsa.Rfc6979.hmacOf w.l.G <;> infer_instance

/-- What the registrations check of the hash functions whose tables the
function takes. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem labelHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.RsaOaep.PPC64LE.labelHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.RsaOaep.PPC64LE.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Spec.Mgf1.hashes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : TVar} (hw : WOk w) : Spec.Ecdsa.Rfc6979.hmacOf w.l.G = some w.l.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.Ecdsa.Rfc6979.hmacOf w.l.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.Ecdsa.Rfc6979.hmacOf_hash _ (labelHashes_sub w.l.mem) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.l.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.l.hash x)⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.l.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (C : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = C.R.E
  tries_pos : 1 ≤ T.tries
  tries_lt : T.tries < 2 ^ 15

/-- The hash function's part of the proof. -/
def kitOf (vs : List TVar) (w : TVar) (hw : WOk w) : Kit :=
  ⟨w.H, w.l.ok, w.l.ct, fnsOf vs, hw.2.2.2.1, hw.2.2.2.2⟩

/-- The instance of the proof for the code of `w`'s index. -/
def rfcOf {C : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT C T) (vs : List TVar) (w : TVar)
    (hw : WOk w) : Rfc :=
  have hz : SizeOk C.R.E C.k (cfgT C T.tries vs (Spec.HashTable.index w.l.G)) :=
    (C.sizes _ hw.2.1).of rfl rfl rfl
  { K := kitOf vs w hw
    R := C.R
    c := cfgT C T.tries vs (Spec.HashTable.index w.l.G)
    I := instOf T w
    k := C.k
    hE := hC.ecdsa
    hHash := rfl
    hD := rfl
    hcD := by show (shapeOf _).1 = w.H.D; rw [hw.2.2.1]
    hcB := by show (shapeOf _).2 = w.H.B; rw [hw.2.2.1]
    hcf := rfl
    hcN := rfl
    hcC := rfl
    hcl := rfl
    hcn := rfl
    hct := rfl
    hk := hz.hk
    hk16 := hz.hk16
    hbits := hz.hbits
    hn₁ := hz.hn₁
    hn₂ := hz.hn₂
    hW := hz.hW
    hT := hC.tries_pos
    hT' := hC.tries_lt }

theorem hblkT (C : RfcCurve) (tries : Nat) (vs : List TVar) {i : Nat} (hi : i ∈ hidx) :
    HBlks (cfgT C tries vs i) := (hblk i hi).of rfl rfl

theorem cblkT (C : RfcCurve) (tries : Nat) (vs : List TVar) {i : Nat} (hi : i ∈ hidx) :
    CBlks (cfgT C tries vs i) := (C.cblk i hi).of rfl rfl rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : TVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.l.G w.l.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.l.len]

/-! ## The contract on entry -/

/-- The state on entry with `scratch` in `r6`, as `entry` leaves it. -/
def entryOf (s : State) : State := { s with gpr := fun r => if r = .r6 then s.gpr .r7 else s.gpr r }

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, of the state `entry` leaves, and the table's index. -/
def PreW (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (w : TVar) (s : State) : Prop :=
  (rfcPPC (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pre (entryOf s) ∧
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `r8` is. -/
def tabK (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW T vs w s →
    match (T.result w.l.G w.l.ok.SH.H s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW T vs w s₁ ∧ PreW T vs w s₂ ∧
    (rfcPPC (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pub (entryOf s₁) (entryOf s₂)

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {F : State → Prop} {ns : List String} {s : State}
    (hS : S' ≤ S) (h : (rfcPPC I S F ns).pre s) : (rfcPPC I S' F ns).pre s := by
  obtain ⟨hrd, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, nt, tout, tsc, tstk, hF⟩ := h
  have hsub : Region.Sub (below s.sp S') (below s.sp S) := Offset.sub_below _ hS (by omega)
  exact ⟨hrd, hwr, od, og, oc, dc, gc, ko.sub_left hsub, kd.sub_left hsub, kg.sub_left hsub, kc.sub_left hsub,
    no, nd, ng, nc, by omega, nt, tout, tsc, tstk.sub_left hsub, hF⟩

/-- The contract the proof is written against, of a state with the same
arguments, regions, memory and symbols. -/
theorem rfc_congr {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {G : Impl.Hmac.Stream.PPC64LE.Hash}
    {f : Impl.RsaOaep.PPC64LE.Fns} {ns : List String} {s t : State} (h : (rfcPPC I S (tabFacts G f) ns).pre s)
    (hg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r8], t.gpr r = s.gpr r) (hsp : t.sp = s.sp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcPPC I S (tabFacts G f) ns).pre t := by
  have e₁ := hg .r3 (by simp); have e₂ := hg .r4 (by simp); have e₃ := hg .r5 (by simp)
  have e₄ := hg .r6 (by simp); have e₅ := hg .r8 (by simp)
  simp only [rfcPPC, tabFacts] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, hsp, hrd, hwr, hm, hsy]
  exact h

/-! ## Correctness -/

variable {C : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.RsaOaep.PPC64LE.labelHashes)
    (hG' : G' ∈ Proof.RsaOaep.PPC64LE.labelHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') :
    G = G' := by
  simp only [Proof.RsaOaep.PPC64LE.labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

theorem idx_lt {w : TVar} (hw : WOk w) : Spec.HashTable.index w.l.G < 8 := by
  have := hw.2.1
  simp only [hidx, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

/-- Two hash functions whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : TVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.l.G) = BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) :
    w'.l.G = w.l.G ∧ w'.l.ok.SH.H = w.l.ok.SH.H := by
  have e : Spec.HashTable.index w'.l.G = Spec.HashTable.index w.l.G := by
    have h₁ := idx_lt hw; have h₂ := idx_lt hw'
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG := index_inj w'.l.mem w.l.mem e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `entry`'s effect, from the state on entry `σ`. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .r6 → r ≠ .r9 → u.gpr r = σ.gpr r) ∧ u.gpr .r6 = σ.gpr .r7 ∧
    u.gpr .r9 = σ.mem.readW (σ.gpr .r8 + BitVec.ofNat 64 24) 64 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.sp = σ.sp ∧ u.lr = σ.lr ∧ u.syms = σ.syms

/-- `entry`: `scratch` to `r6`, the table's index to `r9`. -/
theorem entry_ok {w : TVar} {s : State} (h : PreW T vs w s) : WP isa (.block entry) s (EntryF s) := by
  obtain ⟨⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n8, -⟩, -⟩ := h
  have ht : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 24) 8 :=
    ⟨⟨s.gpr .r8, 40⟩, by
      rw [show s.rd = (entryOf s).rd from rfl, hrd]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))),
      Offset.contains_base _ (by decide) (by have : (entryOf s).gpr .r8 = s.gpr .r8 := rfl; omega)⟩
  refine WP.of_syms (wp_mov (d := .r6) (n := .r7) fun t₁ o₁ e₁ => ?_)
  refine wp_ld (t := .r9) (n := .r8) (a := s.gpr .r8 + BitVec.ofNat 64 24) (by rw [o₁.gpr _ (by decide)])
    (by rw [o₁.rd, o₁.wr]; exact ht) (fun t₂ o₂ e₂ => wp_nil fun hsy => ⟨fun r h₆ h₉ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hsy⟩)
  · rw [o₂.gpr _ (by simpa using h₉), o₁.gpr _ (by simpa using h₆)]
  · rw [o₂.gpr _ (by decide), e₁]
  · rw [e₂, o₁.mem]
  · rw [o₂.mem, o₁.mem]
  · rw [o₂.rd, o₁.rd]
  · rw [o₂.wr, o₁.wr]
  · rw [o₂.sp, o₁.sp]
  · rw [o₂.lr, o₁.lr]

theorem idx_mem {w : TVar} (hw : WOk w) : Spec.HashTable.index w.l.G ∈ idxs := hidx_sub hw.2.1

/-- The frame of the hash function's code fits the stack. -/
theorem stack_le (P : Rfc) : 400 + extra P.c.hHigh P.c.wide ≤ stackT := by
  unfold extra stackT; split
  · decide
  · split <;> decide

/-- What `entry` and the comparisons keep: all but `r6`, `r9` and `r10`. -/
def KeptT (σ u : State) : Prop :=
  (∀ r, r ≠ .r6 → r ≠ .r9 → r ≠ .r10 → u.gpr r = σ.gpr r) ∧ u.gpr .r6 = σ.gpr .r7 ∧ u.mem = σ.mem ∧
    u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.lr = σ.lr ∧ u.syms = σ.syms

/-- After `entry` and the comparisons: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT C T) {w : TVar} (hw : WOk w) {s t : State} (hp : PreW T vs w s) (hk : KeptT s t) :
    (rfcP (rfcOf hC vs w hw) (names vs)).pre t :=
  rfc_mono (stack_le _) (rfc_congr hp.1 (fun r hr => by
    obtain ⟨hg, h6, -⟩ := hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by decide) (by decide) (by decide)
    · exact hg _ (by decide) (by decide) (by decide)
    · exact hg _ (by decide) (by decide) (by decide)
    · exact h6
    · exact hg _ (by decide) (by decide) (by decide)) hk.2.2.2.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1 hk.2.2.1
      hk.2.2.2.2.2.2.2)

theorem keptT_of {σ t u : State} (he : EntryF σ t) (o : ∀ r, r ≠ .r10 → u.gpr r = t.gpr r) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hsp : u.sp = t.sp) (hlr : u.lr = t.lr) (hsy : u.syms = t.syms) :
    KeptT σ u :=
  ⟨fun r h₆ h₉ h₁₀ => (o r h₁₀).trans (he.1 r h₆ h₉), (o _ (by decide)).trans he.2.1, hm.trans he.2.2.2.1,
    hrd.trans he.2.2.2.2.1, hwr.trans he.2.2.2.2.2.1, hsp.trans he.2.2.2.2.2.2.1, hlr.trans he.2.2.2.2.2.2.2.1,
    hsy.trans he.2.2.2.2.2.2.2.2⟩

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers, the stack pointer and the return address. -/
theorem signT_ok (hC : CurveT C T) {s : State} (h : (tabK T vs).pre s) :
    WP isa (signCode C T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCode signT
  refine WP.seq (WP.mono (entry_ok hp) fun t he => ?_)
  refine byIdx_ok (b := fun i => (cfgT C T.tries vs i).sign) (D := Spec.HashTable.index w.l.G)
    (by have := idx_lt hw; omega)
    (F := fun u => KeptT s u ∧ u.gpr .r9 = BitVec.ofNat 64 (Spec.HashTable.index w.l.G))
    (fun u hu => hu.2) (fun u u' ⟨hu, h9⟩ o hsy => ⟨?_, (o.gpr _ (by decide)).trans h9⟩)
    (fun u ⟨hu, _⟩ => ?_) (idx_mem hw) (fun x hx => (idxs_certs x hx).1) t
    ⟨keptT_of he (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl, he.2.2.1.trans hp.2⟩
  · exact ⟨fun r h₆ h₉ h₁₀ => (o.gpr r (by simpa using h₁₀)).trans (hu.1 r h₆ h₉ h₁₀),
      (o.gpr _ (by decide)).trans hu.2.1, o.mem.trans hu.2.2.1, o.rd.trans hu.2.2.2.1, o.wr.trans hu.2.2.2.2.1,
      o.sp.trans hu.2.2.2.2.2.1, o.lr.trans hu.2.2.2.2.2.2.1, hsy.trans hu.2.2.2.2.2.2.2⟩
  · have hpre := pre_at hC hw hp hu
    refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hsp', hlr'⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
    · have hne : ∀ x ∈ [Reg.r6, .r9, .r10], r ≠ x := fun x hx e => by
        subst e; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> exact absurd hr (by decide)
      rw [hcs r hr, hu.1 r (hne _ (by simp)) (hne _ (by simp)) (hne _ (by simp))]
    · rw [hsp', hu.2.2.2.2.2.1]
    · rw [hlr', hu.2.2.2.2.2.2.1]
    · intro w' _ hw' hp'
      obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
      have e₁ := hu.1 .r4 (by decide) (by decide) (by decide)
      have e₂ := hu.1 .r5 (by decide) (by decide) (by decide)
      have e₃ := hu.1 .r3 (by decide) (by decide) (by decide)
      rw [hG, hH]
      have hpost' : match ((instOf T w).result u.mem (u.gpr .r4) (u.gpr .r5)).1 with
        | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (u.gpr .r3)
            (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => (s'.gpr .r3).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (u.gpr .r3)
            (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
      rw [tresult_eq, e₁, e₂, e₃, hu.2.2.1] at hpost'
      exact hpost'

/-! ## Constant time -/

/-- Public data that agree. -/
theorem pub_trans {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {F F' : State → Prop} {ns : List String}
    {a b c : State} (h₁ : (rfcPPC I S F ns).pub a b) (h₂ : (rfcPPC I S F ns).pub a c) :
    (rfcPPC I S' F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, fun n hn => (p₈ n hn).symm.trans (q₈ n hn)⟩

theorem pub_refl {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat} {F : State → Prop} {ns : List String} (a : State) :
    (rfcPPC I S F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same arguments, memory and symbols. -/
theorem pub_congr {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat} {F F' : State → Prop} {ns : List String}
    {a b c : State} (h : (rfcPPC I S F ns).pub a b) (hg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r8], c.gpr r = b.gpr r)
    (hsp : c.sp = b.sp) (hm : c.mem = b.mem) (hsy : c.syms = b.syms) : (rfcPPC I S' F' ns).pub a c := by
  have e₁ := hg .r3 (by simp); have e₂ := hg .r4 (by simp); have e₃ := hg .r5 (by simp)
  have e₄ := hg .r6 (by simp); have e₅ := hg .r8 (by simp)
  simp only [rfcPPC] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, hsp, hm, hsy]
  exact h

/-- The proof's hash function and the public data: the hash function `w`
(by its place in `vs`), and the state the other run agrees with. -/
abbrev Anc (vs : List TVar) := Fin vs.length × State

/-- The hash function of `a`. -/
abbrev Anc.w (a : Anc vs) : TVar := vs.get a.1

theorem Anc.hv (a : Anc vs) : a.w ∈ vs := List.get_mem _ _

/-- After `entry`: the contract with `a.w`'s hash function fixed, public
data that agree with `a.2`'s, and the table's index `D` in `r9`. -/
def PhiT (hC : CurveT C T) (hO : ∀ w ∈ vs, WOk w) (D : Nat) (a : Anc vs) (t : State) : Prop :=
  (rfcP (rfcOf hC vs a.w (hO _ a.hv)) (names vs)).pre t ∧
    (rfcP (rfcOf hC vs a.w (hO _ a.hv)) (names vs)).pub a.2 t ∧
    t.gpr .r9 = BitVec.ofNat 64 D ∧ Spec.HashTable.index a.w.l.G = D

theorem entryF_ok {w : TVar} {s : State} (h : PreW T vs w s) : WP isa (.block entry) s (EntryF s) := entry_ok h

theorem entry_taint : TaintOk [.r8] entry := ⟨_, by taint_decide⟩

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK T vs).pre s₁ ∧ (tabK T vs).pre s₂ ∧ (tabK T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK T vs).pre σ₁ ∧ (tabK T vs).pre σ₂ ∧ (tabK T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  obtain ⟨_, ht⟩ := entry_taint
  refine (RelCT.wpDep (F := EntryF) (VG.RelCT.taint (A := taint) (Taint.ofRegs [.r8])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, ⟨p₁, _, _, _, _, _, p₈, _⟩⟩⟩ => ⟨p₁, fun r hr => by
        rw [List.mem_singleton.mp (Taint.mem_ofRegs.mp hr)]; exact p₈⟩) ht)
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨entryF_ok h₁, entryF_ok h₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

theorem phiT_keep (hC : CurveT C T) (hO : ∀ w ∈ vs, WOk w) (D : Nat) (a : Anc vs) (t t' : State)
    (h : PhiT hC hO D a t) (o : Only [.r10] t t') (hsy : t'.syms = t.syms) : PhiT hC hO D a t' :=
  ⟨rfc_congr h.1 (fun r hr => o.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) o.sp o.rd o.wr o.mem hsy,
    pub_congr h.2.1 (fun r hr => o.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) o.sp o.mem hsy,
    (o.gpr _ (by decide)).trans h.2.2.1, h.2.2.2⟩

theorem entryOf_regs {σ u : State} (f : EntryF σ u) : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r8], u.gpr r = (entryOf σ).gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (f.1 _ (by decide) (by decide)).trans (by simp [entryOf])
  · exact (f.1 _ (by decide) (by decide)).trans (by simp [entryOf])
  · exact (f.1 _ (by decide) (by decide)).trans (by simp [entryOf])
  · exact f.2.1.trans (by simp [entryOf])
  · exact (f.1 _ (by decide) (by decide)).trans (by simp [entryOf])

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table's branch, which is constant time for its hash function. -/
theorem signT_ct (hC : CurveT C T) (hO : ∀ w ∈ vs, WOk w) :
    ConstantTime isa (tabK T vs).pre (tabK T vs).pub (signCode C T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCode signT
  refine entry_ct.seq ((RelCT.exists_ (α := Nat) (P := fun D => VG.Proof.RsaPkcs1Sig.PPC64LE.Two (PhiT hC hO D)) fun D => ?_).mono ?_
    fun _ _ h => h)
  · by_cases hD : D < 8
    · by_cases hDm : D ∈ idxs
      · refine byIdx_ct (b := fun i => (cfgT C T.tries vs i).sign) (D := D) (by omega)
          (Φ := PhiT hC hO D) (R := fun _ _ => True) (fun _ _ h => h.2.2.1)
          (fun a t₁ t₂ h₁ h₂ => h₁.2.1.1.symm.trans h₂.2.1.1) (phiT_keep hC hO D) ?_ hDm idxs_certs
        intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, h₁, h₂⟩ e₁ e₂
        obtain rfl := h₁.2.2.2
        have hw := hO _ a.hv
        have hns : ∀ n ∈ [(rfcOf hC vs a.w hw).K.H.initN, (rfcOf hC vs a.w hw).K.H.updN,
            (rfcOf hC vs a.w hw).K.H.finN], n ∈ names vs := by
          have := mem_names a.hv
          intro n hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          rcases hn with rfl | rfl | rfl
          · exact this.1
          · exact this.2.1
          · exact this.2.2
        exact ⟨sign_ct (P := rfcOf hC vs a.w hw) (hblkT C T.tries vs hw.2.1) (cblkT C T.tries vs hw.2.1) hns
          s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 (pub_trans h₁.2.1 h₂.2.1) e₁ e₂, trivial⟩
      · exact absurd (by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false]; omega) hDm
    · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => hD (h₁.2.2.2 ▸ idx_lt (hO _ a.hv))
  · rintro u₁ u₂ ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩
    have q₁ := pre_at hC hw p₁ (keptT_of f₁ (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl)
    have q₂ := pre_at hC hw p₂ (keptT_of f₂ (fun _ _ => rfl) rfl rfl rfl rfl rfl rfl)
    obtain ⟨k, rfl⟩ := List.get_of_mem hv
    have pu : (rfcP (rfcOf hC vs (vs.get k) (hO _ (List.get_mem _ _))) (names vs)).pub u₁ u₂ :=
      pub_trans (a := entryOf σ₁) (S := stackT) (F := tabFacts (vs.get k).H (fnsOf vs))
        (pub_congr (pub_refl (S := stackT) (F := tabFacts (vs.get k).H (fnsOf vs)) _) (entryOf_regs f₁)
          f₁.2.2.2.2.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.2.2.2.2)
        (pub_congr hpub (entryOf_regs f₂) f₂.2.2.2.2.2.2.1 f₂.2.2.2.1 f₂.2.2.2.2.2.2.2.2)
    exact ⟨Spec.HashTable.index (vs.get k).l.G, (k, u₁), ⟨q₁, pub_refl _, f₁.2.2.1.trans p₁.2, rfl⟩,
      ⟨q₂, pu, f₂.2.2.1.trans p₂.2, rfl⟩⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
