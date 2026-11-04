module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.ByIdx
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Instrs
public import VerifiedGarbage.Proof.HashTable.AArch64
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.ByIdx
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Instrs
meta import VerifiedGarbage.Proof.HashTable.AArch64
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on AArch64: the hash function of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`):
`vg_ecdsa_<curve>_sign` (`signCode`) loads the index of the hash function
from the table `hash` (its word 3) and runs the code for that index's
digest length and block size (`cfgT`), which calls the table's functions.
For the variants `vs` of the hash functions that pass the registration's
checks (`OK`), the table of each variant `w` makes it the code for `w`'s
hash function (`hashOf`, with `cfgT_eq`), which meets the contract with that
hash function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hash` holds, on entry; `TableSpec.lean` shows
`TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HashTable.AArch64 (tables fnsOf names Coh tableOf mem_names tabOK_of)
open VG.Proof.Bignum.AArch64 (Two two_mono)

/-! ## The code -/

/-- The code for the hash function of index `i`, on the curve `R`, with the
bound on candidates `tries` and the tables of `vs`. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List MdHash) (i : Nat) : Cfg where
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
def signCode (R : RfcCurve) (tries : Nat) (vs : List MdHash) : Prog isa := signT (cfgT R tries vs)

/-- The stack it uses: the most of any hash function's. -/
def stackT : Nat := 528

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), its index is one of the code's, and that index's code is
for `w`'s digest length and block size. -/
def WOk (w : MdHash) : Prop :=
  (match Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G with
    | some F => F.blockSize = w.H.P.B
    | none => False) ∧
  Spec.HashTable.index w.mgf.G < 8 ∧ shapeOf (Spec.HashTable.index w.mgf.G) = (w.H.D, w.H.P.B)

instance (w : MdHash) : Decidable (WOk w) := by
  unfold WOk; cases Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

theorem shapeOf_mem (i : Nat) : shapeOf i ∈ shapes := by
  unfold shapeOf; split <;> simp [shapes]

theorem mdHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Spec.Mgf1.hashes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : MdHash} (hw : WOk w) : Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G = some w.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.Ecdsa.Rfc6979.hmacOf w.mgf.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.Ecdsa.Rfc6979.hmacOf_hash _ (mdHashes_sub w.mgf.mem) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.mgf.hash x)⟩

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 16

/-- None of the variants' streaming functions writes a callee-saved SIMD register. -/
theorem fnsKeep_of (vs : List MdHash) :
    FnsKeep (fnsOf vs).init ∧ FnsKeep (fnsOf vs).upd ∧ FnsKeep (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact w.ok.initKeepsV
  · exact w.ok.updKeepsV
  · exact w.ok.finKeepsV

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    (w : MdHash) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.H
  ok := w.ok
  f := fnsOf vs
  fInit := (fnsKeep_of vs).1
  fUpd := (fnsKeep_of vs).2.1
  fFin := (fnsKeep_of vs).2.2
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.2 ▸ shapeOf_mem _
  hS := by have := w.ok.N_le; have := w.ok.B_le; show _ + _ ≤ 192; omega
  hWb := by have := w.ok.stream.hWb; have := w.ok.stream.hW; omega

theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    {w : MdHash} (hw : WOk w) : cfgT R T.tries vs (Spec.HashTable.index w.mgf.G) = cfgOf (hashOf hC vs w hw) := by
  unfold cfgT cfgOf; rw [hw.2.2]; rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.mgf.G w.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.mgf.len]

/-! ## The contract on entry -/

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (w : MdHash) (s : State) :
    Prop :=
  (rfcAArch64 R.E (instOf T w) stackT (tabFacts w.H.stream (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `x5` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.mgf.G w.ok.SH.H s.mem (s.gpr .x1) (s.gpr .x2)).1 with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcAArch64 R.E (instOf T w) stackT (tabFacts w.H.stream (fnsOf vs)) (names vs)).pub s₁ s₂

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, for less stack. -/
theorem rfc_mono {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F : State → Prop} {ns : List String} {s : State} (hS : S' ≤ S) (h : (rfcAArch64 E I S F ns).pre s) :
    (rfcAArch64 E I S' F ns).pre s := by
  obtain ⟨hrd, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, ⟨held, nT, hdw⟩, nt, tout, tsc,
    tstk, hF⟩ := h
  have hsub : Region.Sub (below s.sp S') (below s.sp S) := Offset.sub_below _ hS (by omega)
  refine ⟨hrd, hwr, od, og, oc, dc, gc, ko.sub_left hsub, kd.sub_left hsub, kg.sub_left hsub, kc.sub_left hsub,
    no, nd, ng, nc, by omega, ⟨held, nT, fun r hr => ?_⟩, nt, tout, tsc, tstk.sub_right hsub, hF⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hdw _ (by simp)
  · exact hdw _ (by simp)
  · exact (hdw _ (by simp)).sub_right hsub

/-- The contract the proof is written against, of a state with the same
arguments, regions, memory and symbols. -/
theorem rfc_congr {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat}
    {G : Impl.Pbkdf2.Md.AArch64.Stream} {f : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {ns : List String} {s t : State}
    (h : (rfcAArch64 E I S (tabFacts G f) ns).pre s)
    (hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], t.gpr r = s.gpr r) (hsp : t.sp = s.sp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcAArch64 E I S (tabFacts G f) ns).pre t := by
  have e₀ := hg .x0 (by simp); have e₁ := hg .x1 (by simp); have e₂ := hg .x2 (by simp)
  have e₄ := hg .x4 (by simp); have e₅ := hg .x5 (by simp)
  simp only [rfcAArch64, TblOk, tabFacts] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, hsp, hrd, hwr, hm, hsy]
  exact h

/-! ## Correctness -/

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes)
    (hG' : G' ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') :
    G = G' := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : MdHash} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.mgf.G) = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    w'.mgf.G = w.mgf.G ∧ w'.ok.SH.H = w.ok.SH.H := by
  have e : Spec.HashTable.index w'.mgf.G = Spec.HashTable.index w.mgf.G := by
    have h₁ := hw.2.1; have h₂ := hw'.2.1
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG := index_inj w'.mgf.mem w.mgf.mem e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `entry`'s effect, from the state on entry `σ`: the table's index in `x16`. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .x16 → u.gpr r = σ.gpr r) ∧ u.gpr .x16 = σ.mem.readW (σ.gpr .x5 + BitVec.ofNat 64 24) 64 ∧
    u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧ u.sp = σ.sp ∧ u.syms = σ.syms

/-- `entry`: the table's index to `x16`. -/
theorem tentry_ok {w : MdHash} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) := by
  obtain ⟨⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nt, -⟩, -⟩ := h
  have ht : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 24) 8 :=
    ⟨⟨s.gpr .x5, 40⟩, by
      rw [hrd]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))),
      Offset.contains_base _ (by decide) (by omega)⟩
  apply WP.of_runBlock
  simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bits, Size.bytes,
    BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some, ht,
    Option.map_some, read8, Option.some.injEq, exists_eq_left']
  exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _,
    rfl, rfl, rfl, rfl, rfl⟩

theorem idx_mem {w : MdHash} (hw : WOk w) : Spec.HashTable.index w.mgf.G ∈ idxs := by
  have := hw.2.1
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem idxs_lt : ∀ j ∈ idxs, j < 4096 := by decide

/-- The frame of the hash function's code fits the stack. -/
theorem stack_le (P : RfcHash) : 256 + P.e ≤ stackT := by
  have : P.e ≤ 272 := by anums
  show _ ≤ 528; omega

/-- After `entry` and the comparisons: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : MdHash} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hg : ∀ r, r ≠ .x16 → r ≠ .x17 → t.gpr r = s.gpr r) (hsp : t.sp = s.sp) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsy : t.syms = s.syms) :
    (rfcP (hashOf hC vs w hw) (names vs)).pre t :=
  rfc_mono (stack_le _) (rfc_congr hp.1 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr hm hsy)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and the stack pointer. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCode R T.tries vs) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCode signT
  refine WP.seq (WP.mono (tentry_ok hp) fun t ⟨hg, h16, hm, hrd, hwr, hsp, hsy⟩ => ?_)
  refine byIdx_wp (idx_mem hw) idxs_lt (h16.trans hp.2) fun t' k' => ?_
  rw [cfgT_eq hC vs hw]
  have hg' : ∀ r, r ≠ .x16 → r ≠ .x17 → t'.gpr r = s.gpr r := fun r h₁ h₂ =>
    (k'.gpr r h₂).trans (hg r h₁)
  have hpre := pre_at hC hw hp hg' (k'.sp.trans hsp) (k'.mem.trans hm) (k'.rd.trans hrd) (k'.wr.trans hwr)
    (k'.syms.trans hsy)
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hs'⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [hcs r hr, hg' r (ne_cs hr (by decide)) (ne_cs hr (by decide))]
  · rw [hs', k'.sp, hsp]
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
    have e₁ := hg' .x1 (by decide) (by decide)
    have e₂ := hg' .x2 (by decide) (by decide)
    have e₀ := hg' .x0 (by decide) (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t'.mem (t'.gpr .x1) (t'.gpr .x2)).1 with
      | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (t'.gpr .x0)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (t'.gpr .x0)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₁, e₂, e₀, k'.mem.trans hm] at hpost'
    exact hpost'

/-! ## No instruction writes a callee-saved SIMD register -/

/-- The blocks for index `i`'s sizes, which the curve's file checks. -/
theorem rfcT_cfgT (R : RfcCurve) (tries : Nat) (vs : List MdHash) (i : Nat) : RfcT (cfgT R tries vs i) :=
  let h := R.blkT _ _ (shapeOf_mem i)
  { msgF := h.msgF, msgN := h.msgN, prepW := h.prepW, coreArgs := h.coreArgs, keepV := h.keepV,
    candTop := h.candTop, wipe := h.wipe, digestPtr := h.digestPtr, pad := h.pad, hfinCopy := h.hfinCopy,
    iMsgF := h.iMsgF, iMsgN := h.iMsgN, iPrep := h.iPrep, iCoreArgs := h.iCoreArgs, iKeepV := h.iKeepV,
    iCandTop := h.iCandTop, iWipe := h.iWipe, iDigestPtr := h.iDigestPtr, iPad := h.iPad, iCopy := h.iCopy,
    m8 := h.m8 }

/-- No instruction of `vg_ecdsa_<curve>_sign`, or of the functions it calls,
writes a callee-saved SIMD register. -/
theorem signCode_keepP (R : RfcCurve) (tries : Nat) (vs : List MdHash) : KeepP (signCode R tries vs) := by
  have hs : ∀ i, KeepP (cfgT R tries vs i).sign := fun i =>
    sign_keepP (rfcT_cfgT R tries vs i) (fnsKeep_of vs) R.coreKeepsV
  simp only [signCode, signT, idxs, byIdx]
  exact keepP_seq rfl (keepP_seq rfl (keepP_ite (hs _) (keepP_seq rfl (keepP_ite (hs _) (keepP_seq rfl
    (keepP_ite (hs _) (keepP_seq rfl (keepP_ite (hs _) (keepP_seq rfl (keepP_ite (hs _) (keepP_seq rfl
    (keepP_ite (hs _) (keepP_seq rfl (keepP_ite (hs _) (hs _)))))))))))))))

/-! ## Constant time -/

/-- Public data that agree. -/
theorem pub_trans {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h₁ : (rfcAArch64 E I S F ns).pub a b)
    (h₂ : (rfcAArch64 E I S F ns).pub a c) : (rfcAArch64 E I S' F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, p₈.symm.trans q₈, fun n hn => (p₉ n hn).symm.trans (q₉ n hn)⟩

theorem pub_refl {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat}
    {F : State → Prop} {ns : List String} (a : State) : (rfcAArch64 E I S F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same arguments, memory and symbols. -/
theorem pub_congr {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcAArch64 E I S F ns).pub a b)
    (hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], c.gpr r = b.gpr r) (hsp : c.sp = b.sp) (hm : c.mem = b.mem)
    (hsy : c.syms = b.syms) : (rfcAArch64 E I S' F' ns).pub a c := by
  have e₀ := hg .x0 (by simp); have e₁ := hg .x1 (by simp); have e₂ := hg .x2 (by simp)
  have e₄ := hg .x4 (by simp); have e₅ := hg .x5 (by simp)
  simp only [rfcAArch64] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, hsp, hm, hsy]
  exact h

/-- The proof's hash function and the public data: the variant `w` (by its
place in `vs`), and the state the other run agrees with. -/
abbrev Anc (vs : List MdHash) := Fin vs.length × State

/-- The variant of `a`. -/
abbrev Anc.w (a : Anc vs) : MdHash := vs.get a.1

theorem Anc.hv (a : Anc vs) : a.w ∈ vs := List.get_mem _ _

/-- After `entry`: the contract with `a.w`'s hash function fixed, public
data that agree with `a.2`'s, and the table's index in `x16`. -/
def PhiT (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t : State) : Prop :=
  (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pre t ∧
    (rfcP (hashOf hC vs a.w (hO _ a.hv)) (names vs)).pub a.2 t ∧
    t.gpr .x16 = BitVec.ofNat 64 (Spec.HashTable.index a.w.mgf.G)

theorem entry_taint : TaintOk [.x5] entry := ⟨_, by taint_decide⟩

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK R T vs).pre σ₁ ∧ (tabK R T vs).pre σ₂ ∧ (tabK R T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  obtain ⟨_, ht⟩ := entry_taint
  refine (RelCT.wpDep (F := EntryF) (RelCT.taint (A := taint) (Taint.ofRegs [.x5])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, ⟨p₁, _, _, _, _, p₆, _⟩⟩⟩ => ⟨p₁, fun r hr => by
        have := Taint.mem_ofRegs.mp hr
        simp only [List.mem_singleton] at this; subst this; exact p₆⟩) ht)
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨tentry_ok h₁, tentry_ok h₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

theorem cmp_taint (j : Nat) : TaintOk [] [.subImm .x .x17 .x16 j] :=
  taintOk_erase (is₀ := [.subImm .x .x17 .x16 0]) ⟨_, by taint_decide⟩ rfl

theorem phiT_keep (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) (a : Anc vs) (t t' : State) (h : PhiT hC hO a t)
    (k : Keep17 t t') : PhiT hC hO a t' :=
  ⟨rfc_congr h.1 (fun r hr => k.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) k.sp k.rd k.wr k.mem k.syms,
    pub_congr h.2.1 (fun r hr => k.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) k.sp k.mem k.syms,
    (k.gpr _ (by decide)).trans h.2.2⟩

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table's branch, which is constant time for its hash function. -/
theorem signT_ct (hC : CurveT R T) (hO : ∀ w ∈ vs, WOk w) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCode R T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCode signT
  refine entry_ct.seq ((byIdx_ct (α := Anc vs) (b := fun i => (cfgT R T.tries vs i).sign) (Q := fun _ _ => True)
    (fun a : Anc vs => Spec.HashTable.index a.w.mgf.G) (Φ := PhiT hC hO) (phiT_keep hC hO)
    (fun (a : Anc vs) _ h => ⟨idx_mem (hO _ a.hv), h.2.2⟩) idxs_lt
    (fun j _ => let ⟨_, ht⟩ := cmp_taint j; RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ ⟨_, _, _, hsp⟩ => ⟨hsp, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) ht)
    fun j _ => ?_).mono ?_ fun _ _ h => h)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, ⟨h₁, e⟩, ⟨h₂, _⟩, _⟩ e₁ e₂
    subst e
    rw [cfgT_eq hC vs (hO _ a.hv)] at e₁ e₂
    have hns : ∀ n ∈ [(hashOf hC vs a.w (hO _ a.hv)).H.stream.initN, (hashOf hC vs a.w (hO _ a.hv)).H.stream.updN,
        (hashOf hC vs a.w (hO _ a.hv)).H.stream.finN], n ∈ names vs := by
      have := mem_names a.hv
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2
    exact ⟨sign_ct hns s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 (pub_trans h₁.2.1 h₂.2.1) e₁ e₂, trivial⟩
  · rintro u₁ u₂ ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩
    have reg : ∀ {σ u : State}, EntryF σ u → ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], u.gpr r = σ.gpr r :=
      fun {σ u} f r hr => f.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    have kg : ∀ {σ u : State}, EntryF σ u → ∀ r, r ≠ .x16 → r ≠ .x17 → u.gpr r = σ.gpr r :=
      fun f r h _ => f.1 r h
    have q₁ := pre_at hC hw p₁ (kg f₁) f₁.2.2.2.2.2.1 f₁.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1 f₁.2.2.2.2.2.2
    have q₂ := pre_at hC hw p₂ (kg f₂) f₂.2.2.2.2.2.1 f₂.2.2.1 f₂.2.2.2.1 f₂.2.2.2.2.1 f₂.2.2.2.2.2.2
    obtain ⟨k, rfl⟩ := List.get_of_mem hv
    have pu : (rfcP (hashOf hC vs (vs.get k) (hO _ (List.get_mem _ _))) (names vs)).pub u₁ u₂ :=
      pub_trans (a := σ₁) (S := stackT) (F := tabFacts (vs.get k).H.stream (fnsOf vs))
        (pub_congr (pub_refl (S := stackT) (F := tabFacts (vs.get k).H.stream (fnsOf vs)) _) (reg f₁)
          f₁.2.2.2.2.2.1 f₁.2.2.1 f₁.2.2.2.2.2.2)
        (pub_congr hpub (reg f₂) f₂.2.2.2.2.2.1 f₂.2.2.1 f₂.2.2.2.2.2.2)
    exact ⟨(k, u₁), ⟨q₁, pub_refl _, f₁.2.1.trans p₁.2⟩, ⟨q₂, pu, f₂.2.1.trans p₂.2⟩,
      f₁.2.2.2.2.2.1.trans (hpub.1.trans f₂.2.2.2.2.2.1.symm)⟩

/-- `vg_ecdsa_<curve>_sign` with `tabK`: correct, keeping the ABI's
registers, and constant time. -/
theorem signT_correct (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    ∃ t s', Exec isa (signCode R T.tries vs) s t s' ∧ abiPreserved s s' ∧ (tabK R T vs).post s s' :=
  let ⟨t, s', he, ⟨hg, hsp⟩, hp⟩ := signT_ok hC h
  ⟨t, s', he, ⟨hg, hsp, Exec.preservedV he (signCode_keepP R T.tries vs)⟩, hp⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
