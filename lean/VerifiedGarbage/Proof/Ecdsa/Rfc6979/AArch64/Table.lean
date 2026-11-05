module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
public import VerifiedGarbage.Proof.HmacTable.AArch64
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Instrs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
meta import VerifiedGarbage.Proof.HmacTable.AArch64
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Instrs
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on AArch64: the HMAC of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`):
`vg_ecdsa_<curve>_sign` (`signCodeT`) loads `D` and `B`, the digest length
and HMAC's block size, from the table `hmac` (its words 4 and 5, to `x6`
and `x7`) and runs the one body (`cfgT`, the same for every hash function),
which calls the table's functions. For the variants `vs` of the hash
functions that pass the registration's checks (`OK`), the table of each
variant `w` makes the body the code for `w`'s hash function (`hashOf`, with
`cfgT_eq`, which holds by `rfl`), which meets the contract with that hash
function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hmac` holds, on entry; `TableSpec.lean` shows
`TableInstance.signContract` implies it. No instruction of the function or
of those it calls writes a callee-saved SIMD register (`signT_keepsV`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List MdHash) : Cfg where
  f := fnsOf vs
  w := R.E.n
  len := R.E.C.len
  big := R.big
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List MdHash) : Prog isa := signCode (cfgT R tries vs)

/-- The stack it uses. -/
def stackT : Nat := 256 + 8 * 48

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), of one of the digest lengths and block sizes the frame
holds, and the working space of `w`'s HMAC fits the one in `scratch`. -/
def WOk (w : MdHash) : Prop :=
  (match Spec.HmacTable.hmacOf w.mgf.G with
    | some F => F.blockSize = w.H.P.B
    | none => False) ∧
  (w.H.D, w.H.P.B) ∈ shapes ∧ 8 * w.H.W ≤ 1872 ∧ w.ok.stream.Wb ≤ 1872

instance (w : MdHash) : Decidable (WOk w) := by
  unfold WOk; cases Spec.HmacTable.hmacOf w.mgf.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

theorem mdHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Spec.Mgf1.hashes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : MdHash} (hw : WOk w) : Spec.HmacTable.hmacOf w.mgf.G = some w.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.mgf.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ (mdHashes_sub w.mgf.mem) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.mgf.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem WOk.blockSize {w : MdHash} (hw : WOk w) : Spec.HmacTable.blockSize w.mgf.G = w.H.P.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hB

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

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    (w : MdHash) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.H
  ok := w.ok
  C := w.C
  satI := by rw [w.hSH, w.hW]; exact w.hmacInit.2.2
  satF := by rw [w.hSH, w.hW]; exact w.hmacFin.2.2
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.1
  hS := by have := w.ok.N_le; have := w.ok.B_le; show _ + _ ≤ 192; omega
  hW := hw.2.2.1
  hWb := hw.2.2.2

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    {w : MdHash} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.mgf.G w.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.mgf.len]

/-! ## The contract on entry -/

/-- The state `entry` leaves, with the table of `w`: `D` in `x6` and `B` in `x7`. -/
def entryOf (w : MdHash) (s : State) : State :=
  { s with gpr := fun r => if r = .x6 then BitVec.ofNat 64 w.H.D
    else if r = .x7 then BitVec.ofNat 64 w.H.P.B else s.gpr r }

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, of the state `entry` leaves, and the table's data. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (w : MdHash) (s : State) :
    Prop :=
  (rfcAArch64 R.E (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pre (entryOf w s) ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B

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
    (rfcAArch64 R.E (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pub
      (entryOf w s₁) (entryOf w s₂)

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, of a state with the same
arguments, stack pointer, regions, memory and symbols. -/
theorem rfc_congr {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S : Nat}
    {H : Impl.Pbkdf2.Md.AArch64.Hash} {f : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {ns : List String} {s t : State}
    (h : (rfcAArch64 E I S (tabFacts H f) ns).pre s)
    (hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5, .x6, .x7], t.gpr r = s.gpr r) (hsp : t.sp = s.sp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) :
    (rfcAArch64 E I S (tabFacts H f) ns).pre t := by
  have e₀ := hg .x0 (by simp); have e₁ := hg .x1 (by simp); have e₂ := hg .x2 (by simp)
  have e₄ := hg .x4 (by simp); have e₅ := hg .x5 (by simp); have e₆ := hg .x6 (by simp)
  have e₇ := hg .x7 (by simp)
  simp only [rfcAArch64, TblOk, tabFacts] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, e₆, e₇, hsp, hrd, hwr, hm, hsy]
  exact h

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes)
    (hG' : G' ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') :
    G = G' := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

theorem index_lt {G : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) :
    Spec.HashTable.index G < 8 := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : MdHash} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.mgf.G) = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    w'.mgf.G = w.mgf.G ∧ w'.ok.SH.H = w.ok.SH.H := by
  have e : Spec.HashTable.index w'.mgf.G = Spec.HashTable.index w.mgf.G := by
    have h₁ := index_lt w.mgf.mem; have h₂ := index_lt w'.mgf.mem
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG := index_inj w'.mgf.mem w.mgf.mem e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `entry`'s effect, from the state on entry `σ`. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .x6 → r ≠ .x7 → u.gpr r = σ.gpr r) ∧
    u.gpr .x6 = σ.mem.readW (σ.gpr .x5 + BitVec.ofNat 64 32) 64 ∧
    u.gpr .x7 = σ.mem.readW (σ.gpr .x5 + BitVec.ofNat 64 40) 64 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.sp = σ.sp ∧ u.syms = σ.syms

/-- `entry`: `D` and `B` from the table to `x6` and `x7`. -/
theorem entry_ok {w : MdHash} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) := by
  obtain ⟨⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n5, -⟩, -⟩ := h
  have hin : ∀ o, o + 8 ≤ 48 → InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨⟨s.gpr .x5, 48⟩, by
      rw [show s.rd = (entryOf w s).rd from rfl, hrd]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))),
      Offset.contains_base _ ho (by have : (entryOf w s).gpr .x5 = s.gpr .x5 := rfl; omega)⟩
  have h32 := hin 32 (by decide)
  have h40 := hin 40 (by decide)
  rw [show entry = [.ldr .x .x6 .x5 32, .ldr .x .x7 .x5 40] from rfl]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Nat.reduceMod, Nat.reduceMul,
    Nat.reduceLT, and_self, ite_true, Option.bind_some, State.load, Size.bits, BitVec.setWidth_eq,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_false, h32, h40,
    Option.map_some, read8, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
      reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  simp only [h₁, h₂, ite_false]

/-- After `entry`: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : MdHash} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hf : EntryF s t) : (rfcP (hashOf hC vs w hw) (names vs)).pre t := by
  obtain ⟨hg, h6, h7, hm, hrd, hwr, hsp, hsy⟩ := hf
  exact rfc_congr hp.1 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact h6.trans hp.2.2.1
    · exact h7.trans hp.2.2.2) hsp hrd hwr hm hsy

theorem pres_ne {r : Reg} (hr : r ∈ preserved) {x : Reg} (hx : x ∉ preserved) : r ≠ x :=
  fun h => hx (h ▸ hr)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and the stack pointer. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT signCode
  refine WP.seq (WP.mono (entry_ok hp) fun t hf => ?_)
  rw [cfgT_eq hC vs hw]
  have hpre := pre_at hC hw hp hf
  obtain ⟨hg, -, -, hm, -, -, hsp, -⟩ := hf
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hsp'⟩, hpost⟩ => ⟨⟨fun r hr => ?_, hsp'.trans hsp⟩, ?_⟩
  · rw [hcs r hr, hg r (pres_ne hr (by decide)) (pres_ne hr (by decide))]
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.1.symm.trans hp.2.1)
    have e₁ := hg .x1 (by decide) (by decide)
    have e₂ := hg .x2 (by decide) (by decide)
    have e₀ := hg .x0 (by decide) (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t.mem (t.gpr .x1) (t.gpr .x2)).1 with
      | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (t.gpr .x0)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (t.gpr .x0)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₁, e₂, e₀, hm] at hpost'
    exact hpost'

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

/-- Public data of a state with the same arguments, stack pointer, memory and symbols. -/
theorem pub_congr {E : Impl.Ecdsa.AArch64.Cfg} {I : Spec.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcAArch64 E I S F ns).pub a b)
    (hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], c.gpr r = b.gpr r) (hsp : c.sp = b.sp) (hm : c.mem = b.mem)
    (hsy : c.syms = b.syms) : (rfcAArch64 E I S' F' ns).pub a c := by
  have e₀ := hg .x0 (by simp); have e₁ := hg .x1 (by simp); have e₂ := hg .x2 (by simp)
  have e₄ := hg .x4 (by simp); have e₅ := hg .x5 (by simp)
  simp only [rfcAArch64] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, hsp, hm, hsy]
  exact h

theorem entry_taint : TaintOk [.x5] entry := ⟨_, by taint_decide⟩

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK R T vs).pre σ₁ ∧ (tabK R T vs).pre σ₂ ∧ (tabK R T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  obtain ⟨_, ht⟩ := entry_taint
  refine (RelCT.wpDep (F := EntryF) (RelCT.taint (A := taint) (Taint.ofRegs [.x5])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, ⟨p₁, _, _, _, _, p₆, _⟩⟩⟩ => ⟨p₁, fun r hr => by
        simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact p₆⟩) ht)
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨entry_ok h₁, entry_ok h₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCodeT signCode
  refine entry_ct.seq ?_
  intro u₁ u₂ t₁ t₂ u₁' u₂' ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩ e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [(hashOf hC vs w hw).H.hmacInitN, (hashOf hC vs w hw).H.updN,
      (hashOf hC vs w hw).H.hmacFinN], n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  have reg : ∀ {σ u : State}, EntryF σ u → ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5],
      u.gpr r = (entryOf w σ).gpr r := fun {σ u} f r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact f.1 _ (by decide) (by decide)
  have pu : (rfcP (hashOf hC vs w hw) (names vs)).pub u₁ u₂ :=
    pub_trans (a := entryOf w σ₁) (S := stackT) (F := tabFacts w.H (fnsOf vs))
      (pub_congr (pub_refl (S := stackT) (F := tabFacts w.H (fnsOf vs)) _) (reg f₁) f₁.2.2.2.2.2.2.1
        f₁.2.2.2.1 f₁.2.2.2.2.2.2.2)
      (pub_congr hpub (reg f₂) f₂.2.2.2.2.2.2.1 f₂.2.2.2.1 f₂.2.2.2.2.2.2.2)
  exact ⟨sign_ct hns u₁ u₂ t₁ t₂ u₁' u₂' (pre_at hC hw p₁ f₁) (pre_at hC hw p₂ f₂) pu e₁ e₂, trivial⟩

/-! ## No instruction writes a callee-saved SIMD register -/

theorem fnsOk_of (vs : List MdHash) : FnsOk (fnsOf vs).init ∧ FnsOk (fnsOf vs).upd ∧ FnsOk (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact w.ok.hmacInit_keepsV
  · exact w.ok.updKeepsV
  · exact w.ok.hmacFin_keepsV

/-- No instruction of `vg_ecdsa_<curve>_sign`, or of the functions it calls,
writes a callee-saved SIMD register. -/
theorem signT_keepsV (R : RfcCurve) (tries : Nat) (vs : List MdHash) :
    (signCodeT R tries vs).allInstrs keepsV = true :=
  sign_okP (c := cfgT R tries vs) R.blk (fnsOk_of vs) R.coreKeepsV

end VG.Proof.Ecdsa.Rfc6979.AArch64
