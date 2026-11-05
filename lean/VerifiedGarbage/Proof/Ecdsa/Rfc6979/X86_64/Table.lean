module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
public import VerifiedGarbage.Proof.HmacTable.X86_64
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Instance
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Instrs
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
meta import VerifiedGarbage.Proof.HmacTable.X86_64
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Instrs
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on x86-64: the HMAC of a table

`vg_ecdsa_<curve>_sign` (`signCodeT`) loads `D` and `B`, the digest length
and HMAC's block size, from the table `hmac` (its words 4 and 5) and runs
the one body (`cfgT`, the same for every hash function), which calls the
table's functions. For the variants `vs` of the hash functions that pass
the registration's checks (`OK`: their functions of the same name have the
same code, and each is of one of the hash functions with HMAC, of sizes the
frame holds), the table of each variant `w` makes the body the code for
`w`'s hash function (`hashOf`, with `cfgT_eq`, which holds by `rfl`), which
meets the contract with that hash function fixed (`sign_ok`, `sign_ct`).
`tabK` states that contract for whichever of the tables `hmac` holds, on
entry; `TableSpec.lean` shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

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
def stackT : Nat := 248 + 8 * 48

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

theorem mdHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.Pbkdf2.Md.X86_64.mdHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
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
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) : Proof.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.SH.H
  hashLen := w.H.D
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 32

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    (w : MdHash) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.H
  ok := w.ok
  C := w.C
  K := w.K
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
  simp only [Proof.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.mgf.len]

/-! ## The contract on entry -/

/-- The state `entry` leaves, with the table of `w`: `scratch` in `rcx`,
`D` in `r10` and `B` in `r11`. -/
def entryOf (w : MdHash) (s : State) : State :=
  { s with gpr := fun r => if r = .rcx then s.gpr .r8 else if r = .r10 then BitVec.ofNat 64 w.H.D
    else if r = .r11 then BitVec.ofNat 64 w.H.P.B else s.gpr r }

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, of the state `entry` leaves, and the table's data. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (w : MdHash) (s : State) :
    Prop :=
  (rfcX86_64 R.E.combConsts (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pre (entryOf w s) ∧
    s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
    s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
    s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `r9` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.mgf.G w.ok.SH.H s.mem (s.gpr .rsi) (s.gpr .rdx)).1 with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .rdi) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .rdi) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcX86_64 R.E.combConsts (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pub
      (entryOf w s₁) (entryOf w s₂)

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, of a state with the same
arguments, regions, memory and symbols. -/
theorem rfc_congr {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {S : Nat}
    {H : Impl.Pbkdf2.Md.X86_64.Hash} {f : Impl.Mgf1.X86_64.Table.Fns} {ns : List String} {s t : State}
    (h : (rfcX86_64 cs I S (tabFacts H f) ns).pre s)
    (hg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp, .r10, .r11], t.gpr r = s.gpr r) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) : (rfcX86_64 cs I S (tabFacts H f) ns).pre t := by
  have e₁ := hg .rdi (by simp); have e₂ := hg .rsi (by simp); have e₃ := hg .rdx (by simp)
  have e₄ := hg .rcx (by simp); have e₅ := hg .r9 (by simp); have e₆ := hg .rsp (by simp)
  have e₇ := hg .r10 (by simp); have e₈ := hg .r11 (by simp)
  simp only [rfcX86_64, TblsOk, tabFacts] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, hrd, hwr, hm, hsy]
  exact h

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.X86_64.mdHashes)
    (hG' : G' ∈ Proof.Pbkdf2.Md.X86_64.mdHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') : G = G' := by
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

theorem index_lt {G : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.X86_64.mdHashes) : Spec.HashTable.index G < 8 := by
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
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
  (∀ r, r ≠ .rcx → r ≠ .r10 → r ≠ .r11 → u.gpr r = σ.gpr r) ∧ u.gpr .rcx = σ.gpr .r8 ∧
    u.gpr .r10 = σ.mem.readW (σ.gpr .r9 + BitVec.ofNat 64 32) 64 ∧
    u.gpr .r11 = σ.mem.readW (σ.gpr .r9 + BitVec.ofNat 64 40) 64 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.syms = σ.syms

/-- `entry`: `scratch` to `rcx`, `D` and `B` from the table to `r10` and `r11`. -/
theorem entry_ok {w : MdHash} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) := by
  obtain ⟨⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n9, -⟩, -⟩ := h
  have hin : ∀ o, o + 8 ≤ 48 → InRegions (s.rd ++ s.wr) (s.gpr .r9 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨⟨s.gpr .r9, 48⟩, by
      rw [show s.rd = (entryOf w s).rd from rfl, hrd]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))),
      Offset.contains_base _ ho (by have : (entryOf w s).gpr .r9 = s.gpr .r9 := rfl; omega)⟩
  have h32 := hin 32 (by decide)
  have h40 := hin 40 (by decide)
  apply WP.of_runBlock
  simp only [entry, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, ite_false, h32, h40,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq,
      ite_false, ite_true]
  simp only [h₁, h₂, h₃, ite_false]

/-- After `entry`: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : MdHash} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hf : EntryF s t) : (rfcP (hashOf hC vs w hw) (names vs)).pre t := by
  obtain ⟨hg, hcx, h10, h11, hm, hrd, hwr, hsy⟩ := hf
  exact rfc_congr hp.1 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by decide) (by decide) (by decide)
    · exact hg _ (by decide) (by decide) (by decide)
    · exact hg _ (by decide) (by decide) (by decide)
    · exact hcx
    · exact hg _ (by decide) (by decide) (by decide)
    · exact hg _ (by decide) (by decide) (by decide)
    · exact h10.trans hp.2.2.1
    · exact h11.trans hp.2.2.2) hrd hwr hm hsy

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => gprPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT signCode
  refine WP.seq (WP.mono (entry_ok hp) fun t hf => ?_)
  rw [cfgT_eq hC vs hw]
  have hpre := pre_at hC hw hp hf
  obtain ⟨hg, -, -, -, hm, -, -, -⟩ := hf
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hret⟩, hpost⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [hcs r hr, hg r (ne_cs hr (by decide)) (ne_cs hr (by decide)) (ne_cs hr (by decide))]
  · rw [hg .rsp (by decide) (by decide) (by decide), hm] at hret; exact hret
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.1.symm.trans hp.2.1)
    have e₁ := hg .rsi (by decide) (by decide) (by decide)
    have e₂ := hg .rdx (by decide) (by decide) (by decide)
    have e₃ := hg .rdi (by decide) (by decide) (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t.mem (t.gpr .rsi) (t.gpr .rdx)).1 with
      | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (t.gpr .rdi)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (t.gpr .rdi)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₁, e₂, e₃, hm] at hpost'
    exact hpost'

/-! ## Constant time -/

/-- Public data that agree. -/
theorem pub_trans {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h₁ : (rfcX86_64 cs I S F ns).pub a b)
    (h₂ : (rfcX86_64 cs I S F ns).pub a c) : (rfcX86_64 cs I S' F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, fun c hc => (p₈ c hc).symm.trans (q₈ c hc),
    fun n hn => (p₉ n hn).symm.trans (q₉ n hn)⟩

theorem pub_refl {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {S : Nat}
    {F : State → Prop} {ns : List String} (a : State) : (rfcX86_64 cs I S F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same arguments, memory and symbols. -/
theorem pub_congr {cs : List (String × List (BitVec 64))} {I : Proof.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcX86_64 cs I S F ns).pub a b)
    (hg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp], c.gpr r = b.gpr r) (hm : c.mem = b.mem)
    (hsy : c.syms = b.syms) : (rfcX86_64 cs I S' F' ns).pub a c := by
  have e₁ := hg .rdi (by simp); have e₂ := hg .rsi (by simp); have e₃ := hg .rdx (by simp)
  have e₄ := hg .rcx (by simp); have e₅ := hg .r9 (by simp); have e₆ := hg .rsp (by simp)
  simp only [rfcX86_64] at h ⊢
  rw [e₁, e₂, e₃, e₄, e₅, e₆, hm, hsy]
  exact h

theorem entry_taint : TaintOk [.r9] entry := ⟨_, by taint_decide⟩

theorem entryF_ok {w : MdHash} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) :=
  entry_ok h

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK R T vs).pre σ₁ ∧ (tabK R T vs).pre σ₂ ∧ (tabK R T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  obtain ⟨_, ht⟩ := entry_taint
  refine (RelCT.wpDep (F := EntryF) (RelCT.taint (A := taint) (Taint.ofRegs [.r9])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, ⟨_, _, _, _, _, p₉, _⟩⟩⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact p₉) ht)
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨entryF_ok h₁, entryF_ok h₂⟩).mono (fun _ _ h => h)
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
  have reg : ∀ {σ u : State}, EntryF σ u → ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp],
      u.gpr r = (entryOf w σ).gpr r := fun {σ u} f r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact f.1 _ (by decide) (by decide) (by decide)
    · exact f.1 _ (by decide) (by decide) (by decide)
    · exact f.1 _ (by decide) (by decide) (by decide)
    · exact f.2.1
    · exact f.1 _ (by decide) (by decide) (by decide)
    · exact f.1 _ (by decide) (by decide) (by decide)
  have pu : (rfcP (hashOf hC vs w hw) (names vs)).pub u₁ u₂ :=
    pub_trans (a := entryOf w σ₁) (S := stackT) (F := tabFacts w.H (fnsOf vs))
      (pub_congr (pub_refl (S := stackT) (F := tabFacts w.H (fnsOf vs)) _) (reg f₁) f₁.2.2.2.2.1
        f₁.2.2.2.2.2.2.2)
      (pub_congr hpub (reg f₂) f₂.2.2.2.2.1 f₂.2.2.2.2.2.2.2)
  exact ⟨sign_ct hns u₁ u₂ t₁ t₂ u₁' u₂' (pre_at hC hw p₁ f₁) (pre_at hC hw p₂ f₂) pu e₁ e₂, trivial⟩

/-! ## No instruction loads MXCSR, or writes `rsp` but the frame's -/

theorem fnsOk_of (vs : List MdHash) : FnsOk (fnsOf vs).init ∧ FnsOk (fnsOf vs).upd ∧ FnsOk (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact VG.Proof.RsaOaep.X86_64.okI_all_of
      (Proof.Pbkdf2.Md.X86_64.nosp_of (Proof.Pbkdf2.Md.X86_64.core_hmacInit w.K.cNs w.K.iNs w.C.hinitNs))
      (Proof.Pbkdf2.Md.X86_64.core_hmacInit w.K.cMx w.K.iMx w.C.hinitMx)
  · exact (Proof.RsaOaep.X86_64.HGood.of w.ok w.K).upd
  · exact VG.Proof.RsaOaep.X86_64.okI_all_of
      (Proof.Pbkdf2.Md.X86_64.nosp_of (Proof.Pbkdf2.Md.X86_64.core_hmacFin w.K.cNs w.C.hfinNs))
      (Proof.Pbkdf2.Md.X86_64.core_hmacFin w.K.cMx w.C.hfinMx)

theorem core_okP (R : RfcCurve) : OkP R.coreC :=
  VG.Proof.RsaOaep.X86_64.okI_all_of (Proof.Pbkdf2.Md.X86_64.nosp_of R.coreNs) R.coreMx

theorem body_okP_cfgT (R : RfcCurve) (tries : Nat) (vs : List MdHash) : OkP (cfgT R tries vs).body :=
  body_okP (c := cfgT R tries vs) R.blk (fnsOk_of vs) (core_okP R)

theorem okP_all {c : Prog isa} (h : OkP c) {p : Instr → Bool}
    (hp : ∀ i, VG.Proof.RsaOaep.X86_64.okI i = true → p i = true) : c.allInstrs p = true := by
  have h' : c.allInstrs VG.Proof.RsaOaep.X86_64.okI = true := h
  rw [Code.allInstrs_eq] at h' ⊢
  exact List.all_eq_true.mpr fun i hi => hp i (List.all_eq_true.mp h' i hi)

/-- No instruction of `vg_ecdsa_<curve>_sign`, or of the functions it calls, loads MXCSR. -/
theorem signCode_mx (R : RfcCurve) (tries : Nat) (vs : List MdHash) :
    (signCodeT R tries vs).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hb := okP_all (body_okP_cfgT R tries vs) (p := fun x => !loadsMxcsr x) fun x h => by
    simp only [VG.Proof.RsaOaep.X86_64.okI, Bool.and_eq_true] at h; exact h.2
  show (_ && (_ && _ && _)) = true
  rw [hb]; rfl

/-- `rsp` is written only by the frame's push and pop. -/
theorem signCode_sp (R : RfcCurve) (tries : Nat) (vs : List MdHash) :
    (signCodeT R tries vs).all (fun i => !isa.writesSp i) = true := by
  have hb : (cfgT R tries vs).body.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by
      rw [Code.allInstrs_eq]
      have hn : NoSp (cfgT R tries vs).body := fun x hx => by
        have := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans (body_okP_cfgT R tries vs)) x hx
        simp only [VG.Proof.RsaOaep.X86_64.okI, Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1
      exact List.all_eq_true.mpr fun x hx => by rw [VG.Proof.RsaOaep.X86_64.SpSafe.of_noSp hn x hx]; rfl)
  show (_ && (_ && _ && _)) = true
  rw [hb]; rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64
