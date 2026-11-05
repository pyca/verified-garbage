module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
public import VerifiedGarbage.Proof.HmacTable.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.CT
meta import VerifiedGarbage.Proof.HmacTable.PPC64LE
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on PPC64LE: the HMAC of a table

`vg_ecdsa_<curve>_sign` (`signCodeT`) is the one body (`cfgT`, the same for
every hash function), which saves `D` and `B`, the digest length and HMAC's
block size, from the table `hmac` (its words 4 and 5) and calls the table's
functions. For the variants `vs` of the hash functions that pass the
registration's checks (`OK`: their functions of the same name have the same
code, and each is of a hash function with HMAC, of sizes the frame holds),
the table of each variant `w` makes the body the code for `w`'s hash
function (`hashOf`, with `cfgT_eq`, which holds by `rfl`), which meets the
contract with that hash function fixed (`sign_ok`, `sign_ct`). `tabK` states
that contract for whichever of the tables `hmac` holds; `TableSpec.lean`
shows `TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.HmacTable.PPC64LE (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Cfg where
  f := fnsOf vs
  w := R.w
  len := R.Q
  big := R.big
  sh := R.sh
  n := R.C.E.curve.n
  tries := tries
  coreN := R.C.N
  coreC := R.C.C

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Prog isa := (cfgT R tries vs).sign

/-- The stack it uses. -/
def stackT : Nat := 736

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), of one of the digest lengths and block sizes the frame
holds, and the states and working space of `w`'s HMAC fit those in `scratch`. -/
def WOk (w : HVar) : Prop :=
  (match Spec.HmacTable.hmacOf w.G with
    | some F => F.blockSize = w.H.B
    | none => False) ∧
  (w.H.D, w.H.B) ∈ shapes ∧ w.H.S ≤ 192 ∧ sWork + w.I.scratch * 8 ≤ sMsg ∧ sWork + w.H.W ≤ sMsg

instance (w : HVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.HmacTable.hmacOf w.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem _root_.VG.Proof.HmacTable.PPC64LE.HVar.mem (w : HVar) : w.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : HVar} (hw : WOk w) : Spec.HmacTable.hmacOf w.G = some w.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ w.mem F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem WOk.blockSize {w : HVar} (hw : WOk w) : Spec.HmacTable.blockSize w.G = w.H.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hB

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Spec.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.SH.H
  hashLen := w.H.D
  hashName := ""
  hashTitle := ""
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.C.E
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 15

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    (w : HVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  v := w
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.1
  hS := hw.2.2.1
  hScr := hw.2.2.2.1
  hW := hw.2.2.2.2

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    {w : HVar} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.G w.ok.SH.H m d dg := by
  simp only [Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.len]

/-! ## The contract with whichever table `hmac` is -/

/-- What the contract with the table of `w` says: the contract the proof is
written against, and the table's index. -/
def PreW (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (rfcPPC (instOf T w) stackT (tabFacts w (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `r8` is. -/
def tabK (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW T vs w s →
    match (T.result w.G w.ok.SH.H s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW T vs w s₁ ∧ PreW T vs w s₂ ∧
    (rfcPPC (instOf T w) stackT (tabFacts w (fnsOf vs)) (names vs)).pub s₁ s₂

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : HVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.G) = BitVec.ofNat 64 (Spec.HashTable.index w.G)) :
    w'.G = w.G ∧ w'.ok.SH.H = w.ok.SH.H := by
  have hl : ∀ v : HVar, Spec.HashTable.index v.G < Spec.Mgf1.hashes.length := fun v =>
    (List.getElem?_eq_some_iff.mp v.idx).1
  have h₁ := hl w; have h₂ := hl w'
  have hlen : Spec.Mgf1.hashes.length < 2 ^ 64 := by decide
  have e : Spec.HashTable.index w'.G = Spec.HashTable.index w.G := by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hG : w'.G = w.G := Option.some.inj (w'.idx.symm.trans (e ▸ w.idx))
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers, its stack pointer and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT
  rw [cfgT_eq hC vs hw]
  refine WP.mono (sign_ok (P := hashOf hC vs w hw) (ns := names vs) hp.1) fun s' ⟨hab, hpost⟩ => ⟨hab, ?_⟩
  intro w' _ hw' hp'
  obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3)
        (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3)
        (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) (B : RfcT (cfgC R.w R.Q R.big R.sh R.C.E.curve.n)) :
    ConstantTime isa (tabK T vs).pre (tabK T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, hw, p₁, p₂, hpub⟩ e₁ e₂
  unfold signCodeT at e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [w.initN, w.H.updN, w.finN], n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  exact sign_ct (P := hashOf hC vs w hw) B hns s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Proof.HmacTable.PPC64LE (HVar tables names tableOf held_tableOf hashAt_tableOf mem_names tabOK_of)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa :=
  T.signContract (PPC64LE.abi.withTables T.signSig [("hmac", tables vs)]) stackT

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 6 = ⟨p, 48⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- The table `hmac` points to holds `w`'s. -/
abbrev HeldW (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 64 s.mem (s.gpr .r8) (FnTable.words isa s (tableOf w))

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract the proof is written against. -/
def PreFacts (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW T vs w s

theorem pre_facts (hsw : T.scratchWords = 1024) (hO : OK vs) {s : State} (h : (specK T vs).pre s) :
    PreFacts T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, dc, gc, ct, ko, kd, kg, kc, kt, no, nd, ng, nc, nt,
    hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hlen : (s.gpr .r6).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.len
  rw [hlen] at hrd og gc kg ng
  rw [hsw] at hwr oc dc gc ct kc nc
  rw [List.append_eq, List.append_nil] at hpw
  have hw := hO.2.2.2 w hv
  refine ⟨⟨hrd, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, nt, ot.symm, ct.symm, kt,
    tabOK_of hO.1 hpw hv, hh.1, hh.2.2.1, ?_⟩, hh.2.1⟩
  rw [hh.2.2.2, hw.blockSize]

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts T vs s) : (tabK T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

theorem tried_eq {w : HVar} (hw : WOk w) {s : State} (hp : PreW T vs w s) :
    T.tried 64 s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r8) = ((instOf T w).result s.mem (s.gpr .r4) (s.gpr .r5)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.2, hw.hmac, tresult_eq]

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK T vs).pre s) (hp : (tabK T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HmacTable.hashAt 64 s.mem (s.gpr .r8) = some H → Spec.HmacTable.hmacOf H = some F →
        match (T.result H F s.mem (s.gpr .r4) (s.gpr .r5)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .r3) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .r3) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs) (hsat : ∃ s, (specK T vs).pre s) :
    (tabK T vs).Implies (specK T vs) := by
  refine ⟨fun s h => (pre_facts hsw hO h).pre hO, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp => ?_, hsat⟩
  · have hk := (pre_facts hsw hO h).pre hO
    sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact post_of hk hp
  · obtain ⟨⟨w, hv, hh⟩, f₁⟩ := pre_facts hsw hO h₁
    have f₂ := (pre_facts hsw hO h₂).2
    sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq] at hp
    obtain ⟨hsp, hn, hT, htr, e3, e4, e5, -, e7, e8⟩ := hp
    rw [List.append_eq, List.append_nil] at hn
    have hw := hO.2.2.2 w hv
    have p₁ := f₁ w hv hh
    have p₂ := f₂ w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh)
    refine ⟨w, hv, hw, p₁, p₂, hsp, e3, e4, e5, e7, e8, ?_, hn⟩
    show ((instOf T w).result s₁.mem (s₁.gpr .r4) (s₁.gpr .r5)).2 =
      ((instOf T w).result s₂.mem (s₂.gpr .r4) (s₂.gpr .r5)).2
    rw [← tried_eq hw p₁, ← tried_eq hw p₂]
    exact (List.cons.inj htr).1

/-! ## The contract is satisfiable -/

open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)

/-- Six words at `p`. -/
def put6 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) w₀).writeW (p + BitVec.ofNat 64 (8 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (8 * 2)) w₂).writeW (p + BitVec.ofNat 64 (8 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (8 * 4)) w₄).writeW (p + BitVec.ofNat 64 (8 * 5)) w₅

/-- The table `put6` writes at `0x300000`. -/
theorem put6_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 6) :
    Abi.tableHeld 64 (put6 m 0x300000 (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0)
      (ws.getD 5 0)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put6]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64,
      BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [Mem.readW_writeW_self64, BitVec.setWidth_eq]

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : Addr := if n ∈ names vs then symsOf (names vs) n else 0x100000

/-- A state meeting the contract, for scalars of `Q` bytes, with the table of `w`. -/
def satT (vs : List HVar) (w : HVar) (Q : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => BitVec.ofNat 64 w.H.D | .r7 => 0x8000
    | .r8 => 0x300000 | _ => 0
  lr := 0
  sp := 0x20000
  mem := put6 (fun _ => 0) 0x300000 (symT vs w.initN) (symT vs w.H.updN) (symT vs w.finN)
    (BitVec.ofNat 64 (Spec.HashTable.index w.G)) (BitVec.ofNat 64 w.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G))
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.H.D⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List HVar) (w : HVar) (Q : Nat) :
    Abi.tableHeld 64 (satT vs w Q).mem 0x300000 (FnTable.words isa (satT vs w Q) (tableOf w)) :=
  put6_held (ws := [symT vs w.initN, symT vs w.H.updN, symT vs w.finN,
    BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)]) rfl

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 32) :
    (names vs).Pairwise fun f g => f ≠ g → symT vs f ≠ symT vs g :=
  (symsOf_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

theorem sat_nil (hO : OK vs) (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) :
    ∃ s, (specK T vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w T.ecdsa.curve.len, ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD : w.H.D ≤ 64 := by
    have h := hw.2.1
    simp only [shapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    omega
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hG : Spec.HmacTable.hashAt 64 (satT vs w T.ecdsa.curve.len).mem 0x300000 = some w.G :=
    hashAt_tableOf (held_tableOf (satT_held vs w _)).2.1
  simp only [hDn, hsw, satT] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.len.symm, by rw [hw.hmac]; rfl⟩)

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract`. -/
theorem signT_verified (hC : CurveT R T) (B : RfcT (cfgC R.w R.Q R.big R.sh R.C.E.curve.n))
    (hsw : T.scratchWords = 1024) (hO : OK vs) (hQ : T.ecdsa.curve.len ≤ 66) :
    Verified PPC64LE.target (signCodeT R T.tries vs) (specK T vs) :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC B) (tab_implies hsw hO (sat_nil hO hQ hsw))

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
