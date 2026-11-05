module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on AArch64: the contract with the hash function as a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSpec.lean`):
`TableInstance.signContract`, with the tables of `vs` for `hmac`, the
curve's comb tables and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hmac` points to is one of `vs`', whose words
give the contract the proof of the body is written against, after the entry
(`preW_of`); its hash function is the one the table names, so the results
agree; and two runs whose public data agree take the same table. So
`vg_ecdsa_<curve>_sign` is verified (`signT_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- The contract on the arguments, with the curve's comb tables `cs` and the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List MdHash) :
    Contract isa :=
  T.signContract ((AArch64.abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]) stackT

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 6 = ⟨p, 48⟩ := rfl

theorem names_eq (vs : List MdHash) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hmac` points to holds `w`'s. -/
abbrev HeldW (w : MdHash) (s : State) : Prop := Abi.tableHeld 64 s.mem (s.gpr .x5) (FnTable.words isa s (tableOf w))

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

/-- The comb tables are where the code reads them. -/
theorem tableAddr_eq (hne : R.E.tbl.isEmpty = false) (sy : String → Addr) : tableAddr R.E sy = sy R.E.tsym := by
  simp only [tableAddr, hne, Bool.false_eq_true, ite_false]

theorem tableRegions_eq (hne : R.E.tbl.isEmpty = false) (p : Addr) :
    tableRegions R.E p = [⟨p, 8 * R.E.combWords.length⟩] := by
  simp only [tableRegions, hne, Bool.false_eq_true, ite_false]

/-- The precondition. -/
theorem pre_facts (hne : R.E.tbl.isEmpty = false) (hsw : T.scratchWords = 1024) (hO : OK vs) {s : State}
    (h : (specK T [(R.E.tsym, R.E.combWords)] vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, stackT,
    String.reduceEq, Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left', hsw, tableRegion_eq, List.append_nil, names_eq, below] at h
  obtain ⟨hsp, hdrop, hheld, hfit, hdw, hstk, -, ⟨Tb, hTb, hth⟩, hpw, htake, hwr, od, og, oc, ot, dc, gc, ct,
    ko, kd, kg, kc, kt, no, nd, ng, nc, n5, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hth⟩, fun w hv hw' => ?_⟩
  have hw := hO.2.2.2 w hv
  have hh := held_tableOf hw'
  have hlen : (s.gpr .x3).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.mgf.len
  rw [hlen] at og gc kg ng htake
  rw [List.append_eq, List.append_nil] at hpw
  rw [hw.blockSize] at hh
  simp only [hsw, Nat.reduceMul] at hwr oc dc gc kc nc ct
  refine ⟨⟨?_, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, ⟨?_, ?_, ?_⟩, n5, ot.symm, ct.symm,
    kt.symm, tabOK_of hO.1 hpw hv, hh.1, rfl, rfl⟩, hh.2.1, hh.2.2.1, hh.2.2.2⟩
  · show s.rd = _
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop, tableRegions_eq hne, tableAddr_eq hne]
    rfl
  · intro i hi
    show s.mem.readW (tableAddr R.E s.syms + BitVec.ofNat 64 (8 * i)) 64 = R.E.combWords.getD i 0
    rw [tableAddr_eq hne]; exact hheld i hi
  · show (tableAddr R.E s.syms).toNat + 8 * R.E.combWords.length ≤ 2 ^ 64
    rw [tableAddr_eq hne]; exact hfit
  · show ∀ r ∈ _, Region.Disjoint ⟨tableAddr R.E s.syms, 8 * R.E.combWords.length⟩ r
    rw [tableAddr_eq hne]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hdw _ (by rw [hwr]; exact List.mem_cons_self ..)
    · exact hdw _ (by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · exact hstk

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HmacTable.hashAt 64 s.mem (s.gpr .x5) = some H → Spec.HmacTable.hmacOf H = some F →
        match (T.result H F s.mem (s.gpr .x1) (s.gpr .x2)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .x0) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .x0) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .x0) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.2.1))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ s₁.sp = s₂.sp ∧
    (∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], s₁.gpr r = s₂.gpr r) ∧
    T.tried 64 s₁.mem (s₁.gpr .x1) (s₁.gpr .x2) (s₁.gpr .x5) =
      T.tried 64 s₂.mem (s₂.gpr .x1) (s₂.gpr .x2) (s₂.gpr .x5) ∧
    s₁.syms R.E.tsym = s₂.syms R.E.tsym ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : MdHash} (hw : WOk w) {s : State} (hp : PreW R T vs w s) :
    T.tried 64 s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x5) =
      ((instOf T w).result s.mem (s.gpr .x1) (s.gpr .x2)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.2.1, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hne : R.E.tbl.isEmpty = false) (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁)
    (h₂ : PreFacts R T vs s₂) (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hsp, hg, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  refine ⟨w, hv, hw, p₁, p₂, hsp, hg .x0 (by simp), hg .x1 (by simp), hg .x2 (by simp), hg .x4 (by simp),
    hg .x5 (by simp), ?_, by show tableAddr R.E s₁.syms = tableAddr R.E s₂.syms; rw [tableAddr_eq hne,
      tableAddr_eq hne, hc], hn⟩
  show ((instOf T w).result s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 =
    ((instOf T w).result s₂.mem (s₂.gpr .x1) (s₂.gpr .x2)).2
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

/-- The public data. -/
theorem pub_facts {s₁ s₂ : State} (h : (specK T [(R.E.tsym, R.E.combWords)] vs).pub s₁ s₂) :
    PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq, below] at h
  obtain ⟨hsp, hc₀, hn, hT, htr, e₀, e₁, e₂, -, e₄, e₅⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, fun r hr => ?_, (List.cons.inj htr).1,
    hc₀, hn⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts R T vs s) : (tabK R T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hne : R.E.tbl.isEmpty = false) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) : (tabK R T vs).Implies (specK T R.E.combConsts vs) := by
  rw [show R.E.combConsts = [(R.E.tsym, R.E.combWords)] from rfl] at hsat ⊢
  refine ⟨fun s h => (pre_facts hne hsw hO h).pre hO, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => pub_of hne hO (pre_facts hne hsw hO h₁) (pre_facts hne hsw hO h₂) (pub_facts hp), hsat⟩
  have hk := (pre_facts hne hsw hO h).pre hO
  sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq, below]
  exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hne : R.E.tbl.isEmpty = false) (hsw : T.scratchWords = 1024)
    (hO : OK vs) (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) :
    Verified AArch64.target (signCodeT R T.tries vs) (specK T R.E.combConsts vs) :=
  Verified.of_correct (fun _ h => let ⟨t, s', he, ⟨hg, hsp⟩, hp⟩ := signT_ok hC h
      ⟨t, s', he, ⟨hg, hsp, Exec.preservedV he (signT_keepsV R T.tries vs)⟩, hp⟩)
    (signT_ct hC) (tab_implies hne hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.AArch64
