module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_rsa_pss_sign_precomputed` on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. `signP`, the code of
`vg_rsa_pss_sign` calling `vg_rsa_private_checked_precomputed` (`signG …
true`), against `Spec.RsaPss.signPrecomputedMdTableContract`: its
precondition gives `PreS true` and `PreXS` (`preS_ofP`) and the tables
(`spec_tabSP`), its public data `PubS true` (`pubS_ofP`), and the proofs
shared with `vg_rsa_pss_sign` (`correct_of`, `constantTime_of`) the rest. A
state meeting the precondition (`signP_sat`), and `signP_ok'`, which the
registration binds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.RsaOaep.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.MdHashTable.PPC64LE (MVar)

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17] := rfl

abbrev signPSpec (hs gs : List FnTable) : Contract isa :=
  Spec.RsaPss.signPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", hs), ("mgf1", gs)]) (stackBytes true)

macro "signP_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes true = 3791 + 1 := rfl
  unfold signPSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq, List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.RsaPss.digestLenOk, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables,
    Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq, List.range, List.range.loop] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

theorem preS_ofP {hs gs : List FnTable} {s : State} (h : (signPSpec hs gs).pre s) :
    PreXS s ∧ ∀ {H : Spec.Mgf1.Hash}, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some H →
      PreS true H.len s := by
  signP_pre at h
  obtain ⟨sp1, sp2, -, -, -, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oP, oth, otg, oa, ns, es, ps, qs,
    dps, dqs, qis, dgs, sls, sP, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kP, kth, ktg, ka, wo, wn,
    we, wp, wq, wdp, wdq, wqi, wdg, wsl, wsc, wP, wth, wtg, ⟨k1, k2⟩, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, hpl,
    -, hl⟩ := h
  refine ⟨⟨oP, sP, kP, wP, hpl⟩, fun {H} hH => ?_⟩
  have hl := hl H hH
  rw [hl] at hrd odg dgs kdg wdg
  exact ⟨sp1, by omega, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oth, otg, oa, ns, es, ps, qs, dps,
    dqs, qis, dgs, sls, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kth, ktg, ka, wo, wn, we, wp,
    wq, wdp, wdq, wqi, wdg, wsl, wsc, wth, wtg, k1, k2, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs⟩

/-- The variant's precondition: `pre` holds the key's precomputed values. -/
theorem hypS_ofP {hs gs : List FnTable} {s : State} (h : (signPSpec hs gs).pre s) : HypS true s := by
  signP_pre at h
  obtain ⟨sp1, sp2, -, -, -, hrd, hwr, on, oe, op, oq, odp, odq, oqi, odg, osl, os, oP, oth, otg, oa, ns, es, ps, qs,
    dps, dqs, qis, dgs, sls, sP, sth, stg, sa, ko, kn, ke, kp, kq, kdp, kdq, kqi, kdg, ksl, ks, kP, kth, ktg, ka, wo, wn,
    we, wp, wq, wdp, wdq, wqi, wdg, wsl, wsc, wP, wth, wtg, ⟨k1, k2⟩, ok, e1, e2, p1, p2, q1, q2, h3, h7, h5, hs, hpl,
    hk, -⟩ := h
  exact fun _ => hk

/-- The tables, as the variant's contract gives them. -/
theorem spec_tabSP {hs gs : List FnTable} {s : State} (h : (signPSpec hs gs).pre s) : TabFacts hs gs s := by
  signP_pre at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The variant's public data: `PubS true`, the tables' functions at the
same addresses, and the same tables held. -/
theorem pubS_ofP {hs gs : List FnTable} {s₁ s₂ : State} (h : (signPSpec hs gs).pub s₁ s₂) :
    PubS true s₁ s₂ ∧
      (∀ f ∈ (hs.map (fun T : FnTable => T.fns)).flatten ++ (gs.map (fun T : FnTable => T.fns)).flatten,
        s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ hs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 14) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 14) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ gs, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T)) := by
  have e : stackBytes true = 3791 + 1 := rfl
  unfold signPSpec at h
  rw [e] at h
  sig_pub [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_eighteen, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htab, htab', hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17⟩ := h
  obtain ⟨hne, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h6, h8])
  simp only [List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp [bytesAt_length, h6])
  have inj := fun {w : Nat} {x y : List (BitVec w)} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm,
    fun _ => ⟨a16.symm, a17.symm, (inj hw).symm⟩⟩, hsy, fun T hT => htab _ _ rfl rfl T hT,
    fun T hT => htab' _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm]

section
variable {vs : List MVar} {gs : List MVar}

/-- The correctness of `vg_rsa_pss_sign_precomputed`, against its contract,
for the tables of `vs` and `gs`. -/
theorem codeP_correct (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) (s : State)
    (h : (signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    ∃ t s', Exec isa (signP (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs)) s t s' ∧
      abiPreserved s s' ∧ (signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).post s s' := by
  obtain ⟨X, hP⟩ := preS_ofP h
  obtain ⟨H, G, hH, hG, t, s', he, habi, hr⟩ :=
    correct_of (pc := true) hc hc' (spec_tabSP h) hP (fun _ => X)
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes true = 3791 + 1 := rfl
  unfold signPSpec
  rw [e]
  sig_post [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_eighteen,
    List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr (hypS_ofP h)

/-- Constant time: `constantTime_of` with the variant's contract's facts. -/
theorem codeP_constantTime (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs) :
    ConstantTime isa (signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre
      (signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pub
      (signP (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs)) :=
  constantTime_of (pc := true) hc hc' spec_tabSP (fun h hH => (preS_ofP h).2 hH) (fun h _ => (preS_ofP h).1)
    pubS_ofP

/-- `vg_rsa_pss_sign_precomputed` against its contract, for the tables of
`vs` and `gs`, given a state meeting it. -/
theorem signP_verified (hc : MdHashTable.PPC64LE.Coh vs) (hc' : MdHashTable.PPC64LE.Coh gs)
    (hsat : ∃ s, (signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s) :
    Verified PPC64LE.target (signP (MdHashTable.PPC64LE.fnsOf vs) (MdHashTable.PPC64LE.fns3 gs))
      (signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)) :=
  ⟨codeP_correct hc hc', codeP_constantTime hc hc', hsat⟩

end

end VG.Proof.RsaPss.PPC64LE.Sg

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Proof.HashTable (symsOf_distinct)
open VG.Proof.MdHashTable.PPC64LE (MVar)

/-! ## A key for the witness

`p = q = 2²⁵⁶ − 1` (32 octets each) and `n = p q` (64 octets): `n` is odd,
at least `2⁵¹¹`, and `p q = n`, so `privatePrecompute` has a value, `kPre`
(24 words). `keyMem` holds `n` at `0x2000`, `p` at `0x4200`, `q` at
`0x4300` and `kPre` at `0x4800`. -/

def kP : Nat := 2 ^ 256 - 1
def kN : Nat := kP * kP

/-- The key's precomputed values. -/
def kPre : List (BitVec 64) :=
  (Spec.Rsa.privatePrecompute (Spec.Rsa.i2osp kN 64) (Spec.Rsa.i2osp kP 32) (Spec.Rsa.i2osp kP 32)).getD []

/-- Whether the address `i` is in the key's buffers. -/
def keyIn (i : Nat) : Bool :=
  (Nat.ble 0x2000 i && Nat.blt i 0x2040) || (Nat.ble 0x4200 i && Nat.blt i 0x4220) ||
    (Nat.ble 0x4300 i && Nat.blt i 0x4320) || (Nat.ble 0x4800 i && Nat.blt i 0x48C0)

/-- The key's buffers. -/
def keyMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.blt i 0x2040 then (Spec.Rsa.i2osp kN 64).getD (i - 0x2000) 0
  else bif Nat.blt i 0x4800 then 0xFF
  else BitVec.ofNat 8 ((kPre.getD ((i - 0x4800) / 8) 0).toNat / 256 ^ ((i - 0x4800) % 8))

theorem keyMem_pre : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt keyMem 0x2000 64)
    (Spec.Rsa.bytesAt keyMem 0x4200 32) (Spec.Rsa.bytesAt keyMem 0x4300 32) =
      some (Spec.Rsa.wordsAt keyMem 0x4800 24) := by lit_decide

/-- The memory of `signPSatBase dl`: the key, the stack arguments that
differ, and `signSatBase dl`'s. -/
def pMem (dl : Nat) (a : Addr) : Byte :=
  bif keyIn a.toNat then keyMem a
  else bif Nat.beq a.toNat 0x10068 then 32 else bif Nat.beq a.toNat 0x10078 then 32
  else bif Nat.beq a.toNat 0x10088 then 32 else bif Nat.beq a.toNat 0x10098 then 32
  else bif Nat.beq a.toNat 0x100E1 then 0x48 else bif Nat.beq a.toNat 0x100E8 then 24
  else (signSatBase dl).mem a

/-- `signSatBase dl` with the key (`keyMem`) and its precomputed values:
`p`, `q`, `dp`, `dq` and `qinv` of 32 octets, `pre_len` 24 words at
`0x4800`. -/
def signPSatBase (dl : Nat) : State :=
  { signSatBase dl with
    gpr := fun r => bif r == .r10 then 32 else (signSatBase dl).gpr r
    mem := pMem dl
    rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
      ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300100, 88⟩, ⟨0x10060, 144⟩] }

/-- The stack arguments of `signPSatBase dl`. -/
def signPArgs (dl : Nat) (j : Nat) : BitVec 64 :=
  if j = 16 then 0x4800 else if j = 17 then 24 else if j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 then 32 else signArgs dl j

/-- A memory that agrees with `keyMem` on the key's buffers holds the key. -/
theorem key_pre_of {m : Mem} (h : ∀ a : Addr, keyIn a.toNat = true → m a = keyMem a) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m 0x2000 64) (Spec.Rsa.bytesAt m 0x4200 32)
      (Spec.Rsa.bytesAt m 0x4300 32) = some (Spec.Rsa.wordsAt m 0x4800 24) := by
  have hb : ∀ (A : Addr) (L : Nat), (∀ i < L, keyIn (A + BitVec.ofNat 64 i).toNat = true) →
      Spec.Rsa.bytesAt m A L = Spec.Rsa.bytesAt keyMem A L := fun A L hk =>
    List.map_congr_left fun i hi => h _ (hk i (List.mem_range.mp hi))
  have kin : ∀ (A : Addr) (i : Nat), A.toNat + i < 0x300000 →
      (A + BitVec.ofNat 64 i).toNat = A.toNat + i := fun A i h => by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have kb : ∀ (A : Addr) (L : Nat), A.toNat + L < 0x300000 →
      (∀ i < L, keyIn (A.toNat + i) = true) → ∀ i < L, keyIn (A + BitVec.ofNat 64 i).toNat = true :=
    fun A L hL h i hi => by rw [kin A i (by omega)]; exact h i hi
  have ki : ∀ x, ((0x2000 ≤ x ∧ x < 0x2040) ∨ (0x4200 ≤ x ∧ x < 0x4220) ∨ (0x4300 ≤ x ∧ x < 0x4320) ∨
      (0x4800 ≤ x ∧ x < 0x48C0)) → keyIn x = true := fun x hx => by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
  rw [hb 0x2000 64 (kb _ _ (by decide) fun i hi => ki _ (by have : (0x2000 : Addr).toNat = 0x2000 := rfl; omega)),
    hb 0x4200 32 (kb _ _ (by decide) fun i hi => ki _ (by have : (0x4200 : Addr).toNat = 0x4200 := rfl; omega)),
    hb 0x4300 32 (kb _ _ (by decide) fun i hi => ki _ (by have : (0x4300 : Addr).toNat = 0x4300 := rfl; omega))]
  have hw : Spec.Rsa.wordsAt m 0x4800 24 = Spec.Rsa.wordsAt keyMem 0x4800 24 := by
    refine List.map_congr_left fun i hi => Mem.readW_congr fun j hj => h _ ?_
    have hi := List.mem_range.mp hi
    have e0 : (0x4800 : Addr).toNat = 0x4800 := rfl
    have e1 : ((0x4800 : Addr) + BitVec.ofNat 64 (8 * i)).toNat = 0x4800 + 8 * i := kin _ _ (by omega)
    rw [kin _ j (by rw [e1]; omega), e1]
    exact ki _ (by omega)
  rw [hw]
  exact keyMem_pre

theorem signPSat_args (dl : Nat) : ∀ j < 18, (stackArgAddr (signPSatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, signPSatBase, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- The variant's precondition, from the facts of a state. -/
theorem signP_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signPSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 18, stackArg s j = signPArgs dl j)
    (hrd : s.rd = (signPSatBase dl).rd) (hwr : s.wr = (signPSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl))
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (Sg.signPSpec tsH tsG).pre s := by
  have e : Sg.stackBytes true = 3791 + 1 := rfl
  unfold Sg.signPSpec
  rw [e]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, Sg.stackArgs_eighteen, List.append_eq, Sig.tableRegion, List.range,
    List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), hg, hsp, hrd, hwr, hA, signPArgs, signArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Nat.reduceEqDiff]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, Sg.stackArgs_eighteen, List.append_eq, Sig.tableRegion, List.range,
    List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hdl']; simp; omega)
    | exact hk
    | skip

theorem tabMem_lt {m : Mem} {vs : List MVar} {gs : List MVar} {w : MVar} {w' : MVar} {a : Addr}
    (h : a.toNat < 0x300000) : tabMem m vs gs w w' a = m a := by
  simp only [tabMem, Nat.blt_eq.mpr h, Bool.cond_true]

theorem signPSatBase_key (dl : Nat) {a : Addr} (h : keyIn a.toNat = true) : (signPSatBase dl).mem a = keyMem a := by
  show pMem dl a = keyMem a
  unfold pMem
  rw [h]
  exact Bool.cond_true

theorem signP_sat_of {vs : List MVar} {gs : List MVar} {w : MVar} (hw : w ∈ vs) {w' : MVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 18, stackArg (signPSatBase dl) j = signPArgs dl j) :
    (Sg.signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre
      (withTabs (signPSatBase dl) vs gs w w') :=
  signP_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (signPSat_args dl j hj)).trans (hb j hj)) rfl
    rfl ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩
    ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩ (symsOf_distinct hl) (fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (signPSatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]
    ) (key_pre_of fun a ha => by
      have h3 : a.toNat < 0x300000 := by
        simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
      exact (tabMem_lt h3).trans (signPSatBase_key dl ha))

theorem signPSat_b16 : ∀ j < 18, stackArg (signPSatBase 16) j = signPArgs 16 j := by decide
theorem signPSat_b20 : ∀ j < 18, stackArg (signPSatBase 20) j = signPArgs 20 j := by decide
theorem signPSat_b28 : ∀ j < 18, stackArg (signPSatBase 28) j = signPArgs 28 j := by decide
theorem signPSat_b32 : ∀ j < 18, stackArg (signPSatBase 32) j = signPArgs 32 j := by decide
theorem signPSat_b48 : ∀ j < 18, stackArg (signPSatBase 48) j = signPArgs 48 j := by decide
theorem signPSat_b64 : ∀ j < 18, stackArg (signPSatBase 64) j = signPArgs 64 j := by decide

theorem signP_sat {vs : List MVar} {gs : List MVar} {w : MVar} (hw : w ∈ vs) {w' : MVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (Sg.signPSpec (MdHashTable.PPC64LE.tables vs) (MdHashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, signP_sat_of hw hw' hl (by decide) e signPSat_b16⟩
  · exact ⟨_, signP_sat_of hw hw' hl (by decide) e signPSat_b20⟩
  · exact ⟨_, signP_sat_of hw hw' hl (by decide) e signPSat_b28⟩
  · exact ⟨_, signP_sat_of hw hw' hl (by decide) e signPSat_b32⟩
  · exact ⟨_, signP_sat_of hw hw' hl (by decide) e signPSat_b48⟩
  · exact ⟨_, signP_sat_of hw hw' hl (by decide) e signPSat_b64⟩

/-- `vg_rsa_pss_sign_precomputed`, with the tables of `vs` and `gs`. -/
theorem signP_ok' {vs : List MVar} {gs : List MVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.Sign.signP (MdHashTable.PPC64LE.fnsOf vs)
      (MdHashTable.PPC64LE.fns3 gs)) (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", MdHashTable.PPC64LE.tables vs),
          ("mgf1", MdHashTable.PPC64LE.tables gs)]) 3792) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  Sg.stackBytes_true ▸ Sg.signP_verified h.1 h.2.1 (signP_sat hw hw' h.2.2.2.2)

end VG.Proof.RsaPss.PPC64LE
