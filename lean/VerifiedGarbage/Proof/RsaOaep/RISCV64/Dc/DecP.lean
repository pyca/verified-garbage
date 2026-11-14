module

-- separate module: it builds in parallel with encryption's proofs (`RsaOaep.RISCV64.Verified`), which `Inst` also needs.

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Verified
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# `vg_rsa_oaep_decrypt_precomputed` on RISC-V

Untrusted: everything here is checked by Lean. As on PPC64LE: the code of
`vg_rsa_oaep_decrypt` calling `vg_rsa_private_checked_precomputed`
(`decryptG … true`), against `Spec.RsaOaep.decryptPrecomputedMdTablesContract`:
its precondition gives `PreD true`, with `pre`'s facts (`preD_ofP`), and the
tables (`spec_tabDP`), its public data `PubD true` (`pubD_ofP`), and the
proofs shared with `vg_rsa_oaep_decrypt` (`code_ok`, `code_constantTimeG`)
the rest. A state meeting the precondition holds a real key (`decP_sat`,
`Rsa.PreKey`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem stackArgs_nineteen (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17,
      stackArg s 18] := rfl

/-- The variant's contract, with both hash functions each one of the tables
`ts`, and the stack of the frames and of
`vg_rsa_private_checked_precomputed`. -/
abbrev decPSpec (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) (stackBytes true)

/-- Unfolds the variant's precondition at `h`. -/
macro "decP_pre" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes true = 3487 + 1 := rfl
  unfold decPSpec at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop, Spec.Rsa.lenValid] at $h:ident
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Sig.pairFacts, List.filterMap_cons, List.filterMap_nil,
    Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil] at $h:ident))

/-- The variant's precondition gives `PreD true` (`pre`'s facts in `px`). -/
theorem preD_ofP {ts : List FnTable} {s : State} (h : (decPSpec ts).pre s) : PreD true s := by
  decP_pre at h
  obtain ⟨spal, sp1, sp2, -, -, -, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, -, otl, ot, oa, mln, mle,
    mlp, mlq, mldp, mldq, mlqi, mll, mlct, mls, -, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, sP, stl, st,
    sa, ko, kml, kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, kP, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi,
    wl, wct, wsc, wP, wtl, wt, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs, hpl, hk, alm, als, altl, alt,
    alP⟩ := h
  exact ⟨spal, sp1, sp2, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot, oa, mln, mle, mlp,
    mlq, mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, stl, st, sa, ko, kml,
    kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi, wl, wct, wsc, wtl,
    wt, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs, alm, als, altl, alt,
    fun _ => ⟨sP, kP, wP, hpl, alP, fun _ => hk⟩⟩

/-- The tables, as the variant's contract gives them. -/
theorem spec_tabDP {ts : List FnTable} {s : State} (h : (decPSpec ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ (ts.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  decP_pre at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- The variant's public data: `PubD true`, the tables' functions at the same
addresses, and the same tables held at both tables' addresses. -/
theorem pubD_ofP {ts : List FnTable} {s₁ s₂ : State} (h : (decPSpec ts).pub s₁ s₂) :
    PubD true s₁ s₂ ∧ (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T)) := by
  have e : stackBytes true = 3487 + 1 := rfl
  unfold decPSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, g0, g1, g2, g3, g4, g5, g6, g7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  obtain ⟨hne, hw⟩ := List.append_inj hl (by simp [bytesAt_length, g4, g6])
  simp only [List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp [bytesAt_length, g4])
  have inj := fun {w : Nat} {x y : List (BitVec w)} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm,
    fun _ => ⟨a17.symm, a18.symm⟩, fun _ => hw.symm⟩,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g0.symm, g1.symm, g2.symm, g3.symm, g4.symm, g5.symm, g6.symm, g7.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm, a16.symm]

open VG.Proof.MdHashTable.RISCV64 (MVar tables fns3 Coh)

/-- The correctness of `vg_rsa_oaep_decrypt_precomputed`, against its
contract, for the tables of `vs`. -/
theorem codeP_correct {vs : List MVar} (hc : Coh vs) (s : State) (h : (decPSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (Impl.RsaOaep.RISCV64.Dec.decryptP (fns3 vs)) s t s' ∧ abiPreserved s s' ∧
      (decPSpec (tables vs)).post s s' := by
  have P : PreD true s := preD_ofP h
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofG hc P (spec_tabDP h)
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.w.l.ok w.w.l.ok w₁.w.l.fits w.w.l.fits w₁.w.l.hash w₁.w.l.len w₁.w.l.valid
    w.w.l.hash w.w.l.len w.w.l.valid P T TL w₁.w.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes true = 3487 + 1 := rfl
  unfold decPSpec
  rw [e]
  sig_post [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Abi.withTables, abi, argRegs, stackArgs_nineteen,
    List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

/-- Constant time: `code_constantTimeG` with the variant's contract's facts. -/
theorem codeP_constantTime {vs : List MVar} (hc : Coh vs) :
    ConstantTime isa (decPSpec (tables vs)).pre (decPSpec (tables vs)).pub
      (Impl.RsaOaep.RISCV64.Dec.decryptP (fns3 vs)) :=
  code_constantTimeG hc (fun h => ⟨preD_ofP h, spec_tabDP h⟩) pubD_ofP

/-! ## A state meeting the precondition -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.HashTable (putWs add8_toNat)

/-- The stack arguments of `decPSatState`: the key (`keyMem`'s), an empty
label, a 64-byte ciphertext, a working space of 2080 words, both tables at
`0x300000`, and `pre` at `0x4800`. -/
def decPArgs : List Nat :=
  [32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x4700, 0, 0x4100, 64, 0x20000, 2080, 0x300000, 0x300000,
    0x4800, 24]

/-- The memory of `decPSatState`: the stack arguments from `0x10000`, and the
key. -/
def decPMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000 i && Nat.blt i 0x10098 then
    BitVec.ofNat 8 (decPArgs.getD ((i - 0x10000) / 8) 0 / 256 ^ ((i - 0x10000) % 8))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the variant's precondition but for the tables: the key
`keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit primes at `0x4200`
and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def decPSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4200 | _ => 0
  sp := 0x10000
  mem := decPMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10000, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem decPSat_args : ∀ j < 19, stackArg decPSatState j = BitVec.ofNat 64 (decPArgs.getD j 0) := by decide

/-- Below the words `putWs` writes, a byte as before. -/
theorem putWs_byte {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)}, a.toNat < p.toNat →
    p.toNat + 8 * ws.length < 2 ^ 64 → putWs m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega_using [hp])
    simp only [putWs]
    rw [putWs_byte (by rw [h8]; omega_using [h]) (by rw [h8]; omega_using [hp])]
    have hne : ¬ (a - p).toNat < 64 / 8 := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [hp]
    simp only [Mem.writeW, Mem.write, hne, ↓reduceIte]

theorem decPSat_key (vs : List MVar) (w : MVar) :
    Spec.Rsa.privatePrecompute
      (Spec.Rsa.bytesAt (Proof.MdHashTable.RISCV64.withTable decPSatState vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (Proof.MdHashTable.RISCV64.withTable decPSatState vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (Proof.MdHashTable.RISCV64.withTable decPSatState vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (Proof.MdHashTable.RISCV64.withTable decPSatState vs w).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    have h2 : (Nat.ble 0x10000 a.toNat && Nat.blt a.toNat 0x10098) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    show putWs decPMem 0x300000 (Proof.MdHashTable.RISCV64.twL vs w) a = keyMem a
    rw [putWs_byte (by show a.toNat < 0x300000; omega_using [hk]) (Proof.MdHashTable.RISCV64.twL_room vs w)]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

/-- A state meeting the variant's contract, with both tables that of `w`, at
`0x300000`. -/
theorem decP_sat {vs : List MVar} {w : MVar} (hw : w ∈ vs)
    (hl : (Proof.MdHashTable.RISCV64.names vs).length < 2 ^ 32) : ∃ s, (decPSpec (tables vs)).pre s := by
  refine ⟨Proof.MdHashTable.RISCV64.withTable decPSatState vs w, ?_⟩
  have hA : ∀ j < 19, (stackArgAddr decPSatState j).toNat + 8 ≤ 0x300000 := by decide
  have hb : ∀ j < 19, stackArg (Proof.MdHashTable.RISCV64.withTable decPSatState vs w) j =
      BitVec.ofNat 64 (decPArgs.getD j 0) :=
    fun j hj => (Proof.MdHashTable.RISCV64.withTable_below _ _ _ (hA j hj)).trans (decPSat_args j hj)
  have e : stackArgAddr (Proof.MdHashTable.RISCV64.withTable decPSatState vs w) 0 = 0x10000 :=
    show stackArgAddr decPSatState 0 = _ by decide
  have e3488 : stackBytes true = 3487 + 1 := rfl
  unfold decPSpec
  rw [e3488]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide), hb 9 (by decide), hb 10 (by decide),
    hb 11 (by decide), hb 12 (by decide), hb 13 (by decide), hb 14 (by decide), hb 15 (by decide),
    hb 16 (by decide), hb 17 (by decide), hb 18 (by decide), decPArgs, e]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact decPSat_key vs w)
    | exact ⟨Proof.MdHashTable.RISCV64.tableOf w, List.mem_map_of_mem hw,
        Proof.MdHashTable.RISCV64.held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.HashTable.symsOf_distinct2 hl
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

end VG.Proof.RsaOaep.RISCV64.Dec
