module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTBase
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTMain
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP decryption on PPC64LE: `vg_rsa_oaep_decrypt_precomputed`

Untrusted: everything here is checked by Lean. `decryptP`, the code of
`vg_rsa_oaep_decrypt` calling `vg_rsa_private_checked_precomputed`
(`decryptG true`), against `Spec.RsaOaep.decryptPrecomputedMdTablesContract`:
its precondition gives `PreD true` and `PreXD` (`preDP_of`), its public data
`PubD` and `PubP` (`pubDP_of`), and the proofs shared with
`vg_rsa_oaep_decrypt` (`code_ok`, `code_ct`) the rest. A state meeting the
precondition holds a real key (`decP_sat`, `Rsa.PreKey`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.MdHashTable.PPC64LE (MVar tables fns3 Coh)
open VG.Proof.Rsa.PreKey
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

theorem stackArgs_nineteen (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17,
      stackArg s 18] := rfl

/-- The precomputed contract, with both hash functions each one of the
tables `ts`, and the stack of the frames and of
`vg_rsa_private_checked_precomputed`. -/
abbrev decSpecP (ts : List FnTable) : Contract isa :=
  Spec.RsaOaep.decryptPrecomputedMdTablesContract
    (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stackBytes

/-- Unfolds the precomputed precondition at `h`. -/
macro "dec_preP" " at " h:ident : tactic => `(tactic| (
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpecP at $h:ident
  rw [e] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at $h:ident
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at $h:ident
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', Sig.pairFacts, List.filterMap_cons, List.filterMap_nil,
    Bool.cond_true, Bool.cond_false, Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil] at $h:ident))

theorem preDP_of {ts : List FnTable} {s : State} (h : (decSpecP ts).pre s) : PreD true s ∧ PreXD s := by
  dec_preP at h
  obtain ⟨sp1, sp2, -, -, -, hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, oP, otl, ot, oa, mln, mle, mlp,
    mlq, mldp, mldq, mlqi, mll, mlct, mls, mlP, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts, sP, stl, st,
    sa, ko, kml, kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, kP, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq, wqi,
    wl, wct, wsc, wP, wtl, wt, ⟨k1, k2⟩, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs, hpl, hyp⟩ := h
  exact ⟨⟨sp1, by simp only [↓reduceIte]; omega_using [sp2], hrd, hwr, oml, on, oe, op, oq, odp, odq, oqi, ol, oct, os, otl, ot,
    oa, mln, mle, mlp, mlq, mldp, mldq, mlqi, mll, mlct, mls, mltl, mlt, mla, ns, es, ps, qs, dps, dqs, qis, ls, cts,
    stl, st, sa, ko, kml, kn, ke, kp, kq, kdp, kdq, kqi, kl, kct, ks, ktl, kt, ka, wo, wml, wn, we, wp, wq, wdp, wdq,
    wqi, wl, wct, wsc, wtl, wt, k1, k2, ok, oc, e1, e2, p1, p2, q1, q2, h4, h8, h6, hs⟩,
    ⟨oP, mlP, sP, kP, wP, hpl, hyp⟩⟩

/-- The tables, as the contract gives them. -/
theorem spec_tabDP {ts : List FnTable} {s : State} (h : (decSpecP ts).pre s) :
    (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s T)) ∧
      (∃ T ∈ ts, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      ((ts.map (fun T : FnTable => T.fns)).flatten ++ (ts.map (fun T : FnTable => T.fns)).flatten).Pairwise
        (fun f g => f ≠ g → s.syms f ≠ s.syms g) := by
  dec_preP at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function and holds what the calls through it need. -/
theorem tab_ofDP {vs : List MVar} (hc : Coh vs) {s : State} (h : (decSpecP (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.l.G ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some w.l.G ∧
      TabS w₁.H (fns3 vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.H (fns3 vs) 16 (SD s) s (stackArg s 16) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tabDP h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  have P := (preDP_of h).1
  exact ⟨w₁, hw₁, w, hw, Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh₁).2.2.2,
    Proof.MdHashTable.PPC64LE.hashAt_tableOf (Proof.MdHashTable.PPC64LE.held_tableOf hh).2.2.2,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

/-- The correctness of `vg_rsa_oaep_decrypt_precomputed`, against its
contract, for the tables of `vs`. -/
theorem code_correctP {vs : List MVar} (hc : Coh vs) (s : State) (h : (decSpecP (tables vs)).pre s) :
    ∃ t s', Exec isa (decryptP (fns3 vs)) s t s' ∧ abiPreserved s s' ∧ (decSpecP (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofDP hc h
  obtain ⟨P, X⟩ := preDP_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    P T TL (fun _ => X) w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpecP
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

/-- The contract's public data: `PubD`, `pre`'s (`PubP`), the tables'
functions at the same addresses, and the same tables held at both tables'
addresses. -/
theorem pubDP_of {ts : List FnTable} {s₁ s₂ : State} (h : (decSpecP ts).pub s₁ s₂) :
    PubD s₁ s₂ ∧ PubP s₁ s₂ ∧ (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 15) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 15) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 3791 + 1 := rfl
  unfold decSpecP at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htabL, htab, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  obtain ⟨hne, hlk⟩ := List.append_inj hl (by simp [bytesAt_length, h7, h9])
  simp only [List.map_append] at hne
  obtain ⟨hn, he⟩ := List.append_inj hne (by simp [bytesAt_length, h7])
  have inj := fun {x y : List Byte} (h : x.map (·.toNat) = y.map (·.toNat)) =>
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, (inj hn).symm, (inj he).symm⟩,
    ⟨a17.symm, a18.symm, hlk.symm⟩,
    fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htabL _ _ rfl rfl T hT,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm, h10.symm]
  · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm, a13.symm, a14.symm, a15.symm, a16.symm]

theorem pubP_refl (s : State) : PubP s s := ⟨rfl, rfl, rfl⟩

theorem code_constantTimeP {vs : List MVar} (hc : Coh vs) :
    ConstantTime isa (decSpecP (tables vs)).pre (decSpecP (tables vs)).pub (decryptP (fns3 vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, hpw₁⟩ := spec_tabDP h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, q, hsy, hiffL, hiff⟩ := pubDP_of hp
  have hhL₂ := (hiffL _ hT₁).mp hhL₁
  have hh₂ := (hiff _ hT).mp hh₁
  have q₁ := hpw₁.sublist (List.sublist_append_left _ _)
  have q₂ := (spec_tabDP h₂).2.2.sublist (List.sublist_append_left _ _)
  have hn := Proof.MdHashTable.PPC64LE.mem_names hw
  have hnL := Proof.MdHashTable.PPC64LE.mem_names hw₁
  obtain ⟨P₁, X₁⟩ := preDP_of h₁
  obtain ⟨P₂, X₂⟩ := preDP_of h₂
  exact code_ct w₁.l.ok w₁.l.ct w.l.ok w.l.ct w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    true w₁.l.lens_mem _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entryD hc P₁ q₁ hw hh₁, tabS_entryDL hc P₁ q₁ hw₁ hhL₁⟩, ⟨pubD_refl s₁, ⟨rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩, fun _ => ⟨X₁, pubP_refl s₁⟩⟩,
      ⟨⟨P₂, tabS_entryD hc P₂ q₂ hw hh₂, tabS_entryDL hc P₂ q₂ hw₁ hhL₂⟩, ⟨p,
        ⟨(hsy _ hn.1).symm, (hsy _ hn.2.1).symm, (hsy _ hn.2.2.1).symm⟩,
        ⟨(hsy _ hnL.1).symm, (hsy _ hnL.2.1).symm, (hsy _ hnL.2.2.1).symm⟩⟩, fun _ => ⟨X₂, q⟩⟩⟩ e₁ e₂

/-- `vg_rsa_oaep_decrypt_precomputed` against its contract, for the tables
of `vs`, given a state meeting it. -/
theorem decP_verified {vs : List MVar} (hc : Coh vs) (hsat : ∃ s, (decSpecP (tables vs)).pre s) :
    Verified PPC64LE.target (decryptP (fns3 vs)) (decSpecP (tables vs)) :=
  ⟨code_correctP hc, code_constantTimeP hc, hsat⟩

/-! ## A state meeting the precondition

`n`, `p` and `q` and the precomputed values at `keyMem`'s addresses (`n` of
64 octets at `0x2000`, `p` and `q` of 32 at `0x4200` and `0x4300`, `pre` of
24 words at `0x4800`); `out` at `0x1000`, `msg_len` at `0x1800`, `e` (one
octet) at `0x3000`, the ciphertext at `0x4100`, `dp`, `dq` and `qinv` at
`0x4400`–`0x4600`, an empty label at `0x4700`, a working space of 2080
words at `0x20000`, the stack arguments at `sp + 96`, and both tables'
address `0x300000`. -/

/-- The stack arguments that are not zero, by their bytes. -/
def argMemP (i : Nat) : Byte :=
  bif Nat.beq i 0x10060 then 0x20
  else bif Nat.beq i 0x10069 then 0x43 else bif Nat.beq i 0x10070 then 0x20
  else bif Nat.beq i 0x10079 then 0x44 else bif Nat.beq i 0x10080 then 0x20
  else bif Nat.beq i 0x10089 then 0x45 else bif Nat.beq i 0x10090 then 0x20
  else bif Nat.beq i 0x10099 then 0x46 else bif Nat.beq i 0x100A0 then 0x20
  else bif Nat.beq i 0x100A9 then 0x47 else bif Nat.beq i 0x100B9 then 0x41
  else bif Nat.beq i 0x100C0 then 64 else bif Nat.beq i 0x100CA then 0x02
  else bif Nat.beq i 0x100D0 then 0x20 else bif Nat.beq i 0x100D1 then 0x08
  else bif Nat.beq i 0x100DA then 0x30 else bif Nat.beq i 0x100E2 then 0x30
  else bif Nat.beq i 0x100E9 then 0x48 else bif Nat.beq i 0x100F0 then 24 else 0

def decSatStateP : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1800 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4200 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif keyIn a.toNat then keyMem a else argMemP a.toNat
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 88⟩, ⟨0x300000, 88⟩, ⟨0x10060, 152⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

/-- `putWs` leaves the bytes below where it writes. -/
theorem putWs_below {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    a.toNat < p.toNat → p.toNat + 8 * ws.length < 2 ^ 64 → Proof.HashTable.putWs m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    have h8 := Proof.HashTable.add8_toNat (p := p) (by omega_using [hp])
    show Proof.HashTable.putWs (m.writeW p w) (p + 8) ws a = m a
    rw [putWs_below (by omega_using [h, h8]) (by omega_using [hp, h8])]
    refine Mem.write_apply ?_
    rw [BitVec.toNat_sub]
    have := a.isLt
    omega_using [h, hp]

section
variable {vs : List MVar} {w : MVar}

theorem satP_key {a : Addr} (h : keyIn a.toNat = true) :
    (Proof.MdHashTable.PPC64LE.withTable decSatStateP vs w).mem a = keyMem a := by
  have hb : a.toNat < 0x48C0 := by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h; omega
  show Proof.HashTable.putWs decSatStateP.mem 0x300000 (Proof.MdHashTable.PPC64LE.twL vs w) a = _
  rw [putWs_below (by show a.toNat < 0x300000; omega_using [hb]) (Proof.MdHashTable.PPC64LE.twL_room vs w)]
  show (bif keyIn a.toNat then keyMem a else argMemP a.toNat) = keyMem a
  rw [h]
  exact Bool.cond_true

theorem stackArgAddr_dsatP (j : Nat) (hj : j < 19) : (stackArgAddr decSatStateP j).toNat + 8 ≤ 0x300000 := by
  revert j; decide

theorem stackArg_dsatP {j : Nat} {v : Addr} (hj : j < 19) (e : stackArg decSatStateP j = v) :
    stackArg (Proof.MdHashTable.PPC64LE.withTable decSatStateP vs w) j = v :=
  (Proof.MdHashTable.PPC64LE.withTable_below _ _ _ (stackArgAddr_dsatP j hj)).trans e

/-- The stack arguments of `decSatStateP`. -/
def satArgsP (j : Nat) : BitVec 64 :=
  bif Nat.beq j 1 then 0x4300 else bif Nat.beq j 3 then 0x4400 else bif Nat.beq j 5 then 0x4500
  else bif Nat.beq j 7 then 0x4600 else bif Nat.beq j 9 then 0x4700 else bif Nat.beq j 10 then 0
  else bif Nat.beq j 11 then 0x4100 else bif Nat.beq j 12 then 64 else bif Nat.beq j 13 then 0x20000
  else bif Nat.beq j 14 then 2080 else bif Nat.beq j 15 then 0x300000 else bif Nat.beq j 16 then 0x300000
  else bif Nat.beq j 17 then 0x4800 else bif Nat.beq j 18 then 24 else 32

theorem dsatP_args : ∀ j < 19, stackArg decSatStateP j = satArgsP j := by decide

omit vs w in
/-- The precondition, from the facts of a state. -/
theorem pre_of_factsP {vs : List MVar} {s : State} (hg : s.gpr = decSatStateP.gpr) (hsp : s.sp = 0x10000)
    (ha : ∀ j < 19, stackArg s j = satArgsP j) (hrd : s.rd = decSatStateP.rd) (hwr : s.wr = decSatStateP.wr)
    (ht : ∃ T ∈ tables vs, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hsy : (((tables vs).map (fun T : FnTable => T.fns)).flatten ++
      ((tables vs).map (fun T : FnTable => T.fns)).flatten).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g))
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (decSpecP (tables vs)).pre s := by
  have e : stackArgAddr s 0 = 0x10060 := by simp only [stackArgAddr, hsp]; rfl
  have e3792 : stackBytes = 3791 + 1 := rfl
  unfold decSpecP
  rw [e3792]
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, stackArgs_nineteen, List.append_eq,
    List.range, List.range.loop]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', ha 0 (by decide), ha 1 (by decide), ha 2 (by decide),
    ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide),
    ha 9 (by decide), ha 10 (by decide), ha 11 (by decide), ha 12 (by decide), ha 13 (by decide),
    ha 14 (by decide), ha 15 (by decide), ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), e, hg, hsp, hrd,
    hwr, satArgsP, decSatStateP]
  simp only [Nat.beq, Bool.cond_false, Bool.cond_true]
  sig_and_intros
  all_goals first
    | exact hk
    | exact ht
    | exact hsy
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (unfold Spec.Rsa.lenValid; decide)
    | (unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords; decide)

/-- A state meeting the contract, with both tables that of `w`, at
`0x300000`. -/
theorem decP_sat (hw : w ∈ vs) (hl : (Proof.MdHashTable.PPC64LE.names vs).length < 2 ^ 32) :
    ∃ s, (decSpecP (tables vs)).pre s :=
  ⟨Proof.MdHashTable.PPC64LE.withTable decSatStateP vs w, pre_of_factsP rfl rfl
    (fun j hj => stackArg_dsatP hj (dsatP_args j hj)) rfl rfl
    ⟨Proof.MdHashTable.PPC64LE.tableOf w, List.mem_map_of_mem hw, Proof.MdHashTable.PPC64LE.held_twL _ _ _ rfl⟩
    (Proof.HashTable.symsOf_distinct2 hl) (key_pre_of fun _ ha => satP_key ha)⟩

end

end VG.Proof.RsaOaep.PPC64LE.Dec
