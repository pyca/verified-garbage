module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Main
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Unmask
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Out
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
public import VerifiedGarbage.Proof.HashTable.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# RSAES-OAEP decryption on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The entry, the private
operation (`priv_ok`), the check of `k ≥ 2 hLen + 2` (public), then either
zeros and the result `r = 2 ? 2 : 0` (`decFail_ok`, which is what `decOut`
says for a too short `k`) or the decoding (`decMain_ok`), and the restores:
RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2), with MGF1's hash function the
table's. `code_correct`: the function against its contract, for the tables
of `vs` (`tab_ofD`: the table is one of them, whose hash function it
names).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_sub wp_lsr wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes)
open VG.Proof.RsaOaep (decOut decOut_short)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf Coh)

/-- The result and the outputs, from the entry state `s`. -/
def Post (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((s'.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

/-- Before the restores. -/
def Done (Hs Gs : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ Spec.RsaOaep.writtenDecrypt t.mem (s.gpr .r3) (s.gpr .r5) (kk s) ((t.gpr .r3).setWidth 32)
    (decOut Hs Gs (labB s) (privO s))

theorem AfterPriv.only {s v v' : State} {rs : List Reg} (A : AfterPriv s v) (P : PreD s) (o : Only rs v v')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : AfterPriv s v' := by
  have hm : v'.mem = v.mem := o.mem
  have b := A.base
  rw [← hm] at b
  exact ⟨b.only (fitsM P) o hrs, hm ▸ A.mem, hm ▸ A.em⟩

/-- The tail for a digest length, which is all it uses of the hash
function's shape. -/
theorem decTail_D {G G' : Hash} (hD : G.D = G'.D) (f : Fns) : decTail G f = decTail G' f := by
  simp only [Dec.decTail, Dec.decMain, Dec.chkK, Dec.accLh, Dec.scan, Dec.tArgs, Dec.copyT, Dec.decRet, seedArgs,
    dbArgs, hD]

/-- `EM` too short for the hash: what decryption returns, from the private
operation's result. -/
theorem decOut_short' {Hs Gs : Spec.Mgf1.Hash} {lab : List Byte} {o : Spec.Rsa.Outcome} {k : Nat}
    (hl : ∀ em, o = .ok em → em.length = k) (hk : k < 2 * Hs.len + 2) :
    decOut Hs Gs lab o = if rcOf o = 2 then .fault else .invalid := by
  rw [decOut_short hl hk]
  cases o <;> rfl

section
variable {H G : Hash} (hH : HashOK H) (hG : HashOK G) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
  {f : Fns} {s : State} (P : PreD s) (T : TabS G f 16 (SD s) s (stackArg s 16))
  (TL : TabS H f 15 (SD s) s (stackArg s 15))
include hH hG hHh hHl hHv hGh hGl hGv P T TL

omit hH hG hHh hHv hGh hGl hGv T TL in
theorem fail_done {v : State} (A : AfterPriv s v) (hk : kk s < 2 * H.D + 2) :
    WP isa decFail v (Done Hs Gs s) := by
  have hrc := rcOf_le (privO s)
  refine WP.mono (decFail_ok P A.base hrc) fun u ⟨sv, _, hm, h3⟩ => ⟨sv, ?_⟩
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have hl : ∀ em, privO s = .ok em → em.length = kk s := fun em he => by
    have := A.em; rw [he] at this; simp only [emOf] at this; rw [← this, bytesAt_length]
  rw [decOut_short' hl (by rw [hHl]; exact hk)]
  have hout : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
    have e := bytesAt_writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)
      (by rw [List.length_replicate]; omega)
    rw [List.length_replicate] at e
    rw [← e, hm]
    have f : Frame [mlR s] (writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0))
        ((writeBytes v.mem (s.gpr .r3) (List.replicate (kk s) 0)).writeW (s.gpr .r5) (0#64)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact f _ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc => P.oml _ (Offset.contains_base _ (by have := P.ok; omega) (by omega)) hc)
  have hml : u.mem.readW (s.gpr .r5) 64 = 0 := by rw [hm, Mem.readW_writeW_self64]; rfl
  have hrc2 := rcOf_le (privO s)
  by_cases h2 : rcOf (privO s) = 2
  · rw [ifp h2]; exact ⟨by rw [h3, ifp h2]; decide, hout, hml⟩
  · rw [ifn h2]; exact ⟨by rw [h3, ifn h2]; decide, hout, hml⟩

omit hH hG hHh hHl hHv hGh hGl hGv T TL in
/-- The check of `k`: in `r3`, whether it is too short. -/
theorem chk_ok (hD64 : H.D ≤ 64) {v : State} (A : AfterPriv s v) :
    WP isa (.block (Dec.chkK H)) v fun v' => AfterPriv s v' ∧ (v'.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2) := by
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have e7 : s.gpr .r7 = BitVec.ofNat 64 (kk s) := ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  refine wp_li (by omega) fun v₁ o₁ e₁ => wp_sub fun v₂ o₂ e₂ => wp_lsr fun v₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.r3] v v₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨A.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, o₁.get .r15, Base.r15 A.base, e7]
  exact ne_zero_ltBit (by omega) (by omega)

/-- The branch on the check of `k`. -/
theorem ite_done {v : State} (A : AfterPriv s v) (hsy : v.syms = s.syms)
    (r3 : (v.gpr .r3 != 0) = decide (kk s < 2 * H.D + 2)) :
    WP isa (.ite (.nonzero .d .r3) decFail (decMain H f)) v (Done Hs Gs s) :=
  WP.ite _ (eval_nonzero _ _) (fun hc => fail_done hHl P A (by rw [r3] at hc; simpa using hc))
    (fun hc => WP.mono (decMain_ok P hH hG hHh hHl hHv hGh hGl hGv T TL A hsy (by rw [r3] at hc; simp at hc; omega))
      fun u ⟨sv, _, hw⟩ => ⟨sv, hw⟩)

theorem checks_done {v : State} (A : AfterPriv s v) (hsy : v.syms = s.syms) :
    WP isa (.block (Dec.chkK H)) v fun v' =>
      WP isa (.ite (.nonzero .d .r3) decFail (decMain H f)) v' (Done Hs Gs s) :=
  WP.mono_syms (chk_ok P hH.hD64 A) fun _ ⟨A', r3⟩ y => ite_done hH hG hHh hHl hHv hGh hGl hGv P T TL A' (y.trans hsy) r3

theorem code_ok (hl : H.D ∈ lens) : WP isa (decrypt f) s (Post Hs Gs s) := by
  have hD64 := hH.hD64
  refine WP.alloc (by decide) (by have := P.sp1; rw [stackBytes_eq] at this; unfold frameBytes; omega) ?_
  refine WP.seq (WP.mono_syms (entry_ok P) fun t E y₁ => ?_)
  refine WP.seq (WP.mono_syms (priv_ok P E) fun v A y₂ => ?_)
  -- The label's hash function's digest length to `r3`.
  have TL' := tabS_wmL P TL A.mem
  refine WP.seq (WP.of_syms ?_)
  show WP isa (.block (tword .r3 15 4 ++ [])) v _
  refine wp_tword TL' A.base (k := 4) (by decide) (d := .r3) (by decide) fun v₁ o₁ e₁ => wp_nil fun y₃ => ?_
  have e3 : v₁.gpr .r3 = BitVec.ofNat 64 H.D := e₁.trans TL'.d
  -- The code for that length.
  refine WP.seq (byLen_ok (D := H.D) (by omega)
    (F := fun u => AfterPriv s u ∧ u.syms = s.syms ∧ u.gpr .r3 = BitVec.ofNat 64 H.D)
    (fun _ h => h.2.2) (fun u u' ⟨A', y', r3'⟩ o y => ⟨A'.only P o, y.trans y', by rw [o.get .r3]; exact r3'⟩) ?_
    hl (fun x hx => (lens_certs x hx).1) v₁ ⟨A.only P o₁, y₃.trans (y₂.trans y₁), e3⟩)
  intro u ⟨A', y', _⟩
  rw [decTail_D (G := ofLen H.D) (G' := H) rfl]
  exact WP.seq (WP.mono (checks_done hH hG hHh hHl hHv hGh hGl hGv P T TL A' y') fun v' h => WP.mono h
    fun t' ⟨sv, res⟩ => WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, by
      rw [freed_mem, freed_gpr, hm, h3]; exact res⟩)

end

/-- The label's hash function's table, on entry, if it is `w`'s: what its
calls need of it. -/
theorem tabS_entryDL {vs : List TVar} (hc : Coh vs) {s : State} (P : PreD s)
    (hpw : (Proof.HashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (Proof.HashTable.PPC64LE.tableOf w))) :
    TabS w.H (fnsOf vs) 15 (SD s) s (stackArg s 15) := by
  refine Proof.HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
    (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 9 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) (P.ktl.sub_left kR_sub)
    (P.stl.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

/-- MGF1's table, on entry, if it is `w`'s: what MGF1 needs of it. -/
theorem tabS_entryD {vs : List TVar} (hc : Coh vs) {s : State} (P : PreD s)
    (hpw : (Proof.HashTable.PPC64LE.names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) {w : TVar}
    (hw : w ∈ vs)
    (hh : Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s (Proof.HashTable.PPC64LE.tableOf w))) :
    TabS w.H (fnsOf vs) 16 (SD s) s (stackArg s 16) := by
  refine Proof.HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
    (in_aR (by decide)) ?_ (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
    (by rw [P.hrd]; iterate 10 apply List.mem_cons_of_mem
        exact List.mem_cons_self ..) (P.kt.sub_left kR_sub)
    (P.st.sub_left (sc_sub P)) hc hpw hw hh
  rw [stackArgAddr_eq]
  exact Offset.sub_base _ (by omega)

/-- The tables, on entry: each one of the tables of `vs`, which names its
hash function and holds what the calls through it need. -/
theorem tab_ofD {vs : List TVar} (hc : Coh vs) {s : State} (h : (decSpec (tables vs)).pre s) :
    ∃ w₁ ∈ vs, ∃ w ∈ vs, Spec.HashTable.hashAt 64 s.mem (stackArg s 15) = some w₁.l.G ∧
      Spec.HashTable.hashAt 64 s.mem (stackArg s 16) = some w.l.G ∧
      TabS w₁.H (fnsOf vs) 15 (SD s) s (stackArg s 15) ∧ TabS w.H (fnsOf vs) 16 (SD s) s (stackArg s 16) := by
  obtain ⟨⟨T₁, hT₁, hh₁⟩, ⟨T, hT, hh⟩, hpw⟩ := spec_tabD h
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  have hpw' := hpw.sublist (List.sublist_append_left _ _)
  have P := preD_of h
  exact ⟨w₁, hw₁, w, hw, Proof.HashTable.PPC64LE.hashAt_tableOf (Proof.HashTable.PPC64LE.held_tableOf hh₁).2.1,
    Proof.HashTable.PPC64LE.hashAt_tableOf (Proof.HashTable.PPC64LE.held_tableOf hh).2.1,
    tabS_entryDL hc P hpw' hw₁ hh₁, tabS_entryD hc P hpw' hw hh⟩

/-- The correctness of `vg_rsa_oaep_decrypt`, against its contract, for the
tables of `vs`. -/
theorem code_correct {vs : List TVar} (hc : Coh vs) (s : State) (h : (decSpec (tables vs)).pre s) :
    ∃ t s', Exec isa (decrypt (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (decSpec (tables vs)).post s s' := by
  obtain ⟨w₁, -, w, -, hH, hG, TL, T⟩ := tab_ofD hc h
  have P : PreD s := preD_of h
  obtain ⟨t, s', he, habi, hr⟩ := code_ok w₁.l.ok w.l.ok w₁.l.hash w₁.l.len w₁.l.valid w.l.hash w.l.len w.l.valid
    P T TL w₁.l.lens_mem
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3775 + 1 := rfl
  unfold decSpec
  rw [e]
  sig_post [Spec.RsaOaep.decryptTablesContract, Spec.RsaOaep.decryptTablesSig, Spec.RsaOaep.decryptSig,
    Spec.HashTable.param, Abi.withTables, abi, argRegs, stackArgs_seventeen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [Proof.RsaOaep.decrypt_eq (by rw [bytesAt_length, bytesAt_length])]
  exact hr

end VG.Proof.RsaOaep.PPC64LE.Dec
