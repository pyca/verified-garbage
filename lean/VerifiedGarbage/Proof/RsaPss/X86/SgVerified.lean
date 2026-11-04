module

public import VerifiedGarbage.Proof.RsaPss.X86.SgCall
public import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
public import VerifiedGarbage.Proof.MdHashTable.X86.Tables
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSpT
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# RSASSA-PSS signing on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/SgVerified.lean`), with the hash functions as
tables: the checks, then zeros or the encoding and the private-key
operation (`tail_vp`), for the hash function `h` of the table of `MdHash` at
the argument 22 and MGF1's `g` of the table of `Hash` at 23; the index of
`h` (the table's word 5, `idx_vp`) chooses that tail among those of `idxs`
(`body_vp`, by `Proof.RsaOaep.X86.byLen_vp`), whose code for the index is
that for `h`'s sizes (`Shape`). The body writes `esp` only through the frames
of its calls (`body_noSp`); with the frames around it (`wrap_ok`, `wrap_ct`)
and the result as the shared contract states it, for the variants `w` and
`wg` whose tables the arguments are (`held_entered`, `tabFacts_entered`):
`vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `vs` and MGF1's any of those of `gs`, is
verified (`sign_verified`), given a state that meets the contract
(`SgSat.lean`). Every stage keeps the addresses of the statics (`VP.syms`),
which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)
open VG.Impl.RsaOaep.X86 (Fns byLen)
open VG.Proof.RsaOaep.X86 (OHash TabFacts VP.syms byLen_vp byLen_noSp St_roW)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable (h : PssHash)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The checks, then zeros or the encoding and the private-key operation,
for the hash function `h` of the table at the argument 22 and MGF1's `g` of
that at 23. -/
theorem tail_vp (P : EP) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (v : CrtImpl) :
    VP (Sy (S h P)) (signTail f h.H fG (privName v) (privCode v)) (Fin h g.G P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk ++ params h.H)) (.ite .ne signFail (.seq (signEncT f h.H fG)
    (.seq (.block privArgs) (.call (privName v) (privCode v)))))) _
  exact (VP.syms (chk_vp h P)).seq (VP.ite
    (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.1.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((fail_vp h g.G P).mono (fun σ s ⟨⟨h1, _⟩, e⟩ => ⟨h1, e⟩) fun _ _ h => h)
    (((enc_vp h P hP hTH fneH g hT fne).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩)
      fun _ _ h => h.1).seq ((pa_vp h g.G P).seq (call_vp h g.G g.valid P v))))

/-- The index of the hash function of the table at the argument 22, to
`edx`. -/
theorem idx_vp (P : EP) {ix : Nat} (hix : ∀ σ, P.TH σ → σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix) :
    VP (Sy (S h P)) (.block (idxLoad 22)) (fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = BitVec.ofNat 32 ix) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.tblH5
  show VP _ (.block ([ld .edx (arg 22)] ++ [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 20))])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = P.tabH)
    (VP.taint [.esp] idxArg22_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] idxWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.sp, h₂.1.2.sp]
  · obtain ⟨⟨hi, hs⟩, sy⟩ := hs
    simp only [ld]
    refine hs.wp_arg (sg_arg h (j := 22) (by decide)) (by decide) fun t1 s1 u1 => WP.block_nil
      ⟨⟨⟨hi, s1⟩, u1.syms.trans sy⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.2.sp, h₂.1.1.2.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨⟨hi, hs⟩, sy⟩, hdx⟩ := hs
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabH 20) 4 := ⟨tR, hs.inRo tRo, tC⟩
    refine wp_ldm (B := P.tabH) hdx hin fun t2 u2 => WP.block_nil ⟨⟨⟨hi, hs.upd u2 (by decide)⟩, u2.syms.trans sy⟩, ?_⟩
    rw [u2.gpr, St_roW hs tRo tC, hix σ hi.tabTH]

/-- The tail for an index is that for the sizes of its hash function. -/
theorem tail_eq {i : Nat} {f : MdFns} {fG : Fns} {pn : String} {pc : Prog isa}
    (hs : sizes h.H = sizesOf i) : signTail f (ofIdx i) fG pn pc = signTail f h.H fG pn pc := by
  rw [show ofIdx i = ofSizes (sizes h.H) by rw [hs]; rfl]
  rfl

/-- The body, for the hash function `h` of index `ix` and MGF1's `g`. -/
theorem body_vp (P : EP) {dn : String} {f : MdFns} {ix : Nat} (hix₀ : ix ∈ idxs) (hs : sizes h.H = sizesOf ix)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ ∧
      σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (v : CrtImpl) :
    VP (Sy (S h P)) (signBodyT f fG (privName v) (privCode v)) (Fin h g.G P) := by
  have hlt : ix < 2 ^ 32 := (cmpIdxs_taint ix hix₀).1
  show VP _ (.seq (.block (idxLoad 22)) (byLen (fun i => signTail f (ofIdx i) fG (privName v) (privCode v)) idxs)) _
  refine (idx_vp h P fun σ hσ => (hTH σ hσ).2).seq (byLen_vp (D := ix) hlt (fun _ _ hs => hs.2)
    (fun σ s t ⟨⟨⟨hi, hs⟩, sy⟩, dx⟩ fu sy' => ⟨⟨⟨hi, hs.fupd fu⟩, sy'.trans sy⟩, by rw [fu.gpr]; exact dx⟩) ?_ hix₀
    cmpIdxs_taint)
  rw [tail_eq h hs]
  exact (tail_vp h P (fun σ hσ => (hTH σ hσ).1) fneH g hT fne v).mono (fun _ _ hs => hs.1) fun _ _ h => h

/-! ## The stack -/

theorem tail_noSp {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {fG : Fns} (gi : ∀ q ∈ fG.init, NoSp q.2) (gu : ∀ q ∈ fG.upd, NoSp q.2)
    (gf : ∀ q ∈ fG.fin, NoSp q.2) (v : CrtImpl) : NoSp (signTail f h.H fG (privName v) (privCode v)) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig16
  have p3 := sp.cpSalt
  have p4 := sp.lenArgs19
  have p5 := sp.putH
  have p6 := sp.mgfArgs
  have hct := ctHashT_noSp h hi hc hd (j := 22) (NoSp.of_all (by decide +kernel))
  have hm := Proof.RsaOaep.X86.mgfX_noSp gi gu gf (j := 23) (NoSp.of_all (by decide +kernel))
  have hp := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  simp only [signTail, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [signEncT, yDig, signFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

/-- `vs`' and `gs`' functions write `esp` only through their frames. -/
structure FnsSp (f : MdFns) (fG : Fns) : Prop where
  hi : ∀ q ∈ f.init, NoSp q.2
  hc : ∀ q ∈ f.comp, NoSp q.2
  hd : ∀ q ∈ f.dig, NoSp q.2
  gi : ∀ q ∈ fG.init, NoSp q.2
  gu : ∀ q ∈ fG.upd, NoSp q.2
  gf : ∀ q ∈ fG.fin, NoSp q.2

theorem body_noSp {f : MdFns} {fG : Fns} (hf : FnsSp f fG) (hall : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i)
    (v : CrtImpl) : NoSp (signBodyT f fG (privName v) (privCode v)) := by
  refine noSp_seq (NoSp.of_all (by decide +kernel)) (byLen_noSp fun i hi => ?_)
  obtain ⟨h', hs⟩ := hall i hi
  rw [tail_eq h' hs]
  exact tail_noSp h' hf.hi hf.hc hf.hd hf.gi hf.gu hf.gf v

/-! ## The entry -/

/-- What the registration checks of the variants `vs` of the tables of
`MdHash` and `gs` of `Hash`: the functions of one name have one code, each
hash function has the sizes of its index, each index has a variant, and few
enough functions for the contract's satisfiability. -/
def OK (vs : List MVar) (gs : List TVar) : Prop :=
  Proof.MdHashTable.X86.Coh vs ∧ (∀ w ∈ vs, Proof.MdHashTable.X86.Shape w) ∧ Proof.HashTable.X86.Coh gs ∧
    (∀ i ∈ idxs, ∃ w ∈ vs, Proof.MdHashTable.X86.idx w = i) ∧ gs ≠ [] ∧
    (Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs).length < 2 ^ 24

instance (vs : List MVar) (gs : List TVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

variable {vs : List MVar} {gs : List TVar}

/-- The code, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `vs` and MGF1's any of `gs`. -/
abbrev signCode (vs : List MVar) (gs : List TVar) (v : CrtImpl) : Prog isa :=
  sign (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) (privName v) (privCode v)

/-- The contract, with those tables. -/
abbrev sspec (vs : List MVar) (gs : List TVar) : Contract isa :=
  spec (Proof.MdHashTable.X86.tables vs) (Proof.HashTable.X86.tables gs)

theorem fnsSp (vs : List MVar) (gs : List TVar) :
    FnsSp (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) := by
  obtain ⟨gi, gu, gf⟩ := Proof.HashTable.X86.fnsOf_noSp gs
  refine ⟨?_, ?_, ?_, gi, gu, gf⟩ <;> simp only [Proof.MdHashTable.X86.fnsOf, List.mem_map] <;>
    rintro _ ⟨w, -, rfl⟩
  exacts [w.h.ok.hH.initSp, w.h.ok.comp.nosp, w.h.certs.digSp]

theorem hall_of (hok : OK vs gs) : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i := fun i hi => by
  obtain ⟨w, hw, rfl⟩ := hok.2.2.2.1 i hi
  exact ⟨w.h, (hok.2.1 w hw).2⟩

theorem code_noSp (hok : OK vs gs) (v : CrtImpl) : NoSp (signCode vs gs v) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp (fnsSp vs gs) (hall_of hok) v)) restore_noSp)

theorem code_sp (hok : OK vs gs) (v : CrtImpl) : (signCode vs gs v).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp hok v)

theorem spec_sp {s : State} (hs : (sspec vs gs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sign_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

theorem fne_of {w : MVar} (hw : w ∈ vs) {wg : TVar} (hwg : wg ∈ gs) :
    ((Proof.MdHashTable.X86.fnsOf vs).init ≠ [] ∧ (Proof.MdHashTable.X86.fnsOf vs).comp ≠ [] ∧
      (Proof.MdHashTable.X86.fnsOf vs).dig ≠ []) ∧
    ((Proof.HashTable.X86.fnsOf gs).init ≠ [] ∧ (Proof.HashTable.X86.fnsOf gs).upd ≠ [] ∧
      (Proof.HashTable.X86.fnsOf gs).fin ≠ []) := by
  have h1 := List.ne_nil_of_mem hw
  have h2 := List.ne_nil_of_mem hwg
  simp only [Proof.MdHashTable.X86.fnsOf, Proof.HashTable.X86.fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨⟨h1, h1, h1⟩, h2, h2, h2⟩

/-- What the entry state holds of the table of `MdHash` of `w` at `p`, with
its functions where `s'` has them. -/
abbrev THw (vs : List MVar) (w : MVar) (p : BitVec 32) (s' : State) (σ : State) : Prop :=
  HFacts w.h (Proof.MdHashTable.X86.digName w) (Proof.MdHashTable.X86.fnsOf vs) p (s'.syms w.h.H.st.initN)
      (s'.syms w.h.H.compN) (s'.syms (Proof.MdHashTable.X86.digName w)) σ ∧
    σ.mem.readW (VG.X86.addr p 20) 32 = BitVec.ofNat 32 (Proof.MdHashTable.X86.idx w)

/-- The public parameters for the table of `MdHash` of `w` and that of
`Hash` of `wg`, with their functions where `s'` has them. -/
abbrev epw (vs : List MVar) (gs : List TVar) (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep s (s'.syms w.h.H.st.initN) (s'.syms w.h.H.compN) (s'.syms (Proof.MdHashTable.X86.digName w))
    (THw vs w (arg s 22) s') (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (TabFacts wg.g.H (Proof.HashTable.X86.fnsOf gs) (arg s 23) (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN)
      (s'.syms wg.g.H.finN))

/-- The digest's length, from the hash function the table names. -/
theorem dlen_of {s : State} (hs : (sspec vs gs).pre s) {w : MVar}
    (hh : Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w))) :
    (arg s 17).toNat = w.h.D := by
  obtain ⟨-, -, -, hfitH, -, hdl⟩ := spec_tab hs
  have := hdl _ (Proof.MdHashTable.X86.hashAt_tableOf hfitH (Proof.MdHashTable.X86.held_tableOf hfitH hh).2.2.2)
  rw [this, w.h.glen]

/-- The entry state, for the tables of `w` at the argument 22 and `wg` at
23, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hok : OK vs gs) {s s' : State} (hs : (sspec vs gs).pre s) {w : MVar} {wg : TVar}
    (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hhH : Abi.tableHeld 32 s.mem ((arg s 22).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w)))
    (hh : Abi.tableHeld 32 s.mem ((arg s 23).setWidth 64) (FnTable.words isa s (Proof.HashTable.X86.tableOf wg)))
    (hsy : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s.syms n = s'.syms n) :
    Sy (S w.h (epw vs gs s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitH, hfit, -⟩ := spec_tab hs
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hD := dlen_of hs hhH
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 fun _ => True
  have ok := (in_of_pre (hai := 0) (hac := 0) (had := 0) (TH := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) hs trivial trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.MdHashTable.X86.mem_names hw
  have hng := Proof.HashTable.X86.mem_names hwg
  have hsyH : ∀ n ∈ Proof.MdHashTable.X86.names vs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_left _ h)
  have hsyG : ∀ n ∈ Proof.HashTable.X86.names gs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_right _ h)
  have tf := Proof.HashTable.X86.tabFacts_entered (argv := e0.argv (arg s 17).toNat) (ro := e0.ro (arg s 17).toNat)
    (rw := e0.rw) (C := 3448) hsp ok (p := arg s 23) (by simp [e0, ep]) hfit hok.2.2.1 hpwG hwg hh
  rw [hsyG _ hng.1, hsyG _ hng.2.1, hsyG _ hng.2.2] at tf
  have sy : (entered frameBytes s).syms = s.syms := pushRegs_syms s _
  obtain ⟨m0, m3, m4, m5⟩ := Proof.MdHashTable.X86.held_entered (argv := e0.argv (arg s 17).toNat)
    (ro := e0.ro (arg s 17).toNat) (rw := e0.rw) (C := 3448) hsp ok (p := arg s 22) (by simp [e0, ep]) hfitH hhH
  have hf := Proof.MdHashTable.X86.hfacts_of hok.1 (σ := entered frameBytes s) (by rw [sy]; exact hpwH) hw m0 m3 m4
  rw [sy, hsyH _ hn.1, hsyH _ hn.2.2.2.1, hsyH _ hn.2.2.2.2] at hf
  have hi := in_of_pre (hai := s'.syms w.h.H.st.initN) (hac := s'.syms w.h.H.compN)
    (had := s'.syms (Proof.MdHashTable.X86.digName w)) (TH := THw vs w (arg s 22) s')
    (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN) (af := s'.syms wg.g.H.finN) hs ⟨hf, m5⟩ tf
  rw [hD] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hok : OK vs gs) (v : CrtImpl) {s : State} (hs : (sspec vs gs).pre s) :
    WP isa (signCode vs gs v) s fun t => abiPreserved s t ∧ (sspec vs gs).post s t := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨T, hT, hh⟩, -, hfitH, hfit, -⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  have hidxH := (Proof.MdHashTable.X86.held_tableOf hfitH hhH).2.2.2
  have hidx := (Proof.HashTable.X86.held_tableOf hfit hh).2.1
  have he := entered_state hok hs hw hwg hhH hh (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  obtain ⟨fneH, fne⟩ := fne_of hw hwg
  have hb := (body_vp w.h (epw vs gs s s w wg) (hok.2.1 w hw).1 (hok.2.1 w hw).2 (fun _ x => x) fneH wg.g
    (fun _ x => x) fne v).wp _ _ he
  have hD := dlen_of hs hhH
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp (fnsSp vs gs) (hall_of hok) v) hsp hfit4
    (W := ((epw vs gs s s w wg).lay w.h.D).W)
    (Q := fun r m => Res w.h wg.g.G (epw vs gs s s w wg) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok hr
    rw [save_eq (argv := (epw vs gs s s w wg).argv (arg s 17).toNat) (ro := (epw vs gs s s w wg).ro (arg s 17).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 3448) hsp,
      ret_eq (argv := (epw vs gs s s w wg).argv (arg s 17).toNat) (ro := (epw vs gs s s w wg).ro (arg s 17).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 3448) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw vs gs s s w wg).ro (arg s 17).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal, argBytes]
    intro H G hH hG
    rw [Proof.MdHashTable.X86.hashAt_tableOf hfitH hidxH, Option.some.injEq] at hH
    rw [Proof.HashTable.X86.hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    rw [show pB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).PP) (by simp),
      show qB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).QQ) (by simp),
      show dpB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).DP) (by simp),
      show dqB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).DQ) (by simp),
      show qiB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).QI) (by simp),
      show saltB (epw vs gs s s w wg) (entered frameBytes s) = _ from ro (R := (epw vs gs s s w wg).SALT) (by simp)]
      at res
    have hdg : digB w.h (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 16).setWidth 64) (arg s 17).toNat := by
      unfold digB; rw [← hD]; exact ro (R := (epw vs gs s s w wg).DIG (arg s 17).toNat) (by simp)
    rw [hdg, hD] at res
    rw [BitVec.setWidth_append_eq_right, w.h.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hok : OK vs gs) (v : CrtImpl) : ConstantTime isa (sspec vs gs).pre (sspec vs gs).pub (signCode vs gs v) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨T, hT, hh₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
    Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argSlots, argVal,
    argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabH, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23⟩ := hp
  have hhH₂ := (htabH _ _ rfl rfl _ hTH).mp hhH₁
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s₂.syms n = s₁.syms n :=
    fun n hn => (hsy n (by simpa [Proof.MdHashTable.X86.names, Proof.HashTable.X86.names] using hn)).symm
  have hep : epw vs gs s₁ s₁ w wg = epw vs gs s₂ s₁ w wg := by
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hl) (by simp [RsaPkcs1Sig.bytesAt_len, a3])
    simp only [ep]
    rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a12, a14, a16, a18, a19, a20, a21, a22, a23]
    rw [a2, a3] at hn
    rw [a4, a5] at he
    rw [hn, he]
  have hD₁ := dlen_of h₁ hhH₁
  obtain ⟨fneH, fne⟩ := fne_of hw hwg
  refine (wrap_ct (F := frameBytes) (body_noSp (fnsSp vs gs) (hall_of hok) v) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w.h (epw vs gs s₁ s₁ w wg) (hok.2.1 w hw).1 (hok.2.1 w hw).2 (fun _ x => x) fneH wg.g
    (fun _ x => x) fne v).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hok h₁ hw hwg hhH₁ hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hok h₂ hw hwg hhH₂ hh₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the
hash function any of the tables of `vs` and MGF1's any of `gs`, meets the
shared contract (satisfiable, `SgSat.lean`). -/
theorem sign_verified (hok : OK vs gs) (hsat : ∃ s, (sspec vs gs).pre s) (v : CrtImpl) :
    Verified target (signCode vs gs v) (sspec vs gs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hok v hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hok v, hsat⟩

end VG.Proof.RsaPss.X86.Sg
