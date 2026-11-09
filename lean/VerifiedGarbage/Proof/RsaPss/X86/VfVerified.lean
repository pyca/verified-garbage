module

public import VerifiedGarbage.Proof.RsaPss.X86.VfMain
public import VerifiedGarbage.Proof.RsaPss.X86.SgVerified
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSpT
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# RSASSA-PSS verification with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/VfVerified.lean`), with the hash functions as
tables, as for signing (`SgVerified.lean`): the index of the hash function
of the table of `MdHash` at the argument 14 (`idx_vp`) chooses the tail for
it among those of `idxs` (`byLen_vq`, `body_vq'`), whose code for the index
is that for its sizes, with MGF1's of the table of `Hash` at 15. The body
writes `esp` only through the frames of its calls (`body_noSp`); with the
frames around it (`wrap_ok`, `wrap_ct`) and the result as the shared
contract states it: `vg_rsa_pss_verify_precomputed`, calling a precomputed
public operation `c`, with the hash function any of the tables of `vs` and
MGF1's any of `gs`, is verified (`verify_verified`), given a state that meets
the contract (`VfSat.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Vf

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Impl.RsaOaep.X86 (Fns byLen)
open VG.Proof.RsaOaep.X86 (OHash TabFacts VP.syms St_roW)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable (h : PssHash)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

theorem VQ.mono_pre {F F' G : State → State → Prop} {c : Prog isa} (hq : VQ F c G) (hF : ∀ σ s, F' σ s → F σ s) :
    VQ F' c G :=
  ⟨fun σ s hs => hq.1 σ s (hF σ s hs),
    hq.2.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, hF _ _ h₁, hF _ _ h₂⟩) fun _ _ h => h⟩

/-- `byLen` from stages with the index `D` in `edx`, which a `cmp` keeps:
the branch of `D`, at the end of the body. -/
theorem byLen_vq {F G : State → State → Prop} {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 32)
    (h16 : ∀ σ s, F σ s → s.gpr .edx = BitVec.ofNat 32 D)
    (hst : ∀ σ s t, F σ s → Fupd s t → t.syms = s.syms → F σ t)
    (hb : VQ F (b D) G) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x < 2 ^ 32 ∧
      TaintOk [] (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 x))])) → VQ F (byLen b ds) G
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, htx⟩ := hx x (List.mem_cons_self ..)
    refine VQ.seq (G := fun σ s => F σ s ∧ isa.eval .e s = some (decide (D = x)))
      (VP.taint [] htx (fun _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) fun σ s hs =>
        WP.mono_syms (Q := fun t => Fupd s t ∧ t.zf = some (s.gpr .edx - BitVec.ofNat 32 x == 0))
          (wp_cmpi fun t f _ z => WP.block_nil ⟨f, z⟩) fun t ⟨f, z⟩ sy => ⟨hst σ s t hs f sy, ?_⟩) ?_
    · show eval .e t = _
      simp only [eval, z, h16 σ s hs, Proof.RsaOaep.X86.ofNat_sub_beq32 hD hx0]
    refine VQ.ite (fun σ s hs => ⟨_, hs.2⟩) (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono_pre fun σ s hs => hs.1.1
      · exact VQ.of_vp (VP.empty fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e)
    · by_cases hDx : D = x
      · exact VQ.of_vp (VP.empty fun σ s hs => by
          have e := hs.1.2.symm.trans hs.2
          simp [hDx] at e)
      · exact (byLen_vq hD h16 hst hb ((List.mem_cons.mp h).resolve_left hDx)
          fun z hz => hx z (List.mem_cons_of_mem _ hz)).mono_pre fun σ s hs => hs.1.1

/-- The index of the hash function of the table at the argument 14, to
`edx`. -/
theorem idx_vp (P : EP) {ix : Nat} (hix : ∀ σ, P.TH σ → σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix) :
    VP (Sy (S h P)) (.block (idxLoad 14)) (fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = BitVec.ofNat 32 ix) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.tblH5
  show VP _ (.block ([ld .edx (arg 14)] ++ [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 20))])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = P.tabH)
    (VP.taint [.esp] idxArg14_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] idxWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.sp, h₂.1.2.sp]
  · obtain ⟨⟨hi, hs⟩, sy⟩ := hs
    simp only [ld]
    refine hs.wp_arg (vf_arg h (j := 14) (by decide)) (by decide) fun t1 s1 u1 => WP.block_nil
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
    (hs : sizes h.H = sizesOf i) : verifyTail f (ofIdx i) fG pn pc = verifyTail f h.H fG pn pc := by
  rw [show ofIdx i = ofSizes (sizes h.H) by rw [hs]; rfl]
  rfl

/-- The body, for the hash function `h` of index `ix` and MGF1's `P.g`. -/
theorem body_vq' (P : EP) (c : Ver.PublicImpl) {dn : String} {f : MdFns} {ix : Nat} (hix₀ : ix ∈ idxs)
    (hs : sizes h.H = sizesOf ix)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ ∧
      σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix)
    (hTHs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.TH τ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts P.g.H fG P.tab P.ai P.au P.af σ)
    (hTs : ∀ σ τ, In h.D P σ → (P.lay h.D).St σ τ → τ.syms = σ.syms → P.T τ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) :
    VQ (Sy (S h P)) (verifyBodyT f fG c.name c.code) (Fin h P) := by
  have hlt : ix < 2 ^ 32 := (cmpIdxs_taint ix hix₀).1
  show VQ _ (.seq (.block (idxLoad 14)) (byLen (fun i => verifyTail f (ofIdx i) fG c.name c.code) idxs)) _
  refine VQ.seq (idx_vp h P fun σ hσ => (hTH σ hσ).2) (byLen_vq (D := ix) hlt (fun _ _ hs => hs.2)
    (fun σ s t ⟨⟨⟨hi, hs⟩, sy⟩, dx⟩ fu sy' => ⟨⟨⟨hi, hs.fupd fu⟩, sy'.trans sy⟩, by rw [fu.gpr]; exact dx⟩) ?_ hix₀
    cmpIdxs_taint)
  rw [tail_eq h hs]
  exact (body_vq h P c (fun σ hσ => (hTH σ hσ).1) hTHs fneH hT hTs fne).mono_pre fun _ _ hs => hs.1

/-! ## The stack -/

theorem tail_noSp {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {fG : Fns} (gi : ∀ q ∈ fG.init, NoSp q.2) (gu : ∀ q ∈ fG.upd, NoSp q.2)
    (gf : ∀ q ∈ fG.fin, NoSp q.2) (c : Ver.PublicImpl) : NoSp (verifyTail f h.H fG c.name c.code) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig4
  have p3 := sp.lenArgs8
  have p4 := sp.fxSalt
  have p5 := sp.cpDb
  have p6 := sp.passSet
  have p7 := sp.anyLen
  have p8 := sp.cmpArgs
  have p9 := sp.mgfArgs
  have hct := ctHashT_noSp h hi hc hd (j := 14) (NoSp.of_all (by decide +kernel))
  have hm := Proof.RsaOaep.X86.mgfX_noSp gi gu gf (j := 15) (NoSp.of_all (by decide +kernel))
  have hcc := c.noSp
  simp only [verifyTail, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [verifyMainT, fixedPathT, anyPathT, yDig, shift, passOne, cmpH, seqs, countLoop]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

theorem body_noSp {f : MdFns} {fG : Fns} (hf : Sg.FnsSp f fG) (hall : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i)
    (c : Ver.PublicImpl) : NoSp (verifyBodyT f fG c.name c.code) := by
  refine noSp_seq (NoSp.of_all (by decide +kernel)) (Proof.RsaOaep.X86.byLen_noSp fun i hi => ?_)
  obtain ⟨h', hs⟩ := hall i hi
  rw [tail_eq h' hs]
  exact tail_noSp h' hf.hi hf.hc hf.hd hf.gi hf.gu hf.gf c

/-! ## The entry -/

variable {vs : List MVar} {gs : List TVar}

/-- The code, calling `c`, with the hash function any of the tables of `vs`
and MGF1's any of `gs`. -/
abbrev verifyCode (vs : List MVar) (gs : List TVar) (c : Ver.PublicImpl) : Prog isa :=
  verifyPrecomputed (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs) c.name c.code

/-- The contract, with those tables. -/
abbrev vspec (vs : List MVar) (gs : List TVar) : Contract isa :=
  spec (Proof.MdHashTable.X86.tables vs) (Proof.HashTable.X86.tables gs)

theorem code_noSp (hok : Sg.OK vs gs) (c : Ver.PublicImpl) : NoSp (verifyCode vs gs c) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp (Sg.fnsSp vs gs) (Sg.hall_of hok) c)) restore_noSp)

theorem code_sp (hok : Sg.OK vs gs) (c : Ver.PublicImpl) : (verifyCode vs gs c).all (fun i => !isa.writesSp i) = true :=
  Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp hok c)

theorem spec_sp {s : State} (hs : (vspec vs gs).pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  verify_pre at hs
  obtain ⟨hsp, hsa, -⟩ := hs
  exact ⟨hsp, by omega⟩

/-- The public parameters for the table of `MdHash` of `w` and that of
`Hash` of `wg`, with their functions where `s'` has them. -/
abbrev epw (vs : List MVar) (gs : List TVar) (s s' : State) (w : MVar) (wg : TVar) : EP :=
  ep s (s'.syms w.h.H.st.initN) (s'.syms w.h.H.compN) (s'.syms (Proof.MdHashTable.X86.digName w))
    (Sg.THw vs w (arg s 14) s') (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN) (s'.syms wg.g.H.finN)
    (TabFacts wg.g.H (Proof.HashTable.X86.fnsOf gs) (arg s 15) (s'.syms wg.g.H.initN) (s'.syms wg.g.H.updN)
      (s'.syms wg.g.H.finN)) wg.g

/-- The digest's length, from the hash function the table names. -/
theorem dlen_of {s : State} (hs : (vspec vs gs).pre s) {w : MVar}
    (hh : Abi.tableHeld 32 s.mem ((arg s 14).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w))) :
    (arg s 5).toNat = w.h.D := by
  obtain ⟨-, -, -, hfitH, -, hdl⟩ := spec_tab hs
  have := hdl _ (Proof.MdHashTable.X86.hashAt_tableOf hfitH (Proof.MdHashTable.X86.held_tableOf hfitH hh).2.2.2)
  rw [this, w.h.glen]

/-- The entry state, for the tables of `w` at the argument 14 and `wg` at
15, with the functions where `s'` has them (`s'` has them where `s` does). -/
theorem entered_state (hok : Sg.OK vs gs) {s s' : State} (hs : (vspec vs gs).pre s) {w : MVar} {wg : TVar}
    (hw : w ∈ vs) (hwg : wg ∈ gs)
    (hhH : Abi.tableHeld 32 s.mem ((arg s 14).setWidth 64) (FnTable.words isa s (Proof.MdHashTable.X86.tableOf w)))
    (hh : Abi.tableHeld 32 s.mem ((arg s 15).setWidth 64) (FnTable.words isa s (Proof.HashTable.X86.tableOf wg)))
    (hsy : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s.syms n = s'.syms n) :
    Sy (S w.h (epw vs gs s s' w wg)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitH, hfit, -⟩ := spec_tab hs
  have hpwH := hpw.sublist (List.sublist_append_left _ _)
  have hpwG := (hpw.sublist (List.sublist_append_right _ _)).sublist (List.sublist_append_left _ _)
  obtain ⟨hsp0, -⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hD := dlen_of hs hhH
  let e0 := ep s 0 0 0 (fun _ => True) 0 0 0 (fun _ => True) wg.g
  have ok := (in_of_pre (hai := 0) (hac := 0) (had := 0) (TH := fun _ => True) (ai := 0) (au := 0) (af := 0)
    (T := fun _ => True) (g := wg.g) hs trivial trivial).ok
  rw [ep_lay] at ok
  have hn := Proof.MdHashTable.X86.mem_names hw
  have hng := Proof.HashTable.X86.mem_names hwg
  have hsyH : ∀ n ∈ Proof.MdHashTable.X86.names vs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_left _ h)
  have hsyG : ∀ n ∈ Proof.HashTable.X86.names gs, s.syms n = s'.syms n := fun n h => hsy n (List.mem_append_right _ h)
  have tf := Proof.HashTable.X86.tabFacts_entered (argv := e0.argv (arg s 5).toNat) (ro := e0.ro (arg s 5).toNat)
    (rw := e0.rw) (C := 100) hsp ok (p := arg s 15) (by simp [e0, ep]) hfit hok.2.2.1 hpwG hwg hh
  rw [hsyG _ hng.1, hsyG _ hng.2.1, hsyG _ hng.2.2] at tf
  have sy : (entered frameBytes s).syms = s.syms := pushRegs_syms s _
  obtain ⟨m0, m3, m4, m5⟩ := Proof.MdHashTable.X86.held_entered (argv := e0.argv (arg s 5).toNat)
    (ro := e0.ro (arg s 5).toNat) (rw := e0.rw) (C := 100) hsp ok (p := arg s 14) (by simp [e0, ep]) hfitH hhH
  have hf := Proof.MdHashTable.X86.hfacts_of hok.1 (σ := entered frameBytes s) (by rw [sy]; exact hpwH) hw m0 m3 m4
  rw [sy, hsyH _ hn.1, hsyH _ hn.2.2.2.1, hsyH _ hn.2.2.2.2] at hf
  have hi := in_of_pre (hai := s'.syms w.h.H.st.initN) (hac := s'.syms w.h.H.compN)
    (had := s'.syms (Proof.MdHashTable.X86.digName w)) (TH := Sg.THw vs w (arg s 14) s')
    (ai := s'.syms wg.g.H.initN) (au := s'.syms wg.g.H.updN) (af := s'.syms wg.g.H.finN) (g := wg.g) hs ⟨hf, m5⟩ tf
  rw [hD] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

/-- The body, for the tables of `w` and `wg`. -/
theorem bodyw_vq (hok : Sg.OK vs gs) (c : Ver.PublicImpl) (s s' : State) {w : MVar} {wg : TVar} (hw : w ∈ vs)
    (hwg : wg ∈ gs) :
    VQ (Sy (S w.h (epw vs gs s s' w wg))) (verifyBodyT (Proof.MdHashTable.X86.fnsOf vs) (Proof.HashTable.X86.fnsOf gs)
      c.name c.code) (Fin w.h (epw vs gs s s' w wg)) := by
  obtain ⟨fneH, fne⟩ := Sg.fne_of hw hwg
  refine body_vq' w.h (epw vs gs s s' w wg) c (hok.2.1 w hw).1 (hok.2.1 w hw).2 (fun _ x => x) ?_ fneH
    (fun _ x => x) (fun σ τ hi hs sy => tabfacts_st w.h hi hs sy hi.tabT) fne
  intro σ τ hi hs sy
  obtain ⟨tR, tRo, tC⟩ := hi.tblH5
  exact ⟨hfacts_st w.h hi hs sy hi.tabTH.1, (St_roW hs tRo tC).trans hi.tabTH.2⟩

theorem code_ok (hok : Sg.OK vs gs) (c : Ver.PublicImpl) {s : State} (hs : (vspec vs gs).pre s) :
    WP isa (verifyCode vs gs c) s fun t => abiPreserved s t ∧ (vspec vs gs).post s t := by
  obtain ⟨⟨TH, hTH, hhH⟩, ⟨T, hT, hh⟩, -, hfitH, hfit, -⟩ := spec_tab hs
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  have hidxH := (Proof.MdHashTable.X86.held_tableOf hfitH hhH).2.2.2
  have hidx := (Proof.HashTable.X86.held_tableOf hfit hh).2.1
  have he := entered_state hok hs hw hwg hhH hh (s' := s) fun _ _ => rfl
  have hin := he.1.1
  obtain ⟨hsp0, hfit4⟩ := spec_sp hs
  have hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hsp0 ⊢; omega
  have hb := (bodyw_vq hok c s s hw hwg).1 _ _ he
  have hD := dlen_of hs hhH
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp (Sg.fnsSp vs gs) (Sg.hall_of hok) c) hsp hfit4
    (W := ((epw vs gs s s w wg).lay w.h.D).W)
    (Q := fun r _ => Res w.h (epw vs gs s s w wg) (entered frameBytes s) r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok hr
    rw [save_eq (argv := (epw vs gs s s w wg).argv (arg s 5).toNat) (ro := (epw vs gs s s w wg).ro (arg s 5).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 100) hsp,
      ret_eq (argv := (epw vs gs s s w wg).argv (arg s 5).toNat) (ro := (epw vs gs s s w wg).ro (arg s 5).toNat)
        (rw := (epw vs gs s s w wg).rw) (C := 100) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [← hD, ep_lay] at ok
    have ro := fun {R : Region} (hR : R ∈ (epw vs gs s s w wg).ro (arg s 5).toNat) => entered_ro hsp ok hR
    sig_post [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argSlots, argVal, argBytes]
    intro H G hH hG
    rw [Proof.MdHashTable.X86.hashAt_tableOf hfitH hidxH, Option.some.injEq] at hH
    rw [Proof.HashTable.X86.hashAt_tableOf hfit hidx, Option.some.injEq] at hG
    subst hH hG
    unfold Res at res
    have hG : sigB (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (arg s 1).toNat := by
      have e : Spec.Rsa.bytesAt (entered frameBytes s).mem ((arg s 6).setWidth 64) (epw vs gs s s w wg).gl =
          Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64) (epw vs gs s s w wg).gl :=
        ro (R := (epw vs gs s s w wg).SIG) (by simp)
      rw [hin.glK] at e
      exact e
    have hdg : digB w.h (epw vs gs s s w wg) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat := by
      unfold digB; rw [← hD]; exact ro (R := (epw vs gs s s w wg).DIG (arg s 5).toNat) (by simp)
    rw [hdg, hG, hD] at res
    rw [BitVec.setWidth_append_eq_right, w.h.glen]
    exact res

theorem code_ct (hok : Sg.OK vs gs) (c : Ver.PublicImpl) :
    ConstantTime isa (vspec vs gs).pre (vspec vs gs).pub (verifyCode vs gs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨TH, hTH, hhH₁⟩, ⟨T, hT, hh₁⟩, -, -, -, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hTH
  obtain ⟨wg, hwg, rfl⟩ := List.mem_map.mp hT
  sig_pub [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argSlots, argVal, argBytes] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabH, htab, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hp
  have hhH₂ := (htabH _ _ rfl rfl _ hTH).mp hhH₁
  have hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  have hsy' : ∀ n ∈ Proof.MdHashTable.X86.names vs ++ Proof.HashTable.X86.names gs, s₂.syms n = s₁.syms n :=
    fun n hn => (hsy n (by simpa [Proof.MdHashTable.X86.names, Proof.HashTable.X86.names] using hn)).symm
  have hep : epw vs gs s₁ s₁ w wg = epw vs gs s₂ s₁ w wg := by
    obtain ⟨hab, hw'⟩ := List.append_inj hl (by simp [RsaPkcs1Sig.bytesAt_len, a1, a3])
    obtain ⟨hn, he⟩ := List.append_inj (Sg.map_toNat_inj hab) (by simp [RsaPkcs1Sig.bytesAt_len, a1])
    have hw'' := Sg.map_toNat_inj hw'
    simp only [ep]
    rw [hsp, a0, a1, a2, a3, a4, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
    rw [a0, a1] at hn
    rw [a2, a3] at he
    rw [a12, a13] at hw''
    rw [hn, he, hw'']
  refine (wrap_ct (F := frameBytes) (body_noSp (Sg.fnsSp vs gs) (Sg.hall_of hok) c)
    (P := fun a b => a = s₁ ∧ b = s₂) (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
    e₁ e₂).1
  refine (bodyw_vq hok c s₁ s₁ hw hwg).2.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hok h₁ hw hwg hhH₁ hh₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hok h₂ hw hwg hhH₂ hh₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_pss_verify_precomputed`, calling `c`, with the hash function any
of the tables of `vs` and MGF1's any of `gs`, meets the shared contract
(satisfiable, `VfSat.lean`). -/
theorem verify_verified (hok : Sg.OK vs gs) (hsat : ∃ s, (vspec vs gs).pre s) (c : Ver.PublicImpl) :
    Verified target (verifyCode vs gs c) (vspec vs gs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hok c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hok c, hsat⟩

end VG.Proof.RsaPss.X86.Vf
