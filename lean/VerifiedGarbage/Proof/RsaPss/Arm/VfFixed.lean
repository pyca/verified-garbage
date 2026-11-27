module

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.SgEnc1
public import VerifiedGarbage.Proof.RsaPss.Arm.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPss.Arm.VfPass
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.Params
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
meta import VerifiedGarbage.Proof.RsaPss.VerifyCases
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
meta import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
public import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
meta import VerifiedGarbage.Proof.RsaPss.Params
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
meta import VerifiedGarbage.Spec.RsaPss.MdTable
meta import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.SgCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `RsaPss.Arm.VfY`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.VfPos`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.VfScan`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.VfAcc`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.VfCall`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.VfChk`, which this module and modules that import it used -/

section

/-! ### `RsaPss.Arm.VfBase`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: where everything is

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
`salt_len`, `any_salt_len`, and the public key's bytes and precomputed
words), its layout (`EP.lay`), with the 56 bytes below the frame that the
call of `vg_rsa_public_precomputed_checked` uses. `In P σ`: the state `σ`
the body starts from (`in_of_pre`); the working space's bound is used in
one place, `In.pubScr`.

`VQ F c G`: a piece correct (`wp`) and constant time with nothing after it
(`ct`), as the end of a body; the pieces after the call are proven over the
state the call leaves (`VQ.reidx`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP Two)

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  n : BitVec 32
  e : BitVec 32
  dig : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  gl : Nat
  slt : Nat
  any : BitVec 32
  scl : Nat
  rl : Nat
  nB : List Byte
  eB : List Byte
  pw : List (BitVec 64)
  hd : BitVec 32
  hi : BitVec 32
  hc : BitVec 32
  hdg : BitVec 32
  HT : State → Prop
  tab : BitVec 32
  ai : BitVec 32
  au : BitVec 32
  af : BitVec 32
  T : State → Prop
  /-- MGF1's hash function. -/
  G : Spec.Mgf1.Hash

namespace EP

variable (D : Nat) (P : EP)

abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev DIG : Region := ⟨State.addr P.dig, D⟩
abbrev SIG : Region := ⟨State.addr P.sig, P.gl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.scl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.rl * 8⟩
abbrev HTAB : Region := Sig.tableRegion 32 (State.addr P.hd) 11
abbrev TAB : Region := Sig.tableRegion 32 (State.addr P.tab) 11

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.dig, BitVec.ofNat 32 D, P.sig, BitVec.ofNat 32 P.gl,
    BitVec.ofNat 32 P.slt, P.any, P.scr, BitVec.ofNat 32 P.scl, P.pre, BitVec.ofNat 32 P.rl, P.hd, P.tab]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 48
  argv := P.argv D
  ro := [P.N, P.E, P.DIG D, P.SIG, P.PRE, P.HTAB, P.TAB]
  rw := [P.SCR]
  C := 104

end EP

/-- The state the body starts from. -/
structure In (D : Nat) (P : EP) (σ : State) : Prop where
  ok : (P.lay D).Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  glK : P.gl = P.K
  scrK : Spec.RsaPss.publicScratchWords P.K ≤ P.scl
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  slt32 : P.slt < 2 ^ 32
  scl32 : P.scl < 2 ^ 32
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.rl = P.pw
  htabT : P.HT σ
  tabT : P.T σ

namespace In

variable {D : Nat} {P : EP} {σ : State} (h : In D P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2

/-- The working space: ours, and the public operation's after it. This is
the one place the contract's bound on `scratch_len` is used. -/
theorem pubScr : Spec.Rsa.publicScratchWords P.K ≤ P.scl - 1024 ∧ 1025 ≤ P.scl := by
  have := h.scrK
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords at this
  unfold Spec.Rsa.publicScratchWords
  omega_arith

/-- Our part of `scratch`. -/
theorem geo : Geo (P.lay D) P.scr := by
  have hs := h.pubScr.2
  have hf := h.ok.fits (P.SCR) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨rfl, by unfold oRsa; omega_arith, ⟨P.scl * 8, by unfold oRsa; omega_arith, by simp⟩, ⟨σ, h.ok⟩,
    by show 16 ≤ 104; decide⟩

/-- The table of `MdHash`, in a buffer only read. -/
theorem htbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (RsaOaep.Arm.tA P.hd o) 4 := by
  have hf := h.ok.fits P.HTAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.HTAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.hd, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.hd + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The table of `MdHash`, in a buffer only read. -/
theorem tbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (RsaOaep.Arm.tA P.tab o) 4 := by
  have hf := h.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.tab, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.tab + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 104

/-- The shared contract, with the hash function one of the tables `hs`,
MGF1's one of `ts`, and that stack. -/
abbrev spec (hs ts : List FnTable) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", hs), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "verify_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val] at $h:ident
  simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq,
    exists_eq_left'] at $h:ident))

/-- The public parameters of an entry state, with what `HT` and `T` say of
the tables. -/
def ep (G : Spec.Mgf1.Hash) (s : State) (hi hc hdg : BitVec 32) (HT : State → Prop) (ai au af : BitVec 32) (T : State → Prop) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  n := s.gpr .r0
  e := s.gpr .r2
  dig := stackArg s 0
  sig := stackArg s 2
  scr := stackArg s 6
  pre := stackArg s 8
  K := (s.gpr .r1).toNat
  el := (s.gpr .r3).toNat
  gl := (stackArg s 3).toNat
  slt := (stackArg s 4).toNat
  any := stackArg s 5
  scl := (stackArg s 7).toNat
  rl := (stackArg s 9).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  pw := Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) (stackArg s 9).toNat
  hd := stackArg s 10
  hi := hi
  hc := hc
  hdg := hdg
  HT := HT
  tab := stackArg s 11
  ai := ai
  au := au
  af := af
  T := T
  G := G

variable {G : Spec.Mgf1.Hash} {hi hc hdg : BitVec 32} {HT : State → Prop} {ai au af : BitVec 32} {T : State → Prop}

theorem ep_lay (D : Nat) (s : State) :
    (ep G s hi hc hdg HT ai au af T).lay D = layOf frameBytes 48 ((ep G s hi hc hdg HT ai au af T).argv D)
      [(ep G s hi hc hdg HT ai au af T).N, (ep G s hi hc hdg HT ai au af T).E, (ep G s hi hc hdg HT ai au af T).DIG D,
        (ep G s hi hc hdg HT ai au af T).SIG, (ep G s hi hc hdg HT ai au af T).PRE, (ep G s hi hc hdg HT ai au af T).HTAB,
        (ep G s hi hc hdg HT ai au af T).TAB] [(ep G s hi hc hdg HT ai au af T).SCR] s 104 := rfl

theorem in_of_pre {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) {D : Nat}
    (hD : (stackArg s 1).toNat = D) (hHT : HT (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In D (ep G s hi hc hdg HT ai au af T) (entered frameBytes s) := by
  verify_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr nS eS dS gS sR sTH sT sA kN kE kD kG kS kR kTH kT kA fN fE fD fG fS fR
    fTH fT kv el1 elK glK scrK rlK
  have h288 : 288 ≤ s.sp.toNat := hsp
  have a1 : stackArg s 1 = BitVec.ofNat 32 D := by
    apply BitVec.eq_of_toNat_eq; rw [hD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hD]; exact (stackArg s 1).isLt)]
  rw [hD] at dS kD fD hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56) ⟨State.addr s.sp - BitVec.ofNat 64 288, 288⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, glK := glK, scrK := scrK, rlK := rlK
      slt32 := (stackArg s 4).isLt
      scl32 := (stackArg s 7).isLt
      nB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kN.sub_left below).symm)
        (by show (s.gpr .r1).toNat ≤ 2 ^ 64; omega_arith)
      eB := bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below).symm)
        (by show (s.gpr .r3).toNat ≤ 2 ^ 64; omega_arith)
      pw := wordsAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below).symm)
        (by show (stackArg s 9).toNat * 8 ≤ 2 ^ 64; omega_arith)
      htabT := hHT
      tabT := hT }
  rw [ep_lay]
  refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kD, kG, kR, kTH, kT, kS, kA]
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hw
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [nS.symm, eS.symm, dS.symm, gS.symm, sR, sTH, sT, sA]
  · exact List.pairwise_singleton _ _
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fN, fE, fD, fG, fR, fTH, fT, fS]
  · intro j hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · rfl
    · simp [regArg, ep]
    · rfl
    · simp [regArg, ep]
  · intro i hi
    have : i < 12 := hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10 ∨ i = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1]

/-- What the proofs need of the tables, for the hash function `h`, whose
digest is named `dn`, and MGF1's `g`: an indirect call of `f`'s and `fg`'s
functions (not empty) through the table reaches theirs, in every run. -/
structure TF (h : PssHash) (g : RsaOaep.Arm.OHash) (f : MdFns) (fg : Impl.RsaOaep.Arm.Fns) (dn : String) (P : EP) :
    Prop where
  ht : ∀ σ, P.HT σ → HTab h dn f P.hd P.hi P.hc P.hdg σ
  t : ∀ σ, P.T σ → RsaOaep.Arm.TabFacts g.H fg P.tab P.ai P.au P.af σ
  fne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []
  gne : fg.init ≠ [] ∧ fg.upd ≠ [] ∧ fg.fin ≠ []
  gG : P.G = g.G
  /-- What the tables' facts need of a state: its statics' addresses and the
  tables' words. -/
  htk : ∀ σ s, P.HT σ → s.syms = σ.syms → (∀ o, o + 4 ≤ 44 →
    s.mem.readW (RsaOaep.Arm.tA P.hd o) 32 = σ.mem.readW (RsaOaep.Arm.tA P.hd o) 32) → P.HT s
  tk : ∀ σ s, P.T σ → s.syms = σ.syms → (∀ o, o + 4 ≤ 44 →
    s.mem.readW (RsaOaep.Arm.tA P.tab o) 32 = σ.mem.readW (RsaOaep.Arm.tA P.tab o) 32) → P.T s

/-! ## Pieces at the end of the body -/

/-- Correct, and constant time with nothing after it. -/
def VQ (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop :=
  (∀ σ s, F σ s → WP isa c s (G σ)) ∧ RelCT isa (Two F) c fun _ _ => True

theorem VQ.of_vp {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) : VQ F c G :=
  ⟨h.wp, h.ct.mono (fun _ _ h => h) fun _ _ _ => trivial⟩

theorem VQ.seq {F G H : State → State → Prop} {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VQ G c₂ H) :
    VQ F (.seq c₁ c₂) H :=
  ⟨fun σ s hs => WP.seq (WP.mono (h₁.wp σ s hs) fun t ht => h₂.1 σ t ht), RelCT.seq h₁.ct h₂.2⟩

theorem VQ.ite {F G : State → State → Prop} {c : Cond} {t e : Prog isa}
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VQ (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VQ (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VQ F (.ite c t e) G := by
  refine ⟨fun σ s hs => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, isa.eval c s = some b := by cases c <;> exact ⟨_, rfl⟩
    exact WP.ite b hb (fun h => ht.1 σ s ⟨hs, by rw [hb, h]⟩) (fun h => he.1 σ s ⟨hs, by rw [hb, h]⟩)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁ h₂) ?_ ?_
    · exact ht.2.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h
    · exact he.2.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨h₁, e⟩, h₂, (hc _ _ _ _ h₁ h₂).symm.trans e⟩) fun _ _ h => h

/-- A piece proven over the state it starts from, as a piece of a run from `σ`. -/
theorem VQ.reidx {F F' G G' : State → State → Prop} {c : Prog isa} (h : VP F' c G')
    (hF : ∀ σ s, F σ s → F' s s) (hG : ∀ σ s t, F σ s → G' s t → G σ t) : VQ F c G :=
  ⟨fun σ s hs => WP.mono (h.wp s s (hF σ s hs)) fun t ht => hG σ s t hs ht,
    h.ct.mono (fun s₁ s₂ ⟨_, _, h₁, h₂⟩ => ⟨s₁, s₂, hF _ _ h₁, hF _ _ h₂⟩) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.Arm.Vf

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the checks

`scratch` to its slot and the arguments of `params` (`chk_vp`); the
encoding's parameters, `[any_salt_len ≠ 0]` and whether everything fits
(`par_vp`): the modulus' first byte not zero, and `lo + hLen + 2 + sLen ≤ k`
for the expected salt length `sLen` (0 if any); if not, 0 (`fail_vp`), as the
specification answers (`verify_false`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In h.D P σ ∧ (P.lay h.D).St σ s

/-- The modulus' first byte, `lo`, the salt length the checks take, and
whether everything fits. -/
abbrev n0 (P : EP) : Byte := P.nB.getD 0 0
abbrev lo (P : EP) : Nat := if (n0 P).toNat ≤ 1 then 1 else 0
abbrev eLen (P : EP) : Nat := if P.any = 0 then P.slt else 0
abbrev fits (P : EP) : Prop := (n0 P).toNat ≠ 0 ∧ lo P + h.D + 2 + eLen P ≤ P.K

/-- The salt length verification expects. -/
abbrev sLenO (P : EP) : Option Nat := if P.any = 0 then some P.slt else none

/-- The buffers the body only reads, in the run from `σ`. -/
abbrev digB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D
abbrev sigB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.sig) P.K

/-- The result. -/
abbrev Res (G : Spec.Mgf1.Hash) (P : EP) (σ : State) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    r = if Spec.RsaPss.verify h.G G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) then 1 else 0

/-- The end of the body. -/
abbrev Fin (G : Spec.Mgf1.Hash) (P : EP) (σ s : State) : Prop := S h P σ s ∧ Res h G P σ (s.gpr .r0)

theorem arg_lt {j : Nat} (hj : j < 16) : arg j < 4096 := by
  unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith

/-- An argument: its place, readable, and its value. -/
theorem argAt {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) {j : Nat} (hj : j < 16) :
    State.addr (P.B + BitVec.ofNat 32 (arg j)) = (P.lay D).fr (arg j) ∧
    InRegions (s.rd ++ s.wr) ((P.lay D).fr (arg j)) 4 ∧
    s.mem.readW ((P.lay D).fr (arg j)) 32 = (P.argv D).getD j 0 := by
  have hl : j < (P.lay D).argv.length := by simp only [EP.argv, List.length_cons, List.length_nil]; omega_arith
  exact ⟨hi.ok.addrB (by
      show arg j < frameBytes + 56 + 48; unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith),
    by rw [hs.rd, hs.wr]; exact hi.ok.arg_read hl, hs.arg hl⟩

/-- A slot, written with `r12 = sp`. -/
theorem slotAt {D : Nat} {P : EP} {σ : State} (hi : In D P σ) {d : Nat} (hd : d + 4 ≤ frameBytes) :
    State.addr (P.B + BitVec.ofNat 32 d) = (P.lay D).fr d :=
  hi.ok.addrB (by show d < frameBytes + 56 + 48; unfold frameBytes at hd ⊢; omega_arith)

/-- After `verifyChk`. -/
abbrev C0 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.gpr .r0 = P.n ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧
    s.gpr .r2 = BitVec.ofNat 32 P.slt ∧ s.gpr .r10 = P.any ∧ s.gpr .r11 = BitVec.ofNat 32 (h.D + 1) ∧
    s.gpr .r12 = P.B

theorem chk_vp (P : EP) : VP (S h P) (.block (verifyChk h.sh)) (C0 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.2.sp.trans h₂.2.sp.symm) fun σ s ⟨hi, hs⟩ => ?_
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  obtain ⟨a9, r9, v9⟩ := argAt hi hs (j := 10) (by decide)
  obtain ⟨a0, r0, v0⟩ := argAt hi hs (j := 0) (by decide)
  obtain ⟨a1, r1, v1⟩ := argAt hi hs (j := 1) (by decide)
  obtain ⟨a7, r7, v7⟩ := argAt hi hs (j := 8) (by decide)
  obtain ⟨a8, r8, v8⟩ := argAt hi hs (j := 9) (by decide)
  have k : ∀ (j : Nat) (v : BitVec 32), j < 16 →
      (s.mem.writeW ((P.lay h.D).fr sS) v).readW ((P.lay h.D).fr (arg j)) 32 = s.mem.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun j v hj => Lay.readW_fr_other _ _ _ (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes sS; split <;> omega_arith) (by
      unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by decide)
  have hw : WP isa (.block (verifyChk h.sh)) s fun t => t.mem = s.mem.writeW ((P.lay h.D).fr sS) P.scr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.n ∧ t.gpr .r1 = BitVec.ofNat 32 P.K ∧
      t.gpr .r2 = BitVec.ofNat 32 P.slt ∧ t.gpr .r10 = P.any ∧ t.gpr .r11 = BitVec.ofNat 32 (h.D + 1) ∧
      t.gpr .r12 = P.B := by
    prun [verifyChk, sp0, ld, st, mw, hs.sp, a9, r9, v9, a0, r0, v0, a1, r1, v1, a7, r7, v7, a8, r8, v8,
      k 0 _ (by decide), k 1 _ (by decide), k 8 _ (by decide), k 9 _ (by decide),
      slotAt hi (d := sS) (by decide), hs.inFr (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide), arg_lt,
      movw_val (show dig h.sh + 1 < 2 ^ 16 by show h.D + 1 < 2 ^ 16; omega_arith)]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0, t1, t2, t10, t11, t12⟩ => ⟨⟨?_, ?_⟩, hi, t0, t1, t2, t10, t11, t12⟩
  · exact hs.frameW (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes; decide) (by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) rd wr sp
  · rw [m, Mem.readW_writeW_self32]

/-! ## The parameters, and whether everything fits -/

/-- After the checks. -/
abbrev C1 (P : EP) (σ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ s.mem.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    s.mem.readW ((P.lay h.D).fr sDb) 32 = dbW P.K h.D ((n0 P).setWidth 32) ∧
    s.mem.readW ((P.lay h.D).fr sAny) 32 = (if P.any = 0 then 0 else 1) ∧ s.z = decide (fits h P)

theorem par_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r2, .r10, .r11, .r12])
    (.block (params ++ expLen ++ saltFits)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The modulus' first byte, in a state of the body. -/
theorem n0_at {D : Nat} {P : EP} {σ s : State} (hi : In D P σ) (hs : (P.lay D).St σ s) :
    s.mem (State.addr P.n) = n0 P ∧ InRegions (s.rd ++ s.wr) (State.addr P.n) 1 := by
  have hK := hi.k64
  refine ⟨?_, ⟨P.N, by rw [hs.rd, hi.ok.rd]; simp, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩⟩
  have e : Spec.Rsa.bytesAt s.mem (State.addr P.n) P.K = P.nB := (hs.ro (R := P.N) (by simp)).trans hi.nB
  show s.mem (State.addr P.n) = P.nB.getD 0 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD (by omega_arith), BitVec.add_zero]

theorem par_vp (P : EP) : VP (C0 h P) (.block (params ++ expLen ++ saltFits)) (C1 h P) := by
  refine VP.taint _ par_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, r0, r1, r2, r10, r11, r12⟩ => ?_
  · obtain ⟨-, -, a0, a1, a2, a10, a11, a12⟩ := h₁
    obtain ⟨-, -, b0, b1, b2, b10, b11, b12⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a10, b10]
    · rw [a11, b11]
    · rw [a12, b12]
  have hg := hi.geo
  have hK := hi.k1024
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  obtain ⟨nb, hn⟩ := n0_at hi hc.st
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (params_wp hg hc (K := P.K) (D := h.D) r0 hn r1 r11 r12)
    fun t ⟨m, rd, wr, sp, t8, t9, t2, t10, t12⟩ => ?_)
  rw [nb] at m t8 t9
  have fr1 : Frame [slotR (P.lay h.D) sC, slotR (P.lay h.D) sLo, slotR (P.lay h.D) sDb] s.mem t.mem := by
    rw [m]
    exact (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  have hct : Ctx (P.lay h.D) P.scr σ t := hc.write fr1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)) rd wr sp
  refine WP.block_append (WP.mono (expLen_wp hg hct (by rw [t12, r12]))
    fun u ⟨mu, rdu, wru, spu, u2, u8, u9⟩ => ?_)
  refine WP.mono (saltFits_wp u) fun w ⟨mw', rdw, wrw, spw, z⟩ => ?_
  have fr2 : Frame [slotR (P.lay h.D) sAny] t.mem w.mem := by rw [mw', mu]; exact slot_frame _ _ _ _
  refine ⟨hct.write fr2 (fun r hr => ?_) (fun r hr => ?_) (rdw.trans rdu) (wrw.trans wru) (spw.trans spu), hi,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · rw [mw', mu, t10, r10, slot_ww _ _ (by decide) (by decide) (by decide), m,
      slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [mw', mu, t10, r10, slot_ww _ _ (by decide) (by decide) (by decide), m,
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, loW_byte]
  · rw [mw', mu, t10, r10, slot_ww _ _ (by decide) (by decide) (by decide), m, Mem.readW_writeW_self32]
  · rw [mw', mu, t10, r10, Mem.readW_writeW_self32]
  · have e2 : w.z = ((t.gpr .r8 ||| (t.gpr .r9 - BitVec.ofNat 32 (eLen P)) >>> 31 |||
        BitVec.ofNat 32 (eLen P) >>> 31) - 0 == 0) := by
      rw [z, u8, u9, u2, t10, r10, t2, r2]
      unfold eLen
      split <;> rfl
    rw [e2, t8, t9, dbW_byte, setWidth_byte]
    exact fits_z (n0 P).isLt hK hD (by unfold eLen; have := hi.slt32; split <;> omega_arith) (by split <;> omega_arith)

/-! ## When something does not fit -/

theorem nB_length {D : Nat} {P : EP} {σ : State} (hi : In D P σ) : P.nB.length = P.K := by
  rw [← hi.nB, RsaPkcs1Sig.Arm.bytesAt_length]

/-- `emLen = k - lo`, for a modulus whose first byte is not zero. -/
theorem emLen_eq {P : EP} {b : Byte} {rest : List Byte} (hbr : P.nB = b :: rest) (hl : rest.length + 1 = P.K)
    (hbt : b.toNat ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) = P.K - lo P := by
  have hb0 : b ≠ 0 := fun e => hbt (by rw [e]; rfl)
  have e2 := RsaPss.emLength_eq rest hb0
  have hn0 : n0 P = b := by simp [n0, hbr]
  unfold lo; rw [hn0]
  by_cases hb1 : b.toNat = 1
  · rw [ite_eq_left hb1] at e2; rw [ite_eq_left (by omega_arith)]; all_goals omega_arith
  · rw [ite_eq_right hb1] at e2; rw [ite_eq_right (by have := b.isLt; omega_arith)]; all_goals omega_arith

/-- `verify` refuses an encoding too short for the salt (as in
`Proof/RsaPss/VerifyCases.lean`), with MGF1's hash function `G` another than
`H`. -/
theorem verify_short₂ (H G : Spec.Mgf1.Hash) {nB : List Byte} (eB mHash sB : List Byte) {sLen : Option Nat}
    (h : Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip nB) - 1) < H.len + sLen.getD 0 + 2) :
    Spec.RsaPss.verify H G nB eB mHash sB sLen = false := by
  unfold Spec.RsaPss.verify
  cases Spec.Rsa.publicOpChecked nB eB sB with
  | none => simp
  | some x =>
    have : Spec.RsaPss.verifyEncoding H G mHash (x.drop (nB.length - Spec.RsaPss.emLength
        (Spec.RsaPss.bitLength (Spec.Rsa.os2ip nB) - 1))) (Spec.RsaPss.bitLength (Spec.Rsa.os2ip nB) - 1) sLen =
        false := by
      unfold Spec.RsaPss.verifyEncoding
      rw [ite_eq_left (Or.inr (Or.inr h))]
    simp [this]

/-- The specification refuses what does not fit. -/
theorem verify_false (G : Spec.Mgf1.Hash) {P : EP} {σ : State} (hi : In h.D P σ) (hf : ¬ fits h P) :
    Spec.RsaPss.verify h.G G P.nB P.eB (digB h P σ) (sigB P σ) (sLenO P) = false := by
  have hl := nB_length hi
  have hK := hi.k64
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, P.nB = b :: rest := by
    cases e : P.nB with
    | nil => rw [e] at hl; simp at hl; omega_arith
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hn0 : n0 P = b := by simp [n0, hbr]
  rw [hbr]
  by_cases hb : b.toNat = 0
  · have : b = 0 := BitVec.eq_of_toNat_eq hb
    subst this
    exact RsaPss.verify_zero₂ G h.G ..
  · rw [hbr, List.length_cons] at hl
    have hem := emLen_eq hbr hl hb
    refine verify_short₂ h.G G _ _ _ ?_
    have gl : h.G.len = h.D := h.glen
    have hs : (sLenO P).getD 0 = eLen P := by unfold sLenO eLen; split <;> rfl
    rw [hem, gl, hs]
    unfold fits at hf
    rw [hn0] at hf
    have : lo P ≤ 1 := by unfold lo; split <;> omega_arith
    omega_arith

theorem ret0_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [])
    (.block [mw .r0 0]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem fail_vp (G : Spec.Mgf1.Hash) (P : EP) :
    VP (fun σ s => C1 h P σ s ∧ isa.eval .ne s = some true) (.block [mw .r0 0]) (Fin h G P) := by
  refine VP.taint [] ret0_cert (fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil)
    fun σ s ⟨⟨hc, hi, _, _, _, _, z⟩, e⟩ => ?_
  have hf : ¬ fits h P := fun hfits => by
    rw [VG.Proof.X25519.Arm.eval_ne, z, decide_eq_true hfits] at e
    exact absurd e (by decide)
  have hw : WP isa (.block [mw .r0 0]) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = 0 := by
    prun [mw]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, t0⟩ => ⟨⟨hi, hc.st.regs rd wr sp m⟩, fun _ => ?_⟩
  rw [t0, verify_false h G hi hf]
  rfl

end VG.Proof.RsaPss.Arm.Vf

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the call

The arguments of `vg_rsa_public_precomputed_checked` (`pa_vp`): `EM`'s place
(`oEm`), `pre`, `e`, the signature, and the rest of `scratch` from `oRsa` on;
the call (`call_vp`, correct and constant time: its arguments and the public
data it reads are the same in two runs), which writes RSAVP1 of the
signature to `EM`, or zeros (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (wl wl_cons wl_nil wl_other wl_read wl_frame rdS)

variable (h : PssHash)

/-- `dbLen`. -/
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots after the checks. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW ((n0 P).setWidth 32) ∧ m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) ∧
    m.readW ((P.lay h.D).fr sAny) 32 = (if P.any = 0 then 0 else 1)

/-- When everything fits. -/
abbrev M0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ In h.D P σ ∧ fits h P ∧ Bm h P s.mem

theorem m0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : M0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, sa, z⟩ := hc
  obtain hz : s.z = true := by
    rw [VG.Proof.X25519.Arm.eval_ne] at e
    simpa using e
  obtain hf : fits h P := of_decide_eq_true (z ▸ hz)
  refine ⟨hc, hi, hf, sc, sl, ?_, sa⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  have := hf.2
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by omega_arith), Offset.ofNat_sub_ofNat (by omega_arith)]
  congr 1

theorem rdArg {L : Lay} (m : Mem) (v : BitVec 32) {d j : Nat} (hd : d + 4 ≤ 64) (hj : j < 16) :
    (m.writeW (L.fr d) v).readW (L.fr (arg j)) 32 = m.readW (L.fr (arg j)) 32 :=
  Lay.readW_fr_other L m v (by unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by
    unfold arg Impl.RsaPkcs1Sig.Arm.argOff frameBytes; split <;> omega_arith) (by omega_arith)

/-- The call's stack arguments but the first. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [BitVec.ofNat 32 P.el, P.sig, BitVec.ofNat 32 P.K, P.scr + BitVec.ofNat 32 oRsa, BitVec.ofNat 32 (P.scl - 1024)]

theorem pa_wp (P : EP) {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) (hi : In h.D P σ) :
    WP isa (.block pubArgs) s fun t =>
      t.mem = wl (P.lay h.D) (s.mem.writeW (State.addr P.B) P.e) 1 (outv P) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      t.gpr .r1 = BitVec.ofNat 32 P.K ∧ t.gpr .r2 = P.pre ∧ t.gpr .r3 = BitVec.ofNat 32 P.rl := by
  have hg := hi.geo
  have hs1 := hi.pubScr.2
  obtain ⟨a1, r1, v1⟩ := argAt hi hc.st (j := 1) (by decide)
  obtain ⟨a2, r2, v2⟩ := argAt hi hc.st (j := 2) (by decide)
  obtain ⟨a3, r3, v3⟩ := argAt hi hc.st (j := 3) (by decide)
  obtain ⟨a5, r5, v5⟩ := argAt hi hc.st (j := 6) (by decide)
  obtain ⟨a10, r10, v10⟩ := argAt hi hc.st (j := 11) (by decide)
  obtain ⟨a11, r11, v11⟩ := argAt hi hc.st (j := 12) (by decide)
  obtain ⟨a12, r12, v12⟩ := argAt hi hc.st (j := 13) (by decide)
  replace v1 : s.mem.readW ((P.lay h.D).fr (arg 1)) 32 = BitVec.ofNat 32 P.K := v1
  replace v2 : s.mem.readW ((P.lay h.D).fr (arg 2)) 32 = P.e := v2
  replace v3 : s.mem.readW ((P.lay h.D).fr (arg 3)) 32 = BitVec.ofNat 32 P.el := v3
  replace v5 : s.mem.readW ((P.lay h.D).fr (arg 6)) 32 = P.sig := v5
  replace v10 : s.mem.readW ((P.lay h.D).fr (arg 11)) 32 = BitVec.ofNat 32 P.scl := v10
  replace v11 : s.mem.readW ((P.lay h.D).fr (arg 12)) 32 = P.pre := v11
  replace v12 : s.mem.readW ((P.lay h.D).fr (arg 13)) 32 = BitVec.ofNat 32 P.rl := v12
  obtain wF : ∀ d, d + 4 ≤ frameBytes → InRegions s.wr ((P.lay h.D).fr d) 4 := fun d hd => hc.st.inFr hd
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  obtain w0 : InRegions s.wr (State.addr P.B) 4 := by rw [q0]; exact wF 0 (by decide)
  obtain rdA0 : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j < 16 →
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr (arg j)) 32 = m.readW ((P.lay h.D).fr (arg j)) 32 :=
    fun m v j hj => by rw [q0]; exact rdArg m v (by decide) hj
  obtain rdS0 : ∀ (m : Mem) (v : BitVec 32),
      (m.writeW (State.addr P.B) v).readW ((P.lay h.D).fr sS) 32 = m.readW ((P.lay h.D).fr sS) 32 :=
    fun m v => by rw [q0]; exact rdS m v (by decide)
  prun [pubArgs, copyArg, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, wF, hc.slotS, arg_lt,
    a1, r1, v1, a2, r2, v2, a3, r3, v3, a5, r5, v5, a10, r10, v10, a11, r11, v11, a12, r12, v12, rdArg, rdS, w0,
    rdA0, rdS0, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oRsa < 2 ^ 16 by decide),
    movw_val (show 1024 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (w := 32) (show 1024 ≤ P.scl by omega_arith),
    Nat.reduceMul, wl_cons, wl_nil, Nat.reduceAdd]

/-- Before the call. -/
abbrev V1 (P : EP) (σ s : State) : Prop :=
  M0 h P σ s ∧ PdArgs s (P.scr + BitVec.ofNat 32 oEm) P.pre P.e P.sig (P.scr + BitVec.ofNat 32 oRsa) P.K P.el P.rl
    (P.scl - 1024)

theorem pa_vp (P : EP) : VP (M0 h P) (.block pubArgs) (V1 h P) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hf, hb⟩ => ?_
  have hg := hi.geo
  refine WP.mono (pa_wp h P hc hi) fun t ⟨m, rd, wr, sp, t0, t1, t2, t3⟩ => ?_
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  rw [q0] at m
  obtain fr : Frame [⟨(P.lay h.D).fr 0, 64⟩] s.mem t.mem := by
    rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl 0) (by decide)
      (by decide))).trans (wl_frame _ _ _ 1 (by simp))
  obtain rd0 : ∀ i, i < 16 → stackArg t i = t.mem.readW ((P.lay h.D).fr (4 * i)) 32 := by
    intro i hi'
    simp only [stackArg, stackArgAddr, sp, hc.st.sp]
    rw [hc.aFr hg (4 * i) (by unfold frameBytes; omega_arith)]
  obtain v0 : stackArg t 0 = P.e := by
    rw [rd0 0 (by decide), m, wl_other _ _ _ 1 0 (by decide) (by simp), Mem.readW_writeW_self32]
  obtain v : ∀ i, 1 ≤ i → i < 6 → stackArg t i = (outv P).getD (i - 1) 0 := fun i h1 h2 => by
    rw [rd0 i (by omega_arith), m, wl_read _ _ _ 1 i h1 (by simp; omega_arith) (by simp)]
  have hK := hi.k1024
  obtain slots : ∀ d, 64 ≤ d → d + 4 ≤ frameBytes → t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
    fun d h1 h2 => fr.readW (r := slotR (P.lay h.D) d) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by omega_arith) (by unfold frameBytes at h2; omega_arith) (by decide)) (by decide)
  refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, hf, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(P.lay h.D).FR, List.mem_cons_self, Offset.sub_base _ (show 0 + 64 ≤ frameBytes by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact Lay.fr_sep (by decide) (by decide) (by decide)
  · rw [slots sC (by decide) (by decide)]; exact hb.1
  · rw [slots sLo (by decide) (by decide)]; exact hb.2.1
  · rw [slots sDb (by decide) (by decide)]; exact hb.2.2.1
  · rw [slots sAny (by decide) (by decide)]; exact hb.2.2.2
  obtain ⟨ps, hs1⟩ := hi.pubScr
  exact ⟨t0, t1, t2, t3, v0, v 1 (by decide) (by decide), v 2 (by decide) (by decide), v 3 (by decide) (by decide),
    v 4 (by decide) (by decide), v 5 (by decide) (by decide), hi.kv, hi.rlK, hi.el1, hi.elK, ps,
    by have := hi.scl32; omega_arith⟩

/-- What the call writes to `EM` and returns. -/
abbrev CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (State.addr (P.scr + BitVec.ofNat 32 oEm)) P.K r
      (Spec.Rsa.publicOpChecked P.nB P.eB (sigB P σ))

/-- After the call. -/
abbrev V2 (P : EP) (σ s : State) : Prop := M0 h P σ s ∧ CR P σ s.mem (s.gpr .r0)

/-- `EM` and the call's working space, in `scratch`. -/
theorem call_geo {P : EP} {σ : State} (hi : In h.D P σ) :
    State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm ∧
    State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa ∧
    Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩ P.SCR ∧
    Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩ P.SCR ∧
    Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩
      ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩ ∧
    P.scr.toNat + P.scl * 8 ≤ 2 ^ 32 ∧ 1025 ≤ P.scl ∧ P.K ≤ 1024 := by
  obtain hf := hi.ok.fits P.SCR (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hs := hi.pubScr.2
  have hK := hi.k1024
  obtain e1 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr + BitVec.ofNat 64 oEm :=
    addr_add (by unfold oEm; omega_arith)
  obtain e2 : State.addr (P.scr + BitVec.ofNat 32 oRsa) = State.addr P.scr + BitVec.ofNat 64 oRsa :=
    addr_add (by unfold oRsa; omega_arith)
  refine ⟨e1, e2, ?_, ?_, ?_, hf, hs, hK⟩
  · rw [e1]; exact Offset.sub_base _ (by unfold oEm; omega_arith)
  · rw [e2]; exact Offset.sub_base _ (by unfold oRsa; omega_arith)
  · rw [e1, e2]; exact Offset.disjoint _ (by unfold oEm oRsa; omega_arith) (by unfold oEm; omega_arith)
      (by unfold oRsa; omega_arith)

theorem call_pre {P : EP} {σ s : State} (hr : V1 h P σ s) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 104).pre
      (s.callEntry.withRegions (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
        (pdWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024))) := by
  obtain ⟨⟨hc, hi, -, -⟩, pa⟩ := hr
  have ok := hi.ok
  have hg := hi.geo
  obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
  have fit := ok.fit
  have hB := ok.B56
  obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
  obtain sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by show _ = (⟨State.addr P.sig, P.gl⟩ : Region); rw [hi.glK]
  obtain fs := fun {R : Region} (hR : R ∈ (P.lay h.D).ro ++ (P.lay h.D).rw) => ok.fits R hR
  obtain hfr : ∀ {R : Region}, R ∈ (P.lay h.D).ro ∨ R ∈ (P.lay h.D).rw → ∀ {d n : Nat}, d + n ≤ frameBytes + 56 →
      Region.Disjoint ⟨(P.lay h.D).fr d, n⟩ R := fun hR _ _ hd => ok.stk_fr hR hd
  refine pd_pre pa hc.st.sp hB (by simp only [frameBytes] at fit; omega_arith)
    (by rw [hg.scr_lt (by decide)]; unfold oEm; omega_arith)
    (by have := fs (R := P.PRE) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.E) (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this)
    (by have := fs (R := P.SIG) (by simp); simp only [Proof.X25519.Arm.addr_toNat] at this; rw [hi.glK] at this; omega_arith)
    (by rw [hg.scr_lt (Nat.le_refl _)]; unfold oRsa; omega_arith)
    ((ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).sub_left sI)
    ((ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).sub_left sI)
    (by rw [sigR]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).sub_left sI) dIS
    (by rw [q0]; exact ((hfr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 24) (by decide)).symm).sub_left sI)
    ((ok.rw_ro (w := P.SCR) (r := P.PRE) (by simp) (by simp)).symm.sub_right sS')
    ((ok.rw_ro (w := P.SCR) (r := P.E) (by simp) (by simp)).symm.sub_right sS')
    (by rw [sigR]; exact (ok.rw_ro (w := P.SCR) (r := P.SIG) (by simp) (by simp)).symm.sub_right sS')
    (by rw [q0]; exact ((hfr (R := P.SCR) (.inr (by simp)) (d := 0) (n := 24) (by decide)).symm).sub_left sS') ?_
  intro r hr
  have low : (⟨State.addr P.B - BitVec.ofNat 64 104, 104⟩ : Region) = (P.lay h.D).LOW := rfl
  rw [low]
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok.low_buf (R := P.PRE) (.inl (by simp))
  · exact ok.low_buf (R := P.E) (.inl (by simp))
  · rw [sigR]; exact ok.low_buf (R := P.SIG) (.inl (by simp))
  · rw [q0]; exact (Lay.fr_low (by decide)).symm
  · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sI
  · exact (ok.low_buf (R := P.SCR) (.inr (by simp))).sub_right sS'

theorem call_vp (P : EP) (c : PdImpl) : VP (V1 h P) (.call c.name c.code) (V2 h P) := by
  refine VP.callF c.verified c.stack (pdRd P.B P.pre P.e P.sig P.K P.el P.rl)
    (pdWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) (fun _ _ hr => call_pre h hr)
    (fun σ s hr => ?_) (fun σ s hr => ?_) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) (fun σ s s' hr rd wr sp fr _ po => ?_)
  · obtain ⟨⟨hc, hi, -, -⟩, -⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hf, hs1, hK⟩ := call_geo h hi
    obtain q0 : State.addr P.B = (P.lay h.D).fr 0 := by simp
    obtain sigR : (⟨State.addr P.sig, P.K⟩ : Region) = P.SIG := by show _ = (⟨State.addr P.sig, P.gl⟩ : Region); rw [hi.glK]
    obtain hro : ∀ R ∈ (P.lay h.D).ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hs.rd, ok.rd]; exact List.mem_append_left _ hR)
    obtain inS : ∀ {o n : Nat}, o + n ≤ P.scl * 8 → Covers [⟨State.addr P.scr + BitVec.ofNat 64 o, n⟩] s.wr :=
      fun hon => Covers.one ⟨P.SCR, by rw [hs.wr, ok.wr]; simp, Offset.contains_base _ hon (by omega_arith)⟩
    obtain wr' : Covers (pdWr (P.scr + BitVec.ofNat 32 oEm) (P.scr + BitVec.ofNat 32 oRsa) P.K (P.scl - 1024)) s.wr :=
      Covers.cons (by rw [e1]; exact inS (by unfold oEm; omega_arith)) (by rw [e2]; exact inS (by unfold oRsa; omega_arith))
    refine ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons ?_)) wr'.right, wr'⟩
    refine Covers.cons ?_ (Covers.cons ?_ Covers.nil)
    · rw [sigR]; exact hro P.SIG (by simp)
    · rw [q0]; exact (Covers.one (hs.inFr (by show 0 + 24 ≤ frameBytes; decide))).right
  · rw [hr.1.1.st.sp]; exact hr.1.2.1.ok.B56
  · exact pd_pub h₁.2 h₂.2 (by rw [h₁.1.1.st.sp, h₂.1.1.st.sp])
      (by rw [(h₁.1.1.st.ro_words (R := P.PRE) (by simp) rfl).trans h₁.1.2.1.pw,
        (h₂.1.1.st.ro_words (R := P.PRE) (by simp) rfl).trans h₂.1.2.1.pw])
      (by rw [(h₁.1.1.st.ro (R := P.E) (by simp)).trans h₁.1.2.1.eB, (h₂.1.1.st.ro (R := P.E) (by simp)).trans
        h₂.1.2.1.eB]) _ _
  · obtain ⟨⟨hc, hi, hf, hb⟩, pa⟩ := hr
    have ok := hi.ok
    have hs := hc.st
    obtain ⟨e1, e2, sI, sS', dIS, hfit, hs1, hK⟩ := call_geo h hi
    obtain low : FrameStack.belowA s.sp 104 = (P.lay h.D).LOW := by rw [hs.sp]; exact ok.low_eq
    rw [low] at fr
    have fr' : Frame [⟨State.addr (P.scr + BitVec.ofNat 32 oEm), P.K⟩,
        ⟨State.addr (P.scr + BitVec.ofNat 32 oRsa), (P.scl - 1024) * 8⟩, (P.lay h.D).LOW] s.mem s'.mem := fr
    obtain hct : Ctx (P.lay h.D) P.scr σ s' := hc.write fr' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨P.SCR, by simp, sI⟩
      · exact ⟨P.SCR, by simp, sS'⟩
      · exact ⟨(P.lay h.D).LOW, by simp, fun _ h => h⟩) (fun r hr => by
      have hg := hi.geo
      obtain ⟨σ', ok'⟩ := hg.ok
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)).sub_right sI
      · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := sS) (n := 4) (by show sS + 4 ≤ frameBytes + 56; decide)).sub_right sS'
      · exact Lay.fr_low (by decide) (by have := ok.B56; have := P.B.isLt; omega_arith)) rd wr sp
    obtain slots : ∀ d, d + 4 ≤ frameBytes → s'.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
      fun d hd => fr'.readW (r := slotR (P.lay h.D) d) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega_arith)).sub_right sI
        · exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (d := d) (n := 4) (by show d + 4 ≤ frameBytes + 56; unfold frameBytes at hd ⊢; omega_arith)).sub_right sS'
        · exact Lay.fr_low (by unfold frameBytes at hd; omega_arith) (by have := ok.B56; have := P.B.isLt; omega_arith)) (by decide)
    refine ⟨⟨hct, hi, hf, ?_, ?_, ?_, ?_⟩, fun hp => ?_⟩
    · rw [slots sC (by decide)]; exact hb.1
    · rw [slots sLo (by decide)]; exact hb.2.1
    · rw [slots sDb (by decide)]; exact hb.2.2.1
    · rw [slots sAny (by decide)]; exact hb.2.2.2
    have := pd_post pa po P.nB (nB_length hi) (by rw [(hs.ro_words (R := P.PRE) (by simp) rfl).trans hi.pw]; exact hp)
    rw [(hs.ro (R := P.E) (by simp)).trans hi.eB] at this
    obtain sg : Spec.Rsa.bytesAt s.mem (State.addr P.sig) P.K = sigB P σ := by
      obtain e := hs.ro (R := P.SIG) (by simp); dsimp only at e; rw [hi.glK] at e; exact e
    rw [sg] at this
    exact this

end VG.Proof.RsaPss.Arm.Vf

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: after the call

The pieces after the call are proven over the state `τ` the call leaves
(`VQ.reidx`), so that `EM`'s bytes are those of `τ` (`emv`). `acc` (`accW`):
`EM`'s last byte `⊕ 0xbc`, its first if `lo = 1`, and the top bits of
`maskedDB`'s first byte (`acc_vp`); then `DB = maskedDB ⊕ MGF1(H, dbLen)`
with its top bits cleared.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (andByte add_ofNat_sub_one away3_scr away3_slot away3_ctW Away3)

variable (h : PssHash)

/-- A state of a body is one the body may start from. -/
theorem St.ok_self {L : Lay} {σ s : State} (hs : L.St σ s) : L.Ok s :=
  { sp := hs.sp, rd := hs.rd.trans hs.ok.rd, wr := hs.wr.trans hs.ok.wr, B56 := hs.ok.B56, fit := hs.ok.fit,
    F8 := hs.ok.F8, nargs := hs.ok.nargs, A4 := hs.ok.A4, stk := hs.ok.stk, wro := hs.ok.wro, wrw := hs.ok.wrw,
    fits := hs.ok.fits, args := fun _ hj => hs.arg hj }

theorem In.self {P : EP} {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String}
    (Q : TF h g f fg dn P) {σ s : State} (hi : In h.D P σ) (hs : (P.lay h.D).St σ s) (sy : s.syms = σ.syms) :
    In h.D P s :=
  { ok := St.ok_self hs, kv := hi.kv, el1 := hi.el1, elK := hi.elK, glK := hi.glK, scrK := hi.scrK, rlK := hi.rlK,
    slt32 := hi.slt32, scl32 := hi.scl32, nB := (hs.ro (R := P.N) (by simp)).trans hi.nB,
    eB := (hs.ro (R := P.E) (by simp)).trans hi.eB, pw := (hs.ro_words (R := P.PRE) (by simp) rfl).trans hi.pw,
    htabT := Q.htk σ s hi.htabT sy fun o ho => by
      obtain ⟨R, hR, hc⟩ := hi.htbl; exact RsaOaep.Arm.St_roW hs hR (hc o ho),
    tabT := Q.tk σ s hi.tabT sy fun o ho => by
      obtain ⟨R, hR, hc⟩ := hi.tbl; exact RsaOaep.Arm.St_roW hs hR (hc o ho) }

/-- `EM`'s bytes, as the call leaves them. -/
abbrev emv (P : EP) (τ : State) (i : Nat) : Byte := τ.mem (sa P.scr (oEm + i))

/-- `acc`. -/
abbrev accW (P : EP) (τ : State) : BitVec 32 :=
  ((emv P τ (P.K - 1)).setWidth 32 ^^^ 0xbc ||| (emv P τ 0).setWidth 32 &&& (0 - BitVec.ofNat 32 (lo P))) |||
    (emv P τ (lo P)).setWidth 32 &&& (cW ((n0 P).setWidth 32) ^^^ 0xFF)

/-- After the call, over the state `τ` it leaves. -/
abbrev W0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ In h.D P τ ∧ fits h P ∧ Bm h P s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i

theorem w0_self {P : EP} {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String}
    (Q : TF h g f fg dn P) {σ s : State} (hv : V2 h P σ s) (sy : s.syms = σ.syms) : W0 h P s s := by
  obtain ⟨⟨hc, hi, hf, hb⟩, -⟩ := hv
  obtain hi' := In.self h Q hi hc.st sy
  exact ⟨⟨⟨hi'.ok, hc.st.sp, rfl, rfl, Frame.refl _ _⟩, hc.slotS⟩, hi', hf, hb, fun _ _ => rfl⟩

/-- What `acc` keeps. -/
abbrev Ka (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ Bm h P m ∧ m.readW ((P.lay h.D).fr sAcc) 32 = accW P τ

theorem acc0_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r4, .r5, .r6, .r7, .r12])
    (.block acc0) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The bounds of the encoding when everything fits. -/
theorem fitB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ eLen P + 1 ≤ dbN h P ∧ lo P + dbN h P + h.D + 1 = P.K ∧ P.K ≤ 1024 ∧ h.D ≤ 64 ∧ 0 < h.D ∧
      64 ≤ P.K := by
  have := hf.2
  have := hi.k1024
  have := hi.k64
  have := h.D_le
  have := h.N_le
  have := h.D_pos
  have : lo P ≤ 1 := by unfold lo; split <;> omega_arith
  refine ⟨this, ?_, ?_, hi.k1024, by omega_arith, h.D_pos, hi.k64⟩ <;> unfold dbN <;> omega_arith

/-- `acc`, to its slot. -/
theorem acc_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (W0 h P) (.seq (.block accSet) (.block acc0))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun τ s => W0 h P τ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧
      s.gpr .r7 = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) ∧ s.gpr .r4 = BitVec.ofNat 32 (lo P) ∧
      s.gpr .r6 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r5 = cW ((n0 P).setWidth 32) ∧ s.gpr .r12 = P.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hi, hf', hb, he⟩ => ?_)
    (VP.taint _ acc0_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hi, hf', hb, he⟩, r0, r7, r4, r6, r5, r12⟩ => ?_)
  · obtain ⟨a1, ra1, va1⟩ := argAt hi hc.st (j := 1) (by decide)
    replace va1 : s.mem.readW ((P.lay h.D).fr (arg 1)) 32 = BitVec.ofNat 32 P.K := va1
    obtain hw : WP isa (.block accSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r7 = P.scr + BitVec.ofNat 32 (oEm + P.K - 1) ∧
        t.gpr .r4 = BitVec.ofNat 32 (lo P) ∧ t.gpr .r6 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
        t.gpr .r5 = cW ((n0 P).setWidth 32) ∧ t.gpr .r12 = P.B := by
      prun [accSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a1, ra1, va1, arg_lt, hb.1, hb.2.1,
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        add_ofNat_sub_one (x := P.scr) (a := oEm + P.K) (by omega_arith)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t0, t7, t4, t6, t5, t12⟩ =>
      ⟨⟨hc.regs rd wr sp m, hi, hf', m ▸ hb, m ▸ he⟩, t0, t7, t4, t6, t5, t12⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2]
  · have aK : State.addr (P.scr + BitVec.ofNat 32 (oEm + P.K - 1)) = sa P.scr (oEm + (P.K - 1)) := by
      rw [hg.addr (by omega_arith)]; congr 2; omega_arith
    obtain a0 : State.addr (P.scr + BitVec.ofNat 32 oEm) = sa P.scr (oEm + 0) := hg.addr (by omega_arith)
    obtain al : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega_arith)
    obtain rK : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + (P.K - 1))) 1 := hg.rd hc.st (by omega_arith)
    obtain r0' : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + 0)) 1 := hg.rd hc.st (by omega_arith)
    obtain rl : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_arith)
    obtain hw : WP isa (.block acc0) s fun t => t.mem = s.mem.writeW ((P.lay h.D).fr sAcc) (accW P τ) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [acc0, mw, st, r0, r7, r4, r6, r5, r12, aK, a0, al, rK, r0', rl, he _ (show P.K - 1 < P.K by omega_arith),
        he 0 (by omega_arith), he (lo P) (by omega_arith), slotAt hi (d := sAcc) (by decide),
        hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide), dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    obtain fr : Frame [slotR (P.lay h.D) sAcc] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
    obtain ⟨σ', ok⟩ := hg.ok
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨hi, hf', ?_, by rw [m, Mem.readW_writeW_self32]⟩,
      fun i hi' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
    · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
    · rw [m]
      exact ⟨by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.1,
        by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.2.1,
        by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.1,
        by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hb.2.2.2⟩
    · rw [← he i hi']
      exact fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hg.slot ok (o := oEm + i) (n := 1) (d := sAcc) (k := 4) (by omega_arith) (by rw [hg.F]; decide)).symm _
          (Region.contains_self _ _)

/-- `H`, as the call leaves it. -/
abbrev seedV (P : EP) (τ : State) : List Byte := (List.range h.D).map fun i => emv P τ (lo P + dbN h P + i)

/-- The mask. -/
abbrev mkV (P : EP) (τ : State) : List Byte := Spec.Mgf1.mgf1 P.G (seedV h P τ) (dbN h P)

/-- `DB`, unmasked, with its top bits cleared. -/
abbrev dbF (P : EP) (τ : State) (i : Nat) : Byte :=
  if i = 0 then (emv P τ (lo P) ^^^ (mkV h P τ).getD 0 0) &&& (cW ((n0 P).setWidth 32)).setWidth 8
  else emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0

/-- After the unmasking. -/
abbrev U0 (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
    (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- What the unmasking keeps: `acc` and `EM`'s bytes. -/
abbrev Ku (P : EP) (τ s : State) : Prop :=
  Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧ ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i

theorem Ka.keep {P : EP} {τ : State} {m m' : Mem} {rs : List Region} (hk : Ka h P τ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (slotR (P.lay h.D) sC).Disjoint r ∧ (slotR (P.lay h.D) sLo).Disjoint r ∧
      (slotR (P.lay h.D) sDb).Disjoint r ∧ (slotR (P.lay h.D) sAny).Disjoint r ∧ (slotR (P.lay h.D) sAcc).Disjoint r) :
    Ka h P τ m' :=
  ⟨hk.1, hk.2.1, ⟨slot_keep hf (fun r hr => (hd r hr).1) hk.2.2.1.1,
    slot_keep hf (fun r hr => (hd r hr).2.1) hk.2.2.1.2.1, slot_keep hf (fun r hr => (hd r hr).2.2.1) hk.2.2.1.2.2.1,
    slot_keep hf (fun r hr => (hd r hr).2.2.2.1) hk.2.2.1.2.2.2⟩, slot_keep hf (fun r hr => (hd r hr).2.2.2.2) hk.2.2.2⟩

/-- MGF1's slots: its source `H` and its destination `DB`. -/
theorem vslots_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (Ku h P) (.block (mgfSlots h.sh))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (Ka h P τ s.mem ∧
        RsaOaep.Arm.Sl (P.lay h.D) P.scr (oEm + lo P + dbN h P) h.D (oEm + lo P) (dbN h P) s.mem) ∧
        ∀ i < P.K, s.mem (sa P.scr (oEm + i)) = emv P τ i) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, he⟩ => ?_
  let L := P.lay h.D
  obtain hw : WP isa (.block (mgfSlots h.sh)) s fun t =>
      t.mem = (((s.mem.writeW (L.fr Impl.RsaOaep.Arm.sDst) (P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 (lo P))).writeW
        (L.fr Impl.RsaOaep.Arm.sDstLen) (BitVec.ofNat 32 (dbN h P))).writeW (L.fr Impl.RsaOaep.Arm.sSrc)
          (P.scr + BitVec.ofNat 32 oEm + BitVec.ofNat 32 (lo P) + BitVec.ofNat 32 (dbN h P))).writeW
        (L.fr Impl.RsaOaep.Arm.sSrcLen) (BitVec.ofNat 32 h.D) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [mgfSlots, atDb, atS, addSlot, sp0, ld, mw, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS,
      hk.2.2.1.2.1, hk.2.2.1.2.2.1, movw_val (show oEm < 2 ^ 16 by decide),
      movw_val (show dig h.sh < 2 ^ 16 by show h.D < 2 ^ 16; omega_arith), Impl.RsaOaep.Arm.sSrc,
      Impl.RsaOaep.Arm.sSrcLen, Impl.RsaOaep.Arm.sDst, Impl.RsaOaep.Arm.sDstLen]
    rfl
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR L Impl.RsaOaep.Arm.sDst, slotR L Impl.RsaOaep.Arm.sDstLen, slotR L Impl.RsaOaep.Arm.sSrc,
      slotR L Impl.RsaOaep.Arm.sSrcLen] s.mem t.mem := by
    rw [m]
    exact ((((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))).trans ((slot_frame _ _ _ _).mono (by simp))
  obtain dS : ∀ r ∈ [slotR L Impl.RsaOaep.Arm.sDst, slotR L Impl.RsaOaep.Arm.sDstLen, slotR L Impl.RsaOaep.Arm.sSrc,
      slotR L Impl.RsaOaep.Arm.sSrcLen], ∀ o n, o + n ≤ oRsa → (sR P.scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  obtain hem : ∀ i < P.K, t.mem (sa P.scr (oEm + i)) = emv P τ i := fun i hi => by
    rw [← he i hi]
    exact fr _ fun r hr => dS r hr (oEm + i) 1 (by have := hi₀.k1024; pomega) _ (Region.contains_self _ _)
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨Ka.keep h hk fr fun r hr => ?_, ?_, ?_, ?_, ?_⟩,
    hem⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨slotSep (by decide) (by decide) (by decide),
      slotSep (by decide) (by decide) (by decide), slotSep (by decide) (by decide) (by decide),
      slotSep (by decide) (by decide) (by decide), slotSep (by decide) (by decide) (by decide)⟩
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [m, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]

/-- `maskedDB ⊕ MGF1(H, dbLen)`, by MGF1 with the hash function `g` of the
table `mgf1`. -/
theorem vmask_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ku h P τ s ∧ s.syms = τ.syms) (mgfPart fg h.sh 15)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^
          (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : Impl.RsaOaep.Arm.oBuf = 1024 := rfl
  have fit := hg.fit
  obtain fd : oEm + lo P + dbN h P ≤ Impl.RsaOaep.Arm.oBuf := by omega_arith
  obtain mp := RsaOaep.Arm.mpOf g hg (so := oEm + lo P + dbN h P) (sl := h.D) (dOff := oEm + lo P) (dl := dbN h P)
    hD0 (by omega_arith) (by omega_arith) fd (.inr (Nat.le_refl _)) (seed := seedV h P) (fun τ => by simp)
    (X := Ka h P) (fun τ m m' hk hf' => Ka.keep h hk hf' fun r hr =>
      ⟨RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
        RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
        RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
        RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr,
        RsaOaep.Arm.mgfW_slot g hg fd (by decide) (by decide) (by decide) r hr⟩)
    (j := 15) (by simp) hi₀.tbl (fun τ m hk => Q.t τ hk.1.tabT) Q.gne
  refine (VP.syms (vslots_vp h P ⟨σ₀, hi₀⟩)).seq ((RsaOaep.Arm.mgf_vp g mp (arg_lt (by decide))
    (dstv := fun τ i => emv P τ (lo P + i))).mono (fun τ s ⟨⟨hc, ⟨hk, hs⟩, he⟩, sy⟩ => ⟨⟨hc, ⟨hk, hs⟩,
      fun i hi => ?_, fun i hi => ?_⟩, sy⟩) fun τ s ⟨⟨hc, ⟨hk, _⟩, hd, hh⟩, sy⟩ => ⟨⟨hc, hk, by rw [mkV, Q.gG]; exact hd, hh⟩, sy⟩)
  · rw [Nat.add_assoc]; exact he _ (by omega_arith)
  · rw [Nat.add_assoc, Nat.add_assoc, he _ (by omega_arith)]; simp [hi, Nat.add_assoc]

/-- `maskedDB`'s first byte's top bits cleared. -/
theorem vtop_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^
          (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0)
      (.seq (.block topSet) (.block topAnd)) (U0 h P) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have fit := hg.fit
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Ka h P τ s.mem ∧
        (∀ i < dbN h P, s.mem (sa P.scr (oEm + lo P + i)) = emv P τ (lo P + i) ^^^ (mkV h P τ).getD i 0) ∧
        ∀ i < h.D, s.mem (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ s.gpr .r1 = cW ((n0 P).setWidth 32))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hd, hh⟩ => ?_)
    (VP.taint _ Sg.topAnd_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨⟨hc, hk, hd, hh⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block topSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = cW ((n0 P).setWidth 32) := by
      prun [topSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.2.2.1.1,
        hk.2.2.1.2.1, movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd, m ▸ hh⟩, r0, r1⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]
  · have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P)) = sa P.scr (oEm + lo P) := hg.addr (by omega_arith)
    obtain rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P)) 1 := hg.rd hc.st (by omega_arith)
    obtain wd : InRegions s.wr (sa P.scr (oEm + lo P)) 1 := hg.wr hc.st (by omega_arith)
    obtain hw : WP isa (.block topAnd) s fun t =>
        t.mem = s.mem.writeW (sa P.scr (oEm + lo P))
          (s.mem (sa P.scr (oEm + lo P)) &&& (cW ((n0 P).setWidth 32)).setWidth 8) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [topAnd, r0, r1, ad, rd, wd, dpVal, andByte]
    refine WP.mono hw fun t ⟨m, rd', wr', sp'⟩ => ?_
    obtain fr : Frame [sR P.scr (oEm + lo P) 1] s.mem t.mem := by
      rw [m]; exact frame_byte P.scr _ _ (Nat.le_refl _) (by omega_arith) (by omega_arith)
    obtain kk : ∀ d, d + 4 ≤ frameBytes → t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 :=
      fun d hd => by
        rw [slot_keep (v := s.mem.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith)
            (by rw [hg.F]; unfold frameBytes at hd ⊢; omega_arith)) rfl]
    obtain hb' : Bm h P t.mem := ⟨by rw [kk _ (by decide)]; exact hk.2.2.1.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.1,
      by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.1, by rw [kk _ (by decide)]; exact hk.2.2.1.2.2.2⟩
    obtain ha' : t.mem.readW ((P.lay h.D).fr sAcc) 32 = accW P τ := by rw [kk _ (by decide)]; exact hk.2.2.2
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', ⟨hk.1, hk.2.1, hb', ha'⟩,
      fun i hi => ?_, fun i hi => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by omega_arith) (by rw [hg.F]; decide)
    · rw [m, sa_write P.scr _ _ (by omega_arith) (by omega_arith)]
      unfold dbF
      by_cases e : i = 0
      · subst e
        rw [ite_eq_left (by omega_arith), ite_eq_left rfl, show oEm + lo P = oEm + lo P + 0 from rfl, hd 0 (by omega_arith),
          Nat.add_zero]
      · rw [ite_eq_right (by omega_arith), ite_eq_right e, hd i hi]
    · rw [m, sa_write P.scr _ _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith), hh i hi]

end VG.Proof.RsaPss.Arm.Vf

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the end of the padding

`scan_vp`: the scan of `DB` finds the index (`pzF`) and the value (`vzF`) of
its first byte that is not zero, if any (`nfW`), without a branch; then
`acc` takes in that this byte is `0x01` and, if a salt length is expected,
that the salt after it has that length (`pos_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (add_ofNat_sub_one)

variable (h : PssHash)

/-- `DB`, as a list. -/
abbrev dbL (P : EP) (τ : State) : List Byte := (List.range (dbN h P)).map (dbF h P τ)

/-- Where the padding ends. -/
abbrev lzF (P : EP) (τ : State) : Nat := RsaPss.lz (dbL h P τ)

/-- The index and value of `DB`'s first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzJ (P : EP) (τ : State) (j : Nat) : Nat := if lzF h P τ < j then lzF h P τ else 0
abbrev vzJ (P : EP) (τ : State) (j : Nat) : Byte := if lzF h P τ < j then dbF h P τ (lzF h P τ) else 0
abbrev nfJ (P : EP) (τ : State) (j : Nat) : BitVec 32 := if lzF h P τ < j then 0 else BitVec.allOnes 32

theorem bz : ∀ b : Byte, (b.setWidth 32 - 1) >>> 31 = if b = 0 then 1 else 0 := by decide

/-- After `j` bytes of the scan. -/
structure SC (P : EP) (τ : State) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + j)
  r1 : s.gpr .r1 = BitVec.ofNat 32 j
  lr : s.gpr .lr = BitVec.ofNat 32 (dbN h P - j)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (pzJ h P τ j)
  r5 : s.gpr .r5 = (vzJ h P τ j).setWidth 32
  r6 : s.gpr .r6 = nfJ h P τ j
  r7 : s.gpr .r7 = 0

theorem scanBody_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block scanBody) hc).isSome = true := ⟨_, by taint_decide⟩

theorem dbL_getD {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) : (dbL h P τ).getD j 0 = dbF h P τ j := by
  simp [dbL, List.getD_eq_getElem?_getD, hj]

/-- One byte of the scan. -/
theorem scan_step {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) (b : Byte) (hb : b = dbF h P τ j) :
    let r3 : BitVec 32 := if b = 0 then 1 else 0
    let r8 := (r3 - 1) &&& nfJ h P τ j
    BitVec.ofNat 32 (pzJ h P τ j) ||| BitVec.ofNat 32 j &&& r8 = BitVec.ofNat 32 (pzJ h P τ (j + 1)) ∧
    (vzJ h P τ j).setWidth 32 ||| b.setWidth 32 &&& r8 = (vzJ h P τ (j + 1)).setWidth 32 ∧
    nfJ h P τ j &&& (0 - r3) = nfJ h P τ (j + 1) := by
  intro r3 r8
  have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  have za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  have oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  have hlt : lzF h P τ ≤ dbN h P := by
    have e := RsaPss.lz_le (dbL h P τ)
    rw [show (dbL h P τ).length = dbN h P by simp [dbL]] at e
    exact e
  rcases Nat.lt_trichotomy (lzF h P τ) j with hl | hl | hl
  · have h8 : r8 = 0 := by simp only [r8, nfJ, ite_eq_left hl, az]
    simp only [h8, az, oz, pzJ, vzJ, nfJ, ite_eq_left hl, ite_eq_left (by omega_arith : lzF h P τ < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← dbL_getD h (by omega_arith)]
      exact RsaPss.getD_lz_ne (by
        show lzF h P τ < (dbL h P τ).length
        rw [show (dbL h P τ).length = dbN h P by simp [dbL]]; omega_arith)
    have h3 : r3 = 0 := by simp only [r3, hne, ite_false]
    have h8 : r8 = BitVec.allOnes 32 := by
      simp only [r8, h3, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_arith)]; decide
    simp only [h8, h3, BitVec.and_allOnes, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_arith),
      ite_eq_left (show lzF h P τ < j + 1 by omega_arith)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← dbL_getD h hj]; exact RsaPss.getD_lt_lz hl
    have h3 : r3 = 1 := by simp only [r3, hz, ite_true]
    have h8 : r8 = 0 := by
      simp only [r8, h3]; rw [show (1 : BitVec 32) - 1 = 0 by decide, za]
    simp only [h8, h3, az, oz, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_arith),
      ite_eq_right (show ¬ lzF h P τ < j + 1 by omega_arith)]
    exact ⟨trivial, trivial, by decide⟩

/-- The scan of `DB`. -/
theorem scan_vp (P : EP) (hP : ∃ σ, In h.D P σ) {X : State → Mem → Prop}
    (hX : ∀ τ m, X τ m → ∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧ fits h P ∧ SC h P τ 0 s)
      (countLoop scanBody)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  let I : Nat → State → State → Prop := fun k τ s => k ≤ dbN h P ∧ Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧
    fits h P ∧ SC h P τ (dbN h P - k) s
  refine (VP.loop (I := I) (fun k => ?_) (dbN h P - 1)).mono (fun τ s ⟨hc, hx, hf', hs⟩ => ⟨by omega_arith, hc, hx, hf',
    by rw [show dbN h P - (dbN h P - 1 + 1) = 0 by omega_arith]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨hk, hc, hx, hf', hs⟩ => ?_
  · obtain ⟨-, -, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : dbN h P - (k + 1) = j at hs
  have hjn : j < dbN h P := by omega_arith
  have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P + j)) = sa P.scr (oEm + lo P + j) := hg.addr (by omega_arith)
  have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P + j)) 1 := hg.rd hc.st (by omega_arith)
  have lr1 : BitVec.ofNat 32 (dbN h P - j) - 1 = BitVec.ofNat 32 (dbN h P - (j + 1)) := by
    rw [show dbN h P - j = (dbN h P - (j + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  have hw : WP isa (.block scanBody) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + (j + 1)) ∧ t.gpr .r1 = BitVec.ofNat 32 (j + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (dbN h P - (j + 1)) ∧
      t.gpr .r4 = BitVec.ofNat 32 (pzJ h P τ j) ||| BitVec.ofNat 32 j &&&
        ((if dbF h P τ j = 0 then 1 else 0) - 1 &&& nfJ h P τ j) ∧
      t.gpr .r5 = (vzJ h P τ j).setWidth 32 ||| (dbF h P τ j).setWidth 32 &&&
        ((if dbF h P τ j = 0 then 1 else 0) - 1 &&& nfJ h P τ j) ∧
      t.gpr .r6 = nfJ h P τ j &&& (0 - if dbF h P τ j = 0 then 1 else 0) ∧ t.gpr .r7 = 0 ∧
      t.z = decide (dbN h P - (j + 1) = 0) := by
    prun [scanBody, hs.r0, hs.r1, hs.lr, hs.r4, hs.r5, hs.r6, hs.r7, ad, rd, hX τ s.mem hx j hjn, bz, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · exact VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32 _
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  refine WP.mono hw fun t ⟨m, rd', wr, sp, r0, r1, lr, r4, r5, r6, r7, z⟩ => ?_
  have st := scan_step h hjn _ rfl (τ := τ)
  have hc' : Ctx (P.lay h.D) P.scr τ t := hc.regs rd' wr sp m
  have hx' : X τ t.mem := m ▸ hx
  have sk : SC h P τ (j + 1) t :=
    ⟨r0, r1, lr, by rw [r4]; exact st.1, by rw [r5]; exact st.2.1, by rw [r6]; exact st.2.2, r7⟩
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show dbN h P - (j + 1) = k by omega_arith]; cases k <;> simp,
    fun h0 => ⟨hc', hx', hf', by rw [show dbN h P = j + 1 by omega_arith]; exact sk⟩,
    fun hpos => ⟨by omega_arith, hc', hx', hf', by rw [show dbN h P - k = j + 1 by omega_arith]; exact sk⟩⟩

end VG.Proof.RsaPss.Arm.Vf

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the scan's result

The scan's registers (`scanSet_vp`); then `acc` takes in that `DB`'s first
nonzero byte is `0x01` and, if a salt length is expected, that the salt after
it has that length (`acc2`), and its index goes to its slot (`pos_vp`); then
the flags of `any_salt_len = 0` (`anySet_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- What the scan keeps. -/
abbrev Kd (P : EP) (τ : State) (m : Mem) : Prop :=
  Ka h P τ m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    ∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0

/-- The scan's registers. -/
theorem scanSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (U0 h P) (.block scanSet)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ 0 s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun τ s ⟨hc, hk, hd, hh⟩ => ?_
  have hw : WP isa (.block scanSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧ t.gpr .r1 = BitVec.ofNat 32 0 ∧
      t.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧ t.gpr .r4 = BitVec.ofNat 32 0 ∧ t.gpr .r5 = BitVec.ofNat 32 0 ∧
      t.gpr .r6 = BitVec.ofNat 32 0 - 1 ∧ t.gpr .r7 = BitVec.ofNat 32 0 := by
    prun [scanSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.2.2.1.2.1,
      hk.2.2.1.2.2.1, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show 0 < 2 ^ 16 by decide),
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r4, r5, r6, r7⟩ =>
    ⟨hc.regs rd wr sp m, m ▸ ⟨hk, hd, hh⟩, hk.2.1, ⟨by rw [r0, Nat.add_zero], r1, by rw [lr, Nat.sub_zero], ?_, ?_, ?_, r7⟩⟩
  · rw [r4]; simp only [pzJ, Nat.not_lt_zero, ite_false]
  · rw [r5]; simp only [vzJ, Nat.not_lt_zero, ite_false]; rfl
  · rw [r6]; simp only [nfJ, Nat.not_lt_zero, ite_false]; decide

/-- `[any_salt_len ≠ 0]`. -/
abbrev anyW (P : EP) : BitVec 32 := if P.any = 0 then 0 else 1

/-- The index of `DB`'s first nonzero byte, 0 if none. -/
abbrev pzF (P : EP) (τ : State) : Nat := pzJ h P τ (dbN h P)

/-- `acc` after the scan. -/
abbrev acc2 (P : EP) (τ : State) : BitVec 32 :=
  (accW P τ ||| ((vzJ h P τ (dbN h P)).setWidth 32 ^^^ (1 : BitVec 32) ||| nfJ h P τ (dbN h P) >>> 31)) |||
    ((BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) - 1 ^^^ BitVec.ofNat 32 P.slt) &&& (anyW P - 1))

/-- What the paths after the scan keep. -/
abbrev B2 (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧ m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P)

/-- What the paths keep: not `c` and `any_salt_len`, whose slots the shift
reuses. -/
abbrev K2 (P : EP) (τ : State) (m : Mem) : Prop :=
  In h.D P τ ∧ fits h P ∧ B2 h P m ∧ (∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) ∧
    (∀ i < h.D, m (sa P.scr (oEm + lo P + dbN h P + i)) = (seedV h P τ).getD i 0) ∧
    m.readW ((P.lay h.D).fr sPos) 32 = BitVec.ofNat 32 (pzF h P τ) ∧
    m.readW ((P.lay h.D).fr sAcc) 32 = acc2 h P τ

theorem posChk_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r12])
    (.block posChk) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `acc` and `pos` to their slots. -/
theorem pos_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s)
      (.seq (.block posSet) (.block posChk))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧
        s.mem.readW ((P.lay h.D).fr sAny) 32 = anyW P) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kd h P τ s.mem ∧ fits h P) ∧
      s.gpr .r4 = BitVec.ofNat 32 (pzF h P τ) ∧ s.gpr .r5 = (vzJ h P τ (dbN h P)).setWidth 32 ∧
      s.gpr .r6 = nfJ h P τ (dbN h P) ∧
      s.gpr .r1 = accW P τ ∧ s.gpr .r2 = BitVec.ofNat 32 (dbN h P) ∧ s.gpr .r3 = BitVec.ofNat 32 P.slt ∧
      s.gpr .r8 = anyW P ∧ s.gpr .r12 = P.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hf, hs⟩ => ?_)
    (VP.taint _ posChk_cert (fun _ _ _ _ h₁ h₂ r hr => ?_)
      fun τ s ⟨⟨hc, hk, hf⟩, r4, r5, r6, r1, r2, r3, r8, r12⟩ => ?_)
  · have hi := hk.1.1
    obtain ⟨a7, ra7, va7⟩ := argAt hi hc.st (j := 8) (by decide)
    replace va7 : s.mem.readW ((P.lay h.D).fr (arg 8)) 32 = BitVec.ofNat 32 P.slt := va7
    have hw : WP isa (.block posSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r4 = BitVec.ofNat 32 (pzF h P τ) ∧ t.gpr .r5 = (vzJ h P τ (dbN h P)).setWidth 32 ∧
        t.gpr .r6 = nfJ h P τ (dbN h P) ∧
        t.gpr .r1 = accW P τ ∧ t.gpr .r2 = BitVec.ofNat 32 (dbN h P) ∧ t.gpr .r3 = BitVec.ofNat 32 P.slt ∧
        t.gpr .r8 = anyW P ∧ t.gpr .r12 = P.B := by
      prun [posSet, sp0, ld, hc.st.sp, a7, ra7, va7, arg_lt, hc.aFr hg, hc.rFr hg, hk.1.2.2.2, hk.1.2.2.1.2.2.1,
        hk.1.2.2.1.2.2.2, hs.r4, hs.r5, hs.r6]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, t4, t5, t6, t1, t2, t3, t8, t12⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hk, hf⟩, t4, t5, t6, t1, t2, t3, t8, t12⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2]
  · have hi := hk.1.1
    have hw : WP isa (.block posChk) s fun t =>
        t.mem = (s.mem.writeW ((P.lay h.D).fr sPos) (BitVec.ofNat 32 (pzF h P τ))).writeW ((P.lay h.D).fr sAcc)
          (acc2 h P τ) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [posChk, st, r1, r2, r3, r4, r5, r6, r8, r12, slotAt hi (d := sAcc) (by decide),
        slotAt hi (d := sPos) (by decide), hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide),
        hc.st.inFr (d := sPos) (n := 4) (by show sPos + 4 ≤ frameBytes; decide), dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [slotR (P.lay h.D) sPos, slotR (P.lay h.D) sAcc] s.mem t.mem := by
      rw [m]
      exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
    obtain ⟨σ', ok⟩ := hg.ok
    have kk : ∀ d, d + 4 ≤ frameBytes → (d + 4 ≤ sAcc ∨ sPos + 4 ≤ d) →
        t.mem.readW ((P.lay h.D).fr d) 32 = s.mem.readW ((P.lay h.D).fr d) 32 := fun d hd hd' => by
      rw [m, slot_ww _ _ hd (by decide) (by unfold sAcc sPos at hd'; unfold sAcc; omega_arith),
        slot_ww _ _ hd (by decide) (by unfold sAcc sPos at hd'; unfold sPos; omega_arith)]
    have kb : ∀ o, o + 1 ≤ oRsa → t.mem (sa P.scr o) = s.mem (sa P.scr o) := fun o ho =>
      fr _ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hg.slot ok (o := o) (n := 1) (by omega_arith) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
        · exact (hg.slot ok (o := o) (n := 1) (by omega_arith) (by rw [hg.F]; decide)).symm _ (Region.contains_self _ _)
    obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
    have e1 : oEm = 0 := rfl
    have e2 : oRsa = 8192 := rfl
    refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hi, hf,
      ⟨by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.1,
        by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.2.1⟩,
      fun i hi' => by rw [kb _ (by omega_arith)]; exact hk.2.1 i hi',
      fun i hi' => by rw [kb _ (by omega_arith)]; exact hk.2.2 i hi', ?_, by rw [m, Mem.readW_writeW_self32]⟩,
      by rw [kk _ (by decide) (by decide)]; exact hk.1.2.2.1.2.2.2⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

/-- The flags of `any_salt_len = 0`. -/
theorem anySet_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧
        s.mem.readW ((P.lay h.D).fr sAny) 32 = anyW P) (.block anySet)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem) ∧ s.z = decide (P.any = 0)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun τ s ⟨⟨hc, hk⟩, ha⟩ => ?_
  have hw : WP isa (.block anySet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (P.any = 0) := by
    prun [anySet, sp0, ld, hc.st.sp, hc.aFr hg, hc.rFr hg, ha]
    by_cases e : P.any = 0#32 <;> simp [e, anyW]
  exact WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, z⟩

end VG.Proof.RsaPss.Arm.Vf

end

end

/-! ### `RsaPss.Arm.VfTail`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the end of both paths

Whichever path put `M'` in `Y` (`msg`), with its length and blocks in their
slots: its hash compared with `H`, and the result, 1 exactly when `acc` is
zero and the hashes are equal (`tail_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- Away from what `K2` reads. -/
abbrev Away2 (L : Lay) (scr : BitVec 32) (r : Region) : Prop :=
  (slotR L sLo).Disjoint r ∧ (slotR L sDb).Disjoint r ∧ (slotR L sPos).Disjoint r ∧ (slotR L sAcc).Disjoint r ∧ (sR scr oEm 1024).Disjoint r

theorem K2.keep {P : EP} {τ : State} {m m' : Mem} {rs : List Region} (hk : K2 h P τ m) (hf : Frame rs m m')
    (ha : ∀ r ∈ rs, Away2 (P.lay h.D) P.scr r) : K2 h P τ m' := by
  obtain ⟨hi, hfi, ⟨b2, b3⟩, hd, hh, hp, hac⟩ := hk
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hfi
  have kb : ∀ x < 1024, m' (sa P.scr (oEm + x)) = m (sa P.scr (oEm + x)) := fun x hx =>
    sbytes_keep hf (o := oEm) (n := 1024) (fun r hr => (ha r hr).2.2.2.2) (by decide)
      (f := fun i => m (sa P.scr (oEm + i))) (fun _ _ => rfl) x hx
  refine ⟨hi, hfi, ⟨slot_keep hf (fun r hr => (ha r hr).1) b2, slot_keep hf (fun r hr => (ha r hr).2.1) b3⟩,
    fun i hi' => ?_, fun i hi' => ?_, slot_keep hf (fun r hr => (ha r hr).2.2.1) hp,
    slot_keep hf (fun r hr => (ha r hr).2.2.2.1) hac⟩
  · have e := kb (lo P + i) (by omega_using [hsum, hK, hi'])
    rw [← Nat.add_assoc] at e
    rw [e]; exact hd i hi'
  · have e := kb (lo P + dbN h P + i) (by omega_using [hsum, hK, hi'])
    rw [show oEm + (lo P + dbN h P + i) = oEm + lo P + dbN h P + i by omega_using []] at e
    rw [e]; exact hh i hi'

theorem away2_ctW {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctW h L scr T, Away2 L scr r := fun r hr =>
  ⟨ctW_slot h hg hT (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) r hr,
    ctW_em h hg hT (by decide) r hr⟩

/-- What `ctHash` keeps, with `M'`'s length and blocks in their slots. -/
abbrev Kt (P : EP) (msg : State → List Byte) (nbm : Nat) (τ : State) (m : Mem) : Prop :=
  K2 h P τ m ∧ m.readW ((P.lay h.D).fr sL) 32 = BitVec.ofNat 32 (msg τ).length ∧
    m.readW ((P.lay h.D).fr sNb) 32 = BitVec.ofNat 32 nbm

/-- The hash of `x` is `H`. -/
abbrev HOk (P : EP) (τ : State) (x : List Byte) : Prop :=
  ∀ i < h.D, (h.ok.SH.H.hash x).getD i 0 = (seedV h P τ).getD i 0

theorem res_eq (x : BitVec 32) : (x ||| 0 - x) >>> 31 ^^^ 1 = if x = 0 then 1 else 0 := by
  rw [BitVec.or_comm, nzW]
  by_cases e : x = 0
  · rw [ite_eq_left e, ite_eq_left e]; decide
  · rw [ite_eq_right e, ite_eq_right e]; decide

/-- The hash of `M'` compared with `H`, and the result. -/
theorem tail_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ τ, (msg τ).length + 1 + h.L ≤ nbm * h.B) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa P.scr (oY + i)) = (msg τ).getD i 0) ∧ s.syms = τ.syms)
      (.seq (ctHash f h.sh 14) (cmpH h.sh))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (msg τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oDig = 4928 := rfl
  refine (ctHash_vp h hg (j := 14) (by simp) (arg_lt (by decide)) hi₀.htbl Q.fne hnb hnb0 hfit (Inv := Kt h P msg nbm)
    (fun τ m m' hk hf' => ⟨K2.keep h hk.1 hf' (away2_ctW h hg hnb),
      slot_keep hf' (ctW_slot h hg hnb (by decide) (by decide)) hk.2.1,
      slot_keep hf' (ctW_slot h hg hnb (by decide) (by decide)) hk.2.2⟩)
    (fun τ m hk => hk.2.1) (fun τ m hk => hk.2.2) (fun τ m hk => Q.ht τ hk.1.1.htabT)).seq (VP.syms ?_)
  show VP _ (.seq (.block (cmpSet h.sh)) (.seq Impl.Bignum.Arm.compareBytes (.block result))) _
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        ∀ i < h.D, s.mem (sa P.scr (oDig + i)) = (h.ok.SH.H.hash (msg τ)).getD i 0) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 oDig ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧
      s.gpr .lr = BitVec.ofNat 32 h.D ∧ s.gpr .r2 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hd⟩ => ?_)
    (VP.seq (G := fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P msg nbm τ s.mem ∧
        (s.gpr .r2 = 0 ↔ HOk h P τ (msg τ)))
      ((cmp_vp (hg.rbuf (o := oDig) (n := h.D) (by omega_using [hD, e2, e3]) hD0)
        (hg.rbuf (o := oEm + lo P + dbN h P) (n := h.D) (by omega_using [hsum, hK, e1, e2]) hD0) hD0 (Inv := Kt h P msg nbm)
        (f := fun τ i => (h.ok.SH.H.hash (msg τ)).getD i 0) (g := fun τ i => (seedV h P τ).getD i 0)).mono
        (fun τ s ⟨⟨hc, hk, hd⟩, r0, r1, lr, r2⟩ => ⟨hc, hk, r0, r1, lr, r2, fun i hi => ?_, fun i hi => ?_⟩)
        fun τ s h' => h')
      (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hr⟩ => ?_))
  · have hw : WP isa (.block (cmpSet h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 oDig ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P) ∧
        t.gpr .lr = BitVec.ofNat 32 h.D ∧ t.gpr .r2 = 0 := by
      prun [cmpSet, atDb, atS, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1.1,
        hk.1.2.2.1.2, movw_val (show oEm < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide),
        movw_val (show 0 < 2 ^ 16 by decide), movw_val (show dig h.sh < 2 ^ 16 by show h.D < 2 ^ 16; omega_using [hD]),
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rfl
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hd⟩, r0, r1, lr, r2⟩
  · rw [hg.byteAt_scr (by omega_using [hD, e2, e3, hi])]; exact hd i hi
  · rw [hg.byteAt_scr (by omega_using [hsum, hK, e1, e2, hi])]; exact hk.1.2.2.2.2.1 i hi
  · have hw : WP isa (.block result) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = ((acc2 h P τ ||| s.gpr .r2) ||| 0 - (acc2 h P τ ||| s.gpr .r2)) >>> 31 ^^^ 1 := by
      prun [result, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.2.2.2.2,
        movw_val (show 0 < 2 ^ 16 by decide), dpVal]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0⟩ => ⟨hc.regs rd wr sp m, m ▸ hk.1, ?_⟩
    have oz : ∀ x y : BitVec 32, (x ||| y = 0) ↔ (x = 0 ∧ y = 0) := fun x y => BitVec.or_eq_zero_iff
    rw [r0, res_eq]
    simp only [oz, hr]

end VG.Proof.RsaPss.Arm.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the start of both paths

`Y` cleared and `mHash` after its 8 zero bytes (`yDig_vf`), keeping `K2`
through writes away from what it reads (`Away2`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

variable (h : PssHash)

theorem away2_scr {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa)
    (he : oEm + 1024 ≤ o ∨ o + n ≤ oEm) : Away2 L scr (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    Geo.sep (by omega_using [he]) (by decide) ho⟩

theorem away2_slot {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₂ : d + 4 ≤ sLo ∨ sLo + 4 ≤ d) (h₃ : d + 4 ≤ sDb ∨ sDb + 4 ≤ d) (h₅ : d + 4 ≤ sPos ∨ sPos + 4 ≤ d) (h₆ : d + 4 ≤ sAcc ∨ sAcc + 4 ≤ d) :
    Away2 L scr (slotR L d) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨slotSep (by decide) hd (by omega_using [h₂]), slotSep (by decide) hd (by omega_using [h₃]), slotSep (by decide) hd (by omega_using [h₅]),
    slotSep (by decide) hd (by omega_using [h₆]),
    (hg.slot ok (o := oEm) (n := 1024) (by decide) (by rw [hg.F]; omega_using [hd])).symm⟩

theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  have hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  exact ⟨hf, by omega_using [hD], ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `Y`: 8 zero bytes and `mHash`. -/
abbrev Y1 (P : EP) (τ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- `Y` cleared and `mHash` after its 8 zero bytes. -/
theorem yDig_vf (P : EP) (hP : ∃ σ, In h.D P σ) (Q : Prop) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ Q) (yDig h.sh 4)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ Q) ∧ Y1 h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 4) (dgP := P.dig) (by decide) (by simp) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.Arm.bytesAt_length _ _ _) (fun σ s hc i hi => ?_) (X := fun τ m => K2 h P τ m ∧ Q)
    fun σ m m' ⟨hk, hq⟩ hf => ⟨K2.keep h hk hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by decide) (by decide), hq⟩).mono
    (fun σ s ⟨hc, hk, hq⟩ => ⟨hc, hk, hq⟩) fun σ s h' => h'
  have e : Spec.Rsa.bytesAt s.mem (State.addr P.dig) h.D = Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (State.addr P.dig + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD hi]

end VG.Proof.RsaPss.Arm.Vf

end

end

/-! ### `RsaPss.Arm.VfAny`, which the modules that import this one used -/

section

/-! ### `RsaPss.Arm.VfShift`, which only this module used -/

section

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the shift

`DB`, copied after `mHash` in `Y`, shifted left by `a = pos + 1` bytes in ten
passes: pass `p` shifts by `2^p` if bit `p` of `a` is set (`onePass_vp`), so
that after `p` passes byte `j` is byte `j + a mod 2^p` of `DB`, zeros after
its end (`SH`); after ten, `a < 2^10` (`shift_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- Byte `i` of `DB`, zero after its end. -/
abbrev Dp (P : EP) (τ : State) (i : Nat) : Byte := if i < dbN h P then dbF h P τ i else 0

/-- The shift's distance. -/
abbrev aV (P : EP) (τ : State) : Nat := pzF h P τ + 1

/-- What the shift keeps. -/
abbrev Kq (P : EP) (τ : State) (m : Mem) : Prop :=
  K2 h P τ m ∧ ∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0

/-- After `p` passes. -/
abbrev SH (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ p)

theorem pzF_lt {P : EP} {τ : State} (hdb : 1 ≤ dbN h P) : pzF h P τ < dbN h P := by
  unfold pzF pzJ; split <;> omega_arith

/-- The bounds a pass needs. -/
theorem shB {P : EP} {σ : State} (hi : In h.D P σ) (hf : fits h P) :
    lo P ≤ 1 ∧ 1 ≤ dbN h P ∧ dbN h P + h.D ≤ 1023 ∧ h.D ≤ 64 ∧ 0 < h.D := by
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi hf
  exact ⟨hlo, by omega_arith, by omega_arith, hD, hD0⟩

/-- A pass's registers. -/
theorem passSet_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (.block (passSet h.sh))
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .r2 = maskOf (aV h P τ / 2 ^ p % 2 = 1)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  have hpz := pzF_lt h (τ := τ) hdb
  have hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have e3 : oY = 1024 := rfl
  have haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega_arith
  have hav : aV h P τ / 2 ^ p < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  have hw : WP isa (.block (passSet h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      t.gpr .r1 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ t.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧
      t.gpr .r2 = 0 - (BitVec.ofNat 32 (aV h P τ / 2 ^ p) &&& 1) := by
    prun [passSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hs.1, hs.2.1, hk.1.2.2.1.2,
      movw_val (show oY + 8 + dig h.sh < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega_arith),
      movw_val (show 0 < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat, dpVal]
    rfl
  exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ =>
    ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hs⟩, r0, r1, lr, by rw [r2, mask_bit hav]⟩

/-- Between a pass's bytes and its next stage: the slots of pass `p`, the
bytes of pass `p + 1`. -/
abbrev SM (P : EP) (τ : State) (p : Nat) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sA) 32 = BitVec.ofNat 32 (aV h P τ / 2 ^ p) ∧
    m.readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) ∧
    m.readW ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) ∧
    ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ % 2 ^ (p + 1))

/-- A pass's bytes. -/
theorem passMid_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) ∧
        s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        s.gpr .r1 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D + 2 ^ p) ∧ s.gpr .lr = BitVec.ofNat 32 (dbN h P) ∧
        s.gpr .r2 = maskOf (aV h P τ / 2 ^ p % 2 = 1))
      (countLoop passBody)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  obtain hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  have e1 : oEm = 0 := rfl
  refine (pass_vp hg (o := oY + 8 + h.D) (d := 2 ^ p) (n := dbN h P) (by omega_arith) hp0 (by omega_arith)
    (c := fun τ => aV h P τ / 2 ^ p % 2 = 1) (X := fun τ m => Kq h P τ m ∧ SH h P τ p m)).mono
    (fun τ s ⟨⟨hc, hk, hs⟩, r0, r1, lr, r2⟩ => ⟨hc, ⟨hk, hs⟩, r0, r1, lr, r2⟩)
    fun τ s ⟨hc, m₀, ⟨hk, hs⟩, fr, hsel⟩ => ?_
  obtain away : ∀ r ∈ [sR P.scr (oY + 8 + h.D) (dbN h P)], Away2 (P.lay h.D) P.scr r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_arith) (by omega_arith)
  obtain ks : ∀ d, d + 4 ≤ frameBytes → s.mem.readW ((P.lay h.D).fr d) 32 = m₀.readW ((P.lay h.D).fr d) 32 :=
    fun d hd => slot_keep (v := m₀.readW ((P.lay h.D).fr d) 32) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hg.slot ok (by omega_arith) (by rw [hg.F]; omega_arith)) rfl
  refine ⟨hc, ⟨K2.keep h hk.1 fr away, sbytes_keep fr (fun r hr => ?_) (by omega_arith) hk.2⟩,
    by rw [ks _ (by decide)]; exact hs.1, by rw [ks _ (by decide)]; exact hs.2.1,
    by rw [ks _ (by decide)]; exact hs.2.2.1, fun j hj => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ms := mod_succ (aV h P τ) p
  by_cases e : j < dbN h P
  · rw [hsel j e]
    by_cases hc' : aV h P τ / 2 ^ p % 2 = 1
    · rw [ite_eq_left hc', show oY + 8 + h.D + 2 ^ p + j = oY + 8 + h.D + (2 ^ p + j) by omega_arith,
        hs.2.2.2 _ (by omega_arith)]
      congr 1; rw [ms, hc']; omega_arith
    · rw [ite_eq_right hc', hs.2.2.2 _ hj]
      congr 1; rw [ms, show aV h P τ / 2 ^ p % 2 = 0 by omega_arith]; omega_arith
  · have hm : s.mem (sa P.scr (oY + 8 + h.D + j)) = m₀ (sa P.scr (oY + 8 + h.D + j)) :=
      fr _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
          (Region.contains_self _ _)
    rw [hm, hs.2.2.2 j hj]; unfold Dp; rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

/-- The bytes and the slots after a pass. -/
theorem keep3 (P : EP) (hg : Geo (P.lay h.D) P.scr) {τ : State} {m m' : Mem}
    (hf : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] m m') (hk : Kq h P τ m)
    {f : Nat → Byte} (hy : ∀ j < 2040 - h.D, m (sa P.scr (oY + 8 + h.D + j)) = f j) :
    Kq h P τ m' ∧ ∀ j < 2040 - h.D, m' (sa P.scr (oY + 8 + h.D + j)) = f j := by
  obtain ⟨σ', ok⟩ := hg.ok
  have e3 : oY = 1024 := rfl
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  obtain aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  refine ⟨⟨K2.keep h hk.1 hf fun r hr => ?_, sbytes_keep hf (aw _ _ (by omega_arith)) (by omega_arith) hk.2⟩,
    sbytes_keep hf (aw _ _ (by omega_arith)) (by omega_arith) hy⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The next pass's slots, and the flags of whether it was the last. -/
theorem passNext_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SM h P τ p s.mem) (.block passNext)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.z = decide (10 - (p + 1) = 0)) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hs⟩ => ?_
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hk.1.1 hk.1.2.1
  obtain hpz := pzF_lt h (τ := τ) hdb
  obtain haV : aV h P τ < 1024 := by show pzF h P τ + 1 < 1024; omega_arith
  obtain hp9 : 2 ^ p ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain ea : BitVec.ofNat 32 (aV h P τ / 2 ^ p) >>> 1 = BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)), Nat.div_div_eq_div_mul,
      Nat.pow_one, ← Nat.pow_succ]
  obtain ed : BitVec.ofNat 32 (2 ^ p) + BitVec.ofNat 32 (2 ^ p) = BitVec.ofNat 32 (2 ^ (p + 1)) := by
    rw [BitVec.ofNat_add_ofNat, Nat.pow_succ]; congr 1; omega_arith
  obtain ec : BitVec.ofNat 32 (10 - p) - 1 = BitVec.ofNat 32 (10 - (p + 1)) := by
    rw [show 10 - p = (10 - (p + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  obtain hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
  have hi := hk.1.1
  obtain w1 : ∀ v, (s.mem.writeW ((P.lay h.D).fr sA) v).readW ((P.lay h.D).fr sD) 32 = BitVec.ofNat 32 (2 ^ p) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hs.2.1
  obtain w2 : ∀ v v', ((s.mem.writeW ((P.lay h.D).fr sA) v).writeW ((P.lay h.D).fr sD) v').readW
      ((P.lay h.D).fr sPc) 32 = BitVec.ofNat 32 (10 - p) := fun v v' => by
    rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide)]
    exact hs.2.2.1
  obtain hw : WP isa (.block passNext) s fun t =>
      t.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ / 2 ^ (p + 1)))).writeW
        ((P.lay h.D).fr sD) (BitVec.ofNat 32 (2 ^ (p + 1)))).writeW ((P.lay h.D).fr sPc)
          (BitVec.ofNat 32 (10 - (p + 1))) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = decide (10 - (p + 1) = 0) := by
    prun [passNext, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hs.1, hs.2.1, hs.2.2.1,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide), ea, ed, ec, hz0, w1, w2,
      VG.Proof.X25519.Arm.ofNat_beq_zero (show 10 - (p + 1) < 2 ^ 32 by omega_arith), dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨hk', hy'⟩ := keep3 h P hg fr hk hs.2.2.2
  refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk', ?_, ?_, ?_, hy'⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]

/-- A pass. -/
theorem onePass_vp (P : EP) (hP : ∃ σ, In h.D P σ) {p : Nat} (hp : p < 10) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ p s.mem) (passOne h.sh)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ (p + 1) s.mem) ∧
        s.z = decide (10 - (p + 1) = 0)) :=
  (passSet_vp h P hP hp).seq ((passMid_vp h P hP hp).seq (passNext_vp h P hP hp))

/-- The shift's distance, its first pass's, and its passes. -/
theorem shInit_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (.block shInit)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧ SH h P τ 0 s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain hw : WP isa (.block shInit) s fun t =>
      t.mem = ((s.mem.writeW ((P.lay h.D).fr sA) (BitVec.ofNat 32 (aV h P τ))).writeW
        ((P.lay h.D).fr sD) (BitVec.ofNat 32 1)).writeW ((P.lay h.D).fr sPc) (BitVec.ofNat 32 10) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [shInit, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.2.2.2.1,
      slotAt hi (d := sA) (by decide), slotAt hi (d := sD) (by decide), slotAt hi (d := sPc) (by decide),
      hc.st.inFr (d := sA) (n := 4) (by show sA + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sD) (n := 4) (by show sD + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sPc) (n := 4) (by show sPc + 4 ≤ frameBytes; decide),
      movw_val (show 1 < 2 ^ 16 by decide), movw_val (show 10 < 2 ^ 16 by decide),
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sA, slotR (P.lay h.D) sD, slotR (P.lay h.D) sPc] s.mem t.mem := by
    rw [m]
    exact ((slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))).trans
      ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨hk', hy'⟩ := keep3 h P hg fr hk hy
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, hk', ?_, ?_, ?_, fun j hj => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Nat.pow_zero, Nat.div_one]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [hy' j hj, Nat.pow_zero, Nat.mod_one, Nat.add_zero]

/-- `DB` shifted left by `pos + 1` bytes. -/
theorem shift_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) (shift h.sh)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) := by
  refine (shInit_vp h P hP).seq ?_
  let I : Nat → State → State → Prop := fun k τ s => k ≤ 10 ∧ Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
    SH h P τ (10 - k) s.mem
  refine (VP.loop (I := I) (fun k => ?_) 9).mono (fun τ s ⟨hc, hk, hs⟩ => ⟨by omega_arith, hc, hk, hs⟩) fun _ _ h => h
  by_cases hk : k ≤ 9
  swap
  · exact VP.empty fun τ s h' => hk (by have := h'.1; omega_arith)
  refine (onePass_vp h P hP (p := 9 - k) (by omega_arith)).mono
    (fun τ s ⟨_, hc, hq, hs⟩ => ⟨hc, hq, by rw [show 9 - k = 10 - (k + 1) by omega_arith]; exact hs⟩)
    fun τ s ⟨⟨hc, hq, hs⟩, z⟩ => ⟨?_, fun h0 => ⟨hc, hq, fun j hj => ?_⟩, fun hpos => ⟨by omega_arith, hc, hq, ?_⟩⟩
  · rw [VG.Proof.X25519.Arm.eval_ne, z, show 10 - (9 - k + 1) = k by omega_arith]; cases k <;> simp
  · subst h0
    obtain hb := shB h hq.1.1 hq.1.2.1
    obtain hpz := pzF_lt h (τ := τ) hb.2.1
    rw [hs.2.2.2 j hj, Nat.mod_eq_of_lt (show aV h P τ < 2 ^ (9 - 0 + 1) by
      show pzF h P τ + 1 < 1024; omega_arith)]
  · rw [show 10 - k = 9 - k + 1 by omega_arith]; exact hs

end VG.Proof.RsaPss.Arm.Vf

end

end


/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: a salt of any length

`M' = 0⁸ ‖ mHash ‖` the bytes of `DB` after its first nonzero byte (`Ma`):
`DB` copied after `mHash` and shifted into place, hashed over the blocks of
the longest salt, and compared with `H` (`any_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- `M'`. -/
abbrev Ma (P : EP) (τ : State) : List Byte :=
  Spec.RsaPss.zeros 8 ++ digB h P τ ++ (dbL h P τ).drop (pzF h P τ + 1)

/-- Its blocks, those of the longest salt. -/
abbrev nbA (P : EP) : Nat := (dbN h P + (7 + h.D + h.L)) / h.B + 1

theorem pre_length (P : EP) (τ : State) : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
  simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]

theorem dbL_length (P : EP) (τ : State) : (dbL h P τ).length = dbN h P := by simp [dbL]

theorem Ma_length (P : EP) (τ : State) : (Ma h P τ).length = 8 + h.D + (dbN h P - (pzF h P τ + 1)) := by
  rw [Ma, List.length_append, pre_length, List.length_drop, dbL_length]

theorem Ma_getD {P : EP} {τ : State} {j : Nat} :
    (Ma h P τ).getD (8 + h.D + j) 0 = Dp h P τ (j + aV h P τ) := by
  rw [Ma, RsaPss.getD_app, pre_length, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [← List.getD_eq_getElem?_getD]
  unfold Dp aV
  by_cases e : j + (pzF h P τ + 1) < dbN h P
  · rw [ite_eq_left e, Nat.add_comm, ← dbL_getD h e]
  · rw [ite_eq_right e, getD_ge (by rw [dbL_length]; omega_arith)]

/-- `DB` after `mHash`. -/
theorem cpDb_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem)
      (.seq (.block (cpDb h.sh)) Impl.Bignum.Arm.copyBytes)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ j) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.1.1.2.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi₀ hf
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  refine VP.seq (G := fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ True) ∧ Y1 h P τ s.mem) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
      s.gpr .lr = BitVec.ofNat 32 (dbN h P))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_)
    ((copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := dbN h P) (by omega_arith) (by omega_arith))
      (hg.rbuf (o := oEm + lo P) (n := dbN h P) (by omega_arith) (by omega_arith))
      (by rw [hg.addr (by omega_arith), hg.addr (by omega_arith)]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
      (f := fun τ i => dbF h P τ i)
      (Inv := fun τ m => Kq h P τ m ∧ ∀ j, dbN h P ≤ j → j < 2040 - h.D → m (sa P.scr (oY + 8 + h.D + j)) = 0)
      fun τ m m' ⟨hk, hz⟩ hf' => ?_).mono
      (fun τ s ⟨⟨hc, ⟨hk, _⟩, hy⟩, r0, r1, lr⟩ => ⟨hc, ⟨⟨hk, fun i hi => hy i (by omega_arith)⟩, fun j hj hj' => ?_⟩, r0, r1, lr, fun i hi => ?_⟩)
      fun τ s ⟨hc, ⟨hk, hz⟩, hs⟩ => ⟨hc, hk, fun j hj => ?_⟩)
  · have hw : WP isa (.block (cpDb h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P) ∧
        t.gpr .lr = BitVec.ofNat 32 (dbN h P) := by
      prun [cpDb, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hk.1.2.2.1.1,
        hk.1.2.2.1.2, movw_val (show oY + 8 + dig h.sh < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega_arith),
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hk, m ▸ hy⟩, r0, r1, lr⟩
  · rw [hg.addr (by omega_arith)] at hf'
    refine ⟨⟨K2.keep h hk.1 hf' fun r hr => ?_, sbytes_keep hf' (fun r hr => ?_) (by omega_arith) hk.2⟩,
      fun j hj hj' => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
    · rw [← hz j hj hj']
      exact hf' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := P.scr) (o := oY + 8 + h.D + j) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
          (Region.contains_self _ _)
  · rw [show oY + 8 + h.D + j = oY + (8 + h.D + j) by omega_arith, hy _ (by omega_arith)]
    exact getD_ge (by rw [pre_length]; omega_arith)
  · rw [hg.byteAt_scr (by omega_arith), show oEm + lo P + i = oEm + lo P + i from rfl]; exact hk.2.2.2.1 i hi
  · unfold Dp
    by_cases e : j < dbN h P
    · rw [ite_eq_left e, ← hs j e, hg.byteAt_scr (by omega_arith)]
    · rw [ite_eq_right e]; exact hz j (by omega_arith) hj

/-- `M'`'s length and blocks. -/
theorem anyLen_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kq h P τ s.mem ∧
        ∀ j < 2040 - h.D, s.mem (sa P.scr (oY + 8 + h.D + j)) = Dp h P τ (j + aV h P τ)) (.block (anyLen h.sh))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Ma h P) (nbA h P) τ s.mem ∧
        ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Ma h P τ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, hk, hy⟩ => ?_
  have hi := hk.1.1
  obtain ⟨hlo, hdb, hdD, hD, hD0⟩ := shB h hi hk.1.2.1
  obtain hpz := pzF_lt h (τ := τ) hdb
  have hL := h.L_le
  have hB := h.B_ge
  have e3 : oY = 1024 := rfl
  obtain e1 : BitVec.ofNat 32 (dbN h P + (7 + h.D + h.L)) >>> lgB h.sh =
      BitVec.ofNat 32 ((dbN h P + (7 + h.D + h.L)) / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by omega_arith), h.pow_lg]
  obtain w1 : ∀ v, (s.mem.writeW ((P.lay h.D).fr sL) v).readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide)]; exact hk.1.2.2.1.2
  obtain es : BitVec.ofNat 32 (dbN h P) - BitVec.ofNat 32 (pzF h P τ) = BitVec.ofNat 32 (dbN h P - pzF h P τ) :=
    Offset.ofNat_sub_ofNat (w := 32) (by omega_arith)
  obtain hw : WP isa (.block (anyLen h.sh)) s fun t =>
      t.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (dbN h P - pzF h P τ + (7 + h.D)))).writeW
        ((P.lay h.D).fr sNb) (BitVec.ofNat 32 (nbA h P)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [anyLen, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hk.1.2.2.1.2, hk.1.2.2.2.2.2.1, w1, es,
      slotAt hi (d := sL) (by decide), slotAt hi (d := sNb) (by decide),
      hc.st.inFr (d := sL) (n := 4) (by show sL + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sNb) (n := 4) (by show sNb + 4 ≤ frameBytes; decide),
      movw_val (show 7 + dig h.sh < 2 ^ 16 by show 7 + h.D < 2 ^ 16; omega_arith),
      movw_val (show 7 + dig h.sh + lenL h.sh < 2 ^ 16 by show 7 + h.D + h.L < 2 ^ 16; omega_arith),
      BitVec.ofNat_add_ofNat, e1, h.lg_range, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  obtain aw : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb],
      Region.Disjoint (sR P.scr o n) r := fun o n hon r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have e2 : oRsa = 8192 := rfl
  obtain hy' := sbytes_keep fr (aw _ _ (by omega_arith)) (by omega_arith) hy
  obtain hp' := sbytes_keep fr (aw _ _ (by omega_arith)) (by omega_arith) hk.2
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨K2.keep h hk.1 fr fun r hr => ?_, ?_, ?_⟩,
    fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Ma_length]
    congr 1; omega_arith
  · rw [m, Mem.readW_writeW_self32]
  · by_cases e : i < 8 + h.D
    · rw [hp' i e, Ma, RsaPss.getD_app (l := Spec.RsaPss.zeros 8 ++ digB h P τ), pre_length, ite_eq_left e]
    · have := hy' (i - (8 + h.D)) (by omega_arith)
      rw [show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_arith] at this
      rw [this, show i = 8 + h.D + (i - (8 + h.D)) by omega_arith, Ma_getD]
      congr 1; omega_arith

/-- A salt of any length. -/
theorem any_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ True) ∧ s.syms = τ.syms) (anyPath f h.sh)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (Ma h P τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.2.1
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  obtain hB0 : 0 < h.B := by have := h.B_ge; omega_arith
  obtain ⟨hlo, hdb, hdD, hD', hD0⟩ := shB h hi₀ hf
  obtain q1 := Nat.lt_mul_div_succ (dbN h P + (7 + h.D + h.L)) hB0
  obtain q2 := Nat.mul_div_le (dbN h P + (7 + h.D + h.L)) h.B
  obtain hT : nbA h P * h.B ≤ 2048 := by
    show ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_arith
  show VP _ (.seq (yDig h.sh 4) (.seq (.block (cpDb h.sh)) (.seq Impl.Bignum.Arm.copyBytes (.seq (shift h.sh)
    (.seq (.block (anyLen h.sh)) (.seq (ctHash f h.sh 14) (cmpH h.sh))))))) _
  refine (VP.syms (yDig_vf h P ⟨σ₀, hi₀⟩ True)).seq (VP.assoc ((VP.syms (cpDb_vp h P ⟨σ₀, hi₀⟩)).seq
    ((VP.syms (shift_vp h P ⟨σ₀, hi₀⟩)).seq ((VP.syms (anyLen_vp h P ⟨σ₀, hi₀⟩)).seq ?_))))
  exact (tail_vp h P Q ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Ma h P) fun τ => by
      rw [Ma_length]; show _ ≤ ((dbN h P + (7 + h.D + h.L)) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_arith).mono
    (fun τ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_arith)⟩, sy⟩) fun _ _ h' => h'

end VG.Proof.RsaPss.Arm.Vf

end

end

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: a salt of the expected length

`M' = 0⁸ ‖ mHash ‖` the last `sLen` bytes of `DB` (`Mf`), hashed and compared
with `H` (`fixed_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (add_ofNat_sub)

variable (h : PssHash)

/-- The last `sLen` bytes of `DB`. -/
abbrev sltB (P : EP) (τ : State) : List Byte := (List.range P.slt).map fun i => dbF h P τ (dbN h P - P.slt + i)

/-- `M'`. -/
abbrev Mf (P : EP) (τ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P τ ++ sltB h P τ

/-- Its blocks. -/
abbrev nbF (P : EP) : Nat := (P.slt + (8 + h.D) + h.L) / h.B + 1

/-- `Y`, with `M'`. -/
abbrev Yf (P : EP) (τ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mf h P τ).getD i 0

theorem Mf_length (P : EP) (τ : State) : (Mf h P τ).length = P.slt + (8 + h.D) := by
  simp only [Mf, List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length, sltB,
    List.length_map, List.length_range]; omega_using []

/-- What the fixed path starts from. -/
abbrev F0 (P : EP) (τ s : State) : Prop := Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Y1 h P τ s.mem

/-- The last `sLen` bytes of `DB` after `mHash`. -/
theorem fxSalt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (F0 h P) (.seq (.block (fxSalt h.sh)) (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.2.1.1.2.1, h'.2.1.2⟩
  obtain ⟨hf, ha⟩ := hf
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have e1 : oEm = 0 := rfl
  have e2 : oRsa = 8192 := rfl
  have e3 : oY = 1024 := rfl
  have hsl := hi₀.slt32
  refine VP.seq (G := fun τ s => F0 h P τ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.slt) ∧ s.gpr .lr = BitVec.ofNat 32 P.slt ∧
      s.z = decide (P.slt = 0))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, ⟨hk, ha'⟩, hy⟩ => ?_)
    (VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun τ s ⟨⟨⟨hc, hk, hy⟩, _, _, _, z⟩, e⟩ => ⟨hc, hk, fun i hi => ?_⟩) ?_)
  · obtain ⟨a7, r7, v7⟩ := argAt hk.1 hc.st (j := 8) (by decide)
    replace v7 : s.mem.readW ((P.lay h.D).fr (arg 8)) 32 = BitVec.ofNat 32 P.slt := v7
    have hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
    have hw : WP isa (.block (fxSalt h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
        t.gpr .r1 = P.scr + BitVec.ofNat 32 (oEm + lo P + dbN h P - P.slt) ∧
        t.gpr .lr = BitVec.ofNat 32 P.slt ∧ t.z = decide (P.slt = 0) := by
      prun [fxSalt, atS, atDb, addSlot, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a7, r7, v7, arg_lt,
        hk.2.2.1.1, hk.2.2.1.2,
        movw_val (show oY + 8 + dig h.sh < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; omega_arith),
        movw_val (show oEm < 2 ^ 16 by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat, hz0,
        add_ofNat_sub (x := P.scr) (a := oEm + lo P + dbN h P) (b := P.slt) (by omega_arith),
        VG.Proof.X25519.Arm.ofNat_beq_zero hsl]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, z⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ ⟨hk, ha'⟩, m ▸ hy⟩, r0, r1, lr, z⟩
  · have h0 : P.slt = 0 := by
      rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [hy i hi]
    simp [Mf, sltB, h0]
  · by_cases h0 : P.slt = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.slt) (by omega_arith) (by omega_arith))
      (hg.rbuf (o := oEm + lo P + dbN h P - P.slt) (n := P.slt) (by omega_arith) (by omega_arith))
      (by rw [hg.addr (by omega_arith), hg.addr (by omega_arith)]; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
      (f := fun τ i => dbF h P τ (dbN h P - P.slt + i))
      (Inv := fun τ m => (K2 h P τ m ∧ P.any = 0) ∧
        (∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P τ).getD i 0) ∧
        YZ P.scr (8 + h.D + P.slt) m) fun τ m m' ⟨⟨hk, ha'⟩, h1, h2⟩ hf' => ?_).mono
      (fun τ s ⟨⟨⟨hc, hk, hy⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega_arith), fun i hi => ?_⟩, r0, r1, lr,
        fun i hi => ?_⟩) fun τ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨hc, hk, fun i hi => ?_⟩
    · rw [hg.addr (by omega_arith)] at hf'
      refine ⟨⟨K2.keep h hk hf' fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away2_scr hg (by omega_arith) (by omega_arith), ha'⟩,
        sbytes_keep hf' (fun r hr => ?_) (by omega_arith) h1, sbytes_keep hf' (fun r hr => ?_) (by omega_arith) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by omega_arith) (by omega_arith) (by omega_arith)
    · rw [show oY + (8 + h.D + P.slt) + i = oY + (8 + h.D + P.slt + i) by omega_arith, hy _ (by omega_arith),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]; omega_arith)]
    · rw [hg.byteAt_scr (by omega_arith), show oEm + lo P + dbN h P - P.slt + i = oEm + lo P + (dbN h P - P.slt + i) by omega_arith]
      exact hk.1.2.2.2.1 _ (by omega_arith)
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P τ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]
      rw [RsaPss.getD_app, hl]
      by_cases e1 : i < 8 + h.D
      · rw [ite_eq_left e1]; exact h1 i e1
      rw [ite_eq_right e1]
      by_cases e2 : i < 8 + h.D + P.slt
      · have e := hs (i - (8 + h.D)) (by omega_arith)
        rw [hg.byteAt_scr (by omega_arith), show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_arith] at e
        rw [e]
        simp [sltB, List.getD_eq_getElem?_getD, show i - (8 + h.D) < P.slt by omega_arith]
      · rw [getD_ge (l := sltB h P τ) (by simp only [sltB, List.length_map, List.length_range]; omega_arith),
          show oY + i = oY + (8 + h.D + P.slt) + (i - (8 + h.D + P.slt)) by omega_arith]
        exact h2 _ (by omega_arith)

/-- `M'`'s length and blocks. -/
theorem lenF_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ (K2 h P τ s.mem ∧ P.any = 0) ∧ Yf h P τ s.mem) (.block (lenSet h.sh 8))
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ Kt h P (Mf h P) (nbF h P) τ s.mem ∧ Yf h P τ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun τ s ⟨hc, ⟨hk, ha⟩, hy⟩ => ?_
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.slt32
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hk.1 hk.2.1
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  obtain ⟨a7, r7, v7⟩ := argAt hk.1 hc.st (j := 8) (by decide)
  replace v7 : s.mem.readW ((P.lay h.D).fr (arg 8)) 32 = BitVec.ofNat 32 P.slt := v7
  have e1 : BitVec.ofNat 32 (P.slt + (8 + h.D) + h.L) >>> lgB h.sh = BitVec.ofNat 32 ((P.slt + (8 + h.D) + h.L) / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by omega_using [hL, hdb, hsum, hK, es]), h.pow_lg]
  have hw : WP isa (.block (lenSet h.sh 8)) s fun t =>
      t.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.slt + (8 + h.D)))).writeW ((P.lay h.D).fr sNb)
        (BitVec.ofNat 32 (nbF h P)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [lenSet, sp0, ld, st, mw, hc.st.sp, a7, r7, v7, arg_lt, slotAt hk.1 (d := sL) (by decide),
      slotAt hk.1 (d := sNb) (by decide), hc.st.inFr (d := sL) (n := 4) (by show sL + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sNb) (n := 4) (by show sNb + 4 ≤ frameBytes; decide),
      movw_val (show 8 + dig h.sh < 2 ^ 16 by show 8 + h.D < 2 ^ 16; omega_using [hD]),
      movw_val (show lenL h.sh < 2 ^ 16 by show h.L < 2 ^ 16; omega_using [hL]), BitVec.ofNat_add_ofNat, e1, h.lg_range,
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨K2.keep h hk fr fun r hr => ?_, ?_, ?_⟩,
    sbytes_keep fr (fun r hr => ?_) (by decide) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away2_slot hg (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Mf_length]
  · rw [m, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by decide) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by decide) (by rw [hg.F]; decide)).symm

/-- A salt of the expected length. -/
theorem fixed_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧ P.any = 0) ∧ s.syms = τ.syms) (fixedPath f h.sh)
      (fun τ s => (Ctx (P.lay h.D) P.scr τ s ∧ K2 h P τ s.mem ∧
        s.gpr .r0 = if acc2 h P τ = 0 ∧ HOk h P τ (Mf h P τ) then 1 else 0) ∧ s.syms = τ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  by_cases hf : fits h P ∧ P.any = 0
  swap
  · exact VP.empty fun σ s h' => hf ⟨h'.1.2.1.2.1, h'.1.2.2⟩
  obtain ⟨hf, ha⟩ := hf
  have hg := hi₀.geo
  have hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  have hB0 : 0 < h.B := by have := h.B_ge; omega_using [this]
  obtain ⟨hlo, hdb, hsum, hK, hD', hD0, hK0⟩ := fitB h hi₀ hf
  have es : eLen P = P.slt := by simp only [eLen, ha, ite_true]
  have q1 := Nat.lt_mul_div_succ (P.slt + (8 + h.D) + h.L) hB0
  have q2 := Nat.mul_div_le (P.slt + (8 + h.D) + h.L) h.B
  have hT : nbF h P * h.B ≤ 2048 := by
    show ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_using [hD, hL, hB, hB0, hlo, hdb, hsum, hK, hD', hD0, hK0, es, q1, q2]
  show VP _ (.seq (yDig h.sh 4) (.seq (.block (fxSalt h.sh)) (.seq (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes)
    (.seq (.block (lenSet h.sh 8)) (.seq (ctHash f h.sh 14) (cmpH h.sh)))))) _
  refine (VP.syms (yDig_vf h P ⟨σ₀, hi₀⟩ (P.any = 0))).seq ?_
  refine VP.assoc ((VP.syms (fxSalt_vp h P ⟨σ₀, hi₀⟩)).seq ((VP.syms (lenF_vp h P ⟨σ₀, hi₀⟩)).seq ?_))
  exact (tail_vp h P Q ⟨σ₀, hi₀⟩ hT (Nat.succ_pos _) (msg := Mf h P) fun τ => by
      rw [Mf_length]; show _ ≤ ((P.slt + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_using [q1]).mono
    (fun τ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_using [hT, hi])⟩, sy⟩) fun _ _ h' => h'

end VG.Proof.RsaPss.Arm.Vf
