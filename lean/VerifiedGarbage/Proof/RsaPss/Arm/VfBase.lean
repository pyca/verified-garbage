module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Spec.RsaPss.Precomputed
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec

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
abbrev TAB : Region := Sig.tableRegion 32 (State.addr P.tab) 5

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
    by show 16 ≤ 56; decide⟩

/-- The table of `MdHash`, in a buffer only read. -/
theorem htbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 44 → R.Contains (RsaOaep.Arm.tA P.hd o) 4 := by
  have hf := h.ok.fits P.HTAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.HTAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.hd, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.hd + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The table of `Hash`, in a buffer only read. -/
theorem tbl : ∃ R ∈ (P.lay D).ro, ∀ o, o + 4 ≤ 20 → R.Contains (RsaOaep.Arm.tA P.tab o) 4 := by
  have hf := h.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.tab, 5 * (32 / 8)⟩ : Region).Contains (State.addr (P.tab + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + 56

/-- The shared contract, with the hash function one of the tables `hs`,
MGF1's one of `ts`, and that stack. -/
abbrev spec (hs ts : List FnTable) : Contract isa :=
  Spec.RsaPss.verifyPrecomputedTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedTableSig [("hash", hs), ("mgf1", ts)]) stackBytes

/-- Unfolds the contract's precondition at `h`. -/
macro "verify_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at $h:ident
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
        (ep G s hi hc hdg HT ai au af T).TAB] [(ep G s hi hc hdg HT ai au af T).SCR] s := rfl

theorem in_of_pre {hs ts : List FnTable} {s : State} (h : (spec hs ts).pre s) {D : Nat}
    (hD : (stackArg s 1).toNat = D) (hHT : HT (entered frameBytes s)) (hT : T (entered frameBytes s)) :
    In D (ep G s hi hc hdg HT ai au af T) (entered frameBytes s) := by
  verify_pre at h
  sig_split h
  rename_i hsp hsa hheld hheld2 hpw hrd hwr nS eS dS gS sR sTH sT sA kN kE kD kG kS kR kTH kT kA fN fE fD fG fS fR
    fTH fT kv el1 elK glK scrK rlK
  have h240 : 240 ≤ s.sp.toNat := hsp
  have a1 : stackArg s 1 = BitVec.ofNat 32 D := by
    apply BitVec.eq_of_toNat_eq; rw [hD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hD]; exact (stackArg s 1).isLt)]
  rw [hD] at dS kD fD hrd
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56) ⟨State.addr s.sp - BitVec.ofNat 64 240, 240⟩ := by
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
  tk : ∀ σ s, P.T σ → s.syms = σ.syms → (∀ o, o + 4 ≤ 20 →
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
