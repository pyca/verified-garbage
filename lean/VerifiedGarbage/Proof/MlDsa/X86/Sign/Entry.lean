module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Pre
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Params
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call
public import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
meta import VerifiedGarbage.Proof.MlDsa.X86.Sign.Pre
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call
meta import VerifiedGarbage.Impl.MlDsa.X86.Sign.Entry
meta import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# ML-DSA signing on x86 (32-bit): the entries

`vg_mldsa*_sign` and `vg_mldsa*_sign_prepared` (`Impl/MlDsa/X86/Sign/Entry.lean`)
set `KEYS` (and the second copies the prepared key's polynomials to `scratch`)
and call the core (`signCoreContract`), whose precondition this makes hold
(`core_piece`). They are proven as the other top-level functions on x86
(`Proof/MlKem/X86/Top.lean`), in a layout of their own (`YE`: the key, of
`kl` bytes, `mu`, `rnd`, `sig`, `scratch` and 136 bytes of stack), with runs
related by the pointers and what signing may leak (`EPub`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.SignEntry

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Sign
open VG.Impl.MlDsa.X86.KeyGen (setArgs callPR)
open VG.Proof.MlDsa.X86.Sign (keysWord KeysIn signCoreContract lk0)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The entries' layout, for a key of `kl` bytes. -/
def YE (p : Params) (kl : Nat) : Lay :=
  ⟨[(kl, false), (64, false), (32, false), (p.sigLen, true), (scrBytes p, true)], 4, 136⟩

section
variable (p : Params) (s₀ : State)
/-- The encoded private key (the first `skLen` bytes of the key), `μ` and `rnd`, on entry. -/
abbrev eSk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, p.skLen⟩) p.skLen
abbrev eMu : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64
abbrev eRnd : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32
/-- `scratch`. -/
abbrev eScr : Addr := (arg s₀ 4).setWidth 64
end

/-- Two runs with the same pointers and the same leakage. -/
def EPub (p : Params) (kl : Nat) (s₀ s₀' : State) : Prop :=
  TPub (YE p kl) lk0 s₀ s₀' ∧ signLeak p (eSk p s₀) (eMu s₀) (eRnd s₀) = signLeak p (eSk p s₀') (eMu s₀') (eRnd s₀')

/-- The pieces of the entries. -/
abbrev EP (p : Params) (kl : Nat) (A B : State → State → Prop) (c : Prog isa) : Prop :=
  Piece (TPre (YE p kl)) (EPub p kl) A B c

theorem liftE {p : Params} {kl : Nat} {A B : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (YE p kl)) (TPub (YE p kl) lk0) A B c) : EP p kl A B c :=
  h.pre_mono (fun _ h => h) fun _ _ _ _ h => h.1

/-! ## The call of the core -/

section
variable {p : Params} {kl : Nat} {A : State → State → Prop}

/-- What the core leaves: its result and the signature, for the key, `μ` and `rnd` on entry. -/
def CoreDone (p : Params) (s₀ s : State) : Prop :=
  Outcome (fun b => signMu p b (eSk p s₀) (eMu s₀) (eRnd s₀)) (s.gpr .eax)
    (bytesAt s.mem (Buf.addr s₀ ⟨3, 0, p.sigLen⟩) p.sigLen)

theorem ye_ok (hkl : p.skLen ≤ kl) (hsk : 0 < p.skLen) (hsig : 0 < p.sigLen) (hscr : 0 < scrBytes p) :
    (YE p kl).ok ⟨0, 0, p.skLen⟩ = true ∧ (YE p kl).ok ⟨1, 0, 64⟩ = true ∧ (YE p kl).ok ⟨2, 0, 32⟩ = true ∧
      (YE p kl).okW ⟨3, 0, p.sigLen⟩ = true ∧ (YE p kl).okW ⟨4, 0, scrBytes p⟩ = true := by
  simp only [Lay.okW_iff, Lay.ok_iff, YE, Lay.n, Lay.alen, Lay.awr]
  simp only [List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
  exact ⟨⟨by omega, hsk, hkl⟩, ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩,
    ⟨⟨by omega, hsig, by omega⟩, trivial⟩, ⟨by omega, hscr, by omega⟩, trivial⟩

/-- Bytes of a region at `x + o`, from those of a region at `x` around it. -/
theorem off_congr {m m' : Mem} {x : Addr} {L : Nat} (h : ∀ j < L, m' (x + BitVec.ofNat 64 j) = m (x + BitVec.ofNat 64 j))
    {o len : Nat} (ho : o + len ≤ L) : ∀ i < len, m' (x + BitVec.ofNat 64 o + BitVec.ofNat 64 i) =
      m (x + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := fun i hi => by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)

theorem keysWord_congr {m m' : Mem} {x : Addr} {L : Nat}
    (h : ∀ j < L, m' (x + BitVec.ofNat 64 j) = m (x + BitVec.ofNat 64 j)) (hL : oKEYS + 4 ≤ L) :
    keysWord m' x = keysWord m x :=
  Mem.readW_congr fun i hi => off_congr h hL i hi

theorem keysIn_congr {p : Params} {m m' : Mem} {x : Addr} {sk : List Byte}
    (h : ∀ j < scrBytes p, m' (x + BitVec.ofNat 64 j) = m (x + BitVec.ofNat 64 j)) (ps : VG.Proof.MlDsa.X86.Sign.PS p)
    (hk : KeysIn p m x sk) : KeysIn p m' x sk := fun i hi =>
  VG.Proof.MlDsa.Sign.polyIs_congr (off_congr h (by have := ps.hk; have := ps.hl; simp only [scrBytes, scratchWords, oP] at hi ⊢; omega)) (hk i hi)

theorem eScr_addr (s₀ : State) (L : Nat) : Buf.addr s₀ ⟨4, 0, L⟩ = eScr s₀ := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- The call of the core, with `KEYS = v` in `scratch`, and the private key's
polynomials there if it is not 0. -/
theorem core_piece {n : String} {f : Prog isa} (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) (hkl : p.skLen ≤ kl) (ps : VG.Proof.MlDsa.X86.Sign.PS p) (v : BitVec 32)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre (YE p kl) s₀ → A s₀ s → Ctx (YE p kl) s₀ s ∧ keysWord s.mem (eScr s₀) = v ∧
      (v = 0 ∨ KeysIn p s.mem (eScr s₀) (eSk p s₀))) :
    EP p kl A (fun s₀ s' => Ctx (YE p kl) s₀ s' ∧ CoreDone p s₀ s') (callPR 4 n f (coreArgs p)) := by
  have hsk : 0 < p.skLen := by have := ps.hskLen; omega
  have hsig : 0 < p.sigLen := by have := ps.hsigLen; rcases ps.hcLen with h | h | h <;> omega
  have hscr : 0 < scrBytes p := by simp only [scrBytes, scratchWords]; omega
  obtain ⟨o0, o1, o2, w3, w4⟩ := ye_ok hkl hsk hsig hscr
  have r3 := (Lay.okW_iff.mp w3).1
  have r4 := (Lay.okW_iff.mp w4).1
  refine callPR_pieceK (lk := lk0) (K := 96) (coreArgs p) [⟨0, 0, p.skLen⟩, ⟨1, 0, 64⟩, ⟨2, 0, 32⟩]
    [⟨3, 0, p.sigLen⟩, ⟨4, 0, scrBytes p⟩] (fun _ _ h => h.1) hv hsp hst (by simp [coreArgs])
    (by simp [coreArgs]) (by simp [coreArgs, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, o0, o1, o2, r3, r4]) (by simp [YE]) (by simp [YE])
    (by simp [o0, o1, o2]) (by simp [w3, w4]) tt (fun s₀ s hp h => (hA s₀ s hp h).1)
    (fun s₀ s e hp ha he => ?_) (fun s₀ s₀' s s' e e' hp hp' hq ha ha' he he' => ?_)
    (fun s₀ s s' hp ha h' fr ⟨e, s₂, he, m₂, g₂, post⟩ => ?_)
  · obtain ⟨hc, hkw, hkv⟩ := hA s₀ s hp ha
    have hsc : ∀ j < scrBytes p, e.mem (eScr s₀ + BitVec.ofNat 64 j) = s.mem (eScr s₀ + BitVec.ofNat 64 j) := by
      have := he.mem _ r4; rw [eScr_addr] at this; exact this
    have hskb : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.skLen⟩) p.skLen = eSk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    have hkp : keysWord e.mem (eScr s₀) = 0 ∨ KeysIn p e.mem (eScr s₀) (bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.skLen⟩) p.skLen) := by
      rw [hskb, keysWord_congr hsc (by simp only [scrBytes, scratchWords, oKEYS]; omega), hkw]
      rcases hkv with h0 | hk
      · exact .inl h0
      · exact .inr (keysIn_congr hsc ps hk)
    rw [← eScr_addr s₀ (scrBytes p)] at hkp
    obtain ⟨b₀, b₀', b₀'', b₀f⟩ := he.bufK hp (by simp [coreArgs]) o0 (K := 96) (by simp [YE])
    obtain ⟨b₁, b₁', b₁'', b₁f⟩ := he.bufK hp (by simp [coreArgs]) o1 (K := 96) (by simp [YE])
    obtain ⟨b₂, b₂', b₂'', b₂f⟩ := he.bufK hp (by simp [coreArgs]) o2 (K := 96) (by simp [YE])
    obtain ⟨b₃, b₃', b₃'', b₃f⟩ := he.bufK hp (by simp [coreArgs]) r3 (K := 96) (by simp [YE])
    obtain ⟨b₄, b₄', b₄'', b₄f⟩ := he.bufK hp (by simp [coreArgs]) r4 (K := 96) (by simp [YE])
    obtain ⟨x₁, x₂⟩ := he.selfK hp (by simp [coreArgs]) (K := 96) (by simp [YE])
    obtain ⟨en, hE⟩ := he.espNat hp (by simp [YE]) (by simp [coreArgs])
    have hE2 : 120 ≤ (E1 s₀).toNat := by
      rw [E1_nat s₀ hp.E0_big]; have := hp.sp; simp only [YE] at this; omega
    have d03 := Buf.disj hp o0 r3 (by simp [Lay.sep, YE, Lay.awr])
    have d04 := Buf.disj hp o0 r4 (by simp [Lay.sep, YE, Lay.awr])
    have d13 := Buf.disj hp o1 r3 (by simp [Lay.sep, YE, Lay.awr])
    have d14 := Buf.disj hp o1 r4 (by simp [Lay.sep, YE, Lay.awr])
    have d23 := Buf.disj hp o2 r3 (by simp [Lay.sep, YE, Lay.awr])
    have d24 := Buf.disj hp o2 r4 (by simp [Lay.sep, YE, Lay.awr])
    have d34 := Buf.disj hp r3 r4 (by simp [Lay.sep, YE, Lay.awr])
    have := (E1 s₀).isLt
    have a₀ := he.arg 0 (by simp [coreArgs])
    have a₁ := he.arg 1 (by simp [coreArgs])
    have a₂ := he.arg 2 (by simp [coreArgs])
    have a₃ := he.arg 3 (by simp [coreArgs])
    have a₄ := he.arg 4 (by simp [coreArgs])
    have aa := he.argAddr0
    generalize e = e' at *
    sig_pre [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, argAddr_withRegions, a₀, a₁, a₂, a₃, a₄, aa, coreArgs, List.getElem_cons_zero,
      List.getElem_cons_succ, VG.Impl.MlDsa.X86.KeyGen.Arg.val, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceMul, Buf.addr, Buf.rgn, wrR, below, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at *
    and_intros
    all_goals first | exact True.intro | with_reducible assumption | omega_arith
  · obtain ⟨esp, ags⟩ := call_pubs _ hq.1 (by simp [coreArgs, VG.Impl.MlDsa.X86.KeyGen.Arg.ok, o0, o1, o2, r3, r4]) he he'
    obtain ⟨hc, hkw, -⟩ := hA s₀ s hp ha
    obtain ⟨hc', hkw', -⟩ := hA s₀' s' hp' ha'
    have hsc : ∀ j < scrBytes p, e.mem (eScr s₀ + BitVec.ofNat 64 j) = s.mem (eScr s₀ + BitVec.ofNat 64 j) := by
      have := he.mem _ r4; rw [eScr_addr] at this; exact this
    have hsc' : ∀ j < scrBytes p, e'.mem (eScr s₀' + BitVec.ofNat 64 j) = s'.mem (eScr s₀' + BitVec.ofNat 64 j) := by
      have := he'.mem _ r4; rw [eScr_addr] at this; exact this
    have hkL : oKEYS + 4 ≤ scrBytes p := by simp only [scrBytes, scratchWords, oKEYS]; omega
    have k₁ : keysWord e.mem (eScr s₀) = v := by rw [keysWord_congr hsc hkL, hkw]
    have k₂ : keysWord e'.mem (eScr s₀') = v := by rw [keysWord_congr hsc' hkL, hkw']
    have l₁ : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.skLen⟩) p.skLen = eSk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    have l₂ : bytesAt e.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = eMu s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o1)]; exact hc.roBytes hp o1 rfl
    have l₃ : bytesAt e.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = eRnd s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o2)]; exact hc.roBytes hp o2 rfl
    have l₁' : bytesAt e'.mem (Buf.addr s₀' ⟨0, 0, p.skLen⟩) p.skLen = eSk p s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o0)]; exact hc'.roBytes hp' o0 rfl
    have l₂' : bytesAt e'.mem (Buf.addr s₀' ⟨1, 0, 64⟩) 64 = eMu s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o1)]; exact hc'.roBytes hp' o1 rfl
    have l₃' : bytesAt e'.mem (Buf.addr s₀' ⟨2, 0, 32⟩) 32 = eRnd s₀' := by
      rw [Proof.MlKem.bytesAt_congr (he'.mem _ o2)]; exact hc'.roBytes hp' o2 rfl
    rw [← eScr_addr s₀ (scrBytes p)] at k₁
    rw [← eScr_addr s₀' (scrBytes p)] at k₂
    have a₀ := he.arg 0 (by simp [coreArgs])
    have a₁ := he.arg 1 (by simp [coreArgs])
    have a₂ := he.arg 2 (by simp [coreArgs])
    have a₄ := he.arg 4 (by simp [coreArgs])
    have a₀' := he'.arg 0 (by simp [coreArgs])
    have a₁' := he'.arg 1 (by simp [coreArgs])
    have a₂' := he'.arg 2 (by simp [coreArgs])
    have a₄' := he'.arg 4 (by simp [coreArgs])
    have hl := hq.2
    generalize e = e₁ at *
    generalize e' = e₂ at *
    sig_pub [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a₀, a₁, a₂, a₄, a₀', a₁', a₂', a₄', coreArgs, List.getElem_cons_zero,
      List.getElem_cons_succ, VG.Impl.MlDsa.X86.KeyGen.Arg.val, Buf.addr] at *
    refine ⟨esp, ?_, hq.1.ptr o0, hq.1.ptr o1, hq.1.ptr o2, ags 3 (by simp), hq.1.ptr r4⟩
    simp only [k₁, k₂, l₁, l₂, l₃, l₁', l₂', l₃', hl]
  · obtain ⟨hc, -, -⟩ := hA s₀ s hp ha
    have l₁ : bytesAt e.mem (Buf.addr s₀ ⟨0, 0, p.skLen⟩) p.skLen = eSk p s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o0)]; exact hc.roBytes hp o0 rfl
    have l₂ : bytesAt e.mem (Buf.addr s₀ ⟨1, 0, 64⟩) 64 = eMu s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o1)]; exact hc.roBytes hp o1 rfl
    have l₃ : bytesAt e.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = eRnd s₀ := by
      rw [Proof.MlKem.bytesAt_congr (he.mem _ o2)]; exact hc.roBytes hp o2 rfl
    have a₀ := he.arg 0 (by simp [coreArgs])
    have a₁ := he.arg 1 (by simp [coreArgs])
    have a₂ := he.arg 2 (by simp [coreArgs])
    have a₃ := he.arg 3 (by simp [coreArgs])
    generalize e = e' at *
    sig_post [signCoreContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, a₀, a₁, a₂, a₃, coreArgs, List.getElem_cons_zero, List.getElem_cons_succ,
      VG.Impl.MlDsa.X86.KeyGen.Arg.val, m₂, g₂, sw_app, Buf.addr] at post l₁ l₂ l₃
    refine ⟨h', ?_⟩
    unfold CoreDone
    simp only [Buf.addr]
    rw [← l₁, ← l₂, ← l₃]
    exact post

/-! ## `vg_mldsa*_sign` -/

theorem keys_st {kl : Nat} {s₀ : State} (hp : TPre (YE p kl) s₀) {m : Mem}
    (v : Nat) : keysWord (m.writeW (Buf.addr s₀ ⟨4, oKEYS, 4⟩) (BitVec.ofNat 32 v)) (eScr s₀) = BitVec.ofNat 32 v := by
  have hok : (YE p kl).ok ⟨4, oKEYS, 4⟩ = true := by
    simp only [Lay.ok_iff, YE, Lay.n, Lay.alen, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ, scrBytes, scratchWords, oKEYS]; omega
  unfold keysWord
  rw [Buf.addr_eq hp hok]
  exact Mem.readW_writeW_self32 _ _ _

/-- The body of `vg_mldsa*_sign`. -/
theorem entry_piece {n : String} {f : Prog isa} (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true) :
    EP p p.skLen (fun s₀ s => s = P0 s₀) (fun s₀ s' => Ctx (YE p p.skLen) s₀ s' ∧ CoreDone p s₀ s')
      (entryBody p (.block (st32 oKEYS 0)) n f) := by
  unfold entryBody
  have hw : (YE p p.skLen).okW ⟨(YE p p.skLen).sc, oKEYS, 4⟩ = true := by
    simp only [Lay.okW_iff, Lay.ok_iff, YE, Lay.n, Lay.alen, Lay.awr, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, scrBytes, scratchWords, oKEYS]
    exact ⟨⟨by omega, by omega, by omega⟩, trivial⟩
  refine (liftE (ldsc_piece (Y := YE p p.skLen) (ht := .block []) (by kernel_rfl))).seq ?_
  refine (liftE (st32_piece (Y := YE p p.skLen) (A := fun s₀ s => Ctx (YE p p.skLen) s₀ s)
    (B := fun s₀ s => Ctx (YE p p.skLen) s₀ s ∧ keysWord s.mem (eScr s₀) = 0) oKEYS 0 hw (ht := .block [])
    (by kernel_rfl) (fun _ _ _ h => h) fun s₀ s s' hp _ h' m => ⟨h', by rw [m]; exact keys_st hp 0⟩)).seq ?_
  exact core_piece hv hsp hst (Nat.le_refl _) ps 0 tt fun _ _ _ h => ⟨h.1, h.2, .inl rfl⟩

/-! ## The contracts -/

theorem ye_n (p : Params) (kl : Nat) : (YE p kl).n = 5 := rfl

set_option linter.unusedSimpArgs false in
theorem ePre_of {s₀ : State} (h : (signContract p X86.abi 136).pre s₀) : TPre (YE p p.skLen) s₀ := by
  sig_pre [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d03, d04, d0g, d13, d14, d1g, d23, d24, d2g, d34, d3g, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 136#64, 136⟩ : Region) = below (E0 s₀) 136 := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth (by omega)]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (YE p p.skLen).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [ye_n] at hi; omega
  have aw : ∀ i, (YE p p.skLen).awr i = (i == 3 || i == 4) := fun i => by
    rcases i with _ | _ | _ | _ | _ | i <;> rfl
  refine ⟨h1, by show 16 ≤ 136; decide, by rw [ye_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 4 < 5; decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    all_goals simp [aw] at hw
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · simp [aw] at hw
    · simp [aw] at hw
    · simp [aw] at hw
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [h4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hne | (simp [aw] at hw; done) | skip
    exacts [d03, d04, d13, d14, d23, d24, d03.symm, d13.symm, d23.symm, d34, d04.symm, d14.symm, d24.symm, d34.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [d0g.symm, d1g.symm, d2g.symm, d3g.symm, d4g.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [f0, f1, f2, f3, f4]

theorem eaddr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem ePub_of {s₀ s₀' : State} (h : (signContract p X86.abi 136).pub s₀ s₀') : EPub p p.skLen s₀ s₀' := by
  sig_pub [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4⟩ := h
  refine ⟨⟨e₁, fun i hi => ?_, rfl⟩, ?_⟩
  · rw [ye_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [a0, a1, a2, a3, a4]
  · simp only [eSk, eMu, eRnd, eaddr0]
    exact e₂

/-- The prepared private key on entry. -/
abbrev PSK (p : Params) (s₀ : State) : Prop := PreparedSecretKey p s₀.mem ((arg s₀ 0).setWidth 64)

set_option linter.unusedSimpArgs false in
theorem pPre_of {s₀ : State} (h : (Proof.MlDsa.preparedSignContract p X86.abi 136).pre s₀) :
    TPre (YE p (preparedSecretKeyBytes p)) s₀ ∧ PSK p s₀ := by
  sig_pre [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, d03, d04, d0g, d13, d14, d1g, d23, d24, d2g, d34, d3g, d4g, r0, r1, r2, r3, r4, rg,
    s0, s1, s2, s3, s4, sg, f0, f1, f2, f3, f4, kp⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 136#64, 136⟩ : Region) = below (E0 s₀) 136 := by
    simp only [below]; rw [VG.X86.Taint.sub_setWidth (by omega)]
  rw [hs] at s0 s1 s2 s3 s4 sg
  have c5 : ∀ i, i < (YE p (preparedSecretKeyBytes p)).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    rw [ye_n] at hi; omega
  have aw : ∀ i, (YE p (preparedSecretKeyBytes p)).awr i = (i == 3 || i == 4) := fun i => by
    rcases i with _ | _ | _ | _ | _ | i <;> rfl
  refine ⟨⟨h1, by show 16 ≤ 136; decide, by rw [ye_n]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sg, ?_, by show 4 < 5; decide⟩, kp⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    all_goals simp [aw] at hw
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · simp [aw] at hw
    · simp [aw] at hw
    · simp [aw] at hw
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · rw [h4]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hne | (simp [aw] at hw; done) | skip
    exacts [d03, d04, d13, d14, d23, d24, d03.symm, d13.symm, d23.symm, d34, d04.symm, d14.symm, d24.symm, d34.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [d0g.symm, d1g.symm, d2g.symm, d3g.symm, d4g.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3, r4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [s0, s1, s2, s3, s4]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [f0, f1, f2, f3, f4]

/-- `vg_mldsa*_sign`, a leaf around `entry_piece`. -/
theorem entry_leaf {n : String} {f : Prog isa} (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true)
    (hsp' : NoSp (entryBody p (.block (st32 oKEYS 0)) n f)) :
    EP p p.skLen (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (CoreDone p s₀) s₀ s') (signEntry p n f) :=
  Piece.leaf (W (YE p p.skLen)) hsp' (fun _ hp => ⟨hp.E0_big, by have := hp.sp'; omega⟩) (fun _ hp => hp.hW)
    (fun _ _ _ _ hq => hq.1.1) ((entry_piece hv hsp hst ps tt).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

/-- Memory with the arguments `0`, `0x2000`, `0x3000`, `0x8000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x500d then 0x30 else if a = 0x5011 then 0x80 else if a = 0x5016 then 1 else 0

theorem entry_sat (h3 : VG.Proof.MlDsa.X86.Sign.Ok3 p) : ∃ s, (signContract p X86.abi 136).pre s := by
  rcases h3 with rfl | rfl | rfl
  · refine ⟨satState satMem [⟨0, 2560⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 2420⟩, ⟨0x10000, 77824⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  · refine ⟨satState satMem [⟨0, 4032⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 3309⟩, ⟨0x10000, 103424⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  · refine ⟨satState satMem [⟨0, 4896⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩] [⟨0x8000, 4627⟩, ⟨0x10000, 144384⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

/-- `vg_mldsa{44,65,87}_sign`, calling a core verified against `signCoreContract`,
is verified against `signContract`. -/
theorem entry_verified {n : String} {f : Prog isa} (h3 : VG.Proof.MlDsa.X86.Sign.Ok3 p)
    (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true)
    (hsp' : NoSp (entryBody p (.block (st32 oKEYS 0)) n f)) :
    Verified X86.target (signEntry p n f) (signContract p X86.abi 136) := by
  have ps := VG.Proof.MlDsa.X86.Sign.PS.of h3
  refine Piece.verified (((entry_leaf hv hsp hst ps tt hsp').pre_mono (fun _ h => ePre_of h)
    fun _ _ _ _ h => ePub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) (entry_sat h3)
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [signContract, signSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [sw_app, hax, hm]
  unfold CoreDone at hd
  simp only [eSk, eMu, eRnd, eaddr0] at hd
  exact hd

/-! ## `vg_mldsa*_sign_prepared` -/

/-- A piece with a precondition `φ` on the initial state, which it keeps. -/
theorem piece_pure {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop} {c : Prog isa}
    (φ : State → Prop) (h : Piece Pre Pub A B c) :
    Piece Pre Pub (fun s₀ s => A s₀ s ∧ φ s₀) (fun s₀ s => B s₀ s ∧ φ s₀) c where
  wp s₀ s hp ha := (h.wp s₀ s hp ha.1).mono fun _ hb => ⟨hb, ha.2⟩
  ct s₀ s₀' hp hp' hq := (h.ct s₀ s₀' hp hp' hq).mono (fun _ _ ⟨a, a'⟩ => ⟨a.1, a'.1⟩) fun _ _ h => h

/-- The body of `vg_mldsa*_sign_prepared`. -/
theorem prep_piece {n : String} {f : Prog isa} (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo 4 .edi ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩ ++
      ptrTo 4 .ebp ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (256 * (p.ℓ + 2 * p.k))))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true) :
    EP p (preparedSecretKeyBytes p) (fun s₀ s => s = P0 s₀ ∧ PSK p s₀)
      (fun s₀ s' => Ctx (YE p (preparedSecretKeyBytes p)) s₀ s' ∧ CoreDone p s₀ s')
      (entryBody p (copyKeys p) n f) := by
  have hk := ps.hk
  have hl := ps.hl
  have hskl := ps.hskLen
  have eK : keysBytes p = 4 * (256 * (p.ℓ + 2 * p.k)) := by simp only [keysBytes]; omega
  unfold entryBody copyKeys
  rw [eK]
  have hscr : oP (5 + 2 * p.k + 2 * p.ℓ) + 4 * (256 * (p.ℓ + 2 * p.k)) ≤ scrBytes p := by
    simp only [oP, scrBytes, scratchWords]; omega
  have hw : (YE p (preparedSecretKeyBytes p)).okW ⟨(YE p (preparedSecretKeyBytes p)).sc, oKEYS, 4⟩ = true := by
    simp only [Lay.okW_iff, Lay.ok_iff, YE, Lay.n, Lay.alen, Lay.awr, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ, scrBytes, scratchWords, oKEYS]
    exact ⟨⟨by omega, by omega, by omega⟩, trivial⟩
  have hS : (YE p (preparedSecretKeyBytes p)).ok ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩ = true := by
    simp only [Lay.ok_iff, YE, Lay.n, Lay.alen, List.length_cons, List.length_nil, List.getD_cons_zero,
      preparedSecretKeyBytes, Spec.MlDsa.n]
    omega
  have hD : (YE p (preparedSecretKeyBytes p)).okW ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩ = true := by
    simp only [Lay.okW_iff, Lay.ok_iff, YE, Lay.n, Lay.alen, Lay.awr, List.length_cons, List.length_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨⟨by omega, by omega, hscr⟩, trivial⟩
  have hSD : ((YE p (preparedSecretKeyBytes p)).ok ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩ && (YE p (preparedSecretKeyBytes p)).okW ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩ && (YE p (preparedSecretKeyBytes p)).sep ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩ ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨⟨hS, hD⟩, by simp [Lay.sep, YE, Lay.awr]⟩
  refine (piece_pure (PSK p) (liftE (ldsc_piece (Y := (YE p (preparedSecretKeyBytes p))) (ht := .block []) (by kernel_rfl)))).seq ?_
  refine Piece.seq (B := fun s₀ s => Ctx (YE p (preparedSecretKeyBytes p)) s₀ s ∧ keysWord s.mem (eScr s₀) = 1 ∧
      (1 = 0 ∨ KeysIn p s.mem (eScr s₀) (eSk p s₀)))
    (Piece.seq (liftE (st32_piece (Y := YE p (preparedSecretKeyBytes p))
      (A := fun s₀ s => Ctx (YE p (preparedSecretKeyBytes p)) s₀ s ∧ PSK p s₀)
      (B := fun s₀ s => (Ctx (YE p (preparedSecretKeyBytes p)) s₀ s ∧ keysWord s.mem (eScr s₀) = 1) ∧ PSK p s₀)
      oKEYS 1 hw (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
      fun s₀ s s' hp h h' m => ⟨⟨h', by rw [m]; exact keys_st hp 1⟩, h.2⟩))
    (liftE (copyW_piece (Y := YE p (preparedSecretKeyBytes p))
      (A := fun s₀ s => (Ctx (YE p (preparedSecretKeyBytes p)) s₀ s ∧ keysWord s.mem (eScr s₀) = 1) ∧ PSK p s₀)
      0 p.skLen 4 (oP (5 + 2 * p.k + 2 * p.ℓ)) (256 * (p.ℓ + 2 * p.k)) (by omega) (by omega) hSD t₁ t₂
      (fun _ _ _ h => h.1.1) fun s₀ s s' hp h h' fr hb => ?_)))
    (core_piece hv hsp hst (by simp only [preparedSecretKeyBytes]; omega) ps 1 tt fun _ _ _ h => h)
  have hok : (YE p (preparedSecretKeyBytes p)).ok ⟨4, oKEYS, 4⟩ = true := (Lay.okW_iff.mp hw).1
  have hDo := (Lay.okW_iff.mp hD).1
  refine ⟨h', ?_, .inr ?_⟩
  · have hka : (YE p (preparedSecretKeyBytes p)).apart ⟨4, oKEYS, 4⟩
        [⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩] = true := by
      simp only [Lay.apart, hok, hDo, List.all_cons, List.all_nil, Bool.true_and, Bool.and_true]
      exact VG.Proof.MlDsa.X86.Sign.Lay.sep_iff.mpr (.inl ⟨rfl, .inl (by simp only [oKEYS, oP]; omega)⟩)
    have e := keepW hp (N := 0) (by simp [YE]) hka (fr1 fr)
    have ea := Buf.addr_eq hp hok
    unfold keysWord at h ⊢
    rw [show eScr s₀ + BitVec.ofNat 64 oKEYS = Buf.addr s₀ ⟨4, oKEYS, 4⟩ from ea.symm, e, ea]
    exact h.1.2
  · intro i hi
    have hf := (Proof.MlDsa.preparedSecretKey_iff.mp h.2) i hi
    have sk : bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen = eSk p s₀ := by simp only [eSk, eaddr0]
    rw [sk] at hf
    have whole : bytesAt s'.mem (Buf.addr s₀ ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩)
        (4 * (256 * (p.ℓ + 2 * p.k))) =
        bytesAt s₀.mem (Buf.addr s₀ ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩) (4 * (256 * (p.ℓ + 2 * p.k))) := by
      rw [hb]; exact h.1.1.roBytes hp hS rfl
    have sl := congrArg (fun l => (l.drop (1024 * i)).take 1024) whole
    rw [Proof.MlKem.bytesAt_slice _ _ (by omega), Proof.MlKem.bytesAt_slice _ _ (by omega),
      Buf.addr_eq hp hDo, Buf.addr_eq hp hS, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add] at sl
    have e1 : oP (5 + 2 * p.k + 2 * p.ℓ) + 1024 * i = oP (5 + 2 * p.k + 2 * p.ℓ + i) := by simp only [oP]; omega
    have e2 : p.skLen + 1024 * i = p.skLen + 4 * Spec.MlDsa.n * i := by simp only [Spec.MlDsa.n]
    rw [e1, e2] at sl
    exact PreparedKey.polyIs_of_copy sl hf

theorem pPub_of {s₀ s₀' : State} (h : (Proof.MlDsa.preparedSignContract p X86.abi 136).pub s₀ s₀') :
    EPub p (preparedSecretKeyBytes p) s₀ s₀' := by
  sig_pub [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4⟩ := h
  refine ⟨⟨e₁, fun i hi => ?_, rfl⟩, ?_⟩
  · rw [ye_n] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [a0, a1, a2, a3, a4]
  · simp only [eSk, eMu, eRnd, eaddr0]
    exact e₂

/-- `vg_mldsa*_sign_prepared`, a leaf around `prep_piece`. -/
theorem prep_leaf {n : String} {f : Prog isa} (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) (ps : VG.Proof.MlDsa.X86.Sign.PS p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo 4 .edi ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩ ++
      ptrTo 4 .ebp ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (256 * (p.ℓ + 2 * p.k))))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hsp' : NoSp (entryBody p (copyKeys p) n f)) :
    Piece (fun s => TPre (YE p (preparedSecretKeyBytes p)) s ∧ PSK p s) (EPub p (preparedSecretKeyBytes p))
      (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (CoreDone p s₀) s₀ s') (signPrepared p n f) := by
  have hb : Piece (fun s => TPre (YE p (preparedSecretKeyBytes p)) s ∧ PSK p s) (EPub p (preparedSecretKeyBytes p))
      (fun s₀ s => s = P0 s₀) (fun s₀ s' => Ctx (YE p (preparedSecretKeyBytes p)) s₀ s' ∧ CoreDone p s₀ s')
      (entryBody p (copyKeys p) n f) :=
    { wp := fun s₀ s h₀ ha => (prep_piece hv hsp hst ps tt t₁ t₂).wp s₀ s h₀.1 ⟨ha, h₀.2⟩
      ct := fun s₀ s₀' h₀ h₀' hq => ((prep_piece hv hsp hst ps tt t₁ t₂).ct s₀ s₀' h₀.1 h₀'.1 hq).mono
        (fun _ _ ⟨a, a'⟩ => ⟨⟨a, h₀.2⟩, ⟨a', h₀'.2⟩⟩) fun _ _ h => h }
  exact Piece.leaf (W (YE p (preparedSecretKeyBytes p))) hsp' (fun _ hp => ⟨hp.1.E0_big, by have := hp.1.sp'; omega⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1.1) (hb.mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h.2⟩)

/-- `vg_mldsa{44,65,87}_sign_prepared`, calling a core verified against
`signCoreContract`, is verified against `preparedSignContract` (given that
its precondition can hold, which a run of `vg_mldsa*_prepare_signing_key`
shows). -/
theorem prepared_verified {n : String} {f : Prog isa} (h3 : VG.Proof.MlDsa.X86.Sign.Ok3 p)
    (hv : Verified X86.target f (signCoreContract p X86.abi 96))
    (hsp : NoSp f) (hst : stackUse f ≤ 96) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs 4 VG.Impl.MlDsa.X86.KeyGen.argRegs (coreArgs p))) ht).isSome = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo 4 .edi ⟨0, p.skLen, 4 * (256 * (p.ℓ + 2 * p.k))⟩ ++
      ptrTo 4 .ebp ⟨4, oP (5 + 2 * p.k + 2 * p.ℓ), 4 * (256 * (p.ℓ + 2 * p.k))⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (256 * (p.ℓ + 2 * p.k))))] : List Instr))) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.edi, .ebp, .ecx]) (.loop (.block [.mov .eax (.mem (at_ .edi 0)),
      .store (at_ .ebp 0) .eax, .alu .add .edi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .ecx (.imm 1)]) .ne)
      h₂).isSome = true)
    (hsp' : NoSp (entryBody p (copyKeys p) n f))
    (hsat : ∃ s, (Proof.MlDsa.preparedSignContract p X86.abi 136).pre s) :
    Verified X86.target (signPrepared p n f) (Proof.MlDsa.preparedSignContract p X86.abi 136) := by
  have ps := VG.Proof.MlDsa.X86.Sign.PS.of h3
  refine Piece.verified (((prep_leaf hv hsp hst ps tt t₁ t₂ hsp').pre_mono (fun _ h => pPre_of h)
    fun _ _ _ _ h => pPub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) hsat
  obtain ⟨habi, -, -, s, hd, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [Proof.MlDsa.preparedSignContract, Proof.MlDsa.preparedSignSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
  rw [sw_app, hax, hm]
  unfold CoreDone at hd
  simp only [eSk, eMu, eRnd, eaddr0] at hd
  exact hd

end

end VG.Proof.MlDsa.X86.SignEntry
